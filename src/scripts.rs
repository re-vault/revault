//! # Revault Miniscript descriptors
//!
//! Miniscript descriptors compilation and handling for policies specific to the Revault
//! architecture.
//!
//! We use [miniscript](http://bitcoin.sipa.be/miniscript/) in order to "safely" compile,
//! derive, and satisfy Scripts depending on the setup configuration (ie the number of
//! stakeholders, the number of fund managers, and the relative timelock) for all script
//! but the (unknown) Emergency one.
//!
//! **NOTE**: the compilation functions are not safe to reuse after initial set up, as the
//! returned descriptors are non-deterministically compiled from an abstract policy.
//! Backup the output Miniscript descriptors instead.

use crate::error::*;

use miniscript::{
    bitcoin::{secp256k1, util::bip32, Address, PublicKey},
    descriptor::{DescriptorPublicKey, Wildcard, WshInner},
    miniscript::{
        iter::PkPkh,
        limits::{SEQUENCE_LOCKTIME_DISABLE_FLAG, SEQUENCE_LOCKTIME_TYPE_FLAG},
    },
    policy::concrete::Policy,
    Descriptor, ForEachKey, MiniscriptKey, Segwitv0, Terminal, TranslatePk2,
};

use std::{
    fmt::{self, Display},
    str::FromStr,
};

#[cfg(feature = "use-serde")]
use serde::de;

/// Flag applied to the nSequence and CSV value before comparing them.
///
/// <https://github.com/bitcoin/bitcoin/blob/4a540683ec40393d6369da1a9e02e45614db936d/src/primitives/transaction.h#L87-L89>
pub const SEQUENCE_LOCKTIME_MASK: u32 = 0x00_00_ff_ff;

// These are useful to create TxOuts out of the right Script descriptor

macro_rules! impl_descriptor_newtype {
    ($struct_name:ident, $derived_struct_name:ident, $doc_comment:meta, $der_doc_comment:meta) => {
        #[$doc_comment]
        #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $struct_name(Descriptor<DescriptorPublicKey>);

        #[$der_doc_comment]
        #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
        pub struct $derived_struct_name(Descriptor<PublicKey>);

        impl $struct_name {
            pub fn inner(&self) -> &Descriptor<DescriptorPublicKey> {
                &self.0
            }

            pub fn into_inner(self) -> Descriptor<DescriptorPublicKey> {
                self.0
            }

            /// Derives all wildcard keys in the descriptor using the supplied `child_number`
            pub fn derive<C: secp256k1::Verification>(
                &self,
                child_number: bip32::ChildNumber,
                secp: &secp256k1::Secp256k1<C>,
            ) -> $derived_struct_name {
                $derived_struct_name(
                    self.0
                        .derive(child_number.into())
                        .translate_pk2(|xpk| xpk.derive_public_key(secp))
                        .expect("All pubkeys are derived, no wildcard."),
                )
            }
        }

        impl $derived_struct_name {
            pub fn inner(&self) -> &Descriptor<PublicKey> {
                &self.0
            }

            pub fn into_inner(self) -> Descriptor<PublicKey> {
                self.0
            }
        }
    };
}

impl_descriptor_newtype!(
    DepositDescriptor,
    DerivedDepositDescriptor,
    doc = "A **generalistic** (with wildcard xpubs) deposit Miniscript descriptor.",
    doc = "A **concrete** (with raw public keys) deposit Miniscript descriptor. "
);

impl_descriptor_newtype!(
    UnvaultDescriptor,
    DerivedUnvaultDescriptor,
    doc = "A **generalistic** (with wildcard xpubs) Unvault miniscript descriptor.",
    doc = "A **concrete** (with raw public keys) Unvault miniscript descriptor."
);

impl_descriptor_newtype!(
    CpfpDescriptor,
    DerivedCpfpDescriptor,
    doc = "A **generalistic** (with wildcard xpubs) CPFP miniscript descriptor.",
    doc = "A **concrete** (with raw public keys) CPFP miniscript descriptor."
);

macro_rules! deposit_desc_checks {
    ($stakeholders:ident) => {
        if $stakeholders.len() < 2 {
            return Err(ScriptCreationError::BadParameters);
        }
    };
}

macro_rules! deposit_desc {
    ($stakeholders:ident) => {{
        let pubkeys = $stakeholders
            .into_iter()
            .map(Policy::Key)
            .collect::<Vec<Policy<_>>>();

        let policy = Policy::Threshold(pubkeys.len(), pubkeys);

        // This handles the non-safe or malleable cases.
        let ms = policy.compile::<Segwitv0>()?;
        Descriptor::new_wsh(ms)?
    }};
}

macro_rules! unvault_desc_checks {
    ($stakeholders:ident,$managers:ident, $managers_threshold:ident, $cosigners:ident, $csv_value:ident) => {
        if $stakeholders.is_empty()
            || $managers.is_empty()
            || $cosigners.len() != $stakeholders.len()
        {
            return Err(ScriptCreationError::BadParameters);
        }

        if $managers_threshold > $managers.len() {
            return Err(ScriptCreationError::BadParameters);
        }

        // We require the locktime to:
        //  - not be disabled
        //  - be in number of blocks
        //  - be 'clean' / minimal, ie all bits without consensus meaning should be 0
        if ($csv_value & SEQUENCE_LOCKTIME_DISABLE_FLAG) != 0
            || ($csv_value & SEQUENCE_LOCKTIME_TYPE_FLAG) != 0
            || ($csv_value & SEQUENCE_LOCKTIME_MASK) != $csv_value
        {
            return Err(ScriptCreationError::BadParameters);
        }
    };
}

macro_rules! unvault_desc {
    ($stakeholders:ident, $managers:ident, $managers_threshold:ident, $cosigners:ident, $csv_value:ident) => {{
        let mut pubkeys = $managers
            .into_iter()
            .map(Policy::Key)
            .collect::<Vec<Policy<_>>>();
        let spenders_thres = Policy::Threshold($managers_threshold, pubkeys);

        pubkeys = $stakeholders
            .into_iter()
            .map(Policy::Key)
            .collect::<Vec<Policy<_>>>();
        let stakeholders_thres = Policy::Threshold(pubkeys.len(), pubkeys);

        pubkeys = $cosigners
            .into_iter()
            .map(Policy::Key)
            .collect::<Vec<Policy<_>>>();
        let cosigners_thres = Policy::Threshold(pubkeys.len(), pubkeys);

        let cosigners_and_csv = Policy::And(vec![cosigners_thres, Policy::Older($csv_value)]);

        let managers_and_cosigners_and_csv = Policy::And(vec![spenders_thres, cosigners_and_csv]);

        let policy = Policy::Or(vec![
            (1, stakeholders_thres),
            (9, managers_and_cosigners_and_csv),
        ]);

        // This handles the non-safe or malleable cases.
        let ms = policy.compile::<Segwitv0>()?;

        Descriptor::new_wsh(ms)?
    }};
}

// Check all xpubs contain a wildcard
fn check_deriveable<'a>(
    keys: impl Iterator<Item = &'a DescriptorPublicKey>,
) -> Result<(), ScriptCreationError> {
    for key in keys {
        match key {
            DescriptorPublicKey::XPub(xpub) => {
                if matches!(xpub.wildcard, Wildcard::None) {
                    return Err(ScriptCreationError::NonWildcardKeys);
                }
            }
            DescriptorPublicKey::SinglePub(_) => {
                return Err(ScriptCreationError::NonWildcardKeys);
            }
        }
    }

    Ok(())
}

impl DepositDescriptor {
    /// Get the xpub miniscript descriptor for deposit outputs.
    ///
    /// The deposit policy is an N-of-N, so `thresh(len(all_pubkeys), all_pubkeys)`.
    ///
    /// # Examples
    /// ```rust
    /// use revault_tx::{scripts, miniscript::{bitcoin::{self, secp256k1, util::bip32}, DescriptorPublicKey, DescriptorTrait}};
    /// use std::str::FromStr;
    ///
    /// let first_stakeholder = DescriptorPublicKey::from_str("xpub6EHLFGpTTiZgHAHfBJ1LoepGFX5iyLeZ6CVtF9HhzeB1dkxLsEfkiJda78EKhSXuo2m8gQwAs4ZAbqaJixFYHMFWTL9DJX1KsAXS2VY5JJx/*").unwrap();
    /// let second_stakeholder = DescriptorPublicKey::from_str("xpub6F2U61Uh9FNX94mZE6EgdZ3p5Wg8af6MHzFhskEskkAZ9ns2uvsnHBskU47wYY63yiYv8WufvTuHCePwUjK9zhKT1Cce8JGLBptncpvALw6/*").unwrap();
    ///
    /// let deposit_descriptor =
    ///     scripts::DepositDescriptor::new(vec![first_stakeholder, second_stakeholder]).expect("Compiling descriptor");
    /// println!("Deposit descriptor: {}", deposit_descriptor);
    ///
    /// let desc_str = deposit_descriptor.to_string();
    /// assert_eq!(deposit_descriptor, scripts::DepositDescriptor::from_str(&desc_str).unwrap());
    ///
    /// let secp = secp256k1::Secp256k1::verification_only();
    /// println!("Tenth child witness script: {}", deposit_descriptor.derive(bip32::ChildNumber::from(10), &secp).inner().explicit_script());
    /// ```
    ///
    /// # Errors
    /// - If the given `DescriptorPublickKey`s are not wildcards (can be derived from).
    /// - If the given vector contains less than 2 public keys.
    /// - If the policy compilation to miniscript failed, which should not happen (tm) and would be a
    /// bug.
    pub fn new(
        stakeholders: Vec<DescriptorPublicKey>,
    ) -> Result<DepositDescriptor, ScriptCreationError> {
        deposit_desc_checks!(stakeholders);
        check_deriveable(stakeholders.iter())?;

        Ok(DepositDescriptor(deposit_desc!(stakeholders)))
    }

    /// Get the stakeholders xpubs used in this deposit descriptor.
    pub fn xpubs(&self) -> Vec<DescriptorPublicKey> {
        let ms = match self.0 {
            Descriptor::Wsh(ref wsh) => match wsh.as_inner() {
                WshInner::Ms(ms) => ms,
                WshInner::SortedMulti(_) => {
                    unreachable!("Deposit descriptor is not a sorted multi")
                }
            },
            _ => unreachable!("Deposit descriptor is always a P2WSH"),
        };

        // For DescriptorPublicKey, Pk::Hash == Self.
        ms.iter_pk_pkh()
            .map(|pkpkh| match pkpkh {
                PkPkh::PlainPubkey(xpub) => xpub,
                PkPkh::HashedPubkey(xpub) => xpub,
            })
            .collect()
    }
}

impl Display for DepositDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl FromStr for DepositDescriptor {
    type Err = ScriptCreationError;

    fn from_str(s: &str) -> Result<DepositDescriptor, Self::Err> {
        let desc: Descriptor<DescriptorPublicKey> = FromStr::from_str(s)?;

        if !desc.for_each_key(|k| k.as_key().is_deriveable()) {
            return Err(ScriptCreationError::NonWildcardKeys);
        }

        Ok(DepositDescriptor(desc))
    }
}

impl DerivedDepositDescriptor {
    /// Get the derived miniscript descriptor for deposit outputs.
    ///
    /// The deposit policy is an N-of-N, so `thresh(len(all_pubkeys), all_pubkeys)`.
    ///
    /// # Examples
    /// ```rust
    /// use revault_tx::{scripts, miniscript::{bitcoin::{self, secp256k1, util::bip32, PublicKey}, DescriptorTrait}};
    /// use std::str::FromStr;
    ///
    /// let first_stakeholder = PublicKey::from_str("02a17786aca5ea2118e9209702454ab432d5b2c656f8ae19447d4ff3e7317d3b41").unwrap();
    /// let second_stakeholder = PublicKey::from_str("036edaec85bb1eee1a19ca9f9fd5620134ec98bc21cc14c4e8e3d0f8f121e1b6d1").unwrap();
    ///
    /// let deposit_descriptor =
    ///     scripts::DerivedDepositDescriptor::new(vec![first_stakeholder, second_stakeholder]).expect("Compiling descriptor");
    /// println!("Concrete deposit descriptor: {}", deposit_descriptor);
    ///
    /// let desc_str = deposit_descriptor.to_string();
    /// assert_eq!(deposit_descriptor, scripts::DerivedDepositDescriptor::from_str(&desc_str).unwrap());
    /// ```
    ///
    /// # Errors
    /// - If the given vector contains less than 2 public keys.
    /// - If the policy compilation to miniscript failed, which should not happen (tm) and would be a
    /// bug.
    pub fn new(
        stakeholders: Vec<PublicKey>,
    ) -> Result<DerivedDepositDescriptor, ScriptCreationError> {
        deposit_desc_checks!(stakeholders);

        Ok(DerivedDepositDescriptor(deposit_desc!(stakeholders)))
    }
}

impl Display for DerivedDepositDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl FromStr for DerivedDepositDescriptor {
    type Err = ScriptCreationError;

    fn from_str(s: &str) -> Result<DerivedDepositDescriptor, Self::Err> {
        let desc: Descriptor<PublicKey> = FromStr::from_str(s)?;

        Ok(DerivedDepositDescriptor(desc))
    }
}

fn unvault_descriptor_csv<Pk: MiniscriptKey>(desc: &Descriptor<Pk>) -> u32 {
    let ms = match desc {
        Descriptor::Wsh(ref wsh) => match wsh.as_inner() {
            WshInner::Ms(ms) => ms,
            WshInner::SortedMulti(_) => unreachable!("Unvault descriptor is not a sorted multi"),
        },
        _ => unreachable!("Unvault descriptor is always a P2WSH"),
    };

    let csv_frag = ms
        .iter()
        .find(|ms| matches!(ms.node, Terminal::Older(_)))
        .expect("Unvault Miniscript always contains a CSV fragment");
    match csv_frag.node {
        Terminal::Older(csv_value) => csv_value,
        _ => unreachable!("Just matched."),
    }
}

impl UnvaultDescriptor {
    /// Get the miniscript descriptors for Unvault outputs.
    ///
    /// The Unvault policy allows either all the stakeholders to spend, or (the fund managers + the cosigners)
    /// after a timelock.
    ///
    /// # Examples
    /// ```rust
    /// use revault_tx::{scripts, miniscript::{bitcoin::{self, secp256k1, util::bip32}, DescriptorPublicKey, DescriptorTrait}};
    /// use std::str::FromStr;
    ///
    /// let first_stakeholder = DescriptorPublicKey::from_str("xpub6EHLFGpTTiZgHAHfBJ1LoepGFX5iyLeZ6CVtF9HhzeB1dkxLsEfkiJda78EKhSXuo2m8gQwAs4ZAbqaJixFYHMFWTL9DJX1KsAXS2VY5JJx/*").unwrap();
    /// let second_stakeholder = DescriptorPublicKey::from_str("xpub6F2U61Uh9FNX94mZE6EgdZ3p5Wg8af6MHzFhskEskkAZ9ns2uvsnHBskU47wYY63yiYv8WufvTuHCePwUjK9zhKT1Cce8JGLBptncpvALw6/*").unwrap();
    /// let third_stakeholder = DescriptorPublicKey::from_str("xpub6Br1DUfrzxTVGo1sanuKDCUmSxDfLRrxLQBqpMqygkQLkQWodoyvvGtUV8Rp3r6d6BNYvedBSU8c7whhn2U8haRVxsWwuQiZ9LoFp7jXPQA/*").unwrap();
    ///
    /// let first_cosig = DescriptorPublicKey::from_str("02a489e0ea42b56148d212d325b7c67c6460483ff931c303ea311edfef667c8f35").unwrap();
    /// let second_cosig = DescriptorPublicKey::from_str("02767e6dde4877dcbf64de8a45fe1a0575dfc6b0ed06648f1022412c172ebd875c").unwrap();
    /// let third_cosig = DescriptorPublicKey::from_str("0371cdea381b365ea159a3cf4f14029d1bff5b36b4cf12ac9e42be6955d2ed4ecf").unwrap();
    ///
    /// let first_manager = DescriptorPublicKey::from_str("xpub6Duq1ob3cQ8Wxees2fTGNK2wTsVjgTPQcKJiPquXY2rQJTDjeCxkXFxTCGhcunFDt26Ddz45KQu7pbLmmUGG2PXTRVx3iDpBPEhdrijJf4U/*").unwrap();
    /// let second_manager = DescriptorPublicKey::from_str("xpub6EWL35hY9uZZs5Ljt6J3G2ZK1Tu4GPVkFdeGvMknG3VmwVRHhtadCaw5hdRDBgrmx1nPVHWjGBb5xeuC1BfbJzjjcic2gNm1aA7ywWjj7G8/*").unwrap();
    ///
    ///
    /// let unvault_descriptor = scripts::UnvaultDescriptor::new(
    ///     vec![first_stakeholder, second_stakeholder, third_stakeholder],
    ///     vec![first_manager, second_manager],
    ///     1,
    ///     // Cosigners
    ///     vec![first_cosig, second_cosig, third_cosig],
    ///     // CSV
    ///     42
    /// ).expect("Compiling descriptor");
    /// println!("Unvault descriptor: {}", unvault_descriptor);
    ///
    /// let desc_str = unvault_descriptor.to_string();
    /// assert_eq!(unvault_descriptor, scripts::UnvaultDescriptor::from_str(&desc_str).unwrap());
    ///
    /// let secp = secp256k1::Secp256k1::verification_only();
    /// println!("Tenth child witness script: {}", unvault_descriptor.derive(bip32::ChildNumber::from(10), &secp).inner().explicit_script());
    /// ```
    ///
    /// # Errors
    /// - If the given `DescriptorPublickKey`s are not wildcards (can be derived from).
    /// - If any of the slice contains no public key, or if the number of non_managers public keys is
    /// not the same as the number of cosigners public key.
    /// - If the policy compilation to miniscript failed, which should not happen (tm) and would be a
    /// bug.
    pub fn new(
        stakeholders: Vec<DescriptorPublicKey>,
        managers: Vec<DescriptorPublicKey>,
        managers_threshold: usize,
        cosigners: Vec<DescriptorPublicKey>,
        csv_value: u32,
    ) -> Result<UnvaultDescriptor, ScriptCreationError> {
        unvault_desc_checks!(
            stakeholders,
            managers,
            managers_threshold,
            cosigners,
            csv_value
        );

        // Stakeholders' and managers' must be deriveable xpubs.
        check_deriveable(stakeholders.iter().chain(managers.iter()))?;

        // Cosigners' key may not be. We use DescriptorSinglePub for them downstream with static raw
        // keys, but it's not hardcoded into the type system there to allow a more generic usage.

        Ok(UnvaultDescriptor(unvault_desc!(
            stakeholders,
            managers,
            managers_threshold,
            cosigners,
            csv_value
        )))
    }

    /// Get the relative locktime in blocks contained in the Unvault descriptor
    pub fn csv_value(&self) -> u32 {
        unvault_descriptor_csv(&self.0)
    }

    /// Get all the xpubs used in this Unvault descriptor.
    pub fn xpubs(&self) -> Vec<DescriptorPublicKey> {
        let ms = match self.0 {
            Descriptor::Wsh(ref wsh) => match wsh.as_inner() {
                WshInner::Ms(ms) => ms,
                WshInner::SortedMulti(_) => {
                    unreachable!("Unvault descriptor is not a sorted multi")
                }
            },
            _ => unreachable!("Unvault descriptor is always a P2WSH"),
        };

        // For DescriptorPublicKey, Pk::Hash == Self.
        ms.iter_pk_pkh()
            .map(|pkpkh| match pkpkh {
                PkPkh::PlainPubkey(xpub) => xpub,
                PkPkh::HashedPubkey(xpub) => xpub,
            })
            .collect()
    }
}

impl Display for UnvaultDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl FromStr for UnvaultDescriptor {
    type Err = ScriptCreationError;

    fn from_str(s: &str) -> Result<UnvaultDescriptor, Self::Err> {
        let desc: Descriptor<DescriptorPublicKey> = FromStr::from_str(s)?;

        if !desc.for_each_key(|k| match k.as_key() {
            DescriptorPublicKey::SinglePub(_) => true, // For cosigning servers keys
            DescriptorPublicKey::XPub(xpub) => xpub.wildcard != Wildcard::None,
        }) {
            return Err(ScriptCreationError::NonWildcardKeys);
        }

        Ok(UnvaultDescriptor(desc))
    }
}

impl DerivedUnvaultDescriptor {
    /// Get the miniscript descriptors for Unvault outputs.
    ///
    /// The Unvault policy allows either all the stakeholders to spend, or (the fund managers + the cosigners)
    /// after a timelock.
    ///
    /// # Examples
    /// ```rust
    /// use revault_tx::{scripts, miniscript::{bitcoin::{self, secp256k1, util::bip32, PublicKey}, DescriptorTrait}};
    /// use std::str::FromStr;
    ///
    /// let first_stakeholder = PublicKey::from_str("0372f4bb19ecf98d7849148b4f40375d2fcef624a1b56fef94489ad012bc11b4df").unwrap();
    /// let second_stakeholder = PublicKey::from_str("036e7ac7a096270f676b53e9917942cf42c6fb9607e3bc09775b5209c908525e80").unwrap();
    /// let third_stakeholder = PublicKey::from_str("03a02e93cf8c47b250075b0af61f96ebd10376c0aaa7635148e889cb2b51c96927").unwrap();
    ///
    /// let first_cosig = PublicKey::from_str("02a489e0ea42b56148d212d325b7c67c6460483ff931c303ea311edfef667c8f35").unwrap();
    /// let second_cosig = PublicKey::from_str("02767e6dde4877dcbf64de8a45fe1a0575dfc6b0ed06648f1022412c172ebd875c").unwrap();
    /// let third_cosig = PublicKey::from_str("0371cdea381b365ea159a3cf4f14029d1bff5b36b4cf12ac9e42be6955d2ed4ecf").unwrap();
    ///
    /// let first_manager = PublicKey::from_str("03d33a510c0376a3d19ffa0e1ba71d5ee0cbfebbce2df0996b51262142e943c6f0").unwrap();
    /// let second_manager = PublicKey::from_str("030e7d7e1d8014dc17d63057ffc3ef26590bf237ce50054fb4f612be8e0a0dbe2a").unwrap();
    ///
    ///
    /// let unvault_descriptor = scripts::DerivedUnvaultDescriptor::new(
    ///     vec![first_stakeholder, second_stakeholder, third_stakeholder],
    ///     vec![first_manager, second_manager],
    ///     1,
    ///     // Cosigners
    ///     vec![first_cosig, second_cosig, third_cosig],
    ///     // CSV
    ///     42
    /// ).expect("Compiling descriptor");
    /// println!("Unvault descriptor: {}", unvault_descriptor);
    ///
    /// let desc_str = unvault_descriptor.to_string();
    /// assert_eq!(unvault_descriptor, scripts::DerivedUnvaultDescriptor::from_str(&desc_str).unwrap());
    /// ```
    ///
    /// # Errors
    /// - If any of the given vectors contains no public key, or if the number of stakeholders public keys
    /// is not the same as the number of cosigners public keys.
    /// - If the policy compilation to miniscript failed, which should not happen (tm) and would be a
    /// bug.
    pub fn new(
        stakeholders: Vec<PublicKey>,
        managers: Vec<PublicKey>,
        managers_threshold: usize,
        cosigners: Vec<PublicKey>,
        csv_value: u32,
    ) -> Result<DerivedUnvaultDescriptor, ScriptCreationError> {
        unvault_desc_checks!(
            stakeholders,
            managers,
            managers_threshold,
            cosigners,
            csv_value
        );

        Ok(DerivedUnvaultDescriptor(unvault_desc!(
            stakeholders,
            managers,
            managers_threshold,
            cosigners,
            csv_value
        )))
    }

    /// Get the relative locktime in blocks contained in the Unvault descriptor
    pub fn csv_value(&self) -> u32 {
        unvault_descriptor_csv(&self.0)
    }
}

impl Display for DerivedUnvaultDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl FromStr for DerivedUnvaultDescriptor {
    type Err = ScriptCreationError;

    fn from_str(s: &str) -> Result<DerivedUnvaultDescriptor, Self::Err> {
        let desc: Descriptor<PublicKey> = FromStr::from_str(s)?;

        Ok(DerivedUnvaultDescriptor(desc))
    }
}

macro_rules! cpfp_descriptor {
    ($managers: ident) => {{
        let pubkeys = $managers
            .into_iter()
            .map(Policy::Key)
            .collect::<Vec<Policy<_>>>();

        let policy = Policy::Threshold(1, pubkeys);

        // This handles the non-safe or malleable cases.
        let ms = policy.compile::<Segwitv0>()?;
        Descriptor::new_wsh(ms)?
    }};
}

impl CpfpDescriptor {
    /// Get the miniscript descriptor for the Unvault transaction CPFP output.
    ///
    /// It's a basic 1-of-N between the fund managers.
    ///
    /// # Examples
    /// ```rust
    /// use revault_tx::{scripts, miniscript::{bitcoin::{self, secp256k1, util::bip32}, DescriptorPublicKey, DescriptorTrait}};
    /// use std::str::FromStr;
    ///
    /// let first_manager = DescriptorPublicKey::from_str("xpub6EHLFGpTTiZgHAHfBJ1LoepGFX5iyLeZ6CVtF9HhzeB1dkxLsEfkiJda78EKhSXuo2m8gQwAs4ZAbqaJixFYHMFWTL9DJX1KsAXS2VY5JJx/*").unwrap();
    /// let second_manager = DescriptorPublicKey::from_str("xpub6F2U61Uh9FNX94mZE6EgdZ3p5Wg8af6MHzFhskEskkAZ9ns2uvsnHBskU47wYY63yiYv8WufvTuHCePwUjK9zhKT1Cce8JGLBptncpvALw6/*").unwrap();
    ///
    /// let cpfp_descriptor =
    ///     scripts::CpfpDescriptor::new(vec![first_manager, second_manager]).expect("Compiling descriptor");
    /// println!("CPFP descriptor: {}", cpfp_descriptor);
    ///
    /// let secp = secp256k1::Secp256k1::verification_only();
    /// println!("Tenth child witness script: {}", cpfp_descriptor.derive(bip32::ChildNumber::from(10), &secp).inner().explicit_script());
    /// ```
    ///
    /// let desc_str = cpfp_descriptor.to_string();
    /// assert_eq!(cpfp_descriptor, scripts::CpfpDescriptor::from_str(&desc_str).unwrap());
    ///
    /// # Errors
    /// - If the given `DescriptorPublickKey`s are not wildcards (can be derived from).
    /// - If the policy compilation to miniscript failed, which should not happen (tm) and would be a
    /// bug.
    pub fn new(managers: Vec<DescriptorPublicKey>) -> Result<CpfpDescriptor, ScriptCreationError> {
        check_deriveable(managers.iter())?;

        Ok(CpfpDescriptor(cpfp_descriptor!(managers)))
    }

    /// Get all the xpubs used in this Cpfp descriptor.
    pub fn xpubs(&self) -> Vec<DescriptorPublicKey> {
        let ms = match self.0 {
            Descriptor::Wsh(ref wsh) => match wsh.as_inner() {
                WshInner::Ms(ms) => ms,
                WshInner::SortedMulti(_) => {
                    unreachable!("Cpfp descriptor is not a sorted multi")
                }
            },
            _ => unreachable!("Cpfp descriptor is always a P2WSH"),
        };

        // For DescriptorPublicKey, Pk::Hash == Self.
        ms.iter_pk_pkh()
            .map(|pkpkh| match pkpkh {
                PkPkh::PlainPubkey(xpub) => xpub,
                PkPkh::HashedPubkey(xpub) => xpub,
            })
            .collect()
    }
}

impl Display for CpfpDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl FromStr for CpfpDescriptor {
    type Err = ScriptCreationError;

    fn from_str(s: &str) -> Result<CpfpDescriptor, Self::Err> {
        let desc: Descriptor<DescriptorPublicKey> = FromStr::from_str(s)?;

        if !desc.for_each_key(|k| k.as_key().is_deriveable()) {
            return Err(ScriptCreationError::NonWildcardKeys);
        }

        Ok(CpfpDescriptor(desc))
    }
}

impl DerivedCpfpDescriptor {
    /// Get the miniscript descriptor for the Unvault transaction CPFP output.
    ///
    /// It's a basic 1-of-N between the fund managers.
    ///
    /// # Examples
    /// ```rust
    /// use revault_tx::{scripts, miniscript::{bitcoin::{self, secp256k1, util::bip32, PublicKey}, DescriptorTrait}};
    /// use std::str::FromStr;
    ///
    /// let first_manager = PublicKey::from_str("02a17786aca5ea2118e9209702454ab432d5b2c656f8ae19447d4ff3e7317d3b41").unwrap();
    /// let second_manager = PublicKey::from_str("036edaec85bb1eee1a19ca9f9fd5620134ec98bc21cc14c4e8e3d0f8f121e1b6d1").unwrap();
    ///
    /// let cpfp_descriptor =
    ///     scripts::DerivedCpfpDescriptor::new(vec![first_manager, second_manager]).expect("Compiling descriptor");
    /// println!("Concrete CPFP descriptor: {}", cpfp_descriptor);
    ///
    /// let desc_str = cpfp_descriptor.to_string();
    /// assert_eq!(cpfp_descriptor, scripts::DerivedCpfpDescriptor::from_str(&desc_str).unwrap());
    /// ```
    ///
    /// # Errors
    /// - If the policy compilation to miniscript failed, which should not happen (tm) and would be a
    /// bug.
    pub fn new(managers: Vec<PublicKey>) -> Result<DerivedCpfpDescriptor, ScriptCreationError> {
        Ok(DerivedCpfpDescriptor(cpfp_descriptor!(managers)))
    }
}

impl Display for DerivedCpfpDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl FromStr for DerivedCpfpDescriptor {
    type Err = ScriptCreationError;

    fn from_str(s: &str) -> Result<DerivedCpfpDescriptor, Self::Err> {
        let desc: Descriptor<PublicKey> = FromStr::from_str(s)?;

        Ok(DerivedCpfpDescriptor(desc))
    }
}

/// The "Emergency address", it's kept obfuscated for the entire duration of the vault and is
/// necessarily a v0 P2WSH
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EmergencyAddress(Address);
impl EmergencyAddress {
    /// Create a new Emergency Address. Will error if the address isn't a v0 P2WSH
    pub fn from(address: Address) -> Result<EmergencyAddress, ScriptCreationError> {
        if address.script_pubkey().is_v0_p2wsh() {
            Ok(EmergencyAddress(address))
        } else {
            Err(ScriptCreationError::BadParameters)
        }
    }

    /// Get the address
    pub fn address(&self) -> &Address {
        &self.0
    }

    /// Get the address
    pub fn into_address(self) -> Address {
        self.0
    }
}

impl fmt::Display for EmergencyAddress {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "{}", &self.0)
    }
}

#[cfg(feature = "use-serde")]
impl<'de> de::Deserialize<'de> for EmergencyAddress {
    fn deserialize<D>(deserializer: D) -> Result<EmergencyAddress, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        // FIXME: the windows CI build is preventing us from using the 'use-serde' feature of
        // rust-bitcoin.
        let addr_str = String::deserialize(deserializer)?;
        let addr = Address::from_str(&addr_str).map_err(|e| de::Error::custom(e))?;
        EmergencyAddress::from(addr).map_err(de::Error::custom)
    }
}

#[cfg(test)]
mod tests {

    use super::{
        CpfpDescriptor, DepositDescriptor, DerivedCpfpDescriptor, DerivedDepositDescriptor,
        DerivedUnvaultDescriptor, PublicKey, ScriptCreationError, UnvaultDescriptor,
    };

    use miniscript::{
        bitcoin::{secp256k1, util::bip32, Network},
        descriptor::{DescriptorPublicKey, DescriptorXKey, Wildcard},
        policy::compiler::CompilerError,
    };
    use std::{iter::repeat_with, str::FromStr};

    fn rand_xpub<C: secp256k1::Signing>(
        rng: &mut fastrand::Rng,
        secp: &secp256k1::Secp256k1<C>,
    ) -> bip32::ExtendedPrivKey {
        let rand_bytes: Vec<u8> = repeat_with(|| rng.u8(..)).take(64).collect();

        bip32::ExtendedPrivKey::new_master(Network::Bitcoin, &rand_bytes)
            .unwrap_or_else(|_| rand_xpub(rng, secp))
    }

    fn get_random_pubkey<C: secp256k1::Signing>(
        rng: &mut fastrand::Rng,
        secp: &secp256k1::Secp256k1<C>,
    ) -> DescriptorPublicKey {
        DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::ExtendedPubKey::from_private(&secp, &rand_xpub(rng, secp)),
            derivation_path: bip32::DerivationPath::from(vec![]),
            wildcard: Wildcard::Unhardened,
        })
    }

    // Sanity check we error on creating derived descriptors. Non-error cases are in doc comments.
    #[test]
    fn sanity_check_desc_creation() {
        let first_stakeholder = DescriptorPublicKey::from_str("xpub6EHLFGpTTiZgHAHfBJ1LoepGFX5iyLeZ6CVtF9HhzeB1dkxLsEfkiJda78EKhSXuo2m8gQwAs4ZAbqaJixFYHMFWTL9DJX1KsAXS2VY5JJx/*").unwrap();
        let second_stakeholder = DescriptorPublicKey::from_str("xpub6F2U61Uh9FNX94mZE6EgdZ3p5Wg8af6MHzFhskEskkAZ9ns2uvsnHBskU47wYY63yiYv8WufvTuHCePwUjK9zhKT1Cce8JGLBptncpvALw6/*").unwrap();
        let third_stakeholder = DescriptorPublicKey::from_str("xpub6Br1DUfrzxTVGo1sanuKDCUmSxDfLRrxLQBqpMqygkQLkQWodoyvvGtUV8Rp3r6d6BNYvedBSU8c7whhn2U8haRVxsWwuQiZ9LoFp7jXPQA/*").unwrap();

        let first_cosig = DescriptorPublicKey::from_str(
            "02a489e0ea42b56148d212d325b7c67c6460483ff931c303ea311edfef667c8f35",
        )
        .unwrap();
        let second_cosig = DescriptorPublicKey::from_str(
            "02767e6dde4877dcbf64de8a45fe1a0575dfc6b0ed06648f1022412c172ebd875c",
        )
        .unwrap();
        let third_cosig = DescriptorPublicKey::from_str(
            "0371cdea381b365ea159a3cf4f14029d1bff5b36b4cf12ac9e42be6955d2ed4ecf",
        )
        .unwrap();

        let first_manager = DescriptorPublicKey::from_str("xpub6Duq1ob3cQ8Wxees2fTGNK2wTsVjgTPQcKJiPquXY2rQJTDjeCxkXFxTCGhcunFDt26Ddz45KQu7pbLmmUGG2PXTRVx3iDpBPEhdrijJf4U/*").unwrap();
        let second_manager = DescriptorPublicKey::from_str("xpub6EWL35hY9uZZs5Ljt6J3G2ZK1Tu4GPVkFdeGvMknG3VmwVRHhtadCaw5hdRDBgrmx1nPVHWjGBb5xeuC1BfbJzjjcic2gNm1aA7ywWjj7G8/*").unwrap();

        // When a single xpub isn't deriveable
        let invalid_stk = DescriptorPublicKey::from_str("xpub6Br1DUfrzxTVGo1sanuKDCUmSxDfLRrxLQBqpMqygkQLkQWodoyvvGtUV8Rp3r6d6BNYvedBSU8c7whhn2U8haRVxsWwuQiZ9LoFp7jXPQA").unwrap();
        DepositDescriptor::new(vec![
            first_stakeholder.clone(),
            second_stakeholder.clone(),
            invalid_stk.clone(),
        ])
        .expect_err("Accepting a non wildcard xpub");
        DepositDescriptor::new(vec![
            first_stakeholder.clone(),
            first_cosig.clone(), // A derived key
            invalid_stk.clone(),
        ])
        .expect_err("Accepting a non wildcard xpub");

        let invalid_man = DescriptorPublicKey::from_str("xpub6EWL35hY9uZZs5Ljt6J3G2ZK1Tu4GPVkFdeGvMknG3VmwVRHhtadCaw5hdRDBgrmx1nPVHWjGBb5xeuC1BfbJzjjcic2gNm1aA7ywWjj7G8").unwrap();
        CpfpDescriptor::new(vec![
            first_manager.clone(),
            second_manager.clone(),
            invalid_man.clone(),
        ])
        .expect_err("Accepting a non wildcard xpub");

        UnvaultDescriptor::new(
            vec![
                first_stakeholder.clone(),
                second_stakeholder.clone(),
                invalid_stk.clone(),
            ],
            vec![first_manager.clone(), second_manager.clone()],
            1,
            vec![
                first_cosig.clone(),
                second_cosig.clone(),
                third_cosig.clone(),
            ],
            128,
        )
        .expect_err("Accepting a non wildcard stakeholder xpub");
        UnvaultDescriptor::new(
            vec![
                first_stakeholder.clone(),
                second_stakeholder.clone(),
                third_stakeholder.clone(),
            ],
            vec![first_manager.clone(), invalid_man],
            1,
            vec![first_cosig.clone(), second_cosig.clone(), third_cosig],
            128,
        )
        .expect_err("Accepting a non wildcard manager xpub");

        // But for cosigning servers it's fine
        let xpub_first_cosig = DescriptorPublicKey::from_str(
            "xpub6Da8z6vMdBgtfZraAEjruVSyASFbrWqSm724PPbnezQidGH5wVavF6xFKrbpGCC4VtDVnLP5J5NXm8c8do9zC6MRPkgEsxt4oPY7dukETw2",
        )
        .unwrap();
        let xpub_second_cosig = DescriptorPublicKey::from_str(
            "xpub6Cp57dqxsjzveK5XQYJmzRrofaMJLUC3zQjwNNKKWB9kPn1YtUrrPMXxXGQjs9r2RRQ7e9vExWLJinTZmaosezisGG9nTwEVV15iFQYzFfa",
        )
        .unwrap();
        UnvaultDescriptor::new(
            vec![first_stakeholder.clone(), second_stakeholder.clone()],
            vec![first_manager.clone(), second_manager.clone()],
            1,
            vec![xpub_first_cosig, xpub_second_cosig],
            128,
        )
        .expect("Refusing a non wildcard cosigning server xpub");

        let xpub_first_cosig = DescriptorPublicKey::from_str(
            "xpub6Da8z6vMdBgtfZraAEjruVSyASFbrWqSm724PPbnezQidGH5wVavF6xFKrbpGCC4VtDVnLP5J5NXm8c8do9zC6MRPkgEsxt4oPY7dukETw2/*",
        )
        .unwrap();
        let xpub_second_cosig = DescriptorPublicKey::from_str(
            "xpub6Cp57dqxsjzveK5XQYJmzRrofaMJLUC3zQjwNNKKWB9kPn1YtUrrPMXxXGQjs9r2RRQ7e9vExWLJinTZmaosezisGG9nTwEVV15iFQYzFfa/*",
        )
        .unwrap();
        UnvaultDescriptor::new(
            vec![first_stakeholder.clone(), second_stakeholder.clone()],
            vec![first_manager.clone(), second_manager.clone()],
            1,
            vec![xpub_first_cosig, xpub_second_cosig],
            128,
        )
        .expect("Refusing a wildcard cosigning server xpub");

        // You can't mess up by from_str a wildcard descriptor from a derived one, and the other
        // way around.
        let raw_pk_a = PublicKey::from_str(
            "02a489e0ea42b56148d212d325b7c67c6460483ff931c303ea311edfef667c8f35",
        )
        .unwrap();
        let raw_pk_b = PublicKey::from_str(
            "02767e6dde4877dcbf64de8a45fe1a0575dfc6b0ed06648f1022412c172ebd875c",
        )
        .unwrap();
        let raw_pk_c = PublicKey::from_str(
            "0371cdea381b365ea159a3cf4f14029d1bff5b36b4cf12ac9e42be6955d2ed4ecf",
        )
        .unwrap();
        let raw_pk_d = PublicKey::from_str(
            "03b330723c5ebc2b6f2b29b5a8429e020c0806eed0bcbbddfe5fcad2bb2d02e946",
        )
        .unwrap();
        let raw_pk_e = PublicKey::from_str(
            "02c8bd230d2a5cdd0c5716f0ebe774d5a7341e9cbcc87f4f43e39acc43a73d72a9",
        )
        .unwrap();
        let raw_pk_f = PublicKey::from_str(
            "02d07b4b45f93d161b0846a5dd1691720069d8a27baab2f85022fe78b5f896ba07",
        )
        .unwrap();

        let deposit_desc = DepositDescriptor::new(vec![
            first_stakeholder.clone(),
            second_stakeholder.clone(),
            third_stakeholder.clone(),
        ])
        .expect("Valid wildcard xpubs");
        DerivedDepositDescriptor::from_str(&deposit_desc.to_string())
            .expect_err("FromStr on an xpub descriptor");
        let der_deposit_desc =
            DerivedDepositDescriptor::new(vec![raw_pk_a.clone(), raw_pk_b.clone()])
                .expect("Derived pubkeys");
        DepositDescriptor::from_str(&der_deposit_desc.to_string())
            .expect_err("FromStr on a derived descriptor");

        let unvault_desc = UnvaultDescriptor::new(
            vec![first_stakeholder.clone(), second_stakeholder.clone()],
            vec![first_manager.clone(), second_manager.clone()],
            1,
            vec![first_cosig, second_cosig],
            128,
        )
        .expect("Valid, with xpubs");
        DerivedUnvaultDescriptor::from_str(&unvault_desc.to_string())
            .expect_err("FromStr on an xpub descriptor");
        let der_unvault_desc = DerivedUnvaultDescriptor::new(
            vec![raw_pk_a.clone(), raw_pk_b.clone()],
            vec![raw_pk_c, raw_pk_d],
            2,
            vec![raw_pk_e, raw_pk_f],
            1024,
        )
        .expect("Derived pubkeys");
        UnvaultDescriptor::from_str(&der_unvault_desc.to_string())
            .expect_err("FromStr on a derived descriptor");

        let cpfp_desc = CpfpDescriptor::new(vec![
            first_stakeholder.clone(),
            second_stakeholder.clone(),
            third_stakeholder.clone(),
        ])
        .expect("Valid wildcard xpubs");
        DerivedCpfpDescriptor::from_str(&cpfp_desc.to_string())
            .expect_err("FromStr on an xpub descriptor");
        let der_cpfp_desc =
            DerivedCpfpDescriptor::new(vec![raw_pk_a, raw_pk_b]).expect("Derived pubkeys");
        CpfpDescriptor::from_str(&der_cpfp_desc.to_string())
            .expect_err("FromStr on a derived descriptor");
    }

    #[test]
    fn test_xpubs_from_descriptor() {
        let first_stakeholder = DescriptorPublicKey::from_str("xpub6EHLFGpTTiZgHAHfBJ1LoepGFX5iyLeZ6CVtF9HhzeB1dkxLsEfkiJda78EKhSXuo2m8gQwAs4ZAbqaJixFYHMFWTL9DJX1KsAXS2VY5JJx/*").unwrap();
        let second_stakeholder = DescriptorPublicKey::from_str("xpub6F2U61Uh9FNX94mZE6EgdZ3p5Wg8af6MHzFhskEskkAZ9ns2uvsnHBskU47wYY63yiYv8WufvTuHCePwUjK9zhKT1Cce8JGLBptncpvALw6/*").unwrap();
        let third_stakeholder = DescriptorPublicKey::from_str("xpub6Br1DUfrzxTVGo1sanuKDCUmSxDfLRrxLQBqpMqygkQLkQWodoyvvGtUV8Rp3r6d6BNYvedBSU8c7whhn2U8haRVxsWwuQiZ9LoFp7jXPQA/*").unwrap();

        let first_cosig = DescriptorPublicKey::from_str(
            "02a489e0ea42b56148d212d325b7c67c6460483ff931c303ea311edfef667c8f35",
        )
        .unwrap();
        let second_cosig = DescriptorPublicKey::from_str(
            "02767e6dde4877dcbf64de8a45fe1a0575dfc6b0ed06648f1022412c172ebd875c",
        )
        .unwrap();
        let third_cosig = DescriptorPublicKey::from_str(
            "0371cdea381b365ea159a3cf4f14029d1bff5b36b4cf12ac9e42be6955d2ed4ecf",
        )
        .unwrap();

        let first_manager = DescriptorPublicKey::from_str("xpub6Duq1ob3cQ8Wxees2fTGNK2wTsVjgTPQcKJiPquXY2rQJTDjeCxkXFxTCGhcunFDt26Ddz45KQu7pbLmmUGG2PXTRVx3iDpBPEhdrijJf4U/*").unwrap();
        let second_manager = DescriptorPublicKey::from_str("xpub6EWL35hY9uZZs5Ljt6J3G2ZK1Tu4GPVkFdeGvMknG3VmwVRHhtadCaw5hdRDBgrmx1nPVHWjGBb5xeuC1BfbJzjjcic2gNm1aA7ywWjj7G8/*").unwrap();

        let deposit_desc = DepositDescriptor::new(vec![
            first_stakeholder.clone(),
            second_stakeholder.clone(),
            third_stakeholder.clone(),
        ])
        .expect("Valid wildcard xpubs");
        assert_eq!(
            deposit_desc.xpubs(),
            vec![
                first_stakeholder.clone(),
                second_stakeholder.clone(),
                third_stakeholder.clone()
            ]
        );

        let cpfp_desc = DepositDescriptor::new(vec![first_manager.clone(), second_manager.clone()])
            .expect("Valid wildcard xpubs");
        assert_eq!(
            cpfp_desc.xpubs(),
            vec![first_manager.clone(), second_manager.clone(),]
        );

        let unvault_desc = UnvaultDescriptor::new(
            vec![
                first_stakeholder.clone(),
                second_stakeholder.clone(),
                third_stakeholder.clone(),
            ],
            vec![first_manager.clone(), second_manager.clone()],
            2,
            vec![
                first_cosig.clone(),
                second_cosig.clone(),
                third_cosig.clone(),
            ],
            2018,
        )
        .expect("Valid, with xpubs");
        assert_eq!(
            unvault_desc.xpubs().sort(),
            vec![
                first_stakeholder,
                second_stakeholder,
                third_stakeholder,
                first_manager,
                second_manager,
                first_cosig,
                second_cosig,
                third_cosig
            ]
            .sort()
        );
    }

    #[test]
    fn test_possible_default_configurations() {
        // Policy compilation takes time, so just test some remarkable ones
        let configurations = [
            // Single-manager configurations
            ((1, 1), 1),
            ((1, 1), 2),
            ((1, 1), 5),
            // Multiple-manager configurations (with threshold)
            ((2, 2), 3),
            ((3, 4), 2),
            ((7, 7), 1),
            ((2, 3), 8),
            // Huge configurations
            ((15, 15), 5),
            ((20, 20), 5),
            ((7, 7), 13),
            ((8, 8), 12),
            ((3, 3), 18),
        ];
        let secp = secp256k1::Secp256k1::signing_only();

        let mut rng = fastrand::Rng::new();
        for ((thresh, n_managers), n_stakeholders) in configurations.iter() {
            let managers = (0..*n_managers)
                .map(|_| get_random_pubkey(&mut rng, &secp))
                .collect::<Vec<DescriptorPublicKey>>();
            let stakeholders = (0..*n_stakeholders)
                .map(|_| get_random_pubkey(&mut rng, &secp))
                .collect::<Vec<DescriptorPublicKey>>();
            let cosigners = (0..*n_stakeholders)
                .map(|_| get_random_pubkey(&mut rng, &secp))
                .collect::<Vec<DescriptorPublicKey>>();

            UnvaultDescriptor::new(
                stakeholders.clone(),
                managers.clone(),
                *thresh,
                cosigners.clone(),
                18,
            )
            .expect(&format!(
                "Unvault descriptors creation error with ({}, {})",
                n_managers, n_stakeholders
            ));
            DepositDescriptor::new(
                managers
                    .clone()
                    .iter()
                    .chain(stakeholders.iter())
                    .cloned()
                    .collect::<Vec<DescriptorPublicKey>>(),
            )
            .expect(&format!(
                "Deposit descriptors creation error with ({}, {})",
                n_managers, n_stakeholders
            ));
            CpfpDescriptor::new(managers).expect(&format!(
                "CPFP descriptors creation error with ({}, {})",
                n_managers, n_stakeholders
            ));
        }
    }

    #[test]
    fn test_default_configuration_limits() {
        let mut rng = fastrand::Rng::new();
        let secp = secp256k1::Secp256k1::signing_only();

        assert_eq!(
            DepositDescriptor::new(vec![get_random_pubkey(&mut rng, &secp)])
                .unwrap_err()
                .to_string(),
            ScriptCreationError::BadParameters.to_string()
        );

        assert_eq!(
            UnvaultDescriptor::new(
                vec![get_random_pubkey(&mut rng, &secp)],
                vec![get_random_pubkey(&mut rng, &secp)],
                1,
                vec![
                    get_random_pubkey(&mut rng, &secp),
                    get_random_pubkey(&mut rng, &secp)
                ],
                6
            )
            .unwrap_err()
            .to_string(),
            ScriptCreationError::BadParameters.to_string()
        );

        assert_eq!(
            UnvaultDescriptor::new(
                vec![get_random_pubkey(&mut rng, &secp)],
                vec![get_random_pubkey(&mut rng, &secp)],
                1,
                vec![get_random_pubkey(&mut rng, &secp)],
                4194305
            )
            .unwrap_err()
            .to_string(),
            ScriptCreationError::BadParameters.to_string()
        );

        assert_eq!(
            UnvaultDescriptor::new(
                vec![get_random_pubkey(&mut rng, &secp)],
                vec![get_random_pubkey(&mut rng, &secp)],
                2,
                vec![get_random_pubkey(&mut rng, &secp)],
                4194305
            )
            .unwrap_err()
            .to_string(),
            ScriptCreationError::BadParameters.to_string()
        );

        // Maximum N-of-N
        let participants = (0..99)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        DepositDescriptor::new(participants).expect("Should be OK: max allowed value");
        // Now hit the limit
        let participants = (0..100)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        assert_eq!(
            DepositDescriptor::new(participants)
                .unwrap_err()
                .to_string(),
            ScriptCreationError::PolicyCompilation(CompilerError::LimitsExceeded).to_string()
        );

        // Maximum 1-of-N
        let managers = (0..20)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        CpfpDescriptor::new(managers).expect("Should be OK, that's the maximum allowed value");
        // Hit the limit
        let managers = (0..21)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        assert_eq!(
            CpfpDescriptor::new(managers).unwrap_err().to_string(),
            ScriptCreationError::PolicyCompilation(CompilerError::LimitsExceeded).to_string()
        );

        // Maximum non-managers for 2 managers
        let stakeholders = (0..38)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        let managers = (0..2)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        let cosigners = (0..38)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        UnvaultDescriptor::new(stakeholders, managers, 2, cosigners, 145).unwrap();

        // Now hit the limit
        let stakeholders = (0..39)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        let managers = (0..2)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        let cosigners = (0..39)
            .map(|_| get_random_pubkey(&mut rng, &secp))
            .collect::<Vec<DescriptorPublicKey>>();
        assert_eq!(
            UnvaultDescriptor::new(stakeholders, managers, 2, cosigners, 32)
                .unwrap_err()
                .to_string(),
            ScriptCreationError::PolicyCompilation(CompilerError::LimitsExceeded).to_string()
        );
    }

    #[cfg(feature = "use-serde")]
    #[test]
    fn serde_parse_emer_address() {
        use super::EmergencyAddress;

        serde_json::from_str::<EmergencyAddress>(
            "\"bcrt1qrht43q4xt59vr9jytlmckgde6rcvhxcp392kx9\"",
        )
        .expect_err("P2WPKH");
        serde_json::from_str::<EmergencyAddress>(
            "\"bcrt1q5k05km5zn2g7kp0c230r0g8znuhlk4yynne3pwklh6xl82ed087sgr902c\"",
        )
        .expect("P2WSH");

        serde_json::from_str::<EmergencyAddress>("\"1KFHE7w8BhaENAswwryaoccDb6qcT6DbYY\"")
            .expect_err("P2PKH");
        serde_json::from_str::<EmergencyAddress>("\"3DoB8fDRHcNxLCBcgLTvrpfQD5amk6sUce\"")
            .expect_err("P2SH");
        serde_json::from_str::<EmergencyAddress>("\"bc1qw3w0nt60tzh4xqdhx7hmf5uh0nczxhcr8lt7ec\"")
            .expect_err("P2WPKH (mainnet)");
        serde_json::from_str::<EmergencyAddress>(
            "\"bc1qnz0msqjqaw59zex2aw00rm565yg0rlpc5h3dvtps38w60ggw0seqwgjaa6\"",
        )
        .expect("P2WSH (mainnet)");
    }
}

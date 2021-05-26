//! Revault transactions
//!
//! Typesafe routines to create Revault-specific Bitcoin transactions.
//!
//! We use PSBTs as defined in [bip-0174](https://github.com/bitcoin/bips/blob/master/bip-0174.mediawiki)
//! for data structure as well as roles distribution.

use crate::{error::*, scripts::*, txins::*, txouts::*};
use miniscript::{
    bitcoin::{
        consensus::encode::Encodable,
        hash_types,
        hashes::Hash,
        secp256k1,
        util::{
            bip143::SigHashCache, bip32::ChildNumber, psbt::PartiallySignedTransaction as Psbt,
        },
        Address, Amount, Network, OutPoint, PublicKey as BitcoinPubKey, Script, SigHash,
        SigHashType, Transaction, Txid, Wtxid,
    },
    BitcoinSig,
};

use std::fmt;

#[macro_use]
mod utils;

mod cancel;
mod emergency;
mod spend;
mod unvault;
mod unvaultemergency;

pub use cancel::CancelTransaction;
pub use emergency::EmergencyTransaction;
pub use spend::SpendTransaction;
pub use unvault::UnvaultTransaction;
pub use unvaultemergency::UnvaultEmergencyTransaction;

/// The value of the CPFP output in the Unvault transaction.
/// See [practical-revault](https://github.com/revault/practical-revault/blob/master/transactions.md#unvault_tx).
pub const UNVAULT_CPFP_VALUE: u64 = 30000;

/// The feerate, in sat / W, to create the unvaulting transactions with.
pub const UNVAULT_TX_FEERATE: u64 = 6;

/// The feerate, in sat / W, to create the revaulting transactions (both emergency and the
/// cancel) with.
pub const REVAULTING_TX_FEERATE: u64 = 22;

/// We refuse to create a stakeholder-pre-signed transaction that would create an output worth
/// less than this amount of sats. This is worth 30€ for 15k€/btc.
pub const DUST_LIMIT: u64 = 200_000;

/// We can't safely error for insane fees on revaulting transactions, but we can for the unvault
/// and the spend. This is 0.2BTC, or 3k€ currently.
pub const INSANE_FEES: u64 = 20_000_000;

/// This enables CSV and is easier to apply to all transactions anyways.
pub const TX_VERSION: i32 = 2;

/// Maximum weight of a transaction to be relayed.
///
/// <https://github.com/bitcoin/bitcoin/blob/590e49ccf2af27c6c1f1e0eb8be3a4bf4d92ce8b/src/policy/policy.h#L23-L24>
pub const MAX_STANDARD_TX_WEIGHT: u32 = 400_000;

/// This private module is used to make mutable references to the PSBT inside transaction newtypes
/// available to functions inside the transaction module, but not beyond that. This is needed to
/// guarantee invariants that could not be guaranteed if users had arbitrary mutable access to the
/// inner PSBT.
pub(super) mod inner_mut {
    use super::{Psbt, TransactionSerialisationError};

    pub trait PrivateInnerMut: Sized {
        /// Get a mutable reference to the inner transaction, this is only used internally
        fn psbt_mut(&mut self) -> &mut Psbt;

        /// Get a reference to the inner transaction, this is only used internally
        fn psbt(&self) -> &Psbt;

        /// Move inner transaction out
        fn into_psbt(self) -> Psbt;

        fn from_psbt_serialized(raw_psbt: &[u8]) -> Result<Self, TransactionSerialisationError>;
    }
}

/// A Revault transaction.
///
/// Wraps a rust-bitcoin PSBT and defines some BIP174 roles as methods.
/// Namely:
/// - Creator and updater
/// - Signer
/// - Finalizer
/// - Extractor and serializer
pub trait RevaultTransaction: fmt::Debug + Clone + PartialEq {
    /// Get a reference to the inner PSBT
    fn psbt(&self) -> &Psbt;

    /// Get the sighash for an input of a Revault transaction. Will deduce the scriptCode from
    /// the previous scriptPubKey type, assuming either P2WSH or P2WPKH.
    ///
    /// Will error if the input is out of bounds or the PSBT input is insane (eg a P2WSH that
    /// does not contain a Witness Script (ie was already finalized)).
    fn signature_hash(
        &self,
        input_index: usize,
        sighash_type: SigHashType,
    ) -> Result<SigHash, InputSatisfactionError>;

    /// Cached version of [RevaultTransaction::signature_hash]
    fn signature_hash_cached(
        &self,
        input_index: usize,
        sighash_type: SigHashType,
        cache: &mut SigHashCache<&Transaction>,
    ) -> Result<SigHash, InputSatisfactionError>;

    /// Add a signature in order to eventually satisfy this input.
    ///
    /// Checks the signature according to the specified expected sighash type in the PSBT input.
    ///
    /// The BIP174 Signer role.
    fn add_signature<C: secp256k1::Verification>(
        &mut self,
        input_index: usize,
        pubkey: BitcoinPubKey,
        signature: BitcoinSig,
        secp: &secp256k1::Secp256k1<C>,
    ) -> Result<Option<Vec<u8>>, InputSatisfactionError>;

    /// Check and satisfy the scripts, create the witnesses.
    ///
    /// The BIP174 Input Finalizer role.
    fn finalize(
        &mut self,
        ctx: &secp256k1::Secp256k1<impl secp256k1::Verification>,
    ) -> Result<(), Error>;

    /// Check the transaction is valid (fully-signed) and can be finalized.
    /// Slighty more efficient than calling [RevaultTransaction::finalize] on a clone as it gets
    /// rid of the belt-and-suspenders checks.
    fn is_finalizable(&self, ctx: &secp256k1::Secp256k1<impl secp256k1::Verification>) -> bool;

    /// Check if the transaction was already finalized.
    fn is_finalized(&self) -> bool;

    /// Check the transaction is valid
    fn is_valid(&self, ctx: &secp256k1::Secp256k1<impl secp256k1::Verification>) -> bool;

    /// Verify all PSBT inputs against libbitcoinconsensus
    fn verify_inputs(&self) -> Result<(), Error>;

    /// Get the network-serialized (inner) transaction. You likely want to be sure
    /// the transaction [RevaultTransaction.is_finalized] before serializing it.
    ///
    /// The BIP174 Transaction Extractor (without any check, which are done in
    /// [RevaultTransaction.finalize]).
    fn into_bitcoin_serialized(self) -> Vec<u8>;

    /// Get the BIP174-serialized (inner) transaction.
    fn as_psbt_serialized(&self) -> Vec<u8>;

    /// Get the BIP174-serialized (inner) transaction encoded in base64.
    fn as_psbt_string(&self) -> String;

    /// Create a RevaultTransaction from a base64-encoded BIP174-serialized transaction.
    fn from_psbt_str(psbt_str: &str) -> Result<Self, TransactionSerialisationError>;

    fn fees(&self) -> u64;

    /// Get the inner unsigned transaction id
    fn txid(&self) -> Txid;

    /// Get the inner unsigned transaction hash with witness data
    fn wtxid(&self) -> Wtxid;

    /// Get a reference to the inner transaction
    fn tx(&self) -> &Transaction;

    /// Extract the inner transaction of the inner PSBT. You likely want to be sure
    /// the transaction [RevaultTransaction.is_finalized] before serializing it.
    ///
    /// The BIP174 Transaction Extractor (without any check, which are done in
    /// [RevaultTransaction.finalize]).
    fn into_tx(self) -> Transaction;
}

impl<T: inner_mut::PrivateInnerMut + fmt::Debug + Clone + PartialEq> RevaultTransaction for T {
    fn psbt(&self) -> &Psbt {
        inner_mut::PrivateInnerMut::psbt(self)
    }

    fn signature_hash(
        &self,
        input_index: usize,
        sighash_type: SigHashType,
    ) -> Result<SigHash, InputSatisfactionError> {
        let mut cache = SigHashCache::new(self.tx());
        self.signature_hash_cached(input_index, sighash_type, &mut cache)
    }

    fn signature_hash_cached(
        &self,
        input_index: usize,
        sighash_type: SigHashType,
        cache: &mut SigHashCache<&Transaction>,
    ) -> Result<SigHash, InputSatisfactionError> {
        let psbt = self.psbt();
        let psbtin = psbt
            .inputs
            .get(input_index)
            .ok_or(InputSatisfactionError::OutOfBounds)?;
        let prev_txo = psbtin
            .witness_utxo
            .as_ref()
            .expect("We always set witness_txo");

        if prev_txo.script_pubkey.is_v0_p2wsh() {
            let witscript = psbtin
                .witness_script
                .as_ref()
                .ok_or(InputSatisfactionError::MissingWitnessScript)?;
            Ok(cache.signature_hash(input_index, &witscript, prev_txo.value, sighash_type))
        } else {
            assert!(
                prev_txo.script_pubkey.is_v0_p2wpkh(),
                "If not a P2WSH, it must be a feebump input."
            );
            let raw_pkh = &prev_txo.script_pubkey[2..];
            let pkh = hash_types::PubkeyHash::from_slice(raw_pkh).expect("Never fails");
            let witscript = Script::new_p2pkh(&pkh);
            Ok(cache.signature_hash(input_index, &witscript, prev_txo.value, sighash_type))
        }
    }

    fn add_signature<C: secp256k1::Verification>(
        &mut self,
        input_index: usize,
        pubkey: BitcoinPubKey,
        signature: BitcoinSig,
        secp: &secp256k1::Secp256k1<C>,
    ) -> Result<Option<Vec<u8>>, InputSatisfactionError> {
        let psbtin = self
            .psbt()
            .inputs
            .get(input_index)
            .ok_or(InputSatisfactionError::OutOfBounds)?;

        // If we were already finalized, our witness script was wiped.
        if psbtin.final_script_witness.is_some() {
            return Err(InputSatisfactionError::AlreadyFinalized);
        }

        // BIP174:
        // For a Signer to only produce valid signatures for what it expects to sign, it must
        // check that the following conditions are true:
        // -- If a witness UTXO is provided, no non-witness signature may be created.
        let prev_txo = psbtin
            .witness_utxo
            .as_ref()
            .expect("Cannot be reached. We only create transactions with witness_utxo.");
        assert!(
            psbtin.non_witness_utxo.is_none(),
            "We never create transactions with non_witness_utxo."
        );

        // -- If a witnessScript is provided, the scriptPubKey or the redeemScript must be for
        // that witnessScript
        if let Some(witness_script) = &psbtin.witness_script {
            // Note the network is irrelevant here.
            let expected_script_pubkey =
                Address::p2wsh(witness_script, Network::Bitcoin).script_pubkey();
            assert!(
                expected_script_pubkey == prev_txo.script_pubkey,
                "We create TxOut scriptPubKey out of this exact witnessScript."
            );
        } else {
            // We only use P2WSH utxos internally. External inputs are only ever added for fee
            // bumping, for which we require P2WPKH.
            assert!(prev_txo.script_pubkey.is_v0_p2wpkh());
        }
        assert!(
            psbtin.redeem_script.is_none(),
            "We never create Psbt input with legacy txos."
        );

        // -- If a sighash type is provided, the signer must check that the sighash is acceptable.
        // If unacceptable, they must fail.
        let (sig, sighash_type) = signature;
        let expected_sighash_type = psbtin
            .sighash_type
            .expect("We always set the SigHashType in the constructor.");
        if sighash_type != expected_sighash_type {
            return Err(InputSatisfactionError::UnexpectedSighashType);
        }

        let sighash = self.signature_hash(input_index, expected_sighash_type)?;
        let sighash = secp256k1::Message::from_slice(&sighash).expect("sighash is 32 a bytes hash");
        secp.verify(&sighash, &sig, &pubkey.key)
            .map_err(|_| InputSatisfactionError::InvalidSignature(sig, pubkey.key, sighash))?;

        let mut rawsig = sig.serialize_der().to_vec();
        rawsig.push(sighash_type.as_u32() as u8);

        let psbtin = self
            .psbt_mut()
            .inputs
            .get_mut(input_index)
            .expect("Checked at the beginning.");
        Ok(psbtin.partial_sigs.insert(pubkey, rawsig))
    }

    fn finalize(
        &mut self,
        ctx: &secp256k1::Secp256k1<impl secp256k1::Verification>,
    ) -> Result<(), Error> {
        // We could operate on a clone for state consistency in case of error. But we can only end
        // up in an inconsistent state if miniscript's interpreter checks pass but not
        // libbitcoinconsensus' one.
        let mut psbt = self.psbt_mut();

        miniscript::psbt::finalize(&mut psbt, ctx)
            .map_err(|e| Error::TransactionFinalisation(e.to_string()))?;

        // Miniscript's finalize does not check against libbitcoinconsensus. And we are better safe
        // than sorry when dealing with Script ...
        self.verify_inputs()?;

        Ok(())
    }

    /// Check the transaction is valid (fully-signed) and can be finalized.
    /// Slighty more efficient than calling [RevaultTransaction::finalize] on a clone as it gets
    /// rid of the belt-and-suspenders checks.
    fn is_finalizable(&self, ctx: &secp256k1::Secp256k1<impl secp256k1::Verification>) -> bool {
        miniscript::psbt::finalize(&mut self.psbt().clone(), ctx).is_ok()
    }

    /// Check if the transaction was already finalized.
    fn is_finalized(&self) -> bool {
        for i in self.psbt().inputs.iter() {
            // We never mix finalized and non-finalized inputs.
            if i.final_script_witness.is_some() {
                return true;
            }
        }

        false
    }

    /// Check the transaction is valid
    fn is_valid(&self, ctx: &secp256k1::Secp256k1<impl secp256k1::Verification>) -> bool {
        if !self.is_finalized() {
            return false;
        }

        // Miniscript's finalize does not check against libbitcoinconsensus. And we are better safe
        // than sorry when dealing with Script ...
        if self.verify_inputs().is_err() {
            return false;
        }
        assert_eq!(self.psbt().inputs.len(), self.tx().input.len());

        miniscript::psbt::interpreter_check(&self.psbt(), ctx).is_ok()
    }

    /// Verify all PSBT inputs against libbitcoinconsensus
    fn verify_inputs(&self) -> Result<(), Error> {
        let ser_tx = self.clone().into_bitcoin_serialized();

        for (i, psbtin) in self.psbt().inputs.iter().enumerate() {
            let utxo = psbtin
                .witness_utxo
                .as_ref()
                .expect("A witness_utxo is always set");
            let (prev_scriptpubkey, prev_value) = (utxo.script_pubkey.as_bytes(), utxo.value);

            bitcoinconsensus::verify(prev_scriptpubkey, prev_value, &ser_tx, i)?;
        }

        Ok(())
    }

    /// Get the network-serialized (inner) transaction. You likely want to be sure
    /// the transaction [RevaultTransaction.is_finalized] before serializing it.
    ///
    /// The BIP174 Transaction Extractor (without any check, which are done in
    /// [RevaultTransaction.finalize]).
    fn into_bitcoin_serialized(self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(256);
        self.into_psbt()
            .extract_tx()
            .consensus_encode(&mut buf)
            .expect("We only create valid PSBT, serialization cannot fail");
        buf
    }

    /// Get the BIP174-serialized (inner) transaction.
    fn as_psbt_serialized(&self) -> Vec<u8> {
        let mut buff = Vec::with_capacity(256);
        self.psbt()
            .consensus_encode(&mut buff)
            .expect("We only create valid PSBT, serialization cannot fail");
        buff
    }

    /// Get the BIP174-serialized (inner) transaction encoded in base64.
    fn as_psbt_string(&self) -> String {
        base64::encode(self.as_psbt_serialized())
    }

    /// Create a RevaultTransaction from a base64-encoded BIP174-serialized transaction.
    fn from_psbt_str(psbt_str: &str) -> Result<Self, TransactionSerialisationError> {
        Self::from_psbt_serialized(&base64::decode(&psbt_str)?)
    }

    fn fees(&self) -> u64 {
        let mut value_in: u64 = 0;
        for i in self.psbt().inputs.iter() {
            value_in = value_in
                .checked_add(
                    i.witness_utxo
                        .as_ref()
                        .expect("A witness utxo is always set")
                        .value,
                )
                .expect("PSBT bug: overflow while computing spent coins value");
        }

        let mut value_out: u64 = 0;
        for o in self.psbt().global.unsigned_tx.output.iter() {
            value_out = value_out
                .checked_add(o.value)
                .expect("PSBT bug: overflow while computing created coins value");
        }

        value_in
            .checked_sub(value_out)
            .expect("We never create a transaction with negative fees")
    }

    /// Get the inner unsigned transaction id
    fn txid(&self) -> Txid {
        self.psbt().global.unsigned_tx.txid()
    }

    /// Get the inner unsigned transaction hash with witness data
    fn wtxid(&self) -> Wtxid {
        self.psbt().global.unsigned_tx.wtxid()
    }

    /// Get a reference to the inner transaction
    fn tx(&self) -> &Transaction {
        &self.psbt().global.unsigned_tx
    }

    /// Extract the inner transaction of the inner PSBT. You likely want to be sure
    /// the transaction [RevaultTransaction.is_finalized] before serializing it.
    ///
    /// The BIP174 Transaction Extractor (without any check, which are done in
    /// [RevaultTransaction.finalize]).
    fn into_tx(self) -> Transaction {
        self.into_psbt().extract_tx()
    }
}

/// The funding transaction, we don't create nor sign it.
#[derive(Debug, Clone, PartialEq)]
pub struct DepositTransaction(pub Transaction);
impl DepositTransaction {
    /// Assumes that the outpoint actually refers to this transaction. Will panic otherwise.
    pub fn deposit_txin(
        &self,
        outpoint: OutPoint,
        deposit_descriptor: &DerivedDepositDescriptor,
    ) -> DepositTxIn {
        assert!(outpoint.txid == self.0.txid());
        let txo = self.0.output[outpoint.vout as usize].clone();

        DepositTxIn::new(
            outpoint,
            DepositTxOut::new(Amount::from_sat(txo.value), deposit_descriptor),
        )
    }
}

/// The fee-bumping transaction, we don't create nor sign it.
#[derive(Debug, Clone, PartialEq)]
pub struct FeeBumpTransaction(pub Transaction);

/// Get the chain of pre-signed transaction out of a deposit available for a manager.
/// No feebump input.
#[allow(clippy::too_many_arguments)]
pub fn transaction_chain_manager<C: secp256k1::Verification>(
    deposit_outpoint: OutPoint,
    deposit_amount: Amount,
    deposit_descriptor: &DepositDescriptor,
    unvault_descriptor: &UnvaultDescriptor,
    cpfp_descriptor: &CpfpDescriptor,
    derivation_index: ChildNumber,
    lock_time: u32,
    secp: &secp256k1::Secp256k1<C>,
) -> Result<(UnvaultTransaction, CancelTransaction), Error> {
    let (der_deposit_descriptor, der_unvault_descriptor, der_cpfp_descriptor) = (
        deposit_descriptor.derive(derivation_index, secp),
        unvault_descriptor.derive(derivation_index, secp),
        cpfp_descriptor.derive(derivation_index, secp),
    );

    let deposit_txin = DepositTxIn::new(
        deposit_outpoint,
        DepositTxOut::new(deposit_amount, &der_deposit_descriptor),
    );
    let unvault_tx = UnvaultTransaction::new(
        deposit_txin,
        &der_unvault_descriptor,
        &der_cpfp_descriptor,
        lock_time,
    )?;

    let cancel_tx = CancelTransaction::new(
        unvault_tx.revault_unvault_txin(&der_unvault_descriptor),
        None,
        &der_deposit_descriptor,
        lock_time,
    );

    Ok((unvault_tx, cancel_tx))
}

/// Get the entire chain of pre-signed transaction for this derivation index out of a deposit. No feebump input.
#[allow(clippy::too_many_arguments)]
pub fn transaction_chain<C: secp256k1::Verification>(
    deposit_outpoint: OutPoint,
    deposit_amount: Amount,
    deposit_descriptor: &DepositDescriptor,
    unvault_descriptor: &UnvaultDescriptor,
    cpfp_descriptor: &CpfpDescriptor,
    derivation_index: ChildNumber,
    emer_address: EmergencyAddress,
    lock_time: u32,
    secp: &secp256k1::Secp256k1<C>,
) -> Result<
    (
        UnvaultTransaction,
        CancelTransaction,
        EmergencyTransaction,
        UnvaultEmergencyTransaction,
    ),
    Error,
> {
    let (unvault_tx, cancel_tx) = transaction_chain_manager(
        deposit_outpoint,
        deposit_amount,
        deposit_descriptor,
        unvault_descriptor,
        cpfp_descriptor,
        derivation_index,
        lock_time,
        secp,
    )?;

    let der_deposit_descriptor = deposit_descriptor.derive(derivation_index, secp);
    let deposit_txin = DepositTxIn::new(
        deposit_outpoint,
        DepositTxOut::new(deposit_amount, &der_deposit_descriptor),
    );
    let emergency_tx =
        EmergencyTransaction::new(deposit_txin, None, emer_address.clone(), lock_time)?;

    let der_unvault_descriptor = unvault_descriptor.derive(derivation_index, secp);
    let unvault_txin = unvault_tx.revault_unvault_txin(&der_unvault_descriptor);
    let unvault_emergency_tx =
        UnvaultEmergencyTransaction::new(unvault_txin, None, emer_address, lock_time);

    Ok((unvault_tx, cancel_tx, emergency_tx, unvault_emergency_tx))
}

/// Get a spend transaction out of a list of deposits and derivation indexes.
/// The derivation index used for the Spend CPFP is the highest of the deposits one.
#[allow(clippy::too_many_arguments)]
pub fn spend_tx_from_deposits<C: secp256k1::Verification>(
    deposit_txins: Vec<(OutPoint, Amount, ChildNumber)>,
    spend_txos: Vec<SpendTxOut>,
    deposit_descriptor: &DepositDescriptor,
    unvault_descriptor: &UnvaultDescriptor,
    cpfp_descriptor: &CpfpDescriptor,
    lock_time: u32,
    check_insane_fees: bool,
    secp: &secp256k1::Secp256k1<C>,
) -> Result<SpendTransaction, TransactionCreationError> {
    let mut max_deriv_index = ChildNumber::from(0);
    let unvault_txins = deposit_txins
        .into_iter()
        .map(|(outpoint, amount, deriv_index)| {
            let der_deposit_desc = deposit_descriptor.derive(deriv_index, secp);
            let der_unvault_desc = unvault_descriptor.derive(deriv_index, secp);
            let der_cpfp_desc = cpfp_descriptor.derive(deriv_index, secp);

            let txin = DepositTxIn::new(outpoint, DepositTxOut::new(amount, &der_deposit_desc));
            if deriv_index > max_deriv_index {
                max_deriv_index = deriv_index;
            }

            UnvaultTransaction::new(txin, &der_unvault_desc, &der_cpfp_desc, lock_time)
                .map(|unvault_tx| unvault_tx.spend_unvault_txin(&der_unvault_desc))
        })
        .collect::<Result<Vec<UnvaultTxIn>, TransactionCreationError>>()?;

    let der_cpfp_descriptor = cpfp_descriptor.derive(max_deriv_index, secp);
    SpendTransaction::new(
        unvault_txins,
        spend_txos,
        &der_cpfp_descriptor,
        lock_time,
        check_insane_fees,
    )
}

#[cfg(test)]
mod tests {
    use super::{
        transaction_chain, CancelTransaction, DepositTransaction, EmergencyAddress,
        EmergencyTransaction, FeeBumpTransaction, RevaultTransaction, SpendTransaction,
        UnvaultEmergencyTransaction, UnvaultTransaction,
    };
    use crate::{error::*, scripts::*, txins::*, txouts::*};

    use std::{iter::repeat_with, str::FromStr};

    use miniscript::{
        bitcoin::{
            secp256k1,
            util::{bip143::SigHashCache, bip32},
            Address, Amount, Network, OutPoint, SigHash, SigHashType, Transaction, TxIn, TxOut,
        },
        descriptor::{DescriptorPublicKey, DescriptorXKey, Wildcard},
        Descriptor, DescriptorTrait,
    };

    fn get_random_privkey(rng: &mut fastrand::Rng) -> bip32::ExtendedPrivKey {
        let rand_bytes: Vec<u8> = repeat_with(|| rng.u8(..)).take(64).collect();

        bip32::ExtendedPrivKey::new_master(Network::Bitcoin, &rand_bytes)
            .unwrap_or_else(|_| get_random_privkey(rng))
    }

    /// This generates the master private keys to derive directly from master, so it's
    /// [None]<xpub_goes_here>m/* descriptor pubkeys
    fn get_participants_sets(
        n_stk: usize,
        n_man: usize,
        secp: &secp256k1::Secp256k1<secp256k1::All>,
    ) -> (
        (Vec<bip32::ExtendedPrivKey>, Vec<DescriptorPublicKey>),
        (Vec<bip32::ExtendedPrivKey>, Vec<DescriptorPublicKey>),
        (Vec<bip32::ExtendedPrivKey>, Vec<DescriptorPublicKey>),
    ) {
        let mut rng = fastrand::Rng::new();

        let managers_priv = (0..n_man)
            .map(|_| get_random_privkey(&mut rng))
            .collect::<Vec<bip32::ExtendedPrivKey>>();
        let managers = managers_priv
            .iter()
            .map(|xpriv| {
                DescriptorPublicKey::XPub(DescriptorXKey {
                    origin: None,
                    xkey: bip32::ExtendedPubKey::from_private(&secp, &xpriv),
                    derivation_path: bip32::DerivationPath::from(vec![]),
                    wildcard: Wildcard::Unhardened,
                })
            })
            .collect::<Vec<DescriptorPublicKey>>();

        let stakeholders_priv = (0..n_stk)
            .map(|_| get_random_privkey(&mut rng))
            .collect::<Vec<bip32::ExtendedPrivKey>>();
        let stakeholders = stakeholders_priv
            .iter()
            .map(|xpriv| {
                DescriptorPublicKey::XPub(DescriptorXKey {
                    origin: None,
                    xkey: bip32::ExtendedPubKey::from_private(&secp, &xpriv),
                    derivation_path: bip32::DerivationPath::from(vec![]),
                    wildcard: Wildcard::Unhardened,
                })
            })
            .collect::<Vec<DescriptorPublicKey>>();

        let cosigners_priv = (0..n_stk)
            .map(|_| get_random_privkey(&mut rng))
            .collect::<Vec<bip32::ExtendedPrivKey>>();
        let cosigners = cosigners_priv
            .iter()
            .map(|xpriv| {
                DescriptorPublicKey::XPub(DescriptorXKey {
                    origin: None,
                    xkey: bip32::ExtendedPubKey::from_private(&secp, &xpriv),
                    derivation_path: bip32::DerivationPath::from(vec![]),
                    wildcard: Wildcard::Unhardened,
                })
            })
            .collect::<Vec<DescriptorPublicKey>>();

        (
            (managers_priv, managers),
            (stakeholders_priv, stakeholders),
            (cosigners_priv, cosigners),
        )
    }

    // Routine for ""signing"" a transaction
    fn satisfy_transaction_input(
        secp: &secp256k1::Secp256k1<secp256k1::All>,
        tx: &mut impl RevaultTransaction,
        input_index: usize,
        tx_sighash: &SigHash,
        xprivs: &Vec<bip32::ExtendedPrivKey>,
        child_number: Option<bip32::ChildNumber>,
        sighash_type: SigHashType,
    ) -> Result<(), Error> {
        // Can we agree that rustfmt does some nasty formatting now ??
        let derivation_path = bip32::DerivationPath::from(if let Some(cn) = child_number {
            vec![cn]
        } else {
            vec![]
        });

        for xpriv in xprivs {
            let sig = (
                secp.sign(
                    &secp256k1::Message::from_slice(&tx_sighash).unwrap(),
                    &xpriv
                        .derive_priv(&secp, &derivation_path)
                        .unwrap()
                        .private_key
                        .key,
                ),
                sighash_type,
            );

            let xpub = DescriptorPublicKey::XPub(DescriptorXKey {
                origin: None,
                xkey: bip32::ExtendedPubKey::from_private(&secp, xpriv),
                derivation_path: bip32::DerivationPath::from(vec![]),
                wildcard: if child_number.is_some() {
                    Wildcard::Unhardened
                } else {
                    Wildcard::None
                },
            });
            let key = if let Some(index) = child_number {
                xpub.derive(index.into())
            } else {
                xpub
            }
            .derive_public_key(secp)
            .unwrap();

            tx.add_signature(input_index, key, sig, secp)?;
        }

        Ok(())
    }

    #[test]
    fn transaction_derivation() {
        let secp = secp256k1::Secp256k1::new();
        let csv = fastrand::u32(..SEQUENCE_LOCKTIME_MASK);
        eprintln!("Using a CSV of '{}'", csv);

        // Test the dust limit
        assert_eq!(
            derive_transactions(2, 1, csv, 234_631, &secp)
                .unwrap_err()
                .to_string(),
            Error::TransactionCreation(TransactionCreationError::Dust).to_string()
        );
        // Non-minimal CSV
        derive_transactions(2, 1, SEQUENCE_LOCKTIME_MASK + 1, 300_000, &secp)
            .expect_err("Unclean CSV");

        // Absolute minimum
        derive_transactions(2, 1, csv, 234_632, &secp).expect(&format!(
            "Tx chain with 2 stakeholders, 1 manager, {} csv, 235_250 deposit",
            csv
        ));
        // 1 BTC
        derive_transactions(8, 3, csv, 100_000_000, &secp).expect(&format!(
            "Tx chain with 8 stakeholders, 3 managers, {} csv, 1_000_000 deposit",
            csv
        ));
        // 100 000 BTC
        derive_transactions(8, 3, csv, 100_000_000_000_000, &secp).expect(&format!(
            "Tx chain with 8 stakeholders, 3 managers, {} csv, 100_000_000_000_000 deposit",
            csv
        ));
        // 100 BTC
        derive_transactions(38, 5, csv, 100_000_000_000, &secp).expect(&format!(
            "Tx chain with 38 stakeholders, 5 manager, {} csv, 100_000_000_000 deposit",
            csv
        ));
    }

    fn derive_transactions(
        n_stk: usize,
        n_man: usize,
        csv: u32,
        deposit_value: u64,
        secp: &secp256k1::Secp256k1<secp256k1::All>,
    ) -> Result<(), Error> {
        // Let's get the 10th key of each
        let child_number = bip32::ChildNumber::from(10);

        // Keys, keys, keys everywhere !
        let (
            (managers_priv, managers),
            (stakeholders_priv, stakeholders),
            (cosigners_priv, cosigners),
        ) = get_participants_sets(n_stk, n_man, secp);

        // Get the script descriptors for the txos we're going to create
        let unvault_descriptor = UnvaultDescriptor::new(
            stakeholders.clone(),
            managers.clone(),
            managers.len(),
            cosigners.clone(),
            csv,
        )?;
        assert_eq!(unvault_descriptor.csv_value(), csv);
        let cpfp_descriptor =
            CpfpDescriptor::new(managers).expect("Unvault CPFP descriptor generation error");
        let deposit_descriptor =
            DepositDescriptor::new(stakeholders).expect("Deposit descriptor generation error");

        // We reuse the deposit descriptor for the emergency address
        let emergency_address = EmergencyAddress::from(Address::p2wsh(
            &deposit_descriptor
                .derive(child_number, secp)
                .inner()
                .explicit_script(),
            Network::Bitcoin,
        ))
        .expect("It's a P2WSH");

        let der_deposit_descriptor = deposit_descriptor.derive(child_number, secp);
        let der_unvault_descriptor = unvault_descriptor.derive(child_number, secp);
        assert_eq!(
            der_unvault_descriptor.csv_value(),
            unvault_descriptor.csv_value()
        );
        let der_cpfp_descriptor = cpfp_descriptor.derive(child_number, secp);

        // The funding transaction does not matter (random txid from my mempool)
        let deposit_scriptpubkey = der_deposit_descriptor.inner().script_pubkey();
        let deposit_raw_tx = Transaction {
            version: 2,
            lock_time: 0,
            input: vec![TxIn {
                previous_output: OutPoint::from_str(
                    "39a8212c6a9b467680d43e47b61b8363fe1febb761f9f548eb4a432b2bc9bbec:0",
                )
                .unwrap(),
                ..TxIn::default()
            }],
            output: vec![TxOut {
                value: deposit_value,
                script_pubkey: deposit_scriptpubkey.clone(),
            }],
        };
        let deposit_txo = DepositTxOut::new(
            Amount::from_sat(deposit_raw_tx.output[0].value),
            &der_deposit_descriptor,
        );
        let deposit_tx = DepositTransaction(deposit_raw_tx);
        let deposit_outpoint = OutPoint {
            txid: deposit_tx.0.txid(),
            vout: 0,
        };
        let deposit_txin = DepositTxIn::new(deposit_outpoint, deposit_txo.clone());

        // Test that the transaction helper(s) derive the same transactions as we do
        let (h_unvault, h_cancel, h_emer, h_unemer) = transaction_chain(
            deposit_outpoint,
            Amount::from_sat(deposit_txo.txout().value),
            &deposit_descriptor,
            &unvault_descriptor,
            &cpfp_descriptor,
            child_number,
            emergency_address.clone(),
            0,
            secp,
        )?;

        // The fee-bumping utxo, used in revaulting transactions inputs to bump their feerate.
        // We simulate a wallet utxo.
        let mut rng = fastrand::Rng::new();
        let feebump_xpriv = get_random_privkey(&mut rng);
        let feebump_xpub = bip32::ExtendedPubKey::from_private(&secp, &feebump_xpriv);
        let feebump_descriptor = Descriptor::new_wpkh(
            DescriptorPublicKey::XPub(DescriptorXKey {
                origin: None,
                xkey: feebump_xpub,
                derivation_path: bip32::DerivationPath::from(vec![]),
                wildcard: Wildcard::None, // We are not going to derive from this one
            })
            .derive_public_key(secp)
            .unwrap(),
        )
        .unwrap();
        let raw_feebump_tx = Transaction {
            version: 2,
            lock_time: 0,
            input: vec![TxIn {
                previous_output: OutPoint::from_str(
                    "4bb4545bb4bc8853cb03e42984d677fbe880c81e7d95609360eed0d8f45b52f8:0",
                )
                .unwrap(),
                ..TxIn::default()
            }],
            output: vec![TxOut {
                value: 56730,
                script_pubkey: feebump_descriptor.script_pubkey(),
            }],
        };
        let feebump_txo =
            FeeBumpTxOut::new(raw_feebump_tx.output[0].clone()).expect("It is a p2wpkh");
        let feebump_tx = FeeBumpTransaction(raw_feebump_tx);

        // Create and sign the first (deposit) emergency transaction
        // We can sign the transaction without the feebump input
        let mut emergency_tx_no_feebump =
            EmergencyTransaction::new(deposit_txin.clone(), None, emergency_address.clone(), 0)
                .unwrap();
        assert_eq!(h_emer, emergency_tx_no_feebump);

        // 376 is the witstrip weight of an emer tx (1 segwit input, 1 P2WSH txout), 22 is the feerate is sat/WU
        assert_eq!(
            emergency_tx_no_feebump.fees(),
            (376 + deposit_txin.txout().max_sat_weight() as u64) * 22,
        );
        // We cannot get a sighash for a non-existing input
        assert_eq!(
            emergency_tx_no_feebump.signature_hash(10, SigHashType::AllPlusAnyoneCanPay),
            Err(InputSatisfactionError::OutOfBounds)
        );
        // But for an existing one, all good
        let emergency_tx_sighash_vault = emergency_tx_no_feebump
            .signature_hash(0, SigHashType::AllPlusAnyoneCanPay)
            .expect("Input exists");
        // We can't force it to accept a SIGHASH_ALL signature:
        let err = satisfy_transaction_input(
            &secp,
            &mut emergency_tx_no_feebump,
            0,
            &emergency_tx_sighash_vault,
            &stakeholders_priv,
            Some(child_number),
            SigHashType::All,
        );
        assert_eq!(
            err.unwrap_err().to_string(),
            Error::InputSatisfaction(InputSatisfactionError::UnexpectedSighashType).to_string()
        );
        // Now, that's the right SIGHASH
        satisfy_transaction_input(
            &secp,
            &mut emergency_tx_no_feebump,
            0,
            &emergency_tx_sighash_vault,
            &stakeholders_priv,
            Some(child_number),
            SigHashType::AllPlusAnyoneCanPay,
        )?;
        // Without feebump it finalizes just fine
        emergency_tx_no_feebump.finalize(&secp)?;

        let feebump_txin = FeeBumpTxIn::new(
            OutPoint {
                txid: feebump_tx.0.txid(),
                vout: 0,
            },
            feebump_txo.clone(),
        );
        let mut emergency_tx = EmergencyTransaction::new(
            deposit_txin.clone(),
            Some(feebump_txin),
            emergency_address.clone(),
            0,
        )
        .unwrap();
        let emergency_tx_sighash_feebump = emergency_tx
            .signature_hash(1, SigHashType::All)
            .expect("Input exists");
        satisfy_transaction_input(
            &secp,
            &mut emergency_tx,
            0,
            // This sighash was created without knowledge of the feebump input. It's fine.
            &emergency_tx_sighash_vault,
            &stakeholders_priv,
            Some(child_number),
            SigHashType::AllPlusAnyoneCanPay,
        )?;
        satisfy_transaction_input(
            &secp,
            &mut emergency_tx,
            1,
            &emergency_tx_sighash_feebump,
            &vec![feebump_xpriv],
            None,
            SigHashType::All,
        )?;
        emergency_tx.finalize(&secp)?;

        // Create but don't sign the unvaulting transaction until all revaulting transactions
        // are finalized
        let deposit_txin_sat_cost = deposit_txin.txout().max_sat_weight();
        let mut unvault_tx = UnvaultTransaction::new(
            deposit_txin.clone(),
            &der_unvault_descriptor,
            &der_cpfp_descriptor,
            0,
        )?;

        assert_eq!(h_unvault, unvault_tx);
        let unvault_value = unvault_tx.psbt().global.unsigned_tx.output[0].value;
        // 548 is the witstrip weight of an unvault tx (1 segwit input, 2 P2WSH txouts), 6 is the
        // feerate is sat/WU, and 30_000 is the CPFP output value.
        assert_eq!(unvault_tx.fees(), (548 + deposit_txin_sat_cost as u64) * 6);

        // Create and sign the cancel transaction
        let rev_unvault_txin = unvault_tx.revault_unvault_txin(&der_unvault_descriptor);
        assert_eq!(rev_unvault_txin.txout().txout().value, unvault_value);
        // We can create it entirely without the feebump input
        let mut cancel_tx_without_feebump =
            CancelTransaction::new(rev_unvault_txin.clone(), None, &der_deposit_descriptor, 0);
        assert_eq!(h_cancel, cancel_tx_without_feebump);
        // Keep track of the fees we computed..
        let value_no_feebump = cancel_tx_without_feebump.psbt().global.unsigned_tx.output[0].value;
        // 376 is the witstrip weight of a cancel tx (1 segwit input, 1 P2WSH txout), 22 is the feerate is sat/WU
        assert_eq!(
            cancel_tx_without_feebump.fees(),
            (376 + rev_unvault_txin.txout().max_sat_weight() as u64) * 22,
        );
        let cancel_tx_without_feebump_sighash = cancel_tx_without_feebump
            .signature_hash(0, SigHashType::AllPlusAnyoneCanPay)
            .expect("Input exists");
        satisfy_transaction_input(
            &secp,
            &mut cancel_tx_without_feebump,
            0,
            &cancel_tx_without_feebump_sighash,
            &stakeholders_priv,
            Some(child_number),
            SigHashType::AllPlusAnyoneCanPay,
        )?;
        cancel_tx_without_feebump.finalize(&secp).unwrap();
        // We can reuse the ANYONE_ALL sighash for the one with the feebump input
        let feebump_txin = FeeBumpTxIn::new(
            OutPoint {
                txid: feebump_tx.0.txid(),
                vout: 0,
            },
            feebump_txo.clone(),
        );
        let mut cancel_tx = CancelTransaction::new(
            rev_unvault_txin.clone(),
            Some(feebump_txin),
            &der_deposit_descriptor,
            0,
        );
        // It really is a belt-and-suspenders check as the sighash would differ too.
        assert_eq!(
            cancel_tx_without_feebump.psbt().global.unsigned_tx.output[0].value,
            value_no_feebump,
            "Base fees when computing with with feebump differ !!"
        );
        let cancel_tx_sighash_feebump = cancel_tx
            .signature_hash(1, SigHashType::All)
            .expect("Input exists");
        satisfy_transaction_input(
            &secp,
            &mut cancel_tx,
            0,
            &cancel_tx_without_feebump_sighash,
            &stakeholders_priv,
            Some(child_number),
            SigHashType::AllPlusAnyoneCanPay,
        )?;
        satisfy_transaction_input(
            &secp,
            &mut cancel_tx,
            1,
            &cancel_tx_sighash_feebump,
            &vec![feebump_xpriv],
            None, // No derivation path for the feebump key
            SigHashType::All,
        )?;
        cancel_tx.finalize(&secp)?;

        // We can create it without the feebump input
        let mut unemergency_tx_no_feebump = UnvaultEmergencyTransaction::new(
            rev_unvault_txin.clone(),
            None,
            emergency_address.clone(),
            0,
        );
        assert_eq!(h_unemer, unemergency_tx_no_feebump);
        // 376 is the witstrip weight of an emer tx (1 segwit input, 1 P2WSH txout), 22 is the feerate is sat/WU
        assert_eq!(
            unemergency_tx_no_feebump.fees(),
            (376 + rev_unvault_txin.txout().max_sat_weight() as u64) * 22,
        );
        let unemergency_tx_sighash = unemergency_tx_no_feebump
            .signature_hash(0, SigHashType::AllPlusAnyoneCanPay)
            .expect("Input exists");
        satisfy_transaction_input(
            &secp,
            &mut unemergency_tx_no_feebump,
            0,
            &unemergency_tx_sighash,
            &stakeholders_priv,
            Some(child_number),
            SigHashType::AllPlusAnyoneCanPay,
        )?;
        unemergency_tx_no_feebump.finalize(&secp)?;

        let feebump_txin = FeeBumpTxIn::new(
            OutPoint {
                txid: feebump_tx.0.txid(),
                vout: 0,
            },
            feebump_txo.clone(),
        );
        let mut unemergency_tx = UnvaultEmergencyTransaction::new(
            rev_unvault_txin.clone(),
            Some(feebump_txin),
            emergency_address,
            0,
        );
        satisfy_transaction_input(
            &secp,
            &mut unemergency_tx,
            0,
            &unemergency_tx_sighash,
            &stakeholders_priv,
            Some(child_number),
            SigHashType::AllPlusAnyoneCanPay,
        )?;
        // We don't have satisfied the feebump input yet!
        // Note that we clone because Miniscript's finalize() will wipe the PSBT input..
        match unemergency_tx.clone().finalize(&secp) {
            Err(e) => assert!(
                e.to_string()
                    .contains("Missing pubkey for a pkh/wpkh at index 1"),
                "Got another error: {}",
                e
            ),
            Ok(_) => unreachable!(),
        }
        // Now actually satisfy it, libbitcoinconsensus should not yell
        let unemer_tx_sighash_feebump = unemergency_tx
            .signature_hash(1, SigHashType::All)
            .expect("Input exists");
        satisfy_transaction_input(
            &secp,
            &mut unemergency_tx,
            1,
            &unemer_tx_sighash_feebump,
            &vec![feebump_xpriv],
            None,
            SigHashType::All,
        )?;
        unemergency_tx.finalize(&secp)?;

        // Now we can sign the unvault
        let unvault_tx_sighash = unvault_tx
            .signature_hash(0, SigHashType::All)
            .expect("Input exists");
        satisfy_transaction_input(
            &secp,
            &mut unvault_tx,
            0,
            &unvault_tx_sighash,
            &stakeholders_priv,
            Some(child_number),
            SigHashType::All,
        )?;

        unvault_tx.finalize(&secp)?;

        // Create and sign a spend transaction
        let spend_unvault_txin = unvault_tx.spend_unvault_txin(&der_unvault_descriptor); // Off-by-one csv
        let dummy_txo = TxOut::default();
        let cpfp_value = SpendTransaction::cpfp_txout(
            vec![spend_unvault_txin.clone()],
            vec![SpendTxOut::Destination(dummy_txo.clone())],
            &der_cpfp_descriptor,
            0,
        )
        .txout()
        .value;
        let fees = 20_000;
        let spend_txo = TxOut {
            // The CPFP output value won't be > 150k sats for our parameters
            value: spend_unvault_txin.txout().txout().value - cpfp_value - fees,
            ..TxOut::default()
        };

        // "This time for sure !"
        let spend_unvault_txin = unvault_tx.spend_unvault_txin(&der_unvault_descriptor); // Right csv
        let mut spend_tx = SpendTransaction::new(
            vec![spend_unvault_txin],
            vec![SpendTxOut::Destination(spend_txo.clone())],
            &der_cpfp_descriptor,
            0,
            true,
        )
        .expect("Amounts ok");
        let spend_tx_sighash = spend_tx
            .signature_hash(0, SigHashType::All)
            .expect("Input exists");
        satisfy_transaction_input(
            &secp,
            &mut spend_tx,
            0,
            &spend_tx_sighash,
            &managers_priv
                .iter()
                .chain(cosigners_priv.iter())
                .copied()
                .collect::<Vec<bip32::ExtendedPrivKey>>(),
            Some(child_number),
            SigHashType::All,
        )?;
        spend_tx.finalize(&secp)?;

        // The spend transaction can also batch multiple unvault txos
        let spend_unvault_txins = vec![
            UnvaultTxIn::new(
                OutPoint::from_str(
                    "0ed7dc14fe8d1364b3185fa46e940cb8e858f8de32e63f88353a2bd66eb99e2a:0",
                )
                .unwrap(),
                UnvaultTxOut::new(Amount::from_sat(deposit_value), &der_unvault_descriptor),
                csv,
            ),
            UnvaultTxIn::new(
                OutPoint::from_str(
                    "23aacfca328942892bb007a86db0bf5337005f642b3c46aef50c23af03ec333a:1",
                )
                .unwrap(),
                UnvaultTxOut::new(Amount::from_sat(deposit_value * 4), &der_unvault_descriptor),
                csv,
            ),
            UnvaultTxIn::new(
                OutPoint::from_str(
                    "fccabf4077b7e44ba02378a97a84611b545c11a1ef2af16cbb6e1032aa059b1d:0",
                )
                .unwrap(),
                UnvaultTxOut::new(Amount::from_sat(deposit_value / 2), &der_unvault_descriptor),
                csv,
            ),
            UnvaultTxIn::new(
                OutPoint::from_str(
                    "71dc04303184d54e6cc2f92d843282df2854d6dd66f10081147b84aeed830ae1:0",
                )
                .unwrap(),
                UnvaultTxOut::new(
                    Amount::from_sat(deposit_value * 50),
                    &der_unvault_descriptor,
                ),
                csv,
            ),
        ];
        let n_txins = spend_unvault_txins.len();
        let dummy_txo = TxOut::default();
        let cpfp_value = SpendTransaction::cpfp_txout(
            spend_unvault_txins.clone(),
            vec![SpendTxOut::Destination(dummy_txo.clone())],
            &der_cpfp_descriptor,
            0,
        )
        .txout()
        .value;
        let fees = 30_000;
        let spend_txo = TxOut {
            value: spend_unvault_txins
                .iter()
                .map(|txin| txin.txout().txout().value)
                .sum::<u64>()
                - cpfp_value
                - fees,
            ..TxOut::default()
        };
        let mut spend_tx = SpendTransaction::new(
            spend_unvault_txins,
            vec![SpendTxOut::Destination(spend_txo.clone())],
            &der_cpfp_descriptor,
            0,
            true,
        )
        .expect("Amounts Ok");
        assert_eq!(spend_tx.fees(), fees);
        let mut hash_cache = SigHashCache::new(spend_tx.tx());
        let sighashes: Vec<SigHash> = (0..n_txins)
            .into_iter()
            .map(|i| {
                spend_tx
                    .signature_hash_cached(i, SigHashType::All, &mut hash_cache)
                    .expect("Input exists")
            })
            .collect();
        for (i, spend_tx_sighash) in sighashes.into_iter().enumerate() {
            satisfy_transaction_input(
                &secp,
                &mut spend_tx,
                i,
                &spend_tx_sighash,
                &managers_priv
                    .iter()
                    .chain(cosigners_priv.iter())
                    .copied()
                    .collect::<Vec<bip32::ExtendedPrivKey>>(),
                Some(child_number),
                SigHashType::All,
            )?
        }
        spend_tx.finalize(&secp)?;

        #[cfg(feature = "use-serde")]
        {
            macro_rules! roundtrip {
                ($tx:ident) => {
                    let serialized_tx = serde_json::to_string(&$tx).unwrap();
                    let deserialized_tx = serde_json::from_str(&serialized_tx).unwrap();
                    assert_eq!($tx, deserialized_tx);
                };
            }

            roundtrip!(cancel_tx);
            roundtrip!(emergency_tx);
            roundtrip!(unvault_tx);
            roundtrip!(unemergency_tx);
            roundtrip!(spend_tx);
        }

        Ok(())
    }

    // Small sanity checks, see fuzzing targets for more.
    #[cfg(feature = "use-serde")]
    #[test]
    fn test_deserialize_psbt() {
        use crate::bitcoin::consensus::encode::serialize_hex;

        let emergency_psbt_str = "\"cHNidP8BAIcCAAAAAuEAZNxAy8+vO2xoZFvsBYlgw6wk5hMFlx2QfdJAB5dwAAAAAAD9////RpNyUTczj4LUHy4abwuVEH/ha2LhNEkhCljpi+DXvV4AAAAAAP3///8B92ADAAAAAAAiACB0FMmRlU42BMGHgxBjusio4tqifT6ICZ4n3kLt+3y8aAAAAAAAAQErh5QDAAAAAAAiACB0FMmRlU42BMGHgxBjusio4tqifT6ICZ4n3kLt+3y8aCICAtWJr8yKNegqMu9EXe0itf+ZHUpXnhy3kfQeJhP2ofJvSDBFAiEAze1vfVVe1iXV5BZRn4g2bVAmmIoT8nBIzzwxY5yC7eICIEtOnT/7Fw8mS08BbWW19gsTYZzFEBLmJi16OY7DLUPsgSICAg8j1MWiUjZfCK95R07epNukSEsiq1dD/LUlYdW6UArSSDBFAiEArazAnifYyQiE520TFE+qVHrRhtQIhhkJVZ01Aw4OEvUCIEuqzr2McD3zGnEc/yiv1oT1HAuPj0SMIAbk+qgQbHGLgQEDBIEAAAABBUdSIQIPI9TFolI2XwiveUdO3qTbpEhLIqtXQ/y1JWHVulAK0iEC1YmvzIo16Coy70Rd7SK1/5kdSleeHLeR9B4mE/ah8m9SrgABAR+a3QAAAAAAABYAFB5/7V9SvO31sHrYLQ+kuyZaMDkXIgIC5AXAiBkRjiyCnRA7ERx5zxHpEf0/DmrWiF9CstSuJeFIMEUCIQCQ/tFT2iK7rAl57tiXidM7JJ+TVx1FXg4Vu+4EJp5bSwIgOnfEV+xO59P7DJvvEue7qSRDNTGpzRQwwsP5yokME9YBAQMEAQAAAAAA\"";
        let emergency_tx: EmergencyTransaction = serde_json::from_str(&emergency_psbt_str).unwrap();
        assert_eq!(serialize_hex(emergency_tx.tx()), "0200000002e10064dc40cbcfaf3b6c68645bec058960c3ac24e61305971d907dd2400797700000000000fdffffff4693725137338f82d41f2e1a6f0b95107fe16b62e13449210a58e98be0d7bd5e0000000000fdffffff01f7600300000000002200207414c991954e3604c187831063bac8a8e2daa27d3e88099e27de42edfb7cbc6800000000");

        let unvault_psbt_str = "\"cHNidP8BAIkCAAAAAcNuW/2BGMjVscmagDIp0qcLczfNqcYsR0VmBlH0RKSxAAAAAAD9////AkANAwAAAAAAIgAg+aW89btq9yILwX2pSyXJVkCbXsMhUYUKiS9DK3TF42kwdQAAAAAAACIAIMd3+o0VPULHPxJ3dJNASnrGGZpKuuWXCQvPqH5VelwfAAAAAAABASuIlAMAAAAAACIAIE0NCW/hG4IJz3MGCXWOAxzUOoeCsAb8+wHCjZ8nbdjVIgID9cKEhz20F3M+WmbI6fJ/feB9/3pB7koww2bS7UXwtwNHMEQCIEKMsiuj3G7FYxYyHJ49SLNDiAN7raGfdit6a34S87vmAiAuTAGPx3oEo5cE4qa8M6+jmkfHOjS6HzIsBJTUaEFK5wEiAgKYBZ07lA0xglPqVmsqvbvk9Nr5c8vO4Qfrfg1aE05KjkcwRAIgNUEqQwg62+DsrRkEKGaxVPZJtsblXDf5+EaKTOC+XXUCICLe6EMJRW+gyeEdQ3xeJ8IzspVSPZ4Yr1mUmOLyDTzqAQEDBAEAAAABBUdSIQP1woSHPbQXcz5aZsjp8n994H3/ekHuSjDDZtLtRfC3AyECmAWdO5QNMYJT6lZrKr275PTa+XPLzuEH634NWhNOSo5SrgABAashA572FVyzkVmn2VFQgcflckhMyUlgiKS59dRKjkY/um3trFGHZHapFMF2tEWP+sH2PBsMi9ebGQJ+OCyDiKxrdqkUrOnriNTE8/ct3vDm5450tA6IzJ6IrGyTUodnUiED1gNSfO7c/ssUM6GsmpnnbFpjTo3QBd5ioVkPjYPYfU0hAzPCmTt3aK+Gv3oUQ00b5OB3or92V8aSLpnbXJICtHAgUq8DqYwAsmgAAQElIQOe9hVcs5FZp9lRUIHH5XJITMlJYIikufXUSo5GP7pt7axRhwA=\"";
        let unvault_tx: UnvaultTransaction = serde_json::from_str(&unvault_psbt_str).unwrap();
        assert_eq!(serialize_hex(unvault_tx.tx()), "0200000001c36e5bfd8118c8d5b1c99a803229d2a70b7337cda9c62c4745660651f444a4b10000000000fdffffff02400d030000000000220020f9a5bcf5bb6af7220bc17da94b25c956409b5ec32151850a892f432b74c5e3693075000000000000220020c777fa8d153d42c73f12777493404a7ac6199a4abae597090bcfa87e557a5c1f00000000");

        let cancel_psbt_str = "\"cHNidP8BAIcCAAAAAkzK5VoK+JM1I4Xw3KiZP35JunqWaha/kxVH9Fc319rXAAAAAAD9////X9QhbL8SgePLKkLsEYjqhfvEGuCKCVA+gbLKqED1LCcAAAAAAP3///8B0soCAAAAAAAiACBa7dstF6Vns+rNRmKY7eGlFhEC2AAtFyTTeDgluwC2dQAAAAAAAQErQA0DAAAAAAAiACC+HKr/IXfz+quxmQ5qtpJCxZoxx+qrRk4C9POIjpNtcCICAgOXAVovp7XCt5x9D2Sm9/AUXznCaff+S/E6Jy70QLwBRzBEAiAy4dGtkOpTo4Wfpfy2rQPHl2r7XFHTuA2yph4+NDJwRAIgUCQVs1jd1CwvIYveS1EC5sNnDdQktHWkr6WyWnG+duGBIgIDCLuhnyMFaiARCK4sPM8o59gvmw7TyPWOfV9Ayqc7ZahIMEUCIQC2SmI3M+joZZEAg6yoo6blcfKKaMQ9qxcITsDRFyeOxwIgThKCj6Ff4osPuAUA1EIPLxVrAHpKSJGpFGdQGpFTzfOBAQMEgQAAAAEFqyECMBWn8Nqgn7qUY1l+vvScCE4qqbxVBdTolF9Tkv3HjY2sUYdkdqkUeWykpAk/X2ax7K78ROp7r1WtskWIrGt2qRRQDXd90K8a9quA2J9lNts/kbniiYisbJNSh2dSIQIl55eP2dgCboG44aNDNCJvHN9E1q0xh9OzkWkpDT4JiSECcWxkAv3PuRl+Sw+Apd5i41Ezo37D7OecM3xe5eLYZY9SrwNdhgCyaAABAR+a3QAAAAAAABYAFO+2Up6bJOYgAT5JTiN1eP0QVoSjIgIDuy9MjTR/VKR5dOisywUugQJfVeuaYxAc7Lsx+Tey1jJIMEUCIQC/jvo652Srj3gD3GHtn6IaGVcJe6vkae5Tpz6CIVjl6QIgRC7zW3y4ELeM7Sx6nPfe1vyyWSYWaUG1S7v9qKtQK/0BAQMEAQAAAAABAUdSIQIDlwFaL6e1wrecfQ9kpvfwFF85wmn3/kvxOicu9EC8ASEDCLuhnyMFaiARCK4sPM8o59gvmw7TyPWOfV9Ayqc7ZahSrgA=\"";
        let cancel_tx: CancelTransaction = serde_json::from_str(&cancel_psbt_str).unwrap();
        assert_eq!(serialize_hex(cancel_tx.tx()), "02000000024ccae55a0af893352385f0dca8993f7e49ba7a966a16bf931547f45737d7dad70000000000fdffffff5fd4216cbf1281e3cb2a42ec1188ea85fbc41ae08a09503e81b2caa840f52c270000000000fdffffff01d2ca0200000000002200205aeddb2d17a567b3eacd466298ede1a5161102d8002d1724d3783825bb00b67500000000");

        let unemergency_psbt_str = "\"cHNidP8BAIcCAAAAAjyplGpzwkN/c/J75I4KXj7T0IxdhbgFvD5tU4Blnu7KAAAAAAD9////ur9klIwGPaAJacaRQjZpqT9Obs7lska/UMIYQNIH0rcAAAAAAP3///8B0soCAAAAAAAiACCTwim9CPURWR1tVH0w4Y2htmm1Ehh3lq2v1GXhrNUrJwAAAAAAAQErQA0DAAAAAAAiACAACUXLCIZBJ3kDiQattxqigOSInOlK95jxt6EALplTmiICA4OOG3CDuASrKTLzHkEXMImS4aRuzwYLCcTenQH86TLUSDBFAiEA2Sho2nPY66x309D84Bg1twwDOTsUXZ/VmU9MJD9Q4NwCIH1Xh/iloOuo88w9Sc5vDt8Fu385g74+kIwoTykFxbrzgSICAwXaX6NHGbjnVBZYyOIGlLGIRQuIrlN/9dzPz+wZ8hX/RzBEAiACe6bwR6lmcUqfFI/bWoda7q68jc2NNjwJXvG9myGicgIgakM2wQXYqWlEyxwIfyiBkdKT6mWAoPUVq5VFETknf/aBAQMEgQAAAAEFqyECvmXlD4O+L/PFOPumxXyqXd75CEdOPu9lF3gYHLFn4GKsUYdkdqkU7bwUkACg4kLrKTZ9JPFXAuVlvO2IrGt2qRRtrZkIOsEBwl/MbemKESkFo3OllIisbJNSh2dSIQPOgJoUmqKJHsneJ0rfZU3GJaor5YspkCEPTKVbu65vWiECdDni0vMnZykunRfyZWfjOlmD3iJMuptvRti4N89Ty65SrwOyigCyaAABAR+a3QAAAAAAABYAFDD9xz18wXMKz9j0B6pHKbLXMQEOIgICNL89JGq3AY8G+GX+dChQ4WnmeluAZNMgQVkxH/0MX4tIMEUCIQCDqaRzs/7gLCxV1o1qPOJT7xdjAW38SVMY4o2JXR3LkwIgIsGL9LR3nsTuzPfSEMTUyKnPZ+07Rr8GOTGuZ4YsYtYBAQMEAQAAAAAA\"";
        let unemergency_tx: UnvaultEmergencyTransaction =
            serde_json::from_str(&unemergency_psbt_str).unwrap();
        assert_eq!(serialize_hex(unemergency_tx.tx()), "02000000023ca9946a73c2437f73f27be48e0a5e3ed3d08c5d85b805bc3e6d5380659eeeca0000000000fdffffffbabf64948c063da00969c691423669a93f4e6ecee5b246bf50c21840d207d2b70000000000fdffffff01d2ca02000000000022002093c229bd08f511591d6d547d30e18da1b669b512187796adafd465e1acd52b2700000000");

        let spend_psbt_str = "\"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\"";
        let spend_tx: SpendTransaction = serde_json::from_str(&spend_psbt_str).unwrap();
        assert_eq!(serialize_hex(&spend_tx.into_tx()), "020000000001042a9eb96ed62b3a35883fe632def858e8b80c946ea45f18b364138dfe14dcd70e00000000005ed000003a33ec03af230cf5ae463c2b645f003753bfb06da807b02b89428932cacfaa2301000000005ed000001d9b05aa32106ebb6cf12aefa1115c541b61847aa97823a04be4b77740bfcafc00000000005ed00000e10a83edae847b148100f166ddd65428df8232842df9c26c4ed584313004dc7100000000005ed0000002006f0200000000002200202a3ba224413511e5fc8447c9101d477e2f95db7113ae9fca0b1ef84aac122c605cf6c30000000000000500483045022100a36217e123dea9719dbbc704075dc191f08393537e91ff2630eaf0c7ab89677802207604b290f81148edf8f33c0f84f9aad1391a3513e7a687f721267fc48247adde01473044022055da6db73cf4af14bf8294933dc1b738841c2d6ad371215ceafb61701ac14d9402203626f79d9367ae382041136e52bb378df836b16a97b71c15333bfa3523fbdba701483045022100b2a1b4559bca2719b4abaa7c172329f97b198d5eda2d944d24b684cb42291232022038d74603e78e8e35e02adbe08f93ce90d5d407508463f8e425ddd98abe8fda1701ab2103dacf1ec4d8caaabac45e9237e09d69aadce1b8945dcc4776fe73fb9f4c31f7a4ac51876476a914594f6cd0c51687611968c77d63f40f0422ee26ae88ac6b76a9147ec81e31ce46a8c539882613ee54444fab4fe8a288ac6c93528767522102bf9959bfd4e22513e55bb5905ef3a2a29f9f924adb00c627fd1d92b67ff9cf942102fe9abf103eaa2e1180328774261155380eff416a179e61b0a4be99abcaf88d9b52af035ed000b26805004730440220194744ced4f4637ba2b351bd2562632e93a0e39cc087702514fc2b7fa2da4c0a0220700803ec7e681b1ea31b6463711912dc70bad7bbf50b9f3e063c942a8c1bfe72014730440220216306533836fccc08f07cd8ede702f7ef283539943dc10b93576892ed807217022019bd34f280f74578331377b15cb0f3184d30b2ddb87edd79a0bc63db17aa726b0147304402203a24c13039e1a5abdd8d22dc44036b415b96a4a6cf449145f5bcc89a48cf32af022052c6a253de2c38e41fff9cf16f4869a78e07535ec5806a2ff3f985cb7993fbe201ab2103dacf1ec4d8caaabac45e9237e09d69aadce1b8945dcc4776fe73fb9f4c31f7a4ac51876476a914594f6cd0c51687611968c77d63f40f0422ee26ae88ac6b76a9147ec81e31ce46a8c539882613ee54444fab4fe8a288ac6c93528767522102bf9959bfd4e22513e55bb5905ef3a2a29f9f924adb00c627fd1d92b67ff9cf942102fe9abf103eaa2e1180328774261155380eff416a179e61b0a4be99abcaf88d9b52af035ed000b2680500483045022100bea60c83db41973c639d42cd3525efe82b15456bfba0a904fb77ccb8a8e054cb02206498d4a777c56f943f388eb0f1d765ee8395d1c2e781486d0dd4f0700adc8f0901473044022052ebc8f31d96bd172f2491cd85b0ef9b4aa1f2408e185781cd57a550d7b4f463022069f9e78d039665d5a53c13752d1719e567928c465219a64aa7ee5bc89578b4ad01483045022100b29bf7526aab5fad36f77ecd628352afc12d00c32a0747ad91dd61aae767e4d2022023f0c040ee84caf653d541d8b5f1ac6472e52199056112d99d3a739e57bfaac501ab2103dacf1ec4d8caaabac45e9237e09d69aadce1b8945dcc4776fe73fb9f4c31f7a4ac51876476a914594f6cd0c51687611968c77d63f40f0422ee26ae88ac6b76a9147ec81e31ce46a8c539882613ee54444fab4fe8a288ac6c93528767522102bf9959bfd4e22513e55bb5905ef3a2a29f9f924adb00c627fd1d92b67ff9cf942102fe9abf103eaa2e1180328774261155380eff416a179e61b0a4be99abcaf88d9b52af035ed000b2680500483045022100af1f4b2c3455b044970e8bf62c9e75b4b3e87b5bac7af3b3e33a101e3eebed7202204c377b3764a7dfeccb2f82af327eb23dbf408ae48284a1a7206f43dc04a0b39701483045022100f221ee515d63aef0f27545b736367d0d1ae3ce4433b8818686587decc048b1cc0220536fdfb7470dcd28db813d0efcc2acb364a4d1eece7afcdc9510525993f7487401483045022100faca69e1e8c7b969f0ca666a358693b6bac50b9c02c3722dc2d27a0ccc664563022006ce6039bfcae8a28d74b3d584c37723b466983a4c0ccb63591df74185850a5101ab2103dacf1ec4d8caaabac45e9237e09d69aadce1b8945dcc4776fe73fb9f4c31f7a4ac51876476a914594f6cd0c51687611968c77d63f40f0422ee26ae88ac6b76a9147ec81e31ce46a8c539882613ee54444fab4fe8a288ac6c93528767522102bf9959bfd4e22513e55bb5905ef3a2a29f9f924adb00c627fd1d92b67ff9cf942102fe9abf103eaa2e1180328774261155380eff416a179e61b0a4be99abcaf88d9b52af035ed000b26800000000");
    }
}

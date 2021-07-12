//! Revault transactions
//!
//! Typesafe routines to create Revault-specific Bitcoin transactions.
//!
//! We use PSBTs as defined in [bip-0174](https://github.com/bitcoin/bips/blob/master/bip-0174.mediawiki)
//! for data structure as well as roles distribution.

use crate::{error::*, scripts::*, txins::*, txouts::*};
use miniscript::bitcoin::{
    consensus::encode::Encodable,
    hash_types,
    hashes::Hash,
    secp256k1,
    util::{bip143::SigHashCache, bip32::ChildNumber, psbt::PartiallySignedTransaction as Psbt},
    Address, Amount, Network, OutPoint, PublicKey as BitcoinPubKey, Script, SigHash, SigHashType,
    Transaction, Txid, Wtxid,
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

/// A Revault transaction.
///
/// Wraps a rust-bitcoin PSBT and defines some BIP174 roles as methods.
/// Namely:
/// - Creator and updater
/// - Signer
/// - Finalizer
/// - Extractor and serializer
pub trait RevaultTransaction: fmt::Debug + Clone + PartialEq {
    /// Get the inner PSBT
    fn psbt(&self) -> &Psbt;

    // FIXME: how can we not expose this? This in theory breaks our internal assumptions as the
    // caller could just put the inner PSBT in an insane state..
    /// Get the inner PSBT
    fn psbt_mut(&mut self) -> &mut Psbt;

    /// Move inner PSBT out
    fn into_psbt(self) -> Psbt;

    /// Get the sighash for an input of a Revault transaction. Will deduce the scriptCode from
    /// the previous scriptPubKey type, assuming either P2WSH or P2WPKH.
    ///
    /// Will error if the input is out of bounds or the PSBT input is insane (eg a P2WSH that
    /// does not contain a Witness Script (ie was already finalized)).
    fn signature_hash(
        &self,
        input_index: usize,
        sighash_type: SigHashType,
    ) -> Result<SigHash, InputSatisfactionError> {
        let mut cache = SigHashCache::new(self.tx());
        self.signature_hash_cached(input_index, sighash_type, &mut cache)
    }

    /// Cached version of [RevaultTransaction::signature_hash]
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
            use miniscript::bitcoin::hashes::hex::ToHex;
            eprintln!(
                "Tx: '{}', index: '{}', Witscript: '{}', value: '{}', type: '{}', hash: '{}', hash2: '{}'",
                miniscript::bitcoin::consensus::encode::serialize_hex(self.tx()),
                input_index,
                witscript.to_bytes().to_hex(),
                prev_txo.value,
                sighash_type,
                cache.signature_hash(input_index, &witscript, prev_txo.value, sighash_type),
                SigHashCache::new(self.tx()).signature_hash(input_index, &witscript, prev_txo.value, sighash_type)
            );
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

    /// Add a signature in order to eventually satisfy this input.
    ///
    /// Checks the signature according to the specified expected sighash type in the PSBT input.
    ///
    /// The BIP174 Signer role.
    fn add_signature<C: secp256k1::Verification>(
        &mut self,
        input_index: usize,
        pubkey: secp256k1::PublicKey,
        signature: secp256k1::Signature,
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

        let expected_sighash_type = psbtin
            .sighash_type
            .expect("We always set the SigHashType in the constructor.");
        let sighash = self.signature_hash(input_index, expected_sighash_type)?;
        let sighash = secp256k1::Message::from_slice(&sighash).expect("sighash is 32 a bytes hash");
        secp.verify(&sighash, &signature, &pubkey)
            .map_err(|_| InputSatisfactionError::InvalidSignature(signature, pubkey, sighash))?;

        let pubkey = BitcoinPubKey {
            compressed: true,
            key: pubkey,
        };
        let mut rawsig = signature.serialize_der().to_vec();
        rawsig.push(expected_sighash_type.as_u32() as u8);

        let psbtin = self
            .psbt_mut()
            .inputs
            .get_mut(input_index)
            .expect("Checked at the beginning.");
        Ok(psbtin.partial_sigs.insert(pubkey, rawsig))
    }

    /// Check and satisfy the scripts, create the witnesses.
    ///
    /// The BIP174 Input Finalizer role.
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

    /// Create a RevaultTransaction from a BIP174-serialized transaction.
    fn from_psbt_serialized(raw_psbt: &[u8]) -> Result<Self, TransactionSerialisationError>;

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

#[cfg(any(test, feature = "fuzz"))]
pub mod tests_helpers;

#[cfg(test)]
mod tests {
    use super::tests_helpers::derive_transactions;
    use crate::{error::*, scripts::*};

    use miniscript::bitcoin::{blockdata::constants::COIN_VALUE, secp256k1, OutPoint};

    use std::str::FromStr;

    #[test]
    fn transaction_derivation() {
        let secp = secp256k1::Secp256k1::new();
        let csv = fastrand::u32(..SEQUENCE_LOCKTIME_MASK);
        eprintln!("Using a CSV of '{}'", csv);

        let deposit_prevout = OutPoint::from_str(
            "39a8212c6a9b467680d43e47b61b8363fe1febb761f9f548eb4a432b2bc9bbec:0",
        )
        .unwrap();
        let feebump_prevout = OutPoint::from_str(
            "4bb4545bb4bc8853cb03e42984d677fbe880c81e7d95609360eed0d8f45b52f8:0",
        )
        .unwrap();
        let feebump_value = 56730;
        let unvaults_spent = vec![
            (
                OutPoint::from_str(
                    "0ed7dc14fe8d1364b3185fa46e940cb8e858f8de32e63f88353a2bd66eb99e2a:0",
                )
                .unwrap(),
                1_000_000,
            ),
            (
                OutPoint::from_str(
                    "23aacfca328942892bb007a86db0bf5337005f642b3c46aef50c23af03ec333a:1",
                )
                .unwrap(),
                2_897_120,
            ),
            (
                OutPoint::from_str(
                    "fccabf4077b7e44ba02378a97a84611b545c11a1ef2af16cbb6e1032aa059b1d:0",
                )
                .unwrap(),
                9_327_465_907_334,
            ),
            (
                OutPoint::from_str(
                    "71dc04303184d54e6cc2f92d843282df2854d6dd66f10081147b84aeed830ae1:0",
                )
                .unwrap(),
                234_631,
            ),
        ];

        // Test the dust limit
        assert_eq!(
            derive_transactions(
                2,
                1,
                csv,
                deposit_prevout,
                234_631,
                feebump_prevout,
                feebump_value,
                unvaults_spent.clone(),
                &secp
            )
            .unwrap_err()
            .to_string(),
            Error::TransactionCreation(TransactionCreationError::Dust).to_string()
        );
        // Non-minimal CSV
        derive_transactions(
            2,
            1,
            SEQUENCE_LOCKTIME_MASK + 1,
            deposit_prevout,
            300_000,
            feebump_prevout,
            feebump_value,
            unvaults_spent.clone(),
            &secp,
        )
        .expect_err("Unclean CSV");

        // Absolute minimum
        derive_transactions(
            2,
            1,
            csv,
            deposit_prevout,
            234_632,
            feebump_prevout,
            feebump_value,
            unvaults_spent.clone(),
            &secp,
        )
        .expect(&format!(
            "Tx chain with 2 stakeholders, 1 manager, {} csv, 235_250 deposit",
            csv
        ));
        // 1 BTC
        derive_transactions(
            8,
            3,
            csv,
            deposit_prevout,
            COIN_VALUE,
            feebump_prevout,
            feebump_value,
            unvaults_spent.clone(),
            &secp,
        )
        .expect(&format!(
            "Tx chain with 8 stakeholders, 3 managers, {} csv, 1_000_000 deposit",
            csv
        ));
        // 100 000 BTC
        derive_transactions(
            8,
            3,
            csv,
            deposit_prevout,
            100_000 * COIN_VALUE,
            feebump_prevout,
            feebump_value,
            unvaults_spent.clone(),
            &secp,
        )
        .expect(&format!(
            "Tx chain with 8 stakeholders, 3 managers, {} csv, 100_000_000_000_000 deposit",
            csv
        ));
        // 100 BTC
        derive_transactions(
            38,
            5,
            csv,
            deposit_prevout,
            100 * COIN_VALUE,
            feebump_prevout,
            feebump_value,
            unvaults_spent,
            &secp,
        )
        .expect(&format!(
            "Tx chain with 38 stakeholders, 5 manager, {} csv, 100_000_000_000 deposit",
            csv
        ));
    }

    #[test]
    fn repro() {
        use miniscript::bitcoin::{hashes::Hash, Txid};

        let secp = secp256k1::Secp256k1::new();

        let deposit_txid = [
            2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 39, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0,
            0, 0, 0, 12,
        ];
        let deposit_outpoint = OutPoint {
            txid: Txid::from_slice(&deposit_txid).unwrap(),
            vout: 0,
        };
        let feebump_txid = [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 226, 145, 227, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
        ];
        let feebump_outpoint = OutPoint {
            txid: Txid::from_slice(&feebump_txid).unwrap(),
            vout: 0,
        };
        let deposit_value = 1065135112192;
        let feebump_value = 18446744073709551615;

        let unvault_txid_a = [
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 42, 255,
        ];
        let unvault_a = OutPoint {
            txid: Txid::from_slice(&unvault_txid_a).unwrap(),
            vout: 4294967295,
        };
        let unvault_value_a = 2377900603251621887;

        let unvault_txid_b = [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 172, 255, 255, 255, 1, 136, 98, 189, 244,
            2, 2, 2, 2, 2, 2, 2, 2,
        ];
        let unvault_b = OutPoint {
            txid: Txid::from_slice(&unvault_txid_b).unwrap(),
            vout: 33686018,
        };
        let unvault_value_b = 7451037802315252226;

        derive_transactions(
            2,
            8,
            3,
            deposit_outpoint,
            deposit_value,
            feebump_outpoint,
            feebump_value,
            vec![(unvault_a, unvault_value_a), (unvault_b, unvault_value_b)],
            &secp,
        )
        .unwrap();
    }

    #[test]
    fn repro2() {
        use miniscript::bitcoin::{
            blockdata::transaction::SigHashType, consensus::encode::deserialize,
            hashes::hex::FromHex, util::bip143::SigHashCache, Script, Transaction,
        };
        let tx_bytes = Vec::<u8>::from_hex("020000000182000000000000000000000000000000000000000000000000000000000000000000000000fdffffff0170ccfffef7000000220020b20000000000000000000000000000000000000000000000000000000000000000000000").unwrap();
        let tx: Transaction = deserialize(&tx_bytes).unwrap();
        let witscript = Script::from_hex("522103b50000000000000000000000000000014551231950b75fc4402da1732fc9bebf2103a90000000000000000000000000000014551231950b75fc4402da1732fc9bebf52ae").unwrap();
        let value = 1065135112192;

        let sighash_all =
            SigHashCache::new(&tx).signature_hash(0, &witscript, value, SigHashType::All);
        let sighash_acp = SigHashCache::new(&tx).signature_hash(
            0,
            &witscript,
            value,
            SigHashType::AllPlusAnyoneCanPay,
        );
        assert_ne!(sighash_all, sighash_acp,);
    }

    // Small sanity checks, see fuzzing targets for more.
    #[cfg(feature = "use-serde")]
    #[test]
    fn test_deserialize_psbt() {
        use super::{
            CancelTransaction, EmergencyTransaction, RevaultTransaction, SpendTransaction,
            UnvaultEmergencyTransaction, UnvaultTransaction,
        };
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

use crate::{
    error::*,
    scripts::*,
    transactions::{
        utils, RevaultTransaction, INSANE_FEES, MAX_STANDARD_TX_WEIGHT, REVAULTING_TX_FEERATE,
        TX_VERSION,
    },
    txins::*,
    txouts::*,
};

use miniscript::bitcoin::{
    consensus::encode::Decodable,
    util::psbt::{
        Global as PsbtGlobal, Input as PsbtIn, Output as PsbtOut,
        PartiallySignedTransaction as Psbt,
    },
    Amount, SigHashType, Transaction,
};

#[cfg(feature = "use-serde")]
use {
    serde::de::{self, Deserialize, Deserializer},
    serde::ser::{Serialize, Serializer},
};

use std::{collections::BTreeMap, convert::TryInto};

impl_revault_transaction!(
    CancelTransaction,
    doc = "The transaction \"revaulting\" a spend attempt, i.e. spending the unvaulting transaction back to a deposit txo."
);
impl CancelTransaction {
    // Internal DRY routine for creating the inner PSBT
    fn create_psbt(
        unvault_txin: UnvaultTxIn,
        feebump_txin: Option<FeeBumpTxIn>,
        deposit_txo: DepositTxOut,
        lock_time: u32,
    ) -> Psbt {
        let mut txins = vec![unvault_txin.unsigned_txin()];
        let mut psbtins = vec![PsbtIn {
            witness_script: Some(unvault_txin.txout().witness_script().clone()),
            sighash_type: Some(SigHashType::AllPlusAnyoneCanPay),
            witness_utxo: Some(unvault_txin.into_txout().into_txout()),
            ..PsbtIn::default()
        }];
        if let Some(feebump_txin) = feebump_txin {
            txins.push(feebump_txin.unsigned_txin());
            psbtins.push(PsbtIn {
                sighash_type: Some(SigHashType::All),
                witness_utxo: Some(feebump_txin.into_txout().into_txout()),
                ..PsbtIn::default()
            });
        }

        Psbt {
            global: PsbtGlobal {
                unsigned_tx: Transaction {
                    version: TX_VERSION,
                    lock_time,
                    input: txins,
                    output: vec![deposit_txo.into_txout()],
                },
                version: 0,
                xpub: BTreeMap::new(),
                proprietary: BTreeMap::new(),
                unknown: BTreeMap::new(),
            },
            inputs: psbtins,
            // Deposit txout
            outputs: vec![PsbtOut::default()],
        }
    }

    /// A cancel transaction always pays to a deposit output and spends the unvault output, and
    /// may have a fee-bumping input.
    ///
    /// BIP174 Creator and Updater roles.
    pub fn new(
        unvault_input: UnvaultTxIn,
        feebump_input: Option<FeeBumpTxIn>,
        deposit_descriptor: &DerivedDepositDescriptor,
        lock_time: u32,
    ) -> CancelTransaction {
        // First, create a dummy transaction to get its weight without Witness. Note that we always
        // account for the weight *without* feebump input. It pays for itself.
        let dummy_deposit_txo = DepositTxOut::new(Amount::from_sat(u64::MAX), deposit_descriptor);
        let dummy_tx = CancelTransaction::create_psbt(
            unvault_input.clone(),
            None,
            dummy_deposit_txo,
            lock_time,
        )
        .global
        .unsigned_tx;

        // The weight of the cancel transaction without a feebump input is the weight of the
        // witness-stripped transaction plus the weight required to satisfy the unvault txin
        let total_weight = dummy_tx
            .get_weight()
            .checked_add(unvault_input.txout().max_sat_weight())
            .expect("Properly computed weight won't overflow");
        let total_weight: u64 = total_weight.try_into().expect("usize in u64");
        let fees = REVAULTING_TX_FEERATE
            .checked_mul(total_weight)
            .expect("Properly computed weight won't overflow");
        // Without the feebump input, it should not be reachable.
        debug_assert!(fees < INSANE_FEES);

        assert!(
            total_weight <= MAX_STANDARD_TX_WEIGHT as u64,
            "At most 2 inputs and single output"
        );

        // Now, get the revaulting output value out of it.
        let unvault_value = unvault_input.txout().txout().value;
        let revault_value = unvault_value
            .checked_sub(fees)
            .expect("We would not create a dust unvault txo");
        let deposit_txo = DepositTxOut::new(Amount::from_sat(revault_value), deposit_descriptor);

        CancelTransaction(CancelTransaction::create_psbt(
            unvault_input,
            feebump_input,
            deposit_txo,
            lock_time,
        ))
    }

    /// Parse a Cancel transaction from a PSBT
    pub fn from_raw_psbt(raw_psbt: &[u8]) -> Result<Self, TransactionSerialisationError> {
        let psbt = Decodable::consensus_decode(raw_psbt)?;
        let psbt = utils::psbt_common_sanity_checks(psbt)?;

        // Deposit txo
        let output_count = psbt.global.unsigned_tx.output.len();
        if output_count != 1 {
            return Err(PsbtValidationError::InvalidOutputCount(output_count).into());
        }

        // Deposit txo is P2WSH
        let output = &psbt.outputs[0];
        if output.redeem_script.is_some() {
            return Err(PsbtValidationError::InvalidOutputField(output.clone()).into());
        }

        let input_count = psbt.global.unsigned_tx.input.len();
        if input_count > 2 {
            return Err(PsbtValidationError::InvalidInputCount(input_count).into());
        }
        if input_count > 1 {
            let input = utils::find_feebumping_input(&psbt.inputs)
                .ok_or(PsbtValidationError::MissingFeeBumpingInput)?;
            utils::check_feebump_input(&input)?;
        }
        let input = utils::find_revocationtx_input(&psbt.inputs)
            .ok_or(PsbtValidationError::MissingRevocationInput)?;
        utils::check_revocationtx_input(&input)?;

        Ok(CancelTransaction(psbt))
    }
}

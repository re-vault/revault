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
    EmergencyTransaction,
    doc = "The transaction spending a deposit output to The Emergency Script."
);
impl EmergencyTransaction {
    // Internal DRY routine for creating the inner PSBT
    fn create_psbt(
        deposit_txin: DepositTxIn,
        feebump_txin: Option<FeeBumpTxIn>,
        emergency_txo: EmergencyTxOut,
        lock_time: u32,
    ) -> Psbt {
        let mut txins = vec![deposit_txin.unsigned_txin()];
        let mut psbtins = vec![PsbtIn {
            witness_script: Some(deposit_txin.txout().witness_script().clone()),
            sighash_type: Some(SigHashType::AllPlusAnyoneCanPay),
            witness_utxo: Some(deposit_txin.into_txout().into_txout()),
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
                    output: vec![emergency_txo.into_txout()],
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

    /// The first emergency transaction always spends a deposit output and pays to the Emergency
    /// Script. It may also spend an additional output for fee-bumping.
    /// Will error **only** when trying to spend a dust deposit.
    ///
    /// BIP174 Creator and Updater roles.
    pub fn new(
        deposit_input: DepositTxIn,
        feebump_input: Option<FeeBumpTxIn>,
        emer_address: EmergencyAddress,
        lock_time: u32,
    ) -> Result<EmergencyTransaction, TransactionCreationError> {
        // First, create a dummy transaction to get its weight without Witness. Note that we always
        // account for the weight *without* feebump input. It has to pay for itself.
        let emer_txo = EmergencyTxOut::new(emer_address.clone(), Amount::from_sat(u64::MAX));
        let dummy_tx =
            EmergencyTransaction::create_psbt(deposit_input.clone(), None, emer_txo, lock_time)
                .global
                .unsigned_tx;

        // The weight of the emergency transaction without a feebump input is the weight of the
        // witness-stripped transaction plus the weight required to satisfy the deposit txin
        let total_weight = dummy_tx
            .get_weight()
            .checked_add(deposit_input.txout().max_sat_weight())
            .expect("Weight computation bug");
        let total_weight: u64 = total_weight.try_into().expect("usize in u64");
        let fees = REVAULTING_TX_FEERATE
            .checked_mul(total_weight)
            .expect("Weight computation bug");
        // Without the feebump input, it should not be reachable.
        debug_assert!(fees < INSANE_FEES);

        assert!(
            total_weight <= MAX_STANDARD_TX_WEIGHT as u64,
            "At most 2 inputs and a single output"
        );

        // Now, get the emergency output value out of it.
        let deposit_value = deposit_input.txout().txout().value;
        let emer_value = deposit_value
            .checked_sub(fees)
            .ok_or(TransactionCreationError::Dust)?;
        let emer_txo = EmergencyTxOut::new(emer_address, Amount::from_sat(emer_value));

        Ok(EmergencyTransaction(EmergencyTransaction::create_psbt(
            deposit_input,
            feebump_input,
            emer_txo,
            lock_time,
        )))
    }

    /// Parse an Emergency transaction from a PSBT
    pub fn from_raw_psbt(raw_psbt: &[u8]) -> Result<Self, TransactionSerialisationError> {
        let psbt = Decodable::consensus_decode(raw_psbt)?;
        let psbt = utils::psbt_common_sanity_checks(psbt)?;

        // Emergency txo
        let output_count = psbt.global.unsigned_tx.output.len();
        if output_count != 1 {
            return Err(PsbtValidationError::InvalidOutputCount(output_count).into());
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

        Ok(EmergencyTransaction(psbt))
    }
}

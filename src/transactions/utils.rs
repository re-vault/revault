use crate::{error::*, transactions::TX_VERSION};

use miniscript::bitcoin::{
    util::psbt::{Input as PsbtIn, PartiallySignedTransaction as Psbt},
    OutPoint, SigHashType,
};

use std::collections::HashSet;

/// Boilerplate for defining a Revault transaction as a newtype over a Psbt and implementing
/// RevaultTransaction for it.
macro_rules! impl_revault_transaction {
    ( $transaction_name:ident, $doc_comment:meta ) => {
        use crate::transactions::inner_mut;
        use std::{fmt, str};

        #[$doc_comment]
        #[derive(Debug, Clone, PartialEq)]
        pub struct $transaction_name(Psbt);

        impl inner_mut::PrivateInnerMut for $transaction_name {
            fn psbt(&self) -> &Psbt {
                &self.0
            }

            fn psbt_mut(&mut self) -> &mut Psbt {
                &mut self.0
            }

            fn into_psbt(self) -> Psbt {
                self.0
            }

            fn from_psbt_serialized(
                raw_psbt: &[u8],
            ) -> Result<Self, TransactionSerialisationError> {
                $transaction_name::from_raw_psbt(raw_psbt)
            }
        }

        #[cfg(feature = "use-serde")]
        impl Serialize for $transaction_name {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                if serializer.is_human_readable() {
                    serializer.serialize_str(&self.as_psbt_string())
                } else {
                    serializer.serialize_bytes(&self.as_psbt_serialized())
                }
            }
        }

        #[cfg(feature = "use-serde")]
        impl<'de> Deserialize<'de> for $transaction_name {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                if deserializer.is_human_readable() {
                    $transaction_name::from_psbt_str(&String::deserialize(deserializer)?)
                        .map_err(de::Error::custom)
                } else {
                    $transaction_name::from_psbt_serialized(&Vec::<u8>::deserialize(deserializer)?)
                        .map_err(de::Error::custom)
                }
            }
        }

        impl fmt::Display for $transaction_name {
            fn fmt(&self, f: &mut fmt::Formatter) -> std::fmt::Result {
                write!(f, "{}", self.as_psbt_string())
            }
        }

        impl str::FromStr for $transaction_name {
            type Err = TransactionSerialisationError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                $transaction_name::from_psbt_str(s)
            }
        }
    };
}

/// Sanity check a PSBT representing a RevaultTransaction, the part common to all transactions
pub fn psbt_common_sanity_checks(psbt: Psbt) -> Result<Psbt, PsbtValidationError> {
    let inner_tx = &psbt.global.unsigned_tx;

    if inner_tx.version != TX_VERSION {
        return Err(PsbtValidationError::InvalidTransactionVersion(
            inner_tx.version,
        ));
    }

    let input_count = inner_tx.input.len();
    let psbt_input_count = psbt.inputs.len();
    if input_count != psbt_input_count {
        return Err(PsbtValidationError::InputCountMismatch(
            input_count,
            psbt_input_count,
        ));
    }

    let output_count = inner_tx.output.len();
    let psbt_output_count = psbt.outputs.len();
    if output_count != psbt_output_count {
        return Err(PsbtValidationError::OutputCountMismatch(
            output_count,
            psbt_output_count,
        ));
    }

    // Check for duplicated inputs
    let uniq_txins: HashSet<OutPoint> = inner_tx.input.iter().map(|i| i.previous_output).collect();
    if uniq_txins.len() != input_count {
        return Err(PsbtValidationError::DuplicatedInput);
    }

    // None: unknown, Some(true): an input was final, Some(false) an input was non-final
    let mut is_final = None;
    // Record the number of coins spent by the transaction
    let mut value_in: u64 = 0;
    for input in psbt.inputs.iter() {
        // We restrict to native segwit, also for the external fee-bumping wallet.
        if input.witness_utxo.is_none() {
            return Err(PsbtValidationError::MissingWitnessUtxo(input.clone()));
        }

        if input.non_witness_utxo.is_some() {
            return Err(PsbtValidationError::InvalidInputField(input.clone()));
        }

        if input.redeem_script.is_some() {
            return Err(PsbtValidationError::InvalidInputField(input.clone()));
        }

        // Make sure it does not mix finalized and non-finalized inputs or final scripts
        // and non-final scripts.
        if input.final_script_witness.is_some() {
            if is_final == Some(false) || input.witness_script.is_some() {
                return Err(PsbtValidationError::PartiallyFinalized);
            }
            is_final = Some(true);
        } else {
            if is_final == Some(true) {
                return Err(PsbtValidationError::PartiallyFinalized);
            }
            is_final = Some(false);
        }

        // If the witness script is provided, it must be a sane Miniscript
        if let Some(ref script) = input.witness_script {
            let _: miniscript::Miniscript<_, miniscript::Segwitv0> =
                miniscript::Miniscript::parse(script)
                    .map_err(|_| PsbtValidationError::InvalidInWitnessScript(input.clone()))?;
        }

        // We'll then check it doesn't create more than it spends
        value_in = value_in
            .checked_add(
                input
                    .witness_utxo
                    .as_ref()
                    .expect("None checked above")
                    .value,
            )
            .ok_or(PsbtValidationError::InsaneAmounts)?;

        // The previous output must either be P2WSH, in which case the witness script must
        // correspond to the ScriptPubKey, or P2WPKH.
        let spk = &input.witness_utxo.as_ref().unwrap().script_pubkey;
        if spk.is_v0_p2wsh() {
            // It's blanked when finalized
            if is_final == Some(true) {
                continue;
            }

            let ws = match &input.witness_script {
                Some(ws) => ws,
                None => return Err(PsbtValidationError::MissingInWitnessScript(input.clone())),
            };
            if &ws.to_v0_p2wsh() != spk {
                return Err(PsbtValidationError::InvalidInWitnessScript(input.clone()));
            }
        } else if !spk.is_v0_p2wpkh() {
            return Err(PsbtValidationError::InvalidInputField(input.clone()));
        }
    }

    let mut value_out: u64 = 0;
    for o in inner_tx.output.iter() {
        value_out = value_out
            .checked_add(o.value)
            .ok_or(PsbtValidationError::InsaneAmounts)?;
    }

    if value_out > value_in {
        return Err(PsbtValidationError::InsaneAmounts);
    }

    Ok(psbt)
}

/// If one of these inputs is a P2WSH, return it.
pub fn find_revocationtx_input(inputs: &[PsbtIn]) -> Option<&PsbtIn> {
    inputs.iter().find(|i| {
        i.witness_utxo
            .as_ref()
            .map(|o| o.script_pubkey.is_v0_p2wsh())
            == Some(true)
    })
}

/// If one of these inputs is a P2WPKH, return it.
pub fn find_feebumping_input(inputs: &[PsbtIn]) -> Option<&PsbtIn> {
    inputs.iter().find(|i| {
        i.witness_utxo
            .as_ref()
            .map(|o| o.script_pubkey.is_v0_p2wpkh())
            == Some(true)
    })
}

/// Sanity check an "internal" PSBT input of a revocation transaction
pub fn check_revocationtx_input(input: &PsbtIn) -> Result<(), PsbtValidationError> {
    assert!(input
        .witness_utxo
        .as_ref()
        .expect("Checked in the common checks")
        .script_pubkey
        .is_v0_p2wsh());

    if input.final_script_witness.is_some() {
        // Already final, sighash type and witness script are wiped
        return Ok(());
    }

    // The revocation input must indicate that it wants to be signed with ACP
    if input.sighash_type != Some(SigHashType::AllPlusAnyoneCanPay) {
        return Err(PsbtValidationError::InvalidSighashType(input.clone()));
    }

    Ok(())
}

/// Sanity check a feebump PSBT input of a revocation transaction
pub fn check_feebump_input(input: &PsbtIn) -> Result<(), PsbtValidationError> {
    if input.final_script_witness.is_some() {
        // Already final, sighash type and witness script are wiped
        return Ok(());
    }

    // The feebump input must indicate that it wants to be signed with ALL
    if input.sighash_type != Some(SigHashType::All) {
        return Err(PsbtValidationError::InvalidSighashType(input.clone()));
    }

    // The feebump input must be P2WPKH
    if input
        .witness_utxo
        .as_ref()
        .map(|u| u.script_pubkey.is_v0_p2wpkh())
        != Some(true)
    {
        return Err(PsbtValidationError::InvalidPrevoutType(input.clone()));
    }

    // And therefore must not have a witness script
    if input.witness_script.is_some() {
        return Err(PsbtValidationError::InvalidInputField(input.clone()));
    }

    Ok(())
}

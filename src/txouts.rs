//! # Revault PSBT outputs
//!
//! Wrappers around bitcoin's TxOut to statically check Revault transactions creation and ease
//! their PSBT management.

use crate::{
    error::TxoutCreationError,
    scripts::{
        DerivedCpfpDescriptor, DerivedDepositDescriptor, DerivedUnvaultDescriptor, EmergencyAddress,
    },
};

use miniscript::{
    bitcoin::{Amount, Script, TxOut},
    DescriptorTrait,
};

use std::fmt;

/// Any output of a Revault transaction.
pub trait RevaultTxOut: fmt::Debug + Clone + PartialEq {
    /// Get a reference to the inner txout
    fn txout(&self) -> &TxOut;

    /// Get the actual inner txout
    fn into_txout(self) -> TxOut;
}

/// An output of a Revault transaction that we manage "internally", ie for which we have the
/// descriptor.
pub trait RevaultInternalTxOut: fmt::Debug + Clone + PartialEq + RevaultTxOut {
    /// Get a reference to the inner witness script ("redeem Script of the witness program")
    fn witness_script(&self) -> &Script;

    /// Get the actual inner witness script ("redeem Script of the witness program")
    fn into_witness_script(self) -> Script;

    /// Get the maximum size, in weight units, a satisfaction for this scriptPubKey would cost.
    fn max_sat_weight(&self) -> usize {
        miniscript::descriptor::Wsh::new(
            miniscript::Miniscript::parse(self.witness_script())
                .expect("The witness_script is always created from a Miniscript"),
        )
        .expect("The witness_script is always a P2WSH")
        .max_satisfaction_weight()
        .expect("It's a sane Script, derived from a Miniscript")
    }
}

macro_rules! implem_revault_txout {
    ( $struct_name:ident, $doc_comment:meta ) => {
        #[$doc_comment]
        #[derive(Debug, Clone, PartialEq, Default)]
        pub struct $struct_name {
            txout: TxOut,
            witness_script: Script,
        }

        impl RevaultTxOut for $struct_name {
            fn txout(&self) -> &TxOut {
                &self.txout
            }

            fn into_txout(self) -> TxOut {
                self.txout
            }
        }

        impl RevaultInternalTxOut for $struct_name {
            fn witness_script(&self) -> &Script {
                &self.witness_script
            }

            fn into_witness_script(self) -> Script {
                self.witness_script
            }
        }
    };
}

implem_revault_txout!(
    DepositTxOut,
    doc = "A deposit transaction output. Used by the [Deposit](crate::transactions::DepositTransaction), \
            the [Cancel](crate::transactions::CancelTransaction), and the \
            [Spend](crate::transactions::SpendTransaction)."
);
impl DepositTxOut {
    /// Create a new DepositTxOut out of the given Deposit script descriptor
    pub fn new(value: Amount, script_descriptor: &DerivedDepositDescriptor) -> DepositTxOut {
        DepositTxOut {
            txout: TxOut {
                value: value.as_sat(),
                script_pubkey: script_descriptor.inner().script_pubkey(),
            },
            witness_script: script_descriptor.inner().explicit_script(),
        }
    }
}

implem_revault_txout!(UnvaultTxOut, doc = "*The* Unvault transaction output.");
impl UnvaultTxOut {
    /// Create a new UnvaultTxOut out of the given Unvault script descriptor
    pub fn new(value: Amount, script_descriptor: &DerivedUnvaultDescriptor) -> UnvaultTxOut {
        UnvaultTxOut {
            txout: TxOut {
                value: value.as_sat(),
                script_pubkey: script_descriptor.inner().script_pubkey(),
            },
            witness_script: script_descriptor.inner().explicit_script(),
        }
    }
}

/// The Emergency Deep Vault, the destination of the Emergency transactions fund.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct EmergencyTxOut(TxOut);
impl EmergencyTxOut {
    /// Create a new EmergencyTxOut, note that we don't know the witness_script!
    pub fn new(address: EmergencyAddress, value: Amount) -> EmergencyTxOut {
        EmergencyTxOut(TxOut {
            script_pubkey: address.address().script_pubkey(),
            value: value.as_sat(),
        })
    }
}

impl RevaultTxOut for EmergencyTxOut {
    fn txout(&self) -> &TxOut {
        &self.0
    }

    fn into_txout(self) -> TxOut {
        self.0
    }
}

implem_revault_txout!(
    CpfpTxOut,
    doc = "The output attached to the [Unvault](crate::transactions::UnvaultTransaction) \
            so that the fund managers can fee-bump it."
);
impl CpfpTxOut {
    /// Create a new CpfpTxOut out of the given Cpfp descriptor
    pub fn new(value: Amount, script_descriptor: &DerivedCpfpDescriptor) -> CpfpTxOut {
        CpfpTxOut {
            txout: TxOut {
                value: value.as_sat(),
                script_pubkey: script_descriptor.inner().script_pubkey(),
            },
            witness_script: script_descriptor.inner().explicit_script(),
        }
    }
}

/// The output spent by the revocation transactions to bump their feerate
#[derive(Debug, Clone, PartialEq, Default)]
pub struct FeeBumpTxOut(TxOut);
impl FeeBumpTxOut {
    /// Create a new FeeBumpTxOut, note that it's managed externally so we don't need a witness
    /// Script.
    pub fn new(txout: TxOut) -> Result<FeeBumpTxOut, TxoutCreationError> {
        if !txout.script_pubkey.is_v0_p2wpkh() {
            return Err(TxoutCreationError::InvalidScriptPubkeyType);
        }

        Ok(FeeBumpTxOut(txout))
    }
}

impl RevaultTxOut for FeeBumpTxOut {
    fn txout(&self) -> &TxOut {
        &self.0
    }

    fn into_txout(self) -> TxOut {
        self.0
    }
}

/// A [Spend](crate::transactions::SpendTransaction) output can be either a change one (DepositTxOut)
/// or a payee-controlled one (ExternalTxOut).
#[derive(Debug, Clone)]
pub enum SpendTxOut {
    /// The actual destination of the funds, many such output can be present in a Spend
    /// transaction
    Destination(TxOut),
    /// The change output, usually only one such output is present in a Spend transaction
    Change(DepositTxOut),
}

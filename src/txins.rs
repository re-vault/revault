//! # Revault PSBT inputs
//!
//! Wrappers around bitcoin's OutPoint and previous TxOut to statically check Revault
//! transaction creation and ease PSBT management.

use crate::txouts::{CpfpTxOut, DepositTxOut, FeeBumpTxOut, UnvaultTxOut};

use miniscript::bitcoin::{OutPoint, TxIn};

use std::fmt;

/// The default sequence used by bitcoind to signal for RBF: 0xff_ff_ff_fd
pub const RBF_SEQUENCE: u32 = u32::MAX - 2;

/// A transaction input used by a Revault transaction.
pub trait RevaultTxIn<T>: fmt::Debug + Clone + PartialEq {
    /// Get the actual outpoint
    fn outpoint(&self) -> OutPoint;
    /// Get a reference to the txout this txin refers
    fn txout(&self) -> &T;
    /// Get the actual txout this txin refers
    fn into_txout(self) -> T;
    /// Get an actual Bitcoin TxIn out of the OutPoint and the nSequence
    fn unsigned_txin(&self) -> TxIn;
}

macro_rules! implem_revault_txin {
    ( $struct_name:ident, $txout_struct_name:ident, $doc_comment:meta ) => {
        #[$doc_comment]
        #[derive(Debug, Clone, PartialEq)]
        pub struct $struct_name {
            outpoint: OutPoint,
            prev_txout: $txout_struct_name,
            sequence: u32,
        }

        impl RevaultTxIn<$txout_struct_name> for $struct_name {
            fn outpoint(&self) -> OutPoint {
                self.outpoint
            }

            fn txout(&self) -> &$txout_struct_name {
                &self.prev_txout
            }

            fn into_txout(self) -> $txout_struct_name {
                self.prev_txout
            }

            fn unsigned_txin(&self) -> TxIn {
                TxIn {
                    previous_output: self.outpoint,
                    sequence: self.sequence,
                    ..TxIn::default()
                }
            }
        }
    };
}

implem_revault_txin!(
    DepositTxIn,
    DepositTxOut,
    doc = "A deposit txo spent by the [Unvault](crate::transactions::UnvaultTransaction) \
            transaction and the [Emergency](crate::transactions::EmergencyTransaction)"
);
impl DepositTxIn {
    /// Instanciate a TxIn referencing a deposit txout which signals for RBF.
    pub fn new(outpoint: OutPoint, prev_txout: DepositTxOut) -> DepositTxIn {
        DepositTxIn {
            outpoint,
            prev_txout,
            sequence: RBF_SEQUENCE,
        }
    }
}

implem_revault_txin!(
    UnvaultTxIn,
    UnvaultTxOut,
    doc = "An [Unvault](crate::transactions::UnvaultTransaction) txo spent by the \
        [Cancel](crate::transactions::CancelTransaction), \
        [UnvaultEmergency](crate::transactions::UnvaultEmergencyTransaction), and the \
        [Spend](crate::transactions::SpendTransaction)."
);
impl UnvaultTxIn {
    /// Instanciate a TxIn referencing an unvault txout. We need the sequence to be explicitly
    /// specified for this one, as it may spend a CSV-encumbered path.
    pub fn new(outpoint: OutPoint, prev_txout: UnvaultTxOut, sequence: u32) -> UnvaultTxIn {
        UnvaultTxIn {
            outpoint,
            prev_txout,
            sequence,
        }
    }
}

implem_revault_txin!(
    FeeBumpTxIn,
    FeeBumpTxOut,
    doc = "A wallet txo spent by a revocation ([Cancel](crate::transactions::CancelTransaction), \
           [Emergency](crate::transactions::EmergencyTransaction)) transaction to bump the package feerate. \
           \
           This output is from an external wallet and is often created by a first stage transaction."
);
impl FeeBumpTxIn {
    /// Instanciate a txin referencing a feebump txout which signals for RBF.
    pub fn new(outpoint: OutPoint, prev_txout: FeeBumpTxOut) -> FeeBumpTxIn {
        FeeBumpTxIn {
            outpoint,
            prev_txout,
            sequence: RBF_SEQUENCE,
        }
    }
}

implem_revault_txin!(
    CpfpTxIn,
    CpfpTxOut,
    doc = "The [Unvault CPFP txo](crate::txouts::CpfpTxOut) spent to accelerate the confirmation of the \
            [Unvault](crate::transactions::UnvaultTransaction)."
);
impl CpfpTxIn {
    /// Instanciate a TxIn referencing a CPFP txout which signals for RBF.
    pub fn new(outpoint: OutPoint, prev_txout: CpfpTxOut) -> CpfpTxIn {
        CpfpTxIn {
            outpoint,
            prev_txout,
            sequence: RBF_SEQUENCE,
        }
    }
}

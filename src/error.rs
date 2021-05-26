//! # Errors related to Revault transactions and Scripts management

use crate::transactions::INSANE_FEES;

use bitcoinconsensus::Error as LibConsensusError;
use miniscript::{
    bitcoin::{
        consensus::encode::Error as EncodeError,
        secp256k1,
        util::psbt::{Input as PsbtInput, Output as PsbtOutput},
    },
    policy::compiler::CompilerError,
};

use std::{convert::From, error, fmt};

/// Error when creating a Revault Miniscript Descriptor
#[derive(Debug)]
pub enum ScriptCreationError {
    /// Invalid number of keys, threshold, or timelock
    BadParameters,
    /// At least one of the keys was not derivable
    NonWildcardKeys,
    /// Miniscript policy compilation error
    PolicyCompilation(CompilerError),
    /// Miniscript general error, currently only for sanity checks in descriptor
    /// constructors
    MiniscriptError(miniscript::Error),
}

impl fmt::Display for ScriptCreationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::BadParameters => write!(f, "Bad parameters"),
            Self::PolicyCompilation(e) => write!(f, "Policy compilation error: '{}'", e),
            Self::MiniscriptError(e) => write!(f, "Miniscript error: '{}'", e),
            Self::NonWildcardKeys => write!(f, "Not all xpubs were wildcard"),
        }
    }
}

impl From<CompilerError> for ScriptCreationError {
    fn from(e: CompilerError) -> Self {
        Self::PolicyCompilation(e)
    }
}

impl From<miniscript::Error> for ScriptCreationError {
    fn from(e: miniscript::Error) -> Self {
        Self::MiniscriptError(e)
    }
}

impl error::Error for ScriptCreationError {}

/// Error when creating a Revault Bitcoin transaction output
#[derive(PartialEq, Debug)]
pub enum TxoutCreationError {
    InvalidScriptPubkeyType,
}

impl fmt::Display for TxoutCreationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidScriptPubkeyType => write!(f, "Invalid ScriptPubKey type"),
        }
    }
}

impl error::Error for TxoutCreationError {}

/// Error when creating a Revault Bitcoin transaction
#[derive(PartialEq, Eq, Debug)]
pub enum TransactionCreationError {
    /// Fees would be higher than [INSANE_FEES] (not checked for revocation transactions)
    InsaneFees,
    /// Would spend or create a dust output
    Dust,
    /// Sends more than it spends
    NegativeFees,
    /// Transaction weight more than 400k weight units.
    TooLarge,
}

impl fmt::Display for TransactionCreationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InsaneFees => write!(f, "Fees larger than {} sats", INSANE_FEES),
            Self::Dust => write!(f, "Spending or creating a dust output"),
            Self::NegativeFees => write!(
                f,
                "The sum of the inputs value is less than the sum of the outputs value"
            ),
            Self::TooLarge => write!(
                f,
                "Transaction too large: satisfied it could be >400k weight units"
            ),
        }
    }
}

impl error::Error for TransactionCreationError {}

/// Error when satisfying a Revault Bitcoin transaction input
#[derive(PartialEq, Eq, Debug)]
pub enum InputSatisfactionError {
    /// Index is out of bounds of the inputs list
    OutOfBounds,
    /// Provided signature's sighash byte is different from PSBT input's type
    UnexpectedSighashType,
    /// This input was already finalized and its witness map wiped
    AlreadyFinalized,
    /// The PSBT input does not comport a witness_script field
    MissingWitnessScript,
    /// Trying to add an invalid signature
    InvalidSignature(
        secp256k1::Signature,
        secp256k1::PublicKey,
        secp256k1::Message,
    ),
}

impl fmt::Display for InputSatisfactionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::OutOfBounds => write!(f, "Index out of bounds of inputs list"),
            Self::UnexpectedSighashType => {
                write!(f, "Signature's sighash byte differs from PSBT input's type")
            }
            Self::AlreadyFinalized => write!(f, "Input was already finalized"),
            Self::MissingWitnessScript => write!(
                f,
                "Missing witness_script field in PSBT input. Wrong sighash function used?"
            ),
            Self::InvalidSignature(sig, pk, hash) => write!(
                f,
                "Invalid signature '{:x?}' for key '{:x?}' and sighash '{:x?}'",
                &sig, &pk, &hash
            ),
        }
    }
}

impl error::Error for InputSatisfactionError {}

/// Error when validating a correctly serialized PSBT representing a Revault transaction
#[derive(PartialEq, Debug)]
pub enum PsbtValidationError {
    InvalidTransactionVersion(i32),
    InputCountMismatch(usize, usize),
    OutputCountMismatch(usize, usize),
    InvalidInputCount(usize),
    InvalidOutputCount(usize),
    DuplicatedInput,
    MissingRevocationInput,
    MissingFeeBumpingInput,
    MissingWitnessUtxo(PsbtInput),
    MissingInWitnessScript(PsbtInput),
    InvalidInWitnessScript(PsbtInput),
    MissingOutWitnessScript(PsbtOutput),
    InvalidOutWitnessScript(PsbtOutput),
    InvalidSighashType(PsbtInput),
    InvalidInputField(PsbtInput),
    InvalidOutputField(PsbtOutput),
    InvalidPrevoutType(PsbtInput),
    PartiallyFinalized,
    InsaneAmounts,
    TransactionTooLarge,
}

impl fmt::Display for PsbtValidationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::InvalidTransactionVersion(v) => write!(f, "Invalid transaction version: '{}'", v),
            Self::InputCountMismatch(in_count, psbtin_count) => write!(
                f,
                "'{}' inputs but '{}' psbt inputs",
                in_count, psbtin_count
            ),
            Self::OutputCountMismatch(out_count, psbtout_count) => write!(
                f,
                "'{}' outputs but '{}' psbt outputs",
                out_count, psbtout_count
            ),
            Self::InvalidInputCount(c) => write!(f, "Invalid input count: '{}'", c),
            Self::InvalidOutputCount(c) => write!(f, "Invalid output count: '{}'", c),
            Self::DuplicatedInput => write!(f, "Transaction contains duplicated inputs"),
            Self::MissingRevocationInput => {
                write!(f, "Missing P2WSH input for revocation transaction")
            }
            Self::MissingFeeBumpingInput => {
                write!(f, "Missing P2WSH input for feebumping transaction")
            }
            Self::MissingWitnessUtxo(i) => write!(f, "Missing witness utxo for input '{:#?}'", i),
            Self::MissingInWitnessScript(i) => {
                write!(f, "Missing witness script for input '{:#?}'", i)
            }
            Self::InvalidInWitnessScript(i) => {
                write!(f, "Invalid witness script for input '{:#?}'", i)
            }
            Self::MissingOutWitnessScript(o) => {
                write!(f, "Missing witness script for output '{:#?}'", o)
            }
            Self::InvalidOutWitnessScript(o) => {
                write!(f, "Invalid witness script for output '{:#?}'", o)
            }
            Self::InvalidSighashType(i) => write!(f, "Invalid sighash type for input: '{:#?}'", i),
            Self::InvalidInputField(i) => write!(f, "Invalid field in input: '{:#?}'", i),
            Self::InvalidOutputField(o) => write!(f, "Invalid field in output: '{:#?}'", o),
            Self::InvalidPrevoutType(i) => write!(
                f,
                "This input refers to an output of invalid type: '{:#?}'",
                i
            ),
            Self::PartiallyFinalized => write!(f, "PSBT contains both final and non-final inputs"),
            Self::InsaneAmounts => write!(
                f,
                "PSBT contains either overflowing amounts or creates more coins than it spends"
            ),
            Self::TransactionTooLarge => write!(
                f,
                "Transaction too large: satisfied it could be >400k weight units"
            ),
        }
    }
}

impl error::Error for PsbtValidationError {}

/// Error when working with serialized Revault transactions
#[derive(PartialEq, Debug)]
pub enum TransactionSerialisationError {
    // FIXME: have upstream(s) derive PartialEq on Errors?
    /// A (de)serialization error ("EncodeError" by rust-bitcoin name)
    Encode(String),
    /// An error decoding base64
    Base64Decode(base64::DecodeError),
    /// A valid PSBT but invalid Revault transaction
    Validation(PsbtValidationError),
}

impl fmt::Display for TransactionSerialisationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Encode(s) => write!(f, "{}", s),
            Self::Base64Decode(e) => write!(f, "Error decoding base64: '{}'", e),
            Self::Validation(s) => write!(f, "Invalid Revault transaction: '{}'", s),
        }
    }
}

impl From<EncodeError> for TransactionSerialisationError {
    fn from(e: EncodeError) -> Self {
        Self::Encode(e.to_string())
    }
}

impl From<base64::DecodeError> for TransactionSerialisationError {
    fn from(e: base64::DecodeError) -> Self {
        Self::Base64Decode(e)
    }
}

impl From<PsbtValidationError> for TransactionSerialisationError {
    fn from(e: PsbtValidationError) -> Self {
        Self::Validation(e)
    }
}

impl error::Error for TransactionSerialisationError {}

/// An error specific to the management of Revault transactions and scripts.
#[derive(Debug)]
pub enum Error {
    /// Error when creating a Revault Bitcoin Script
    ScriptCreation(ScriptCreationError),
    /// Error when creating a Revault txout
    TxoutCreation(TxoutCreationError),
    /// The transaction creation failed.
    TransactionCreation(TransactionCreationError),
    /// Satisfaction (PSBT signer role) of a Revault transaction input failed.
    InputSatisfaction(InputSatisfactionError),
    // FIXME: have upstream(s) derive PartialEq on Errors?
    /// Completion (PSBT finalizer role) of the Revault transaction failed.
    TransactionFinalisation(String),
    /// The verification of the PSBT input against libbitcoinconsensus failed.
    TransactionVerification(LibConsensusError),
    /// Error when working with serialized Revault transactions
    TransactionSerialisation(TransactionSerialisationError),
}

impl From<ScriptCreationError> for Error {
    fn from(e: ScriptCreationError) -> Self {
        Self::ScriptCreation(e)
    }
}

impl From<TxoutCreationError> for Error {
    fn from(e: TxoutCreationError) -> Self {
        Self::TxoutCreation(e)
    }
}

impl From<TransactionCreationError> for Error {
    fn from(e: TransactionCreationError) -> Self {
        Self::TransactionCreation(e)
    }
}

impl From<InputSatisfactionError> for Error {
    fn from(e: InputSatisfactionError) -> Self {
        Self::InputSatisfaction(e)
    }
}

impl From<LibConsensusError> for Error {
    fn from(e: LibConsensusError) -> Self {
        Self::TransactionVerification(e)
    }
}

impl From<TransactionSerialisationError> for Error {
    fn from(e: TransactionSerialisationError) -> Self {
        Self::TransactionSerialisation(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::ScriptCreation(ref e) => write!(f, "Revault script creation error: '{}'", e),
            Error::TxoutCreation(ref e) => {
                write!(f, "Revault transaction output creation error: '{}'", e)
            }
            Error::TransactionCreation(ref e) => {
                write!(f, "Revault transaction creation error: '{}'", e)
            }
            Error::InputSatisfaction(ref e) => {
                write!(f, "Revault input satisfaction error: '{}'", e)
            }
            Error::TransactionVerification(ref e) => {
                write!(f, "Revault transaction verification error: '{:?}'", e)
            }
            Error::TransactionFinalisation(ref e) => {
                write!(f, "Revault transaction finalisation error: '{}'", e)
            }
            Error::TransactionSerialisation(ref e) => {
                write!(f, "Revault transaction serialisation error: '{}'", e)
            }
        }
    }
}

impl error::Error for Error {}

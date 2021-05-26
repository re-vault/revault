#![no_main]
use libfuzzer_sys::fuzz_target;

use revault_tx::{
    miniscript::bitcoin::{
        secp256k1::{Signature, SECP256K1},
        PublicKey, SigHashType,
    },
    transactions::{RevaultTransaction, SpendTransaction},
};

use std::str::FromStr;

fuzz_target!(|data: &[u8]| {
    if let Ok(mut tx) = SpendTransaction::from_psbt_serialized(data) {
        // We can serialize it back
        tx.as_psbt_serialized();

        // We can network serialize it (without witness data)
        tx.clone().into_bitcoin_serialized();

        // We can compute its size and fees without crashing
        tx.max_feerate();

        let dummykey = PublicKey::from_str(
            "02ca06be8e497d578314c77ca735aa5fcca76d8a5b04019b7a80ff0baaf4a6cf46",
        )
        .unwrap();
        let dummy_sig = Signature::from_str("3045022100e6ffa6cc76339944fa428bcd058a27d0e660d0554a418a79620d7e14cda4cbde022045ba1bcec9fbbdcb4b70328dc7efae7ee59ff496aa8139c81a10b898911b8b52").unwrap();

        // We can compute the sighash for all the unvault inputs and
        // add a signature if the tx is final
        let input_count = tx.psbt().inputs.len();
        for i in 0..input_count {
            if !tx.is_finalized() {
                tx.signature_hash(i, SigHashType::All)
                    .expect("Must be in bound as it was parsed!");
                assert!(tx
                    .add_signature(i, dummykey, (dummy_sig, SigHashType::All), &SECP256K1)
                    .unwrap_err()
                    .to_string()
                    .contains("Invalid signature"));
            } else {
                // But not if it's final
                assert!(tx
                    .signature_hash(i, SigHashType::All)
                    .unwrap_err()
                    .to_string()
                    .contains("Missing witness_script"));
                assert!(tx
                    .add_signature(i, dummykey, (dummy_sig, SigHashType::All), &SECP256K1)
                    .unwrap_err()
                    .to_string()
                    .contains("already finalized"));
            }
            // And verify the input without crashing (will likely fail though)
            tx.verify_inputs().unwrap_or_else(|_| ());
        }

        // Same for the finalization
        tx.finalize(&SECP256K1).unwrap_or_else(|_| ());
    }
});

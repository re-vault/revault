#![no_main]
use libfuzzer_sys::fuzz_target;

use libfuzzer_sys::arbitrary::Arbitrary;

use revault_tx::{
    miniscript::bitcoin::{
        blockdata::constants::max_money, hashes::Hash, secp256k1::SECP256K1, Network, OutPoint,
        Txid,
    },
    transactions::tests_helpers::{derive_transactions, seed_rng},
};

#[derive(Arbitrary, Debug)]
struct Config {
    n_stk: usize,
    n_man: usize,
    csv: u32,
    deposit_txid: [u8; 32],
    deposit_vout: u32,
    deposit_value: u64,
    feebump_txid: [u8; 32],
    feebump_vout: u32,
    feebump_value: u64,
    unvault_spends: Vec<([u8; 32], u32, u64)>,
}

fuzz_target!(|config: Config| {
    if config.n_stk > 150 || config.n_stk < 2 || config.n_man > 150 {
        return;
    }
    if config.deposit_value > max_money(Network::Bitcoin) {
        return;
    }

    seed_rng(0);

    let deposit_prevout = OutPoint {
        txid: Txid::from_slice(&config.deposit_txid).unwrap(),
        vout: config.deposit_vout,
    };
    let feebump_prevout = OutPoint {
        txid: Txid::from_slice(&config.feebump_txid).unwrap(),
        vout: config.deposit_vout,
    };
    let unvault_spends = config
        .unvault_spends
        .into_iter()
        .map(|(txid, vout, value)| {
            (
                OutPoint {
                    txid: Txid::from_slice(&txid).unwrap(),
                    vout,
                },
                value,
            )
        })
        .collect();

    derive_transactions(
        config.n_stk,
        config.n_man,
        config.csv,
        deposit_prevout,
        config.deposit_value,
        feebump_prevout,
        config.feebump_value,
        unvault_spends,
        &SECP256K1,
    )
    .unwrap_or_else(|_| ());
});

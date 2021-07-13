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
    use revault_tx::miniscript::bitcoin::{
        blockdata::transaction::SigHashType, consensus::encode::deserialize, hashes::hex::FromHex,
        util::bip143::SigHashCache, Script, Transaction,
    };
    let tx_bytes = Vec::<u8>::from_hex("020000000182000000000000000000000000000000000000000000000000000000000000000000000000fdffffff0170ccfffef7000000220020b20000000000000000000000000000000000000000000000000000000000000000000000").unwrap();
    let tx: Transaction = deserialize(&tx_bytes).unwrap();
    let witscript = Script::from_hex("522103b50000000000000000000000000000014551231950b75fc4402da1732fc9bebf2103a90000000000000000000000000000014551231950b75fc4402da1732fc9bebf52ae").unwrap();
    let value = 1065135112192;

    let sighash_all = SigHashCache::new(&tx).signature_hash(0, &witscript, value, SigHashType::All);
    let sighash_acp = SigHashCache::new(&tx).signature_hash(
        0,
        &witscript,
        value,
        SigHashType::AllPlusAnyoneCanPay,
    );
    assert_ne!(sighash_all, sighash_acp,);

    if config.n_stk > 150 || config.n_stk < 2 || config.n_man > 150 {
        return;
    }
    if config.deposit_value > max_money(Network::Bitcoin) {
        return;
    }

    seed_rng(0x4523c40f8bca2f2b);

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

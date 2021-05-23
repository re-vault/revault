use super::{
    transaction_chain, CancelTransaction, DepositTransaction, EmergencyAddress,
    EmergencyTransaction, FeeBumpTransaction, RevaultTransaction, SpendTransaction,
    UnvaultEmergencyTransaction, UnvaultTransaction,
};

use crate::{error::*, scripts::*, txins::*, txouts::*};

use std::iter::repeat_with;

use miniscript::{
    bitcoin::{
        secp256k1,
        util::{bip143::SigHashCache, bip32},
        Address, Amount, Network, OutPoint, SigHash, SigHashType, Transaction, TxIn, TxOut,
    },
    descriptor::{DescriptorPublicKey, DescriptorXKey, Wildcard},
    Descriptor, DescriptorTrait,
};

fn get_random_privkey(rng: &mut fastrand::Rng) -> bip32::ExtendedPrivKey {
    let rand_bytes: Vec<u8> = repeat_with(|| rng.u8(..)).take(64).collect();

    bip32::ExtendedPrivKey::new_master(Network::Bitcoin, &rand_bytes)
        .unwrap_or_else(|_| get_random_privkey(rng))
}

// This generates the master private keys to derive directly from master, so it's
// [None]<xpub_goes_here>m/* descriptor pubkeys
fn get_participants_sets(
    n_stk: usize,
    n_man: usize,
    secp: &secp256k1::Secp256k1<secp256k1::All>,
) -> (
    (Vec<bip32::ExtendedPrivKey>, Vec<DescriptorPublicKey>),
    (Vec<bip32::ExtendedPrivKey>, Vec<DescriptorPublicKey>),
    (Vec<bip32::ExtendedPrivKey>, Vec<DescriptorPublicKey>),
    (Vec<bip32::ExtendedPrivKey>, Vec<DescriptorPublicKey>),
) {
    let mut rng = fastrand::Rng::new();

    let mut managers_priv = Vec::with_capacity(n_man);
    let mut managers = Vec::with_capacity(n_man);
    let mut mancpfp_priv = Vec::with_capacity(n_man);
    let mut mancpfp = Vec::with_capacity(n_man);
    for i in 0..n_man {
        managers_priv.push(get_random_privkey(&mut rng));
        managers.push(DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::ExtendedPubKey::from_private(&secp, &managers_priv[i]),
            derivation_path: bip32::DerivationPath::from(vec![]),
            wildcard: Wildcard::Unhardened,
        }));

        mancpfp_priv.push(get_random_privkey(&mut rng));
        mancpfp.push(DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::ExtendedPubKey::from_private(&secp, &mancpfp_priv[i]),
            derivation_path: bip32::DerivationPath::from(vec![]),
            wildcard: Wildcard::Unhardened,
        }));
    }

    let mut stakeholders_priv = Vec::with_capacity(n_stk);
    let mut stakeholders = Vec::with_capacity(n_stk);
    let mut cosigners_priv = Vec::with_capacity(n_stk);
    let mut cosigners = Vec::with_capacity(n_stk);
    for i in 0..n_stk {
        stakeholders_priv.push(get_random_privkey(&mut rng));
        stakeholders.push(DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::ExtendedPubKey::from_private(&secp, &stakeholders_priv[i]),
            derivation_path: bip32::DerivationPath::from(vec![]),
            wildcard: Wildcard::Unhardened,
        }));

        cosigners_priv.push(get_random_privkey(&mut rng));
        cosigners.push(DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::ExtendedPubKey::from_private(&secp, &cosigners_priv[i]),
            derivation_path: bip32::DerivationPath::from(vec![]),
            wildcard: Wildcard::Unhardened,
        }));
    }

    (
        (managers_priv, managers),
        (mancpfp_priv, mancpfp),
        (stakeholders_priv, stakeholders),
        (cosigners_priv, cosigners),
    )
}

// Routine for ""signing"" a transaction
fn satisfy_transaction_input(
    secp: &secp256k1::Secp256k1<secp256k1::All>,
    tx: &mut impl RevaultTransaction,
    input_index: usize,
    tx_sighash: &SigHash,
    xprivs: &Vec<bip32::ExtendedPrivKey>,
    child_number: Option<bip32::ChildNumber>,
) -> Result<(), Error> {
    let derivation_path = bip32::DerivationPath::from(if let Some(cn) = child_number {
        vec![cn]
    } else {
        vec![]
    });

    for xpriv in xprivs {
        let sig = secp.sign(
            &secp256k1::Message::from_slice(&tx_sighash).unwrap(),
            &xpriv
                .derive_priv(&secp, &derivation_path)
                .unwrap()
                .private_key
                .key,
        );

        let xpub = DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: bip32::ExtendedPubKey::from_private(&secp, xpriv),
            derivation_path: bip32::DerivationPath::from(vec![]),
            wildcard: if child_number.is_some() {
                Wildcard::Unhardened
            } else {
                Wildcard::None
            },
        });
        let key = if let Some(index) = child_number {
            xpub.derive(index.into())
        } else {
            xpub
        }
        .derive_public_key(secp)
        .unwrap();

        tx.add_signature(input_index, key.key, sig, secp)?;
    }

    Ok(())
}

/// Derive transactions for a given deployment configuration, asserting some invariants
pub fn derive_transactions(
    n_stk: usize,
    n_man: usize,
    csv: u32,
    deposit_prevout: OutPoint,
    deposit_value: u64,
    feebump_prevout: OutPoint,
    feebump_value: u64,
    // Outpoint and amount of inputs of a Spend
    unvault_spends: Vec<(OutPoint, u64)>,
    secp: &secp256k1::Secp256k1<secp256k1::All>,
) -> Result<(), Error> {
    // Let's get the 10th key of each
    let child_number = bip32::ChildNumber::from(10);

    // Keys, keys, keys everywhere !
    let (
        (managers_priv, managers),
        (_, mancpfp),
        (stakeholders_priv, stakeholders),
        (cosigners_priv, cosigners),
    ) = get_participants_sets(n_stk, n_man, secp);

    // Get the script descriptors for the txos we're going to create
    let unvault_descriptor = UnvaultDescriptor::new(
        stakeholders.clone(),
        managers.clone(),
        managers.len(),
        cosigners.clone(),
        csv,
    )?;
    assert_eq!(unvault_descriptor.csv_value(), csv);
    let cpfp_descriptor =
        CpfpDescriptor::new(mancpfp).expect("Unvault CPFP descriptor generation error");
    let deposit_descriptor =
        DepositDescriptor::new(stakeholders).expect("Deposit descriptor generation error");

    // We reuse the deposit descriptor for the emergency address
    let emergency_address = EmergencyAddress::from(Address::p2wsh(
        &deposit_descriptor
            .derive(child_number, secp)
            .inner()
            .explicit_script(),
        Network::Bitcoin,
    ))
    .expect("It's a P2WSH");

    let der_deposit_descriptor = deposit_descriptor.derive(child_number, secp);
    let der_unvault_descriptor = unvault_descriptor.derive(child_number, secp);
    assert_eq!(
        der_unvault_descriptor.csv_value(),
        unvault_descriptor.csv_value()
    );
    let der_cpfp_descriptor = cpfp_descriptor.derive(child_number, secp);

    // The funding transaction does not matter (random txid from my mempool)
    let deposit_scriptpubkey = der_deposit_descriptor.inner().script_pubkey();
    let deposit_raw_tx = Transaction {
        version: 2,
        lock_time: 0,
        input: vec![TxIn {
            previous_output: deposit_prevout,
            ..TxIn::default()
        }],
        output: vec![TxOut {
            value: deposit_value,
            script_pubkey: deposit_scriptpubkey.clone(),
        }],
    };
    let deposit_txo = DepositTxOut::new(
        Amount::from_sat(deposit_raw_tx.output[0].value),
        &der_deposit_descriptor,
    );
    let deposit_tx = DepositTransaction(deposit_raw_tx);
    let deposit_outpoint = OutPoint {
        txid: deposit_tx.0.txid(),
        vout: 0,
    };
    let deposit_txin = DepositTxIn::new(deposit_outpoint, deposit_txo.clone());

    // Test that the transaction helper(s) derive the same transactions as we do
    let (h_unvault, h_cancel, h_emer, h_unemer) = transaction_chain(
        deposit_outpoint,
        Amount::from_sat(deposit_txo.txout().value),
        &deposit_descriptor,
        &unvault_descriptor,
        &cpfp_descriptor,
        child_number,
        emergency_address.clone(),
        0,
        secp,
    )?;

    // The fee-bumping utxo, used in revaulting transactions inputs to bump their feerate.
    // We simulate a wallet utxo.
    let mut rng = fastrand::Rng::new();
    let feebump_xpriv = get_random_privkey(&mut rng);
    let feebump_xpub = bip32::ExtendedPubKey::from_private(&secp, &feebump_xpriv);
    let feebump_descriptor = Descriptor::new_wpkh(
        DescriptorPublicKey::XPub(DescriptorXKey {
            origin: None,
            xkey: feebump_xpub,
            derivation_path: bip32::DerivationPath::from(vec![]),
            wildcard: Wildcard::None, // We are not going to derive from this one
        })
        .derive_public_key(secp)
        .unwrap(),
    )
    .unwrap();
    let raw_feebump_tx = Transaction {
        version: 2,
        lock_time: 0,
        input: vec![TxIn {
            previous_output: feebump_prevout,
            ..TxIn::default()
        }],
        output: vec![TxOut {
            value: feebump_value,
            script_pubkey: feebump_descriptor.script_pubkey(),
        }],
    };
    let feebump_txo = FeeBumpTxOut::new(raw_feebump_tx.output[0].clone()).expect("It is a p2wpkh");
    let feebump_tx = FeeBumpTransaction(raw_feebump_tx);

    // Create and sign the first (deposit) emergency transaction
    // We can sign the transaction without the feebump input
    let mut emergency_tx_no_feebump =
        EmergencyTransaction::new(deposit_txin.clone(), None, emergency_address.clone(), 0)
            .unwrap();
    assert_eq!(h_emer, emergency_tx_no_feebump);
    assert_eq!(
        emergency_tx_no_feebump.emergency_outpoint(),
        OutPoint {
            txid: emergency_tx_no_feebump.txid(),
            vout: 0
        }
    );

    // 376 is the witstrip weight of an emer tx (1 segwit input, 1 P2WSH txout), 22 is the feerate is sat/WU
    assert_eq!(
        emergency_tx_no_feebump.fees(),
        (376 + deposit_txin.txout().max_sat_weight() as u64) * 22,
    );
    // We cannot get a sighash for a non-existing input
    assert_eq!(
        emergency_tx_no_feebump.signature_hash(10, SigHashType::AllPlusAnyoneCanPay),
        Err(InputSatisfactionError::OutOfBounds)
    );
    // But for an existing one, all good
    let emergency_tx_sighash_vault = emergency_tx_no_feebump
        .signature_hash(0, SigHashType::AllPlusAnyoneCanPay)
        .expect("Input exists");
    // We can't force it to accept a SIGHASH_ALL signature:
    let emer_sighash_all = emergency_tx_no_feebump
        .signature_hash(0, SigHashType::All)
        .unwrap();
    let err = satisfy_transaction_input(
        &secp,
        &mut emergency_tx_no_feebump,
        0,
        &emer_sighash_all,
        &stakeholders_priv,
        Some(child_number),
    );
    assert!(err.unwrap_err().to_string().contains("Invalid signature"),);
    // Now, that's the right SIGHASH
    satisfy_transaction_input(
        &secp,
        &mut emergency_tx_no_feebump,
        0,
        &emergency_tx_sighash_vault,
        &stakeholders_priv,
        Some(child_number),
    )?;
    // Without feebump it finalizes just fine
    emergency_tx_no_feebump.finalize(&secp)?;

    let feebump_txin = FeeBumpTxIn::new(
        OutPoint {
            txid: feebump_tx.0.txid(),
            vout: 0,
        },
        feebump_txo.clone(),
    );
    let mut emergency_tx = EmergencyTransaction::new(
        deposit_txin.clone(),
        Some(feebump_txin),
        emergency_address.clone(),
        0,
    )
    .unwrap();
    assert_eq!(
        emergency_tx.emergency_outpoint(),
        OutPoint {
            txid: emergency_tx.txid(),
            vout: 0
        }
    );

    let emergency_tx_sighash_feebump = emergency_tx
        .signature_hash(1, SigHashType::All)
        .expect("Input exists");
    satisfy_transaction_input(
        &secp,
        &mut emergency_tx,
        0,
        // This sighash was created without knowledge of the feebump input. It's fine.
        &emergency_tx_sighash_vault,
        &stakeholders_priv,
        Some(child_number),
    )?;
    satisfy_transaction_input(
        &secp,
        &mut emergency_tx,
        1,
        &emergency_tx_sighash_feebump,
        &vec![feebump_xpriv],
        None,
    )?;
    emergency_tx.finalize(&secp)?;

    // Create but don't sign the unvaulting transaction until all revaulting transactions
    // are finalized
    let deposit_txin_sat_cost = deposit_txin.txout().max_sat_weight();
    let mut unvault_tx = UnvaultTransaction::new(
        deposit_txin.clone(),
        &der_unvault_descriptor,
        &der_cpfp_descriptor,
        0,
    )?;

    assert_eq!(h_unvault, unvault_tx);
    let unvault_value = unvault_tx.psbt().global.unsigned_tx.output[0].value;
    // 548 is the witstrip weight of an unvault tx (1 segwit input, 2 P2WSH txouts), 6 is the
    // feerate is sat/WU, and 30_000 is the CPFP output value.
    assert_eq!(unvault_tx.fees(), (548 + deposit_txin_sat_cost as u64) * 6);

    // Create and sign the cancel transaction
    let rev_unvault_txin = unvault_tx.revault_unvault_txin(&der_unvault_descriptor);
    assert_eq!(rev_unvault_txin.txout().txout().value, unvault_value);
    // We can create it entirely without the feebump input
    let mut cancel_tx_without_feebump =
        CancelTransaction::new(rev_unvault_txin.clone(), None, &der_deposit_descriptor, 0);
    assert_eq!(h_cancel, cancel_tx_without_feebump);
    assert_eq!(
        cancel_tx_without_feebump
            .deposit_txin(&der_deposit_descriptor)
            .outpoint(),
        OutPoint {
            txid: cancel_tx_without_feebump.txid(),
            vout: 0
        }
    );
    // Keep track of the fees we computed..
    let value_no_feebump = cancel_tx_without_feebump.psbt().global.unsigned_tx.output[0].value;
    // 376 is the witstrip weight of a cancel tx (1 segwit input, 1 P2WSH txout), 22 is the feerate is sat/WU
    assert_eq!(
        cancel_tx_without_feebump.fees(),
        (376 + rev_unvault_txin.txout().max_sat_weight() as u64) * 22,
    );
    let cancel_tx_without_feebump_sighash = cancel_tx_without_feebump
        .signature_hash(0, SigHashType::AllPlusAnyoneCanPay)
        .expect("Input exists");
    satisfy_transaction_input(
        &secp,
        &mut cancel_tx_without_feebump,
        0,
        &cancel_tx_without_feebump_sighash,
        &stakeholders_priv,
        Some(child_number),
    )?;
    cancel_tx_without_feebump.finalize(&secp).unwrap();
    // We can reuse the ANYONE_ALL sighash for the one with the feebump input
    let feebump_txin = FeeBumpTxIn::new(
        OutPoint {
            txid: feebump_tx.0.txid(),
            vout: 0,
        },
        feebump_txo.clone(),
    );
    let mut cancel_tx = CancelTransaction::new(
        rev_unvault_txin.clone(),
        Some(feebump_txin),
        &der_deposit_descriptor,
        0,
    );
    assert_eq!(
        cancel_tx.deposit_txin(&der_deposit_descriptor).outpoint(),
        OutPoint {
            txid: cancel_tx.txid(),
            vout: 0
        }
    );

    // It really is a belt-and-suspenders check as the sighash would differ too.
    assert_eq!(
        cancel_tx_without_feebump.psbt().global.unsigned_tx.output[0].value,
        value_no_feebump,
        "Base fees when computing with with feebump differ !!"
    );
    let cancel_tx_sighash_feebump = cancel_tx
        .signature_hash(1, SigHashType::All)
        .expect("Input exists");
    satisfy_transaction_input(
        &secp,
        &mut cancel_tx,
        0,
        &cancel_tx_without_feebump_sighash,
        &stakeholders_priv,
        Some(child_number),
    )?;
    satisfy_transaction_input(
        &secp,
        &mut cancel_tx,
        1,
        &cancel_tx_sighash_feebump,
        &vec![feebump_xpriv],
        None, // No derivation path for the feebump key
    )?;
    cancel_tx.finalize(&secp)?;

    // We can create it without the feebump input
    let mut unemergency_tx_no_feebump = UnvaultEmergencyTransaction::new(
        rev_unvault_txin.clone(),
        None,
        emergency_address.clone(),
        0,
    );
    assert_eq!(h_unemer, unemergency_tx_no_feebump);
    assert_eq!(
        unemergency_tx_no_feebump.emergency_outpoint(),
        OutPoint {
            txid: unemergency_tx_no_feebump.txid(),
            vout: 0
        }
    );

    // 376 is the witstrip weight of an emer tx (1 segwit input, 1 P2WSH txout), 22 is the feerate is sat/WU
    assert_eq!(
        unemergency_tx_no_feebump.fees(),
        (376 + rev_unvault_txin.txout().max_sat_weight() as u64) * 22,
    );
    let unemergency_tx_sighash = unemergency_tx_no_feebump
        .signature_hash(0, SigHashType::AllPlusAnyoneCanPay)
        .expect("Input exists");
    satisfy_transaction_input(
        &secp,
        &mut unemergency_tx_no_feebump,
        0,
        &unemergency_tx_sighash,
        &stakeholders_priv,
        Some(child_number),
    )?;
    unemergency_tx_no_feebump.finalize(&secp)?;

    let feebump_txin = FeeBumpTxIn::new(
        OutPoint {
            txid: feebump_tx.0.txid(),
            vout: 0,
        },
        feebump_txo.clone(),
    );
    let mut unemergency_tx = UnvaultEmergencyTransaction::new(
        rev_unvault_txin.clone(),
        Some(feebump_txin),
        emergency_address,
        0,
    );
    assert_eq!(
        unemergency_tx.emergency_outpoint(),
        OutPoint {
            txid: unemergency_tx.txid(),
            vout: 0
        }
    );

    satisfy_transaction_input(
        &secp,
        &mut unemergency_tx,
        0,
        &unemergency_tx_sighash,
        &stakeholders_priv,
        Some(child_number),
    )?;
    // We don't have satisfied the feebump input yet!
    // Note that we clone because Miniscript's finalize() will wipe the PSBT input..
    match unemergency_tx.clone().finalize(&secp) {
        Err(e) => assert!(
            e.to_string()
                .contains("Missing pubkey for a pkh/wpkh at index 1"),
            "Got another error: {}",
            e
        ),
        Ok(_) => unreachable!(),
    }
    // Now actually satisfy it, libbitcoinconsensus should not yell
    let unemer_tx_sighash_feebump = unemergency_tx
        .signature_hash(1, SigHashType::All)
        .expect("Input exists");
    satisfy_transaction_input(
        &secp,
        &mut unemergency_tx,
        1,
        &unemer_tx_sighash_feebump,
        &vec![feebump_xpriv],
        None,
    )?;
    unemergency_tx.finalize(&secp)?;

    // Now we can sign the unvault
    let unvault_tx_sighash = unvault_tx
        .signature_hash(0, SigHashType::All)
        .expect("Input exists");
    satisfy_transaction_input(
        &secp,
        &mut unvault_tx,
        0,
        &unvault_tx_sighash,
        &stakeholders_priv,
        Some(child_number),
    )?;

    unvault_tx.finalize(&secp)?;

    // Create and sign a spend transaction
    let spend_unvault_txin = unvault_tx.spend_unvault_txin(&der_unvault_descriptor);
    let dummy_txo = TxOut::default();
    let cpfp_value = SpendTransaction::cpfp_txout(
        vec![spend_unvault_txin.clone()],
        vec![SpendTxOut::Destination(dummy_txo.clone())],
        &der_cpfp_descriptor,
        0,
    )
    .txout()
    .value;
    let fees = 20_000;
    let spend_txo = TxOut {
        // The CPFP output value won't be > 150k sats for our parameters
        value: spend_unvault_txin.txout().txout().value - cpfp_value - fees,
        ..TxOut::default()
    };
    let mut spend_tx = SpendTransaction::new(
        vec![spend_unvault_txin.clone()],
        vec![SpendTxOut::Destination(spend_txo.clone())],
        &der_cpfp_descriptor,
        0,
        true,
    )
    .expect("Amounts ok");
    let spend_tx_sighash = spend_tx
        .signature_hash(0, SigHashType::All)
        .expect("Input exists");
    satisfy_transaction_input(
        &secp,
        &mut spend_tx,
        0,
        &spend_tx_sighash,
        &managers_priv
            .iter()
            .chain(cosigners_priv.iter())
            .copied()
            .collect::<Vec<bip32::ExtendedPrivKey>>(),
        Some(child_number),
    )?;
    spend_tx.finalize(&secp)?;

    // We can't create a dust output with the Spend
    let dust_txo = TxOut {
        value: 470,
        ..TxOut::default()
    };
    SpendTransaction::new(
        vec![spend_unvault_txin],
        vec![SpendTxOut::Destination(dust_txo.clone())],
        &der_cpfp_descriptor,
        0,
        true,
    )
    .expect_err("Creating a dust output");

    // The spend transaction can also batch multiple unvault txos
    let spend_unvault_txins: Vec<UnvaultTxIn> = unvault_spends
        .into_iter()
        .map(|(outpoint, value)| {
            UnvaultTxIn::new(
                outpoint,
                UnvaultTxOut::new(Amount::from_sat(value), &der_unvault_descriptor),
                csv,
            )
        })
        .collect();
    let n_txins = spend_unvault_txins.len();
    let dummy_txo = TxOut::default();
    let cpfp_value = SpendTransaction::cpfp_txout(
        spend_unvault_txins.clone(),
        vec![SpendTxOut::Destination(dummy_txo.clone())],
        &der_cpfp_descriptor,
        0,
    )
    .txout()
    .value;
    let fees = 30_000;
    let spend_txo = TxOut {
        value: spend_unvault_txins
            .iter()
            .map(|txin| txin.txout().txout().value)
            .sum::<u64>()
            - cpfp_value
            - fees,
        ..TxOut::default()
    };
    let mut spend_tx = SpendTransaction::new(
        spend_unvault_txins,
        vec![SpendTxOut::Destination(spend_txo.clone())],
        &der_cpfp_descriptor,
        0,
        true,
    )
    .expect("Amounts Ok");
    assert_eq!(spend_tx.fees(), fees);
    let mut hash_cache = SigHashCache::new(spend_tx.tx());
    let sighashes: Vec<SigHash> = (0..n_txins)
        .into_iter()
        .map(|i| {
            spend_tx
                .signature_hash_cached(i, SigHashType::All, &mut hash_cache)
                .expect("Input exists")
        })
        .collect();
    for (i, spend_tx_sighash) in sighashes.into_iter().enumerate() {
        satisfy_transaction_input(
            &secp,
            &mut spend_tx,
            i,
            &spend_tx_sighash,
            &managers_priv
                .iter()
                .chain(cosigners_priv.iter())
                .copied()
                .collect::<Vec<bip32::ExtendedPrivKey>>(),
            Some(child_number),
        )?
    }
    spend_tx.finalize(&secp)?;

    macro_rules! roundtrip {
        ($tx:ident, $tx_type:ident) => {
            #[cfg(feature = "use-serde")]
            {
                let serialized_tx = serde_json::to_string(&$tx).unwrap();
                let deserialized_tx = serde_json::from_str(&serialized_tx).unwrap();
                assert_eq!($tx, deserialized_tx);
            }

            #[cfg(not(feature = "use-serde"))]
            {
                let serialized_tx = $tx.to_string();
                let deserialized_tx: $tx_type = FromStr::from_str(&serialized_tx).unwrap();
                assert_eq!($tx, deserialized_tx);
            }
        };
    }

    roundtrip!(cancel_tx, CancelTransaction);
    roundtrip!(emergency_tx, EmergencyTransaction);
    roundtrip!(unvault_tx, UnvaultTransaction);
    roundtrip!(unemergency_tx, UnvaultEmergencyTransaction);
    roundtrip!(spend_tx, SpendTransaction);

    Ok(())
}

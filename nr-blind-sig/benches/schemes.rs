#![allow(non_snake_case)]

use criterion::{criterion_group, criterion_main, Criterion};

extern crate nr_blind_sig;
use nr_blind_sig::issuance_proof::*;
use nr_blind_sig::nrproof::*;
use nr_blind_sig::nrsig::*;
use nr_blind_sig::types::*;
use sha2::Digest;

// Note: To filter benchmarks with Criterion, the command:
//     cargo bench -- filter_re
// where filter_re is a regular expression that matches the name given to the bench_function() method.
// For example
//     cargo bench -- "S1"
//     cargo bench -- "^NIZK_Scheme1"

fn benchmark_scheme1(c: &mut Criterion) {
    // Generate a keypair for the issuer
    let keypair = NRKeyPair::generate();

    // Generate parameters for proving knowledge of signatures
    let params_r1csipa = NRProof::create_params_r1csipa();
    let params_spartan = NRProof::create_params_spartan();

    // Create a message to be signed
    let message_bytes = b"blind signature test message";
    let digest: [u8; 32] = sha2::Sha256::digest(message_bytes).into();
    let m = digest_to_F::<Fq>(&digest);

    // Step 1: User generates first message
    let (user1_msg, user_state) = BlindNrProtocols::user1_msg(&keypair.pk, &m);
    c.bench_function("S1 Generate user1_msg", |b| {
        b.iter(|| BlindNrProtocols::user1_msg(&keypair.pk, &m))
    });

    // Step 2: Issuer processes message and returns signature share
    let issuer_msg = BlindNrProtocols::issuer_sign_msg(&keypair, &user1_msg).unwrap();
    c.bench_function("S1 Generate issuer_sign_msg", |b| {
        b.iter(|| BlindNrProtocols::issuer_sign_msg(&keypair, &user1_msg).unwrap())
    });

    // Step 3: User finalizes the signature
    let signature = BlindNrProtocols::user2_finalize(&issuer_msg, &user_state).unwrap();
    c.bench_function("S1 Run user2_finalize", |b| {
        b.iter(|| BlindNrProtocols::user2_finalize(&issuer_msg, &user_state).unwrap())
    });

    // Verify the resulting signature
    assert!(NRKeyPair::verify_from_field_element(
        keypair.pk, &m, &signature
    ));
    assert!(NRKeyPair::verify(keypair.pk, message_bytes, &signature));

    // Configure a benchmark group with reduced sample size
    let mut nizk = c.benchmark_group("NIZK_Scheme1");
    nizk.sample_size(10); // Reduce from default 100 samples to just 10
    nizk.measurement_time(std::time::Duration::from_secs(5)); // Limit each measurement to 5 seconds

    // Create and verify the blind signature with the r1csipa NIZK
    let blind_sig =
        BlindNrProtocols::user_show_scheme1(&signature, &keypair.pk, &m, &params_r1csipa).unwrap();
    nizk.bench_function("S1 User show R1CSIPA", |b| {
        b.iter(|| {
            BlindNrProtocols::user_show_scheme1(&signature, &keypair.pk, &m, &params_r1csipa)
                .unwrap()
        })
    });
    assert!(BlindNrProtocols::verify_show_scheme1(
        &blind_sig,
        &keypair.pk,
        &m,
        &params_r1csipa
    ));
    nizk.bench_function("S1 Verify show R1CSIPA", |b| {
        b.iter(|| {
            BlindNrProtocols::verify_show_scheme1(&blind_sig, &keypair.pk, &m, &params_r1csipa)
        })
    });

    // Create and verify the blind signature with the Spartan NIZK
    let blind_sig =
        BlindNrProtocols::user_show_scheme1(&signature, &keypair.pk, &m, &params_spartan).unwrap();
    nizk.bench_function("S1 User show Spartan", |b| {
        b.iter(|| {
            BlindNrProtocols::user_show_scheme1(&signature, &keypair.pk, &m, &params_spartan)
                .unwrap()
        })
    });
    assert!(BlindNrProtocols::verify_show_scheme1(
        &blind_sig,
        &keypair.pk,
        &m,
        &params_spartan
    ));
    nizk.bench_function("S1 Verify show Spartan", |b| {
        b.iter(|| {
            BlindNrProtocols::verify_show_scheme1(&blind_sig, &keypair.pk, &m, &params_spartan)
        })
    });

    // Finish the group to restore default settings
    nizk.finish();
}

fn benchmark_scheme2(c: &mut Criterion) {
    // Generate a keypair for the issuer
    let keypair = NRKeyPair::generate();

    // Generate parameters for proving knowledge of signatures
    let params_r1csipa = NRProof::create_params_r1csipa();
    let params_spartan = NRProof::create_params_spartan();
    let issuance_params = IssuanceProof::create_params();

    // Create a message to be signed (for Scheme2, it needs to hash to a curve point)
    let message = NRKeyPair::choose_random_message();

    // Step 1: User generates first message (with issuance proof)
    let (user1_msg, user_state) =
        BlindNrProtocolsScheme2::user1_msg(&keypair.pk, &message, &issuance_params);
    c.bench_function("S2 Generate user1_msg", |b| {
        b.iter(|| BlindNrProtocolsScheme2::user1_msg(&keypair.pk, &message, &issuance_params))
    });

    // Step 2: Issuer processes message and returns signature share
    let issuer_msg =
        BlindNrProtocolsScheme2::issuer_sign_msg(&keypair, &user1_msg, &issuance_params).unwrap();
    c.bench_function("S2 Generate issuer_sign_msg", |b| {
        b.iter(|| {
            BlindNrProtocolsScheme2::issuer_sign_msg(&keypair, &user1_msg, &issuance_params)
                .unwrap()
        })
    });

    // Step 3: User finalizes the signature
    let signature = BlindNrProtocolsScheme2::user2_finalize(&issuer_msg, &user_state).unwrap();
    c.bench_function("S2 Run user2_finalize", |b| {
        b.iter(|| BlindNrProtocolsScheme2::user2_finalize(&issuer_msg, &user_state).unwrap())
    });

    // Verify the resulting signature
    assert!(NRKeyPair::verify2(keypair.pk, &message, &signature));

    // Create a proof message
    let proof_message = NRProofMessage {
        scheme: SchemeType::Scheme2,
        message_scheme1: None,
        message_scheme2: Some(message.clone()),
    };

    // Configure a benchmark group with reduced sample size
    let mut nizk = c.benchmark_group("NIZK_Scheme2");
    nizk.sample_size(10); // Reduce from default 100 samples to just 10
    nizk.measurement_time(std::time::Duration::from_secs(5)); // Limit each measurement to 5 seconds

    // Get base points
    let (H, V) = NRKeyPair::get_H_and_V();

    // Create and verify the blind signature with the r1csipa NIZK
    let proof_r1csipa = NRProof::prove(
        &params_r1csipa,
        &signature,
        &proof_message,
        &keypair.pk,
        &H,
        &V,
    );
    nizk.bench_function("S2 User show R1CSIPA", |b| {
        b.iter(|| {
            NRProof::prove(
                &params_r1csipa,
                &signature,
                &proof_message,
                &keypair.pk,
                &H,
                &V,
            )
        })
    });
    assert!(proof_r1csipa.verify(&params_r1csipa, &keypair.pk, &proof_message, &H, &V));
    nizk.bench_function("S2 Verify show R1CSIPA", |b| {
        b.iter(|| proof_r1csipa.verify(&params_r1csipa, &keypair.pk, &proof_message, &H, &V))
    });

    // Create and verify the blind signature with the Spartan NIZK
    let proof_spartan = NRProof::prove(
        &params_spartan,
        &signature,
        &proof_message,
        &keypair.pk,
        &H,
        &V,
    );
    nizk.bench_function("S2 User show Spartan", |b| {
        b.iter(|| {
            NRProof::prove(
                &params_spartan,
                &signature,
                &proof_message,
                &keypair.pk,
                &H,
                &V,
            )
        })
    });
    assert!(proof_spartan.verify(&params_spartan, &keypair.pk, &proof_message, &H, &V));
    nizk.bench_function("S2 Verify show Spartan", |b| {
        b.iter(|| proof_spartan.verify(&params_spartan, &keypair.pk, &proof_message, &H, &V))
    });

    // Finish the group to restore default settings
    nizk.finish();
}

criterion_group!(benches, benchmark_scheme1, benchmark_scheme2,);
criterion_main!(benches);

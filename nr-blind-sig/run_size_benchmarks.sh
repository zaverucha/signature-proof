#!/bin/bash

echo "Sizes for Scheme1 with curve P256/T256"
cargo test --release test_blind_signature_protocol_scheme1 -- --nocapture 2>/dev/null

echo "----"
echo "Sizes for Scheme1 with curve P256/T256"
cargo test --release test_blind_signature_protocol_scheme2 -- --nocapture 2>/dev/null

echo "----"
echo "Sizes for Scheme1 with curve Pallas/Vesta"
cargo test --release test_blind_signature_protocol_scheme1 --features vesta -- --nocapture  2>/dev/null

echo "----"
echo "Sizes for Scheme1 with curve Pallas/Vesta"
cargo test --release test_blind_signature_protocol_scheme2 --features vesta -- --nocapture 2>/dev/null

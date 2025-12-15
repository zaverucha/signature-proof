# r1csipa

A Rust library implementing an R1CS to IPA (Inner Product Argument) transformation with zero-knowledge support.

## Overview

This crate implements the R1CS to IPA transform described in ePrint 2025/327:
"Bulletproofs for R1CS: Bridging the Completeness-Soundness Gap and a ZK Extension" by Gil Segev.

The underlying IPA protocol supports zero-knowledge as described in ePrint 2020/735:
"Bulletproofs+: Shorter Proofs for Privacy-Enhanced Distributed Ledger" by Heewon Chung, Kyoohyung Han, Chanyang Ju, Myungsun Kim, and Jae Hong Seo.

The initial IPA code was derived from the [dalek Bulletproofs implementation](https://github.com/zkcrypto/bulletproofs) by Henry de Valence, Cathie Yun, and Oleg Andreev.

## Features

- **R1CS to IPA transformation**: Compile R1CS constraint systems to efficient inner product arguments
- **Zero-knowledge support**: Optional ZK extensions for privacy-preserving proofs
- **Bellpepper integration**: Express circuits as bellpepper gadgets for convenient constraint generation
- **Flexible curve support**: Works with elliptic curves from halo2curves

## License

MIT



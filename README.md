# Zero-Knowledge Proofs for Nyberg-Rueppel Signatures

Some Rust crates for building zero-knowledge proofs of signature possession.

We provide proof systems for demonstrating knowledge of signatures without revealing the signatures themselves. The primary application is blind signatures based on the Nyberg-Rueppel signature scheme, but the underlying components are general-purpose and can be adapted to prove possession of various signature types. Two proof systems are provided: one based on Bulletproofs/inner-product arguments and a second based on Spartan.  

See the associated paper for more details:
TODO: add TITLE, AUTHORS, EPRINT info

## Crates

### `nr-blind-sig` (blind-nr)
Implementation of blind signatures using the Nyberg-Rueppel signature scheme with zero-knowledge proofs. The main research artifact demonstrating practical applications of the R1CS-to-IPA transformation.

### `r1csipa`
A library implementing an R1CS to IPA (Inner Product Argument) transformation with zero-knowledge support. Based on ePrint 2025/327 by Gil Segev, Bulletproofs (dalek-bulletproofs), and the Bulletproofs+ protocol (ePrint 2020/735). 
Outside of the signature application, this is a stand-along crate that can lets one use Bulletproofs as a backend for proving R1CS instances.  For small circuits (say less than 5k constraints), the prover time remains reasonable and the proofs are very short.

### `spartan-t256`
Fork of the [Spartan proof system](https://github.com/microsoft/Spartan) with T-256 elliptic curve support and bellpepper gadget integration. Originally created by Pui Yung Anna Woo for the sig-pop project, extended by Greg Zaverucha with bellpepper support from [Spartan2](https://github.com/microsoft/Spartan2).

### `halo2curves`
Fork of [halo2curves](https://github.com/privacy-scaling-explorations/halo2curves) that adds support for the T-256 curve.


## Building and Testing

Build all crates:
```bash
cargo build --release
```

Run tests for individual crates:
```bash
cargo test -p r1csipa
cargo test -p nr-blind-sig
cargo test -p ecdsa-pop
cargo test -p spartan-t256
```

## License

MIT


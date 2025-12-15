# Zero-Knowledge Proofs for Signatures

Some Rust crates for building zero-knowledge proofs of signature possession.

We provide two proof systems for demonstrating knowledge of signatures without revealing the signatures themselves.  One is based on Bulletproofs and inner-product arguments and a second based on Spartan. The primary application is a contruction of round-optimal blind signatures without pairings, based on the Nyberg-Rueppel signature scheme.  The underlying components are general-purpose and can be adapted to prove possession of various signature types.   

See the associated paper for more details:  
TODO: add TITLE, AUTHORS, EPRINT info

## Crates
The project is structured as separate crates, so that the two proofs systems `r1csipa` and `spartan-t256` can be used in other applications.

`nr-blind-sig` depends on either `r1csipa` or `spartan-t256`, both of which depend on `halo2curves`.


### `nr-blind-sig`
Implementation of a blind signature scheme based on Nyberg-Rueppel signatures and proofs of signature posession. 

### `r1csipa`
Bulletproofs are great for for small circuits (say less than 5k constraints), the prover time remains reasonable and the proofs are very short.
Expressing such circuits is commonly done with a front end that produces an R1CS instance to be proven.
This crate implements an R1CS to IPA transform with zero-knowledge support. IPAs (Inner Product Argument), are  the core type of statement proven by Bulletproofs.
The transform is based on Bunz's [thesis](https://cs.nyu.edu/~bb/papers/thesis.pdf) and ePrint [2025/327](https://eprint.iacr.org/2017/1066) by Segev, and the IPA implementation is based on [`dalek-bulletproofs`](https://github.com/dalek-cryptography/bulletproofs) and the Bulletproofs+ protocol (ePrint [2020/735](https://eprint.iacr.org/2020/735)). 
The prover time is reduced when compared to other implementations, by combining the scalar multiplications required to update the parameters with the other scalar multiplications; in each recursive step the prover computes one large multi-scalar multiplication, instead of many small ones.
Outside of the signature application, this is a stand-alone crate that can lets one use Bulletproofs as a backend for proving R1CS instances.  

### `spartan-t256`
This is a fork of the [Spartan proof system](https://github.com/microsoft/Spartan) with T-256 elliptic curve support and bellpepper gadget integration. Originally created by Pui Yung Anna Woo for the [sig-pop](https://github.com/pag-crypto/sigpop) project and [paper](https://eprint.iacr.org/2025/538), extended by Greg Zaverucha with bellpepper support from [Spartan2](https://github.com/microsoft/Spartan2).

### `halo2curves`
This is a fork of [halo2curves](https://github.com/privacy-scaling-explorations/halo2curves) that adds support for the T-256 curve.


## Building and Testing

Build and test all crates:
```bash
cargo test --release
```

Run tests for individual crates:
```bash
cargo test -p r1csipa
cargo test -p nr-blind-sig
cargo test -p ecdsa-pop
cargo test -p spartan-t256
```

Run benchmarks for NR blind signautres:
```bash
cd nr-blind-sig
cargo bench
```

## License

MIT


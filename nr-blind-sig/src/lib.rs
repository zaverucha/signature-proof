//! This library implements blind signature schemes based on the Nyberg-Rueppel signature scheme
#![deny(
   //warnings,
   //unused,
   future_incompatible,
   nonstandard_style,
   rust_2018_idioms,
   missing_docs
)]
#![allow(non_snake_case)]
#![forbid(unsafe_code)]
#![allow(missing_docs)]

mod ecc;
mod emulated;
mod errors;
pub mod issuance_proof;
pub mod nrproof;
pub mod nrsig;
mod poseidon;
pub mod types;
mod utils;

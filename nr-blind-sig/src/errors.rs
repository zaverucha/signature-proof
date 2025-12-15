//! This module defines errors returned by the library.

#[derive(Debug)]
pub enum NrError {
    /// The proof Pi_SL didn't verify
    UserIssuanceProofInvalid,
    /// The issued signature does not verify
    InvalidSignature,
}

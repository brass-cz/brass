//! Editor features built on the analysis layer: diagnostics, semantic-token
//! highlighting, hover (with its signature rendering), go-to-definition, and
//! completion, plus the position helpers they share (`nav`).

pub mod completion;
pub mod definition;
pub mod diagnostics;
pub mod hover;
pub mod nav;
pub mod semantic_tokens;
pub mod signature;

//! Finite-counterexample search for implications between equational laws
//! over magmas.
//!
//! ```
//! use magmahunt::{parse_law, refute, Options};
//!
//! let comm = parse_law("x ◇ y = y ◇ x").unwrap();
//! let assoc = parse_law("x ◇ (y ◇ z) = (x ◇ y) ◇ z").unwrap();
//! let result = refute(&comm, &assoc, 4, Options::default()).unwrap();
//! let witness = result.witness.expect("commutativity does not imply associativity");
//! assert_eq!(witness.size(), 2);
//! assert!(magmahunt::verify::verify_witness(&comm, &assoc, &witness).is_ok());
//! ```

pub mod eval;
pub mod implication;
pub mod law;
pub mod magma;
pub mod matrix;
pub mod naive;
pub mod search;
pub mod verify;

pub use eval::CompiledLaw;
pub use law::{generate_laws, parse_law, parse_law_list, Law, ParseError, Term};
pub use magma::Magma;
pub use search::{count_models, Flow, Options, Search, Stats};

/// Result of [`refute`].
#[derive(Clone, Debug)]
pub struct Refutation {
    /// The smallest counterexample found, already re-checked by [`verify`].
    pub witness: Option<Magma>,
    /// Largest size fully searched (equal to the witness size when found).
    pub searched_up_to: usize,
    pub nodes: u64,
}

/// Looks for a magma of size `1..=max_size` that satisfies `hypothesis` and
/// violates `conclusion`, smallest size first.
///
/// Errors if a size would need too many ground instances, or if the
/// independent checker rejects a witness (which would indicate a solver bug).
pub fn refute(
    hypothesis: &Law,
    conclusion: &Law,
    max_size: usize,
    opts: Options,
) -> Result<Refutation, String> {
    let h = CompiledLaw::new(hypothesis);
    let c = CompiledLaw::new(conclusion);
    let mut nodes = 0;
    for n in 1..=max_size {
        search::check_size(&h, n)?;
        let mut found = None;
        let mut s = Search::new(&h, n, opts);
        s.run(&mut |table| {
            if c.holds_in(n, table) {
                Flow::Continue
            } else {
                found = Some(table.to_vec());
                Flow::Stop
            }
        });
        nodes += s.stats.nodes;
        if let Some(table) = found {
            let witness = Magma::new(n, table)?;
            verify::verify_witness(hypothesis, conclusion, &witness)
                .map_err(|e| format!("internal error: solver produced a bad witness: {e}"))?;
            return Ok(Refutation {
                witness: Some(witness),
                searched_up_to: n,
                nodes,
            });
        }
    }
    Ok(Refutation {
        witness: None,
        searched_up_to: max_size,
        nodes,
    })
}

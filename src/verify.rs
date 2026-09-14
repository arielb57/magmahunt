//! Independent brute-force checker.
//!
//! Deliberately shares no code with the compiled evaluator or the search: it
//! walks the term tree recursively and enumerates assignments by decoding a
//! counter, so a bug in the fast path cannot also hide here.

use crate::law::{Law, Term};
use crate::magma::Magma;

fn eval(term: &Term, m: &Magma, values: &[usize]) -> usize {
    match term {
        Term::Var(v) => values[*v as usize],
        Term::Op(l, r) => m.op(eval(l, m, values), eval(r, m, values)),
    }
}

/// Returns an assignment of the law's variables under which the two sides
/// differ in `m`, or `None` if `m` satisfies the law.
pub fn find_violation(law: &Law, m: &Magma) -> Option<Vec<usize>> {
    let n = m.size();
    let total = n.pow(law.nvars as u32);
    let mut values = vec![0; law.nvars];
    for code in 0..total {
        let mut rest = code;
        for slot in values.iter_mut() {
            *slot = rest % n;
            rest /= n;
        }
        if eval(&law.lhs, m, &values) != eval(&law.rhs, m, &values) {
            return Some(values);
        }
    }
    None
}

pub fn satisfies(m: &Magma, law: &Law) -> bool {
    find_violation(law, m).is_none()
}

/// Confirms that `m` satisfies `hypothesis` and violates `conclusion`.
pub fn verify_witness(hypothesis: &Law, conclusion: &Law, m: &Magma) -> Result<Vec<usize>, String> {
    if let Some(values) = find_violation(hypothesis, m) {
        return Err(format!(
            "witness violates the hypothesis {hypothesis} at {values:?}"
        ));
    }
    find_violation(conclusion, m)
        .ok_or_else(|| format!("witness satisfies the conclusion {conclusion}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::law::parse_law;

    #[test]
    fn accepts_a_genuine_witness_and_reports_the_violating_assignment() {
        let comm = parse_law("x ◇ y = y ◇ x").unwrap();
        let assoc = parse_law("x ◇ (y ◇ z) = (x ◇ y) ◇ z").unwrap();
        // NOR-like table: commutative, not associative.
        let m = Magma::new(2, vec![1, 0, 0, 0]).unwrap();
        let values = verify_witness(&comm, &assoc, &m).unwrap();
        let (x, y, z) = (values[0], values[1], values[2]);
        assert_ne!(m.op(x, m.op(y, z)), m.op(m.op(x, y), z));
    }

    #[test]
    fn rejects_witnesses_that_break_the_hypothesis_or_satisfy_the_conclusion() {
        let comm = parse_law("x ◇ y = y ◇ x").unwrap();
        let assoc = parse_law("x ◇ (y ◇ z) = (x ◇ y) ◇ z").unwrap();
        let left_projection = Magma::new(2, vec![0, 0, 1, 1]).unwrap();
        let err = verify_witness(&comm, &assoc, &left_projection).unwrap_err();
        assert!(err.contains("violates the hypothesis"), "{err}");
        let xor = Magma::new(2, vec![0, 1, 1, 0]).unwrap();
        let err = verify_witness(&comm, &assoc, &xor).unwrap_err();
        assert!(err.contains("satisfies the conclusion"), "{err}");
    }

    #[test]
    fn trivial_magma_satisfies_everything() {
        let m = Magma::new(1, vec![0]).unwrap();
        for s in ["x = y", "x = y ◇ (z ◇ x)", "x ◇ y = y ◇ x"] {
            assert!(satisfies(&m, &parse_law(s).unwrap()));
        }
    }
}

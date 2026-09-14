//! Cheap, sound syntactic proofs that one law implies another.
//!
//! These never rely on search: a cell marked implied in the matrix carries a
//! proof, not merely the absence of a small counterexample.

use crate::law::{Law, Term};

/// Why `hypothesis` implies `conclusion`, when a syntactic reason exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Proof {
    /// The two laws are the same law (possibly with sides swapped).
    Same,
    /// The conclusion's sides are identical terms.
    TrivialConclusion,
    /// The hypothesis has the form `x = t` with `x` absent from `t`, which
    /// forces every element to equal `t` evaluated at fixed values: only the
    /// one-element magma satisfies it.
    CollapsesToSingleton,
    /// One side of the conclusion becomes the other by rewriting a single
    /// subterm with an instance of the hypothesis (a one-step equational
    /// derivation; plain substitution instances are the root case).
    Rewrite,
    /// Follows by chaining other proofs.
    Transitive,
}

fn collapses(var_side: &Term, other: &Term) -> bool {
    matches!(var_side, Term::Var(x) if !other.contains_var(*x))
}

fn match_term(pattern: &Term, target: &Term, subst: &mut [Option<Term>]) -> bool {
    match pattern {
        Term::Var(v) => match &subst[*v as usize] {
            Some(bound) => bound == target,
            None => {
                subst[*v as usize] = Some(target.clone());
                true
            }
        },
        Term::Op(pl, pr) => match target {
            Term::Op(tl, tr) => match_term(pl, tl, subst) && match_term(pr, tr, subst),
            Term::Var(_) => false,
        },
    }
}

/// Whether `(s, t)` is a substitution instance of `(rule.lhs, rule.rhs)`.
fn instance_pair(rule: &Law, s: &Term, t: &Term) -> bool {
    let mut subst = vec![None; rule.nvars];
    match_term(&rule.lhs, s, &mut subst) && match_term(&rule.rhs, t, &mut subst)
}

fn one_step(rule: &Law, swapped: &Law, s: &Term, t: &Term) -> bool {
    if instance_pair(rule, s, t) || instance_pair(swapped, s, t) {
        return true;
    }
    match (s, t) {
        (Term::Op(sl, sr), Term::Op(tl, tr)) => {
            (sl == tl && one_step(rule, swapped, sr, tr))
                || (sr == tr && one_step(rule, swapped, sl, tl))
        }
        _ => false,
    }
}

/// A direct (non-transitive) syntactic proof, if one exists.
pub fn direct_proof(hypothesis: &Law, conclusion: &Law) -> Option<Proof> {
    let swapped = hypothesis.swapped();
    if hypothesis == conclusion || swapped == *conclusion {
        Some(Proof::Same)
    } else if conclusion.is_trivial() {
        Some(Proof::TrivialConclusion)
    } else if collapses(&hypothesis.lhs, &hypothesis.rhs)
        || collapses(&hypothesis.rhs, &hypothesis.lhs)
    {
        Some(Proof::CollapsesToSingleton)
    } else if one_step(hypothesis, &swapped, &conclusion.lhs, &conclusion.rhs) {
        Some(Proof::Rewrite)
    } else {
        None
    }
}

/// Closes a row-major `m × m` proof table under transitivity (Warshall).
pub fn transitive_closure(m: usize, table: &mut [Option<Proof>]) {
    assert_eq!(table.len(), m * m, "proof table must be m × m");
    for k in 0..m {
        for i in 0..m {
            if table[i * m + k].is_none() {
                continue;
            }
            for j in 0..m {
                if table[i * m + j].is_none() && table[k * m + j].is_some() {
                    table[i * m + j] = Some(Proof::Transitive);
                }
            }
        }
    }
}

/// Row-major `m × m` table of proofs, closed under transitivity.
pub fn proof_table(laws: &[Law]) -> Vec<Option<Proof>> {
    let m = laws.len();
    let mut table = Vec::with_capacity(m * m);
    for h in laws {
        for c in laws {
            table.push(direct_proof(h, c));
        }
    }
    transitive_closure(m, &mut table);
    table
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::law::parse_law;

    fn proof(h: &str, c: &str) -> Option<Proof> {
        direct_proof(&parse_law(h).unwrap(), &parse_law(c).unwrap())
    }

    #[test]
    fn recognises_each_kind_of_direct_proof() {
        assert_eq!(proof("x◇y = y◇x", "b◇a = a◇b"), Some(Proof::Same));
        assert_eq!(proof("x = x◇x", "x◇x = x"), Some(Proof::Same));
        assert_eq!(
            proof("x◇y = y◇x", "x◇(y◇z) = x◇(y◇z)"),
            Some(Proof::TrivialConclusion)
        );
        assert_eq!(
            proof("x = y", "x◇y = y◇x"),
            Some(Proof::CollapsesToSingleton)
        );
        assert_eq!(
            proof("y◇z = x", "x◇y = y◇x"),
            Some(Proof::CollapsesToSingleton)
        );
        assert_eq!(
            proof("x◇y = y◇x", "(x◇x)◇y = y◇(x◇x)"),
            Some(Proof::Rewrite)
        );
        assert_eq!(proof("x = x◇x", "y◇z = (y◇z)◇(y◇z)"), Some(Proof::Rewrite));
        // Rewriting inside a context: z ◇ (x◇y) → z ◇ (y◇x).
        assert_eq!(
            proof("x◇y = y◇x", "z◇(x◇y) = z◇(y◇x)"),
            Some(Proof::Rewrite)
        );
    }

    #[test]
    fn does_not_claim_non_implications() {
        assert_eq!(proof("x◇y = y◇x", "x◇(y◇z) = (x◇y)◇z"), None);
        // x = x◇y mentions x on both sides, so it does not collapse by that rule.
        assert_eq!(proof("x = x◇y", "x◇y = y◇x"), None);
        // Substitution must be consistent: x ↦ y◇y and x ↦ z clash.
        assert_eq!(proof("x◇x = x", "(y◇y)◇z = y◇y"), None);
        // Instances go from general to specific only.
        assert_eq!(proof("x = x◇x", "x = x◇y"), None);
        // Two rewrites are needed here, so a single step must not claim it.
        assert_eq!(proof("x◇x = x", "x◇y = (x◇x)◇(y◇y)"), None);
    }

    #[test]
    fn closure_chains_proofs_across_rules() {
        let laws: Vec<Law> = ["x◇x = x", "x◇y = (x◇x)◇y", "x◇y = (x◇x)◇(y◇y)"]
            .iter()
            .map(|s| parse_law(s).unwrap())
            .collect();
        let t = proof_table(&laws);
        assert_eq!(t[1], Some(Proof::Rewrite));
        assert!(t.iter().step_by(4).all(|p| *p == Some(Proof::Same)));
        // Nothing proves the idempotence law back from the weaker ones.
        assert_eq!(t[3], None);
        assert_eq!(t[6], None);
    }

    #[test]
    fn closure_on_a_synthetic_chain() {
        let r = Some(Proof::Rewrite);
        // 0 → 1 → 2 → 3, nothing else.
        let mut t = vec![None; 16];
        t[1] = r;
        t[4 + 2] = r;
        t[8 + 3] = r;
        transitive_closure(4, &mut t);
        assert_eq!(t[2], Some(Proof::Transitive));
        assert_eq!(t[3], Some(Proof::Transitive));
        assert_eq!(t[4 + 3], Some(Proof::Transitive));
        assert_eq!(t[4], None);
        assert_eq!(t[12], None);
        assert_eq!(t[1], r);
    }
}

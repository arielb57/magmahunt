//! Property tests: the pruned search against naive enumeration.

mod common;

use magmahunt::implication::direct_proof;
use magmahunt::verify::verify_witness;
use magmahunt::{count_models, naive, refute, CompiledLaw, Flow, Law, Options, Search, Term};
use proptest::prelude::*;

fn term(max_ops: u32) -> BoxedStrategy<Term> {
    let leaf = (0u8..4).prop_map(Term::Var);
    leaf.prop_recursive(max_ops, 16, 2, |inner| {
        (inner.clone(), inner).prop_map(|(l, r)| Term::op(l, r))
    })
    .boxed()
}

/// Laws with at most 4 operations in total.
fn law() -> impl Strategy<Value = Law> {
    (term(4), term(4)).prop_filter_map("more than 4 operations", |(l, r)| {
        (l.ops() + r.ops() <= 4).then(|| Law::new(l, r))
    })
}

fn substitute(t: &Term, v: u8, with: &Term) -> Term {
    match t {
        Term::Var(x) if *x == v => with.clone(),
        Term::Var(_) => t.clone(),
        Term::Op(l, r) => Term::op(substitute(l, v, with), substitute(r, v, with)),
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 64, ..ProptestConfig::default() })]

    #[test]
    fn pruned_search_and_naive_agree_up_to_size_3(h in law(), c in law()) {
        let (slow, _) = naive::refute(&h, &c, 3);
        for opts in [Options::default(), Options::no_symmetry(), Options { symmetry: true, most_constrained: false }] {
            let fast = refute(&h, &c, 3, opts).unwrap();
            prop_assert_eq!(fast.witness.is_some(), slow.is_some(), "{} => {} with {:?}", h, c, opts);
            if let (Some(w), Some(s)) = (&fast.witness, &slow) {
                prop_assert_eq!(w.size(), s.size());
                prop_assert!(verify_witness(&h, &c, w).is_ok());
            }
        }
    }

    #[test]
    fn labelled_counts_match_naive(l in law()) {
        let compiled = CompiledLaw::new(&l);
        for n in 1..=3 {
            prop_assert_eq!(count_models(&compiled, n, Options::no_symmetry()).leaves, naive::count_models(&l, n), "{} at size {}", l, n);
        }
    }

    #[test]
    fn symmetric_counts_are_isomorphism_classes(l in law()) {
        let compiled = CompiledLaw::new(&l);
        let mut labelled = Vec::new();
        naive::for_each_table(3, u64::MAX, &mut |t| {
            if compiled.holds_in(3, t) {
                labelled.push(t.to_vec());
            }
            true
        });
        let mut leaders = Vec::new();
        Search::new(&compiled, 3, Options::default()).run(&mut |t| {
            leaders.push(t.to_vec());
            Flow::Continue
        });
        prop_assert_eq!(leaders.len(), common::iso_classes(3, &labelled));
        for t in &leaders {
            prop_assert_eq!(&common::canonical(3, t), t);
        }
    }

    #[test]
    fn rewrite_proofs_are_sound(h in law(), v in 0u8..4, with in term(2)) {
        // Substituting into h yields a consequence the proof rules must find.
        let c = Law::new(substitute(&h.lhs, v, &with), substitute(&h.rhs, v, &with));
        prop_assert!(direct_proof(&h, &c).is_some(), "{} => {}", h, c);
        prop_assert!(naive::refute(&h, &c, 3).0.is_none());
    }
}

mod common;

use magmahunt::implication::direct_proof;
use magmahunt::matrix::{Cell, Matrix};
use magmahunt::verify::{satisfies, verify_witness};
use magmahunt::{
    count_models, generate_laws, naive, parse_law, refute, CompiledLaw, Flow, Law, Options, Search,
};

const ASSOC: &str = "x ◇ (y ◇ z) = (x ◇ y) ◇ z";
const COMM: &str = "x ◇ y = y ◇ x";

fn law(s: &str) -> Law {
    parse_law(s).unwrap()
}

fn all_orders(symmetry: bool) -> [Options; 2] {
    [
        Options {
            symmetry,
            most_constrained: true,
        },
        Options {
            symmetry,
            most_constrained: false,
        },
    ]
}

fn labelled_models(l: &Law, n: usize) -> Vec<Vec<u8>> {
    let compiled = CompiledLaw::new(l);
    let mut out = Vec::new();
    Search::new(&compiled, n, Options::no_symmetry()).run(&mut |t| {
        out.push(t.to_vec());
        Flow::Continue
    });
    out
}

#[test]
fn labelled_semigroup_counts_match_oeis_a023814() {
    let assoc = CompiledLaw::new(&law(ASSOC));
    for opts in all_orders(false) {
        let counts: Vec<u64> = (1..=4)
            .map(|n| count_models(&assoc, n, opts).leaves)
            .collect();
        assert_eq!(counts, [1, 8, 113, 3492], "{opts:?}");
    }
}

#[test]
fn commutative_magma_counts_are_n_to_the_n_n_plus_1_over_2() {
    let comm = CompiledLaw::new(&law(COMM));
    for n in 1..=4usize {
        let expected = (n as u64).pow((n * (n + 1) / 2) as u32);
        assert_eq!(
            count_models(&comm, n, Options::no_symmetry()).leaves,
            expected,
            "n = {n}"
        );
    }
}

#[test]
fn symmetry_breaking_keeps_exactly_one_table_per_isomorphism_class() {
    let assoc = law(ASSOC);
    let compiled = CompiledLaw::new(&assoc);
    for n in 1..=4 {
        let classes = common::iso_classes(n, &labelled_models(&assoc, n));
        for opts in all_orders(true) {
            assert_eq!(
                count_models(&compiled, n, opts).leaves as usize,
                classes,
                "n = {n}, {opts:?}"
            );
        }
    }
    // OEIS A027851, semigroups up to isomorphism.
    let up_to_iso: Vec<u64> = (1..=4)
        .map(|n| count_models(&compiled, n, Options::default()).leaves)
        .collect();
    assert_eq!(up_to_iso, [1, 5, 24, 188]);
}

#[test]
fn symmetry_breaking_counts_all_magmas_up_to_isomorphism() {
    // OEIS A001329: 1, 10, 3330.
    let any = CompiledLaw::new(&law("x = x"));
    let counts: Vec<u64> = (1..=3)
        .map(|n| count_models(&any, n, Options::default()).leaves)
        .collect();
    assert_eq!(counts, [1, 10, 3330]);
}

#[test]
fn accepted_tables_are_lex_leaders_and_really_models() {
    let idem = law("x = x ◇ x");
    let compiled = CompiledLaw::new(&idem);
    let mut seen = 0;
    Search::new(&compiled, 3, Options::default()).run(&mut |t| {
        assert_eq!(
            common::canonical(3, t),
            t.to_vec(),
            "not the least relabelling"
        );
        let m = magmahunt::Magma::new(3, t.to_vec()).unwrap();
        assert!(satisfies(&m, &idem));
        seen += 1;
        Flow::Continue
    });
    assert_eq!(seen, common::iso_classes(3, &labelled_models(&idem, 3)));
}

#[test]
fn commutativity_does_not_imply_associativity_smallest_witness_is_size_2() {
    let (comm, assoc) = (law(COMM), law(ASSOC));
    assert!(refute(&comm, &assoc, 1, Options::default())
        .unwrap()
        .witness
        .is_none());
    for opts in all_orders(true).into_iter().chain(all_orders(false)) {
        let r = refute(&comm, &assoc, 5, opts).unwrap();
        let w = r.witness.expect("a witness exists");
        assert_eq!(w.size(), 2);
        assert_eq!(r.searched_up_to, 2);
        verify_witness(&comm, &assoc, &w).unwrap();
    }
}

#[test]
fn idempotence_does_not_imply_commutativity() {
    let (idem, comm) = (law("x = x ◇ x"), law(COMM));
    let w = refute(&idem, &comm, 4, Options::default())
        .unwrap()
        .witness
        .unwrap();
    assert_eq!(w.size(), 2);
    verify_witness(&idem, &comm, &w).unwrap();
    // The converse fails too, also at size 2.
    let w = refute(&comm, &idem, 4, Options::default())
        .unwrap()
        .witness
        .unwrap();
    verify_witness(&comm, &idem, &w).unwrap();
}

#[test]
fn x_equals_y_implies_every_law() {
    let singleton = law("x = y");
    for c in generate_laws(3).iter().take(60) {
        let r = refute(&singleton, c, 4, Options::default()).unwrap();
        assert!(r.witness.is_none(), "x = y must imply {c}");
        assert_eq!(r.searched_up_to, 4);
        // Size 1 has one cell to fill; larger sizes are rejected before any assignment.
        assert_eq!(r.nodes, 1);
    }
}

#[test]
fn left_projection_law_implies_associativity() {
    let (proj, assoc) = (law("x ◇ y = x"), law(ASSOC));
    for opts in [Options::default(), Options::no_symmetry()] {
        let r = refute(&proj, &assoc, 5, opts).unwrap();
        assert!(r.witness.is_none());
        assert_eq!(r.searched_up_to, 5);
    }
    // x ◇ y = x has exactly one model per size, so the search must find it.
    for n in 1..=5 {
        assert_eq!(
            count_models(&CompiledLaw::new(&proj), n, Options::no_symmetry()).leaves,
            1
        );
    }
}

#[test]
fn search_agrees_with_naive_on_known_pairs() {
    let pairs = [
        ("x = x ◇ x", "x ◇ (x ◇ y) = x ◇ y"),
        ("x ◇ y = y ◇ x", "x ◇ (y ◇ x) = (x ◇ y) ◇ x"),
        ("x = (x ◇ y) ◇ x", "x ◇ x = x"),
        ("x ◇ (y ◇ z) = (x ◇ y) ◇ z", "x ◇ (y ◇ x) = x"),
        ("x = y ◇ (x ◇ y)", "x ◇ y = y ◇ x"),
    ];
    for (h, c) in pairs {
        let (h, c) = (law(h), law(c));
        let fast = refute(&h, &c, 3, Options::default()).unwrap();
        let (slow, _) = naive::refute(&h, &c, 3);
        assert_eq!(
            fast.witness.as_ref().map(|w| w.size()),
            slow.as_ref().map(|w| w.size()),
            "{h} => {c}"
        );
    }
}

#[test]
fn matrix_cells_agree_with_brute_force() {
    let laws: Vec<Law> = [
        "x = x",
        "x = y",
        "x = x ◇ x",
        "x = x ◇ y",
        "x ◇ y = y ◇ x",
        "x ◇ (y ◇ z) = (x ◇ y) ◇ z",
        "x ◇ y = x",
        "x = y ◇ (x ◇ y)",
        "x ◇ (x ◇ y) = x ◇ y",
        "(x ◇ x) ◇ y = y ◇ (x ◇ x)",
        "x ◇ y = (x ◇ y) ◇ (x ◇ y)",
    ]
    .iter()
    .map(|s| law(s))
    .collect();
    let m = laws.len();
    let matrix = Matrix::build(laws.clone(), 3, Options::default());
    assert_eq!(
        matrix.verify().unwrap(),
        matrix.count(|c| matches!(c, Cell::Refuted(_)))
    );
    for h in 0..m {
        assert!(matches!(matrix.cell(h, h), Cell::Implied(_)));
        for c in 0..m {
            let (naive_witness, _) = naive::refute(&laws[h], &laws[c], 3);
            match matrix.cell(h, c) {
                Cell::Refuted(_) => assert!(naive_witness.is_some()),
                Cell::Implied(_) | Cell::Open => {
                    assert!(
                        naive_witness.is_none(),
                        "{} => {} has a naive counterexample",
                        laws[h],
                        laws[c]
                    )
                }
            }
        }
    }
    // Witness reuse: far fewer witnesses than refuted cells.
    assert!(matrix.witnesses.len() * 4 < matrix.count(|c| matches!(c, Cell::Refuted(_))));
    // x = y implies everything, and the comm => assoc cell is refuted.
    assert!((0..m).all(|c| matches!(matrix.cell(1, c), Cell::Implied(_))));
    assert!(matches!(matrix.cell(4, 5), Cell::Refuted(_)));
    assert!(matches!(matrix.cell(6, 5), Cell::Open));
}

#[test]
fn matrix_without_symmetry_gives_the_same_verdicts() {
    let laws: Vec<Law> = generate_laws(2).into_iter().take(25).collect();
    let a = Matrix::build(laws.clone(), 3, Options::default());
    let b = Matrix::build(laws, 3, Options::no_symmetry());
    let verdict = |c: &Cell| match c {
        Cell::Implied(_) => 0,
        Cell::Refuted(_) => 1,
        Cell::Open => 2,
    };
    assert_eq!(
        a.cells.iter().map(verdict).collect::<Vec<_>>(),
        b.cells.iter().map(verdict).collect::<Vec<_>>()
    );
    assert!(a.stats.nodes < b.stats.nodes);
}

#[test]
fn matrix_csv_has_one_row_and_column_per_law() {
    let laws: Vec<Law> = generate_laws(2).into_iter().take(8).collect();
    let matrix = Matrix::build(laws, 2, Options::default());
    let csv = matrix.to_csv();
    let rows: Vec<&str> = csv.lines().collect();
    assert_eq!(rows.len(), 9);
    for (i, row) in rows.iter().enumerate().skip(1) {
        let fields: Vec<&str> = row.split(',').collect();
        assert_eq!(fields.len(), 9);
        assert_eq!(fields[i], "implied");
        assert!(fields[1..]
            .iter()
            .all(|f| *f == "implied" || *f == "open" || f.starts_with('w')));
    }
    let text = matrix.witnesses_text();
    assert_eq!(
        text.matches("satisfies laws").count(),
        matrix.witnesses.len()
    );
}

#[test]
fn syntactic_proofs_hold_on_every_small_magma() {
    let laws: Vec<Law> = generate_laws(3).into_iter().take(80).collect();
    let magmas: Vec<magmahunt::Magma> = (1..=2)
        .flat_map(|n| {
            let mut all = Vec::new();
            naive::for_each_table(n, u64::MAX, &mut |t| {
                all.push(magmahunt::Magma::new(n, t.to_vec()).unwrap());
                true
            });
            all
        })
        .collect();
    let mut proofs = 0;
    for h in &laws {
        for c in &laws {
            if direct_proof(h, c).is_some() {
                proofs += 1;
                for m in &magmas {
                    assert!(
                        !satisfies(m, h) || satisfies(m, c),
                        "{h} => {c} fails in\n{m}"
                    );
                }
            }
        }
    }
    assert!(proofs > 200, "only {proofs} proofs exercised");
}

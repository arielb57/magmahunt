//! Prints the benchmark table from the README: wall time and nodes for the
//! solver with and without symmetry breaking, against naive enumeration.
//!
//! Run with `cargo run --release --example report`.

use std::time::{Duration, Instant};

use magmahunt::matrix::{Cell, Matrix};
use magmahunt::naive::{self, table_count};
use magmahunt::{count_models, generate_laws, parse_law, CompiledLaw, Options};

const SAMPLE_TABLES: u64 = 20_000_000;

fn row(name: &str, time: Duration, nodes: u64, note: &str) {
    println!(
        "| {name:<44} | {:>12.3} | {nodes:>15} | {note} |",
        time.as_secs_f64()
    );
}

fn main() {
    let modes = [
        (
            "solver, symmetry breaking + most-constrained",
            Options::default(),
        ),
        ("solver, no symmetry breaking", Options::no_symmetry()),
        (
            "solver, no symmetry, row-major order",
            Options {
                symmetry: false,
                most_constrained: false,
            },
        ),
    ];

    println!("(a) count semigroups of size 4");
    println!();
    println!(
        "| {:<44} | {:>12} | {:>15} | result |",
        "method", "seconds", "nodes"
    );
    println!(
        "|{}|-------------:|----------------:|--------|",
        "-".repeat(46)
    );
    let assoc = CompiledLaw::new(&parse_law("x ◇ (y ◇ z) = (x ◇ y) ◇ z").unwrap());
    for (name, opts) in modes {
        let start = Instant::now();
        let stats = count_models(&assoc, 4, opts);
        let kind = if opts.symmetry { "classes" } else { "labelled" };
        row(
            name,
            start.elapsed(),
            stats.nodes,
            &format!("{} {kind}", stats.leaves),
        );
    }
    let start = Instant::now();
    let mut sample_models = 0u64;
    naive::for_each_table(4, SAMPLE_TABLES, &mut |t| {
        sample_models += assoc.holds_in(4, t) as u64;
        true
    });
    let sampled = start.elapsed();
    let total = table_count(4);
    let extrapolated = sampled.mul_f64(total as f64 / SAMPLE_TABLES as f64);
    row(
        "naive enumeration (extrapolated)",
        extrapolated,
        total,
        &format!(
            "sampled {SAMPLE_TABLES} tables in {:.2}s",
            sampled.as_secs_f64()
        ),
    );

    println!();
    let laws: Vec<_> = generate_laws(3).into_iter().take(50).collect();
    println!("(b) 50x50 implication matrix over the first 50 ETP-style laws, sizes 1..=4");
    println!();
    println!(
        "| {:<44} | {:>12} | {:>15} | result |",
        "method", "seconds", "nodes"
    );
    println!(
        "|{}|-------------:|----------------:|--------|",
        "-".repeat(46)
    );
    for (name, opts) in modes {
        let start = Instant::now();
        let matrix = Matrix::build(laws.clone(), 4, opts);
        let elapsed = start.elapsed();
        matrix.verify().expect("every witness re-verifies");
        row(
            name,
            elapsed,
            matrix.stats.nodes,
            &format!(
                "{} refuted, {} implied, {} open, {} witnesses",
                matrix.count(|c| matches!(c, Cell::Refuted(_))),
                matrix.count(|c| matches!(c, Cell::Implied(_))),
                matrix.count(|c| *c == Cell::Open),
                matrix.witnesses.len()
            ),
        );
    }
    // Naive batch baseline: for every ordered pair without a syntactic proof,
    // enumerate tables of sizes 1..=4 until a counterexample appears. Pairs
    // with no counterexample cost all 1 + 16 + 19683 + 4^16 tables, so the
    // size-4 part is extrapolated from the sampled throughput above.
    let proofs = magmahunt::implication::proof_table(&laws);
    let m = laws.len();
    let start = Instant::now();
    let mut tables = 0u64;
    let mut unresolved = 0u64;
    for h in 0..m {
        for c in 0..m {
            if proofs[h * m + c].is_some() {
                continue;
            }
            let (found, visited) = naive::refute(&laws[h], &laws[c], 3);
            tables += visited;
            if found.is_none() {
                unresolved += 1;
            }
        }
    }
    let small = start.elapsed();
    let per_table = sampled.as_secs_f64() / SAMPLE_TABLES as f64;
    let size4 = Duration::from_secs_f64(unresolved as f64 * total as f64 * per_table);
    row(
        "naive per pair (size 4 extrapolated)",
        small + size4,
        tables + unresolved * total,
        &format!("{unresolved} pairs need a full size-4 sweep (upper bound)"),
    );
}

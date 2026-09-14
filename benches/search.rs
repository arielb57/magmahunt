//! Criterion timings. For the node counts and the naive extrapolation shown
//! in the README, run `cargo run --release --example report`.

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use magmahunt::matrix::Matrix;
use magmahunt::naive;
use magmahunt::{count_models, generate_laws, parse_law, CompiledLaw, Options};

const ASSOC: &str = "x ◇ (y ◇ z) = (x ◇ y) ◇ z";

fn semigroups(c: &mut Criterion) {
    let law = parse_law(ASSOC).unwrap();
    let compiled = CompiledLaw::new(&law);
    let mut g = c.benchmark_group("count semigroups, size 4");
    g.sample_size(20);
    g.bench_function("search, symmetry breaking", |b| {
        b.iter(|| count_models(&compiled, 4, Options::default()))
    });
    g.bench_function("search, no symmetry breaking", |b| {
        b.iter(|| count_models(&compiled, 4, Options::no_symmetry()))
    });
    // Naive enumeration cannot finish 4^16 tables per iteration; this measures
    // a fixed prefix of one million tables to get throughput.
    g.bench_function("naive, first 1e6 of 4^16 tables", |b| {
        b.iter(|| {
            let mut count = 0u64;
            naive::for_each_table(4, 1_000_000, &mut |t| {
                count += compiled.holds_in(4, t) as u64;
                true
            });
            count
        })
    });
    g.finish();
}

fn implication_matrix(c: &mut Criterion) {
    let laws: Vec<_> = generate_laws(3).into_iter().take(50).collect();
    let mut g = c.benchmark_group("50x50 implication matrix, sizes 1..=4");
    g.sample_size(10);
    g.bench_function("search, symmetry breaking", |b| {
        b.iter_batched(
            || laws.clone(),
            |l| Matrix::build(l, 4, Options::default()),
            BatchSize::SmallInput,
        )
    });
    g.bench_function("search, no symmetry breaking", |b| {
        b.iter_batched(
            || laws.clone(),
            |l| Matrix::build(l, 4, Options::no_symmetry()),
            BatchSize::SmallInput,
        )
    });
    g.finish();
}

criterion_group!(benches, semigroups, implication_matrix);
criterion_main!(benches);

# magmahunt

Fast finite-counterexample search for implications between equational laws over magmas.

## The problem

To show that one equational law (say `x ◇ y = y ◇ x`) does not imply another (say associativity), you exhibit a small magma that satisfies the first and breaks the second. General model finders such as Mace4 do this well for one query, but they are separate processes with a general first-order front end, which is slow to call thousands of times when you want the implication matrix of hundreds of laws. Writing your own loop over tables does not work either: size 4 already has 4^16 = 4.3 billion tables. magmahunt is a small Rust library and CLI built for exactly this one question: it searches, reuses what it finds, and re-checks every answer with an independent checker.

## How it works

**Parsing.** Laws are written in ETP (Equational Theories Project) notation, `x ◇ (y ◇ z) = (x ◇ y) ◇ z`, with `*` accepted for `◇`. Unparenthesised chains associate to the left, as in ETP's Lean files. Each side becomes a term tree, variables are numbered by first occurrence, and each tree is compiled to postfix code for a small stack machine.

**Partial evaluation.** The search works on a partial `n × n` table in which unassigned cells hold `UNKNOWN`. Evaluating a term under an assignment of its variables either produces a value or stops at the first unknown cell it needs. Both operands of an operation are known by the time it runs, so the unknown short-circuits the whole side, and that cell is the answer: "this instance is waiting on cell (a, b)".

**Backtracking with watch lists.** All `n^k` ground instances of the hypothesis are listed once. Each one sits on the watch list of the cell its evaluation is blocked on. Assigning a cell re-evaluates only that cell's list. Each instance then either holds (and is dropped for this branch), fails (prune), or blocks on another unknown cell (move it to that cell's list). An instance is checked exactly when its evaluation may have become determined, and never earlier. Undo is cheap: moves only append to other lists, so backtracking pops them off in reverse order. The assigned cell's own list is left alone.

Worked example, associativity at size 2, instance `x=1, y=0, z=1`:

```
table empty            (1◇0)◇1 needs cell (1,0)        -> watch[(1,0)]
assign 1◇0 = 0         (0)◇1 needs cell (0,1)          -> watch[(0,1)]
assign 0◇1 = 1         lhs = 1; rhs 1◇(0◇1) = 1◇1 needs (1,1) -> watch[(1,1)]
assign 1◇1 = 0         lhs 1 ≠ rhs 0                   -> prune, try 1◇1 = 1
```

**Cell choice.** The next cell is the unassigned one with the longest watch list, meaning the one whose assignment decides the most pending instances. Ties go to the first cell in row-major order.

**Symmetry breaking.** Relabelling the elements of a model gives another model, so the search keeps only lex-leaders: tables that are smallest in row-major order among all `n!` relabellings. After every assignment, a partial check walks each permutation's relabelled table against the current one. It prunes only when a known prefix already shows that the relabelled table is smaller, which no completion can fix. On a complete table this check is exact, so each isomorphism class is visited exactly once.

**Batch mode.** `matrix` first fills in every implication that has a cheap syntactic proof: identical laws, a trivial conclusion, a hypothesis `x = t` with `x` not in `t` (only the one-element magma satisfies it), or a conclusion that is one rewrite step from the hypothesis (a substitution instance, possibly inside a context). Those proofs are then closed under transitivity. After that it searches size by size across all rows. When a model of row `h`'s law refutes one of that row's open cells, it becomes a witness. The witness is evaluated against every law, and it refutes every open cell `(a, b)` with `a` satisfied and `b` violated, not just the one it was found for. On the 50-law benchmark, 16 witnesses account for all 1533 refutations. Evaluating each witness on every law also covers the refutation half of transitivity: if `a ⇒ h` is proven and `M` refutes `h ⇒ c`, then `M` satisfies `a` and refutes `a ⇒ c` directly.

**Trust.** `verify.rs` is a separate brute-force checker. It evaluates term trees recursively and shares no code with the compiled evaluator or the search. The CLI re-checks every witness with it before printing, and `matrix` re-checks every refuted cell.

## Install and usage

Requires a Rust toolchain (1.74 or newer). There are no runtime dependencies. From a clone of this repository:

```sh
cargo build --release
cargo test                                  # unit, property, conformance and CLI tests
cargo run --release --example report        # the benchmark tables below
cargo bench                                 # Criterion timings of the same workloads
```

Refute an implication:

```
$ cargo run --release -q -- refute 'x ◇ y = y ◇ x' 'x ◇ (y ◇ z) = (x ◇ y) ◇ z' --max-size 5
hypothesis: x ◇ y = y ◇ x
conclusion: x ◇ (y ◇ z) = (x ◇ y) ◇ z
counterexample of size 2 (re-verified by the brute-force checker):
◇ | 0 1
--+----
0 | 1 0
1 | 0 0
nodes explored: 16, time: 29.833µs
```

```
$ cargo run --release -q -- refute 'x ◇ y = x' 'x ◇ (y ◇ z) = (x ◇ y) ◇ z' --max-size 5
hypothesis: x ◇ y = x
conclusion: x ◇ (y ◇ z) = (x ◇ y) ◇ z
none up to size 5
nodes explored: 225, time: 177.083µs
```

`refute` exits with 0 when it finds a counterexample, 1 for none, and 2 on an error. "None up to size N" is not a proof of the implication.

Build an implication matrix. `examples/laws50.txt` is the output of `magmahunt laws --max-ops 3 --limit 50`:

```
$ cargo run --release -q -- matrix examples/laws50.txt --max-size 4 --out-dir out
50 laws, 2500 ordered pairs, sizes 1..=4
  implied (syntactic proof): 806
  refuted by a witness:      1533
  open (none up to size 4): 161
16 witnesses, 1533 refutations re-verified by the brute-force checker
105 searches, 1252846 nodes, 301.500ms
wrote out/matrix.csv and out/witnesses.txt
```

`matrix.csv` has one row per hypothesis and one column per conclusion. Each cell is `implied`, `w<id>` (refuted by that witness) or `open`. `witnesses.txt` lists each table and the 1-based indices of the laws it satisfies:

```
w1: size 2, satisfies laws 1 3 8 23 43 47
◇ | 0 1
--+----
0 | 0 0
1 | 0 1
```

Laws files hold one law per line. Blank lines and `#` comments are ignored.

Other commands:

```
$ cargo run --release -q -- count 'x ◇ (y ◇ z) = (x ◇ y) ◇ z' --size 5
x ◇ (y ◇ z) = (x ◇ y) ◇ z
size 5: 1915 isomorphism classes of models
nodes explored: 247575, time: 72.676ms

$ cargo run --release -q -- count 'x ◇ (y ◇ z) = (x ◇ y) ◇ z' --size 5 --no-symmetry
x ◇ (y ◇ z) = (x ◇ y) ◇ z
size 5: 183732 labelled models
nodes explored: 3373800, time: 282.621ms

$ cargo run --release -q -- laws --max-ops 2 --limit 4
x = x
x = y
x = x ◇ x
x = x ◇ y
```

As a library:

```rust
use magmahunt::{parse_law, refute, Options};

let comm = parse_law("x ◇ y = y ◇ x").unwrap();
let assoc = parse_law("x ◇ (y ◇ z) = (x ◇ y) ◇ z").unwrap();
let r = refute(&comm, &assoc, 4, Options::default()).unwrap();
println!("{}", r.witness.unwrap());
```

## Correctness

`cargo test` runs these checks, among others:

- Labelled semigroup counts for n = 1..4 are 1, 8, 113, 3492 (OEIS A023814), with symmetry breaking off, under both cell orders.
- Commutative magma counts equal n^(n(n+1)/2) for n = 1..4.
- With symmetry breaking on, the number of tables accepted equals the number of isomorphism classes, counted independently by brute-force canonical forms. Semigroups come out as 1, 5, 24, 188 (A027851), and all magmas as 1, 10, 3330 (A001329). Size 5 gives 1915 and 183732 from the CLI, matching A027851 and A023814.
- Known refutations: commutativity does not imply associativity (smallest witness has size 2), and idempotence does not imply commutativity. Known implications: `x = y` gives "none" against 60 laws at every size up to 4, and `x ◇ y = x` gives "none" against associativity up to size 5.
- Every witness is re-checked by the independent checker, and there are tests that the checker rejects bad witnesses.
- Property tests (proptest, random laws with at most 4 operations): pruned search and naive enumeration agree on whether a counterexample exists up to size 3, and on its size, under three option combinations. Labelled model counts match naive counts. Accepted tables are exactly the canonical forms. Substitution instances are always proven, and naive search finds no counterexample for them.
- Every matrix cell over an 11-law list is compared against naive enumeration up to size 3. Every syntactic proof over 80 generated laws is checked against all 17 magmas of size at most 2.
- Parser edge cases: nested and redundant parentheses, repeated variables, bare variables on either side, and malformed input with error offsets.

## Results

Measured with `cargo run --release --example report` on an Apple Silicon (arm64) Mac, macOS, Rust 1.94.1, single thread. Criterion timings for the same workloads come from `cargo bench`.

Nodes are cell assignments tried. For naive enumeration, nodes are complete tables examined. Naive throughput was sampled over the first 20 million tables in odometer order (each checked with the same compiled evaluator) and extrapolated to 4^16.

(a) Count semigroups of size 4

| method | seconds | nodes | result |
|---|--:|--:|---|
| solver, symmetry breaking + most-constrained | 0.002 | 6,920 | 188 classes |
| solver, no symmetry breaking | 0.008 | 42,396 | 3492 labelled |
| solver, no symmetry, row-major order | 0.021 | 136,152 | 3492 labelled |
| naive enumeration (extrapolated) | ~279 | 4,294,967,296 | sampled 20M tables in 1.30 s |

(b) 50 × 50 implication matrix over the first 50 ETP-style laws, sizes 1..4

| method | seconds | nodes | result |
|---|--:|--:|---|
| solver, symmetry breaking + most-constrained | 0.296 | 1,252,846 | 1533 refuted, 806 implied, 161 open, 16 witnesses |
| solver, no symmetry breaking | 4.57 | 22,803,208 | same verdicts, 16 witnesses |
| solver, no symmetry, row-major order | 5.47 | 92,584,310 | same verdicts, 17 witnesses |
| naive per pair, size 4 extrapolated | ~47,000 | ~7.3 × 10^11 | 170 pairs need a full size-4 sweep |

The naive matrix baseline skips pairs with a syntactic proof. It runs sizes 1 to 3 for real, then charges all 4^16 tables for each of the 170 pairs still unrefuted at size 3. That is an upper bound: 9 of those pairs have a size-4 witness, and naive would stop early on them.

On these workloads, symmetry breaking gives about a 6× cut in nodes for semigroups and 15× in wall time for the matrix. Most-constrained cell choice gives about another 3× (semigroups) to 4× (matrix) in nodes over row-major order. The matrix is dominated by a few rows whose law has many models and implies a conclusion that no cheap proof covers. In those rows the search has to enumerate every model to answer "none".

## Design notes

**Watch lists instead of re-checking instances.** The obvious implementation re-evaluates every instance after each assignment, or indexes instances by the cells they "use". Neither works well: which cells an instance uses depends on the table values, so no static index is correct. Blocking on the first unknown cell gives a dynamic index that is always exact. It costs one re-evaluation per instance per move. The leftover watch list of an assigned cell is kept as is rather than cleared, so undo only has to pop what was pushed. The watch-list length is also free to read, so the most-constrained heuristic costs one scan over n² counters.

**Lex-leader under a non-row-major fill order.** Lex-leader constraints prune best when cells are filled in the same row-major order they are compared in. Most-constrained selection works against that. I kept both: the partial check stops at the first unknown position for each permutation, which keeps it sound in any fill order. Ties in the heuristic go to row-major order, which keeps enough of the prefix filled for the check to bite. In the measurements above, turning either technique off costs nodes. The price is checking n! permutations per node: 24 at size 4, 120 at size 5, 720 at size 6. That per-node cost is why the tool is aimed at small sizes. In batch mode I chose to enumerate one hypothesis's models against all its open conclusions at once. A per-pair search would stop at the first witness for that pair, but each new witness could not help other rows until later. Enumerating per row and scoring every witness against all 50 laws is what gets the matrix down to 16 witnesses and 105 searches.

## Limitations

- "None up to size N" is not a proof. The only implications it proves are the syntactic ones listed above: no equational reasoning beyond one rewrite step plus transitivity, no Knuth-Bendix completion, and no infinite counterexamples. In the 50-law matrix, the 161 open cells include true implications that need a longer derivation.
- Search pruning uses only the hypothesis. The conclusion is checked on complete tables, so proving "none" means enumerating every model of the hypothesis up to isomorphism. That is fast for restrictive laws and slow for weak laws at size 5 and above.
- Ground instances are materialised: `n^k` of them for a law with `k` variables. Laws may have at most 8 variables, and a search refuses more than 4 million instances.
- Symmetry breaking checks all n! relabellings per node, so it becomes the bottleneck around size 7.
- One binary operation only. There are no constants, unary operations or multi-sorted signatures.
- `laws` follows ETP's construction order (commutativity is law 43, as in ETP), but the numbering is not guaranteed to match the published ETP list.
- Single-threaded.

## License

MIT. See [LICENSE](LICENSE).

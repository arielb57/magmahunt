//! Batch mode: the full implication matrix over a list of laws.

use crate::eval::CompiledLaw;
use crate::implication::{proof_table, Proof};
use crate::law::Law;
use crate::magma::Magma;
use crate::search::{check_size, Flow, Options, Search};
use crate::verify;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cell {
    /// The implication holds, by a syntactic proof.
    Implied(Proof),
    /// Refuted by the witness with this index.
    Refuted(usize),
    /// No counterexample up to the searched size, and no proof.
    Open,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct MatrixStats {
    pub nodes: u64,
    /// Model searches started (one per hypothesis and size with open cells).
    pub searches: u64,
    /// Searches skipped because the law has too many instances at that size.
    pub skipped_too_large: u64,
}

pub struct Matrix {
    pub laws: Vec<Law>,
    /// Row-major: `cells[h * m + c]` is "does law h imply law c".
    pub cells: Vec<Cell>,
    pub witnesses: Vec<Magma>,
    pub max_size: usize,
    pub stats: MatrixStats,
}

impl Matrix {
    /// Fills the matrix.
    ///
    /// Proven cells come from [`proof_table`]. Remaining cells are searched
    /// size by size across all rows, so every size-2 witness is found before
    /// any size-3 search starts. Each witness is evaluated against every law
    /// and refutes every open cell `(a, b)` with `a` satisfied and `b`
    /// violated, not just the pair it was found for.
    pub fn build(laws: Vec<Law>, max_size: usize, opts: Options) -> Matrix {
        let m = laws.len();
        let compiled: Vec<CompiledLaw> = laws.iter().map(CompiledLaw::new).collect();
        let mut cells: Vec<Cell> = proof_table(&laws)
            .into_iter()
            .map(|p| p.map_or(Cell::Open, Cell::Implied))
            .collect();
        let mut open_in_row: Vec<usize> = (0..m)
            .map(|h| {
                cells[h * m..(h + 1) * m]
                    .iter()
                    .filter(|c| **c == Cell::Open)
                    .count()
            })
            .collect();
        let mut witnesses = Vec::new();
        let mut stats = MatrixStats::default();

        for n in 1..=max_size {
            for h in 0..m {
                if open_in_row[h] == 0 {
                    continue;
                }
                if check_size(&compiled[h], n).is_err() {
                    stats.skipped_too_large += 1;
                    continue;
                }
                stats.searches += 1;
                let mut search = Search::new(&compiled[h], n, opts);
                search.run(&mut |table| {
                    let refutes_open = (0..m)
                        .any(|c| cells[h * m + c] == Cell::Open && !compiled[c].holds_in(n, table));
                    if refutes_open {
                        let id = witnesses.len();
                        witnesses.push(
                            Magma::new(n, table.to_vec()).expect("search tables are well formed"),
                        );
                        let sat: Vec<bool> =
                            compiled.iter().map(|law| law.holds_in(n, table)).collect();
                        for a in (0..m).filter(|&a| sat[a]) {
                            for b in (0..m).filter(|&b| !sat[b]) {
                                match cells[a * m + b] {
                                    Cell::Open => {
                                        cells[a * m + b] = Cell::Refuted(id);
                                        open_in_row[a] -= 1;
                                    }
                                    Cell::Implied(p) => panic!(
                                        "unsound proof {p:?}: {} does not imply {} in\n{}",
                                        laws[a], laws[b], witnesses[id]
                                    ),
                                    Cell::Refuted(_) => {}
                                }
                            }
                        }
                    }
                    if open_in_row[h] == 0 {
                        Flow::Stop
                    } else {
                        Flow::Continue
                    }
                });
                stats.nodes += search.stats.nodes;
            }
        }
        Matrix {
            laws,
            cells,
            witnesses,
            max_size,
            stats,
        }
    }

    pub fn cell(&self, hypothesis: usize, conclusion: usize) -> Cell {
        self.cells[hypothesis * self.laws.len() + conclusion]
    }

    pub fn count(&self, pred: impl Fn(&Cell) -> bool) -> usize {
        self.cells.iter().filter(|c| pred(c)).count()
    }

    /// Re-checks every refuted cell with the independent brute-force checker.
    pub fn verify(&self) -> Result<usize, String> {
        let m = self.laws.len();
        let mut checked = 0;
        for h in 0..m {
            for c in 0..m {
                if let Cell::Refuted(id) = self.cell(h, c) {
                    verify::verify_witness(&self.laws[h], &self.laws[c], &self.witnesses[id])
                        .map_err(|e| format!("cell ({}, {}) witness w{id}: {e}", h + 1, c + 1))?;
                    checked += 1;
                }
            }
        }
        Ok(checked)
    }

    /// CSV with one row per hypothesis and one column per conclusion.
    /// Cells are `implied`, `w<id>` (refuted by that witness) or `open`.
    pub fn to_csv(&self) -> String {
        let mut out = String::from("\"hypothesis \\ conclusion\"");
        for law in &self.laws {
            out.push_str(&format!(",\"{law}\""));
        }
        out.push('\n');
        for (h, law) in self.laws.iter().enumerate() {
            out.push_str(&format!("\"{law}\""));
            for c in 0..self.laws.len() {
                out.push(',');
                match self.cell(h, c) {
                    Cell::Implied(_) => out.push_str("implied"),
                    Cell::Refuted(id) => out.push_str(&format!("w{id}")),
                    Cell::Open => out.push_str("open"),
                }
            }
            out.push('\n');
        }
        out
    }

    /// Every witness table, with the laws (by 1-based index) it satisfies.
    pub fn witnesses_text(&self) -> String {
        let mut out = String::new();
        for (id, w) in self.witnesses.iter().enumerate() {
            let sat: Vec<String> = self
                .laws
                .iter()
                .enumerate()
                .filter(|(_, law)| verify::satisfies(w, law))
                .map(|(i, _)| (i + 1).to_string())
                .collect();
            out.push_str(&format!(
                "w{id}: size {}, satisfies laws {}\n{w}\n",
                w.size(),
                sat.join(" ")
            ));
        }
        out
    }
}

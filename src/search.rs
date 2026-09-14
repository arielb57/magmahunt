//! Backtracking model finder for a single hypothesis law.
//!
//! The table is filled one cell at a time. Every ground instance of the
//! hypothesis sits on the watch list of the first unknown cell its evaluation
//! needs; assigning a cell re-evaluates only that list, so an instance is
//! checked exactly when its evaluation may have become determined.

use crate::eval::{CompiledLaw, Status, UNKNOWN};

/// Searches refuse to materialise more ground instances than this.
pub const MAX_INSTANCES: u64 = 1 << 22;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Options {
    /// Only accept tables that are lexicographically least in their
    /// isomorphism class (one representative per class).
    pub symmetry: bool,
    /// Pick the unassigned cell with the most pending instances next;
    /// otherwise fill cells in row-major order.
    pub most_constrained: bool,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            symmetry: true,
            most_constrained: true,
        }
    }
}

impl Options {
    pub fn no_symmetry() -> Options {
        Options {
            symmetry: false,
            ..Options::default()
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Cell assignments tried.
    pub nodes: u64,
    /// Complete tables reached (models of the hypothesis).
    pub leaves: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Flow {
    Continue,
    Stop,
}

/// Checks that a search of `law` at size `n` stays within [`MAX_INSTANCES`].
pub fn check_size(law: &CompiledLaw, n: usize) -> Result<(), String> {
    if n == 0 || n > 16 {
        return Err(format!("size {n} is out of range (1..=16)"));
    }
    let count = law.instance_count(n);
    if count > MAX_INSTANCES {
        return Err(format!(
            "a law with {} variables has {count} ground instances at size {n}; the limit is {MAX_INSTANCES}",
            law.nvars
        ));
    }
    Ok(())
}

struct Perm {
    sigma: Vec<u8>,
    /// For each row-major position p, the position q with sigma(q) = p.
    source: Vec<usize>,
}

fn permutations(n: usize) -> Vec<Vec<u8>> {
    fn go(prefix: &mut Vec<u8>, used: &mut [bool], out: &mut Vec<Vec<u8>>) {
        if prefix.len() == used.len() {
            out.push(prefix.clone());
            return;
        }
        for v in 0..used.len() {
            if !used[v] {
                used[v] = true;
                prefix.push(v as u8);
                go(prefix, used, out);
                prefix.pop();
                used[v] = false;
            }
        }
    }
    let mut out = Vec::new();
    go(&mut Vec::new(), &mut vec![false; n], &mut out);
    out
}

pub struct Search<'a> {
    n: usize,
    law: &'a CompiledLaw,
    opts: Options,
    table: Vec<u8>,
    filled: usize,
    assigns: Vec<u8>,
    watch: Vec<Vec<u32>>,
    trail: Vec<u32>,
    stack: Vec<u8>,
    perms: Vec<Perm>,
    infeasible: bool,
    pub stats: Stats,
}

impl<'a> Search<'a> {
    /// Prepares a search for models of `law` of size `n`.
    ///
    /// Panics if [`check_size`] would reject the parameters.
    pub fn new(law: &'a CompiledLaw, n: usize, opts: Options) -> Search<'a> {
        if let Err(e) = check_size(law, n) {
            panic!("{e}");
        }
        let k = law.nvars;
        let count = law.instance_count(n) as usize;
        let mut assigns = vec![0u8; count * k];
        for inst in 0..count {
            let mut rest = inst;
            for slot in &mut assigns[inst * k..(inst + 1) * k] {
                *slot = (rest % n) as u8;
                rest /= n;
            }
        }
        let table = vec![UNKNOWN; n * n];
        let mut watch = vec![Vec::new(); n * n];
        let mut stack = Vec::with_capacity(16);
        let mut infeasible = false;
        for inst in 0..count {
            match law.status(n, &table, &assigns[inst * k..(inst + 1) * k], &mut stack) {
                Status::Holds => {}
                Status::Fails => infeasible = true,
                Status::Blocked(cell) => watch[cell].push(inst as u32),
            }
        }
        let perms = if opts.symmetry {
            permutations(n)
                .into_iter()
                .filter(|p| p.iter().enumerate().any(|(i, &v)| i as u8 != v))
                .map(|sigma| {
                    let mut inv = vec![0usize; n];
                    for (i, &s) in sigma.iter().enumerate() {
                        inv[s as usize] = i;
                    }
                    let source = (0..n * n).map(|p| inv[p / n] * n + inv[p % n]).collect();
                    Perm { sigma, source }
                })
                .collect()
        } else {
            Vec::new()
        };
        Search {
            n,
            law,
            opts,
            table,
            filled: 0,
            assigns,
            watch,
            trail: Vec::new(),
            stack,
            perms,
            infeasible,
            stats: Stats::default(),
        }
    }

    /// Enumerates models, calling `visit` with each complete row-major table.
    /// Returns [`Flow::Stop`] if `visit` asked to stop.
    pub fn run(&mut self, visit: &mut dyn FnMut(&[u8]) -> Flow) -> Flow {
        if self.infeasible {
            return Flow::Continue;
        }
        self.dfs(visit)
    }

    fn dfs(&mut self, visit: &mut dyn FnMut(&[u8]) -> Flow) -> Flow {
        if self.filled == self.table.len() {
            self.stats.leaves += 1;
            return visit(&self.table);
        }
        let cell = self.pick_cell();
        for v in 0..self.n as u8 {
            self.stats.nodes += 1;
            self.table[cell] = v;
            self.filled += 1;
            let mark = self.trail.len();
            let ok = self.propagate(cell) && self.lex_leader_so_far();
            let flow = if ok { self.dfs(visit) } else { Flow::Continue };
            // Instances moved during this assignment were appended to other
            // watch lists after every deeper level was undone, so they sit at
            // the ends of those lists and pop off in reverse order.
            while self.trail.len() > mark {
                let c = self.trail.pop().expect("trail length checked") as usize;
                self.watch[c].pop();
            }
            self.table[cell] = UNKNOWN;
            self.filled -= 1;
            if flow == Flow::Stop {
                return Flow::Stop;
            }
        }
        Flow::Continue
    }

    fn pick_cell(&self) -> usize {
        let mut best = usize::MAX;
        let mut best_score = 0;
        for c in 0..self.table.len() {
            if self.table[c] != UNKNOWN {
                continue;
            }
            if !self.opts.most_constrained {
                return c;
            }
            let score = self.watch[c].len();
            if best == usize::MAX || score > best_score {
                best = c;
                best_score = score;
            }
        }
        best
    }

    /// Re-checks instances waiting on `cell`. The watch list of an assigned
    /// cell is left in place (stale) so backtracking only has to undo pushes.
    fn propagate(&mut self, cell: usize) -> bool {
        let k = self.law.nvars;
        let list = std::mem::take(&mut self.watch[cell]);
        let mut ok = true;
        for &inst in &list {
            let i = inst as usize;
            let assign = &self.assigns[i * k..(i + 1) * k];
            match self
                .law
                .status(self.n, &self.table, assign, &mut self.stack)
            {
                Status::Holds => {}
                Status::Fails => {
                    ok = false;
                    break;
                }
                Status::Blocked(next) => {
                    self.watch[next].push(inst);
                    self.trail.push(next as u32);
                }
            }
        }
        self.watch[cell] = list;
        ok
    }

    /// Partial lex-leader test: fails only if some relabelling provably gives
    /// a row-major-smaller table for every completion of the current one.
    fn lex_leader_so_far(&self) -> bool {
        for perm in &self.perms {
            for p in 0..self.table.len() {
                let t = self.table[p];
                let s = self.table[perm.source[p]];
                if t == UNKNOWN || s == UNKNOWN {
                    break;
                }
                let s = perm.sigma[s as usize];
                if t < s {
                    break;
                }
                if t > s {
                    return false;
                }
            }
        }
        true
    }
}

/// Counts models of `law` of size `n`. With symmetry breaking on this is the
/// number of isomorphism classes; with it off, the number of labelled tables.
pub fn count_models(law: &CompiledLaw, n: usize, opts: Options) -> Stats {
    let mut search = Search::new(law, n, opts);
    search.run(&mut |_| Flow::Continue);
    search.stats
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::law::parse_law;

    fn compiled(s: &str) -> CompiledLaw {
        CompiledLaw::new(&parse_law(s).unwrap())
    }

    #[test]
    fn every_labelled_magma_is_visited_once_without_symmetry() {
        let law = compiled("x = x");
        let mut seen = std::collections::HashSet::new();
        let mut search = Search::new(&law, 2, Options::no_symmetry());
        search.run(&mut |t| {
            assert!(seen.insert(t.to_vec()), "duplicate table {t:?}");
            Flow::Continue
        });
        assert_eq!(seen.len(), 16);
    }

    #[test]
    fn row_major_and_most_constrained_orders_agree() {
        let law = compiled("x ◇ (y ◇ x) = y");
        for symmetry in [false, true] {
            let a = count_models(
                &law,
                3,
                Options {
                    symmetry,
                    most_constrained: true,
                },
            );
            let b = count_models(
                &law,
                3,
                Options {
                    symmetry,
                    most_constrained: false,
                },
            );
            assert_eq!(a.leaves, b.leaves);
        }
    }

    #[test]
    fn stop_ends_the_search_immediately() {
        let law = compiled("x = x");
        let mut calls = 0;
        let mut search = Search::new(&law, 3, Options::default());
        let flow = search.run(&mut |_| {
            calls += 1;
            if calls == 5 {
                Flow::Stop
            } else {
                Flow::Continue
            }
        });
        assert_eq!(flow, Flow::Stop);
        assert_eq!(calls, 5);
    }

    #[test]
    fn contradictory_laws_have_no_models_beyond_size_one() {
        let law = compiled("x = y");
        assert_eq!(count_models(&law, 1, Options::default()).leaves, 1);
        let stats = count_models(&law, 3, Options::default());
        assert_eq!((stats.leaves, stats.nodes), (0, 0));
    }

    #[test]
    fn rejects_oversized_problems() {
        let law = compiled("a◇b◇c◇d◇e◇f◇g = h");
        assert!(check_size(&law, 7).is_err());
        assert!(check_size(&law, 3).is_ok());
        assert!(check_size(&law, 0).is_err());
    }
}

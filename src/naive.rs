//! Naive enumeration of all `n^(n²)` tables, the baseline the search is
//! measured and property-tested against.

use crate::eval::CompiledLaw;
use crate::law::Law;
use crate::magma::Magma;

/// Visits complete tables in odometer order, at most `limit` of them.
/// Returns the number of tables visited.
pub fn for_each_table(n: usize, limit: u64, visit: &mut dyn FnMut(&[u8]) -> bool) -> u64 {
    let mut table = vec![0u8; n * n];
    let mut visited = 0;
    while visited < limit {
        visited += 1;
        if !visit(&table) {
            return visited;
        }
        let mut i = 0;
        loop {
            if i == table.len() {
                return visited;
            }
            table[i] += 1;
            if (table[i] as usize) < n {
                break;
            }
            table[i] = 0;
            i += 1;
        }
    }
    visited
}

/// Total number of tables of size `n`, saturating at `u64::MAX`.
pub fn table_count(n: usize) -> u64 {
    (n as u64).checked_pow((n * n) as u32).unwrap_or(u64::MAX)
}

/// Counts labelled models of `law` of size `n` by checking every table.
pub fn count_models(law: &Law, n: usize) -> u64 {
    let law = CompiledLaw::new(law);
    let mut count = 0;
    for_each_table(n, u64::MAX, &mut |t| {
        count += law.holds_in(n, t) as u64;
        true
    });
    count
}

/// First table of size `n` (odometer order) that satisfies `hypothesis` and
/// violates `conclusion`, together with the number of tables examined.
pub fn find_counterexample(hypothesis: &Law, conclusion: &Law, n: usize) -> (Option<Magma>, u64) {
    let h = CompiledLaw::new(hypothesis);
    let c = CompiledLaw::new(conclusion);
    let mut found = None;
    let visited = for_each_table(n, u64::MAX, &mut |t| {
        if h.holds_in(n, t) && !c.holds_in(n, t) {
            found = Some(Magma::new(n, t.to_vec()).expect("enumerated tables are well formed"));
            return false;
        }
        true
    });
    (found, visited)
}

/// Naive refutation over sizes `1..=max_size`.
pub fn refute(hypothesis: &Law, conclusion: &Law, max_size: usize) -> (Option<Magma>, u64) {
    let mut total = 0;
    for n in 1..=max_size {
        let (found, visited) = find_counterexample(hypothesis, conclusion, n);
        total += visited;
        if found.is_some() {
            return (found, total);
        }
    }
    (None, total)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::law::parse_law;

    #[test]
    fn enumerates_every_table_exactly_once() {
        let mut seen = std::collections::HashSet::new();
        let visited = for_each_table(2, u64::MAX, &mut |t| {
            assert!(seen.insert(t.to_vec()));
            true
        });
        assert_eq!((visited, seen.len() as u64), (16, 16));
        assert_eq!(table_count(3), 19683);
        assert_eq!(table_count(10), u64::MAX);
    }

    #[test]
    fn respects_the_limit_and_early_exit() {
        assert_eq!(for_each_table(3, 100, &mut |_| true), 100);
        let mut calls = 0;
        assert_eq!(
            for_each_table(3, u64::MAX, &mut |_| {
                calls += 1;
                calls < 7
            }),
            7
        );
    }

    #[test]
    fn naive_counts_small_cases() {
        assert_eq!(count_models(&parse_law("x ◇ y = y ◇ x").unwrap(), 2), 8);
        assert_eq!(
            count_models(&parse_law("x ◇ (y ◇ z) = (x ◇ y) ◇ z").unwrap(), 2),
            8
        );
        assert_eq!(
            count_models(&parse_law("x = x ◇ x").unwrap(), 3),
            3u64.pow(6)
        );
    }
}

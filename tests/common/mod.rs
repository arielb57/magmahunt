use std::collections::HashSet;

/// Generates every permutation of `0..n`.
pub fn permutations(n: usize) -> Vec<Vec<usize>> {
    if n == 0 {
        return vec![Vec::new()];
    }
    let mut out = Vec::new();
    for p in permutations(n - 1) {
        for pos in 0..=p.len() {
            let mut q = p.clone();
            q.insert(pos, n - 1);
            out.push(q);
        }
    }
    out
}

/// Lexicographically least relabelling of a table, computed by brute force.
pub fn canonical(n: usize, table: &[u8]) -> Vec<u8> {
    permutations(n)
        .into_iter()
        .map(|s| {
            let mut out = vec![0u8; n * n];
            for a in 0..n {
                for b in 0..n {
                    out[s[a] * n + s[b]] = s[table[a * n + b] as usize] as u8;
                }
            }
            out
        })
        .min()
        .expect("at least one permutation")
}

/// Number of isomorphism classes among a set of labelled tables.
pub fn iso_classes<'a>(n: usize, tables: impl IntoIterator<Item = &'a Vec<u8>>) -> usize {
    tables
        .into_iter()
        .map(|t| canonical(n, t))
        .collect::<HashSet<_>>()
        .len()
}

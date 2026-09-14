//! Finite magmas given by a complete operation table.

use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Magma {
    n: usize,
    table: Vec<u8>,
}

impl Magma {
    /// `table` is row-major: `table[a * n + b]` is `a ◇ b`.
    pub fn new(n: usize, table: Vec<u8>) -> Result<Magma, String> {
        if n == 0 {
            return Err("a magma needs at least one element".into());
        }
        if table.len() != n * n {
            return Err(format!(
                "expected {} table entries for size {n}, got {}",
                n * n,
                table.len()
            ));
        }
        if let Some(bad) = table.iter().find(|&&v| v as usize >= n) {
            return Err(format!(
                "table entry {bad} is not an element of a size-{n} magma"
            ));
        }
        Ok(Magma { n, table })
    }

    pub fn size(&self) -> usize {
        self.n
    }

    pub fn table(&self) -> &[u8] {
        &self.table
    }

    pub fn op(&self, a: usize, b: usize) -> usize {
        self.table[a * self.n + b] as usize
    }

    /// Rows separated by `|`, e.g. `0 1|1 0`.
    pub fn compact(&self) -> String {
        self.table
            .chunks(self.n)
            .map(|row| {
                row.iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            })
            .collect::<Vec<_>>()
            .join("|")
    }
}

impl fmt::Display for Magma {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let w = (self.n - 1).to_string().len();
        write!(f, "{:>w$} |", "◇")?;
        for b in 0..self.n {
            write!(f, " {b:>w$}")?;
        }
        writeln!(f)?;
        writeln!(f, "{}-+{}", "-".repeat(w), "-".repeat((w + 1) * self.n))?;
        for a in 0..self.n {
            write!(f, "{a:>w$} |")?;
            for b in 0..self.n {
                write!(f, " {:>w$}", self.op(a, b))?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_shape_and_entries() {
        assert!(Magma::new(2, vec![0, 1, 1, 0]).is_ok());
        assert!(Magma::new(2, vec![0, 1, 1]).is_err());
        assert!(Magma::new(2, vec![0, 1, 2, 0]).is_err());
        assert!(Magma::new(0, vec![]).is_err());
    }

    #[test]
    fn renders_table_and_compact_form() {
        let m = Magma::new(2, vec![1, 0, 0, 0]).unwrap();
        assert_eq!(m.to_string(), "◇ | 0 1\n--+----\n0 | 1 0\n1 | 0 0\n");
        assert_eq!(m.compact(), "1 0|0 0");
        assert_eq!(m.op(0, 0), 1);
    }
}

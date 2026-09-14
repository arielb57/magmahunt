//! Compiled term evaluation over full and partial operation tables.

use crate::law::{Law, Term};

/// Marks a table cell that has not been assigned yet.
pub const UNKNOWN: u8 = u8::MAX;

#[derive(Clone, Copy, Debug)]
enum Code {
    Var(u8),
    Op,
}

/// A term flattened to postfix code for a stack machine.
#[derive(Clone, Debug)]
pub struct Program {
    code: Vec<Code>,
}

impl Program {
    pub fn compile(term: &Term) -> Program {
        fn emit(t: &Term, code: &mut Vec<Code>) {
            match t {
                Term::Var(v) => code.push(Code::Var(*v)),
                Term::Op(l, r) => {
                    emit(l, code);
                    emit(r, code);
                    code.push(Code::Op);
                }
            }
        }
        let mut code = Vec::new();
        emit(term, &mut code);
        Program { code }
    }

    /// Evaluates under `assign` on a table that may contain [`UNKNOWN`] cells.
    ///
    /// Returns the value, or `Err(cell)` for the first unknown cell the
    /// evaluation needs. Both operands of an `Op` are always known when it
    /// runs, so an unknown short-circuits the whole term immediately.
    #[inline]
    pub fn eval_partial(
        &self,
        n: usize,
        table: &[u8],
        assign: &[u8],
        stack: &mut Vec<u8>,
    ) -> Result<u8, usize> {
        stack.clear();
        for c in &self.code {
            match *c {
                Code::Var(v) => stack.push(assign[v as usize]),
                Code::Op => {
                    let r = stack.pop().expect("postfix code is well formed");
                    let l = stack.pop().expect("postfix code is well formed");
                    let cell = l as usize * n + r as usize;
                    let val = table[cell];
                    if val == UNKNOWN {
                        return Err(cell);
                    }
                    stack.push(val);
                }
            }
        }
        Ok(stack[0])
    }
}

/// Outcome of checking one ground instance of a law on a partial table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Holds,
    Fails,
    /// Undetermined; the payload is the first unknown cell it depends on.
    Blocked(usize),
}

/// A law compiled for fast repeated evaluation.
#[derive(Clone, Debug)]
pub struct CompiledLaw {
    pub lhs: Program,
    pub rhs: Program,
    pub nvars: usize,
}

impl CompiledLaw {
    pub fn new(law: &Law) -> CompiledLaw {
        CompiledLaw {
            lhs: Program::compile(&law.lhs),
            rhs: Program::compile(&law.rhs),
            nvars: law.nvars,
        }
    }

    /// Number of ground instances over an `n`-element carrier.
    pub fn instance_count(&self, n: usize) -> u64 {
        (n as u64).saturating_pow(self.nvars as u32)
    }

    #[inline]
    pub fn status(&self, n: usize, table: &[u8], assign: &[u8], stack: &mut Vec<u8>) -> Status {
        let l = match self.lhs.eval_partial(n, table, assign, stack) {
            Ok(v) => v,
            Err(cell) => return Status::Blocked(cell),
        };
        match self.rhs.eval_partial(n, table, assign, stack) {
            Ok(r) if r == l => Status::Holds,
            Ok(_) => Status::Fails,
            Err(cell) => Status::Blocked(cell),
        }
    }

    /// Whether the law holds for every assignment on a complete table.
    pub fn holds_in(&self, n: usize, table: &[u8]) -> bool {
        let mut assign = vec![0u8; self.nvars];
        let mut stack = Vec::with_capacity(16);
        loop {
            if self.status(n, table, &assign, &mut stack) != Status::Holds {
                return false;
            }
            let mut i = 0;
            loop {
                if i == assign.len() {
                    return true;
                }
                assign[i] += 1;
                if (assign[i] as usize) < n {
                    break;
                }
                assign[i] = 0;
                i += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::law::parse_law;

    #[test]
    fn partial_evaluation_reports_the_first_missing_cell() {
        let law = CompiledLaw::new(&parse_law("(x ◇ y) ◇ z = x ◇ (y ◇ z)").unwrap());
        let n = 2;
        let mut table = vec![UNKNOWN; 4];
        let mut stack = Vec::new();
        // x=1, y=0, z=1: lhs needs cell (1,0) first.
        let assign = [1, 0, 1];
        assert_eq!(
            law.status(n, &table, &assign, &mut stack),
            Status::Blocked(2)
        );
        table[2] = 0; // 1◇0 = 0, lhs now needs (0,1)
        assert_eq!(
            law.status(n, &table, &assign, &mut stack),
            Status::Blocked(1)
        );
        table[1] = 1; // lhs = 1; rhs needs (0,1) = 1 then (1,1)
        assert_eq!(
            law.status(n, &table, &assign, &mut stack),
            Status::Blocked(3)
        );
        table[3] = 0;
        assert_eq!(law.status(n, &table, &assign, &mut stack), Status::Fails);
        table[3] = 1;
        assert_eq!(law.status(n, &table, &assign, &mut stack), Status::Holds);
    }

    #[test]
    fn variable_only_laws_need_no_cells() {
        let law = CompiledLaw::new(&parse_law("x = y").unwrap());
        let table = [UNKNOWN; 9];
        let mut stack = Vec::new();
        assert_eq!(law.status(3, &table, &[2, 2], &mut stack), Status::Holds);
        assert_eq!(law.status(3, &table, &[2, 1], &mut stack), Status::Fails);
    }

    #[test]
    fn holds_in_checks_every_assignment() {
        let comm = CompiledLaw::new(&parse_law("x◇y = y◇x").unwrap());
        // Only cell (2,1) differs from (1,2): a failure at the last assignments.
        let mut table = vec![0, 1, 2, 1, 1, 2, 2, 2, 2];
        assert!(comm.holds_in(3, &table));
        table[7] = 0;
        assert!(!comm.holds_in(3, &table));
        assert_eq!(comm.instance_count(3), 9);
    }
}

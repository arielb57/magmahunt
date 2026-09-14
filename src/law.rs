//! Terms, laws, the ETP-notation parser and an ETP-style law generator.

use std::collections::HashSet;
use std::fmt;

/// Laws with more distinct variables than this are rejected by the parser:
/// the solver materialises all `n^vars` ground instances.
pub const MAX_VARS: usize = 8;

const DEFAULT_NAMES: [&str; MAX_VARS] = ["x", "y", "z", "w", "u", "v", "r", "s"];

/// A term over variables (numbered from 0) and a single binary operation.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Term {
    Var(u8),
    Op(Box<Term>, Box<Term>),
}

impl Term {
    pub fn op(l: Term, r: Term) -> Term {
        Term::Op(Box::new(l), Box::new(r))
    }

    /// Number of operation nodes.
    pub fn ops(&self) -> usize {
        match self {
            Term::Var(_) => 0,
            Term::Op(l, r) => 1 + l.ops() + r.ops(),
        }
    }

    pub fn contains_var(&self, v: u8) -> bool {
        match self {
            Term::Var(x) => *x == v,
            Term::Op(l, r) => l.contains_var(v) || r.contains_var(v),
        }
    }

    fn first_occurrences(&self, out: &mut Vec<u8>) {
        match self {
            Term::Var(v) => {
                if !out.contains(v) {
                    out.push(*v);
                }
            }
            Term::Op(l, r) => {
                l.first_occurrences(out);
                r.first_occurrences(out);
            }
        }
    }

    fn rename(&self, map: &[u8]) -> Term {
        match self {
            Term::Var(v) => Term::Var(map[*v as usize]),
            Term::Op(l, r) => Term::op(l.rename(map), r.rename(map)),
        }
    }

    fn max_var(&self) -> Option<u8> {
        match self {
            Term::Var(v) => Some(*v),
            Term::Op(l, r) => l.max_var().max(r.max_var()),
        }
    }

    fn write(&self, f: &mut fmt::Formatter<'_>, names: &[String], top: bool) -> fmt::Result {
        match self {
            Term::Var(v) => f.write_str(&names[*v as usize]),
            Term::Op(l, r) => {
                if !top {
                    f.write_str("(")?;
                }
                l.write(f, names, false)?;
                f.write_str(" ◇ ")?;
                r.write(f, names, false)?;
                if !top {
                    f.write_str(")")?;
                }
                Ok(())
            }
        }
    }
}

/// An equational law `lhs = rhs`, universally quantified over its variables.
///
/// Variables are numbered `0..nvars` in order of first occurrence (left side
/// first), so two laws that differ only by variable names compare equal.
#[derive(Clone, Debug)]
pub struct Law {
    pub lhs: Term,
    pub rhs: Term,
    pub nvars: usize,
    names: Vec<String>,
}

impl PartialEq for Law {
    fn eq(&self, other: &Law) -> bool {
        self.lhs == other.lhs && self.rhs == other.rhs
    }
}

impl Eq for Law {}

impl Law {
    /// Builds a law from two terms, renumbering variables by first occurrence.
    pub fn new(lhs: Term, rhs: Term) -> Law {
        let mut order = Vec::new();
        lhs.first_occurrences(&mut order);
        rhs.first_occurrences(&mut order);
        let size = lhs
            .max_var()
            .max(rhs.max_var())
            .map_or(0, |m| m as usize + 1);
        let mut map = vec![0u8; size];
        for (new, old) in order.iter().enumerate() {
            map[*old as usize] = new as u8;
        }
        let names = (0..order.len())
            .map(|i| {
                DEFAULT_NAMES
                    .get(i)
                    .map_or_else(|| format!("v{i}"), |s| s.to_string())
            })
            .collect();
        Law {
            lhs: lhs.rename(&map),
            rhs: rhs.rename(&map),
            nvars: order.len(),
            names,
        }
    }

    /// The same law with its two sides exchanged (and variables renumbered).
    pub fn swapped(&self) -> Law {
        Law::new(self.rhs.clone(), self.lhs.clone())
    }

    /// Total number of operations on both sides.
    pub fn ops(&self) -> usize {
        self.lhs.ops() + self.rhs.ops()
    }

    /// True when both sides are syntactically identical, so every magma satisfies it.
    pub fn is_trivial(&self) -> bool {
        self.lhs == self.rhs
    }

    /// Variable names used when printing, in variable-number order.
    pub fn names(&self) -> &[String] {
        &self.names
    }
}

impl fmt::Display for Law {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.lhs.write(f, &self.names, true)?;
        f.write_str(" = ")?;
        self.rhs.write(f, &self.names, true)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    /// Byte offset into the input where the problem was detected.
    pub offset: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (at byte {})", self.message, self.offset)
    }
}

impl std::error::Error for ParseError {}

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    LParen,
    RParen,
    Op,
    Eq,
}

fn tokenize(s: &str) -> Result<Vec<(Tok, usize)>, ParseError> {
    let mut toks = Vec::new();
    let mut chars = s.char_indices().peekable();
    while let Some(&(i, c)) = chars.peek() {
        match c {
            c if c.is_whitespace() => {
                chars.next();
            }
            '(' => {
                toks.push((Tok::LParen, i));
                chars.next();
            }
            ')' => {
                toks.push((Tok::RParen, i));
                chars.next();
            }
            '=' => {
                toks.push((Tok::Eq, i));
                chars.next();
            }
            '◇' | '*' | '∘' | '·' => {
                toks.push((Tok::Op, i));
                chars.next();
            }
            c if c.is_alphabetic() || c == '_' => {
                let mut name = String::new();
                while let Some(&(_, c)) = chars.peek() {
                    if c.is_alphanumeric() || c == '_' || c == '\'' {
                        name.push(c);
                        chars.next();
                    } else {
                        break;
                    }
                }
                toks.push((Tok::Ident(name), i));
            }
            other => {
                return Err(ParseError {
                    message: format!("unexpected character '{other}'"),
                    offset: i,
                });
            }
        }
    }
    Ok(toks)
}

struct Parser {
    toks: Vec<(Tok, usize)>,
    pos: usize,
    end: usize,
    names: Vec<String>,
}

impl Parser {
    fn offset(&self) -> usize {
        self.toks.get(self.pos).map_or(self.end, |t| t.1)
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|t| &t.0)
    }

    fn err<T>(&self, message: impl Into<String>) -> Result<T, ParseError> {
        Err(ParseError {
            message: message.into(),
            offset: self.offset(),
        })
    }

    // term := factor (OP factor)*, left associative like ETP's `infixl ◇`.
    fn term(&mut self) -> Result<Term, ParseError> {
        let mut acc = self.factor()?;
        while self.peek() == Some(&Tok::Op) {
            self.pos += 1;
            let rhs = self.factor()?;
            acc = Term::op(acc, rhs);
        }
        Ok(acc)
    }

    fn factor(&mut self) -> Result<Term, ParseError> {
        match self.peek().cloned() {
            Some(Tok::Ident(name)) => {
                self.pos += 1;
                let idx = match self.names.iter().position(|n| *n == name) {
                    Some(i) => i,
                    None => {
                        if self.names.len() == MAX_VARS {
                            return Err(ParseError {
                                message: format!("more than {MAX_VARS} distinct variables"),
                                offset: self.toks[self.pos - 1].1,
                            });
                        }
                        self.names.push(name);
                        self.names.len() - 1
                    }
                };
                Ok(Term::Var(idx as u8))
            }
            Some(Tok::LParen) => {
                self.pos += 1;
                let t = self.term()?;
                if self.peek() != Some(&Tok::RParen) {
                    return self.err("expected ')'");
                }
                self.pos += 1;
                Ok(t)
            }
            Some(Tok::RParen) => self.err("unexpected ')'"),
            Some(Tok::Op) => self.err("operator is missing its left operand"),
            Some(Tok::Eq) => self.err("'=' is missing a term on its left"),
            None => self.err("unexpected end of input, expected a term"),
        }
    }
}

/// Parses a law in ETP notation, e.g. `x ◇ (y ◇ z) = (x ◇ y) ◇ z`.
///
/// `◇`, `*`, `∘` and `·` are all accepted as the operation symbol. Chains
/// without parentheses associate to the left, matching ETP's Lean notation.
pub fn parse_law(input: &str) -> Result<Law, ParseError> {
    let toks = tokenize(input)?;
    let mut p = Parser {
        toks,
        pos: 0,
        end: input.len(),
        names: Vec::new(),
    };
    let lhs = p.term()?;
    if p.peek() != Some(&Tok::Eq) {
        return p.err("expected '='");
    }
    p.pos += 1;
    let rhs = p.term()?;
    if p.pos != p.toks.len() {
        return p.err("unexpected trailing input");
    }
    // Parser numbering is already by first occurrence, so names line up with
    // the renumbered variables in `Law::new`.
    let mut law = Law::new(lhs, rhs);
    law.names = p.names;
    Ok(law)
}

/// Parses a law list: one law per line, blank lines and `#` comments ignored.
pub fn parse_law_list(text: &str) -> Result<Vec<Law>, String> {
    let mut laws = Vec::new();
    for (lineno, line) in text.lines().enumerate() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let law = parse_law(line).map_err(|e| format!("line {}: {e}", lineno + 1))?;
        laws.push(law);
    }
    Ok(laws)
}

fn shapes(ops: usize) -> Vec<Term> {
    if ops == 0 {
        return vec![Term::Var(0)];
    }
    let mut out = Vec::new();
    for left in 0..ops {
        for l in shapes(left) {
            for r in shapes(ops - 1 - left) {
                out.push(Term::op(l.clone(), r));
            }
        }
    }
    out
}

fn fill(shape: &Term, pattern: &[u8], next: &mut usize) -> Term {
    match shape {
        Term::Var(_) => {
            let t = Term::Var(pattern[*next]);
            *next += 1;
            t
        }
        Term::Op(l, r) => {
            let l = fill(l, pattern, next);
            let r = fill(r, pattern, next);
            Term::op(l, r)
        }
    }
}

// Restricted growth strings: variable patterns up to renaming.
fn patterns(len: usize, prefix: &mut Vec<u8>, max: u8, out: &mut Vec<Vec<u8>>) {
    if prefix.len() == len {
        out.push(prefix.clone());
        return;
    }
    let limit = if prefix.is_empty() {
        0
    } else {
        (max + 1).min(MAX_VARS as u8 - 1)
    };
    for v in 0..=limit {
        prefix.push(v);
        patterns(len, prefix, max.max(v), out);
        prefix.pop();
    }
}

/// Enumerates laws with at most `max_ops` operations in the order the
/// Equational Theories Project uses to build its list: by total operation
/// count, then by operations on the left side, then by tree shape, then by
/// variable pattern. Laws equal up to renaming or swapping sides appear once,
/// and trivial laws other than `x = x` are dropped.
///
/// The ordering follows ETP's construction but the numbering is not
/// guaranteed to match the published equation list beyond the first blocks.
pub fn generate_laws(max_ops: usize) -> Vec<Law> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for total in 0..=max_ops {
        for left_ops in 0..=total / 2 {
            let rshapes = shapes(total - left_ops);
            for ls in shapes(left_ops) {
                for rs in &rshapes {
                    let mut pats = Vec::new();
                    patterns(total + 2, &mut Vec::new(), 0, &mut pats);
                    for pat in pats {
                        let mut next = 0;
                        let lhs = fill(&ls, &pat, &mut next);
                        let rhs = fill(rs, &pat, &mut next);
                        let law = Law::new(lhs, rhs);
                        if law.is_trivial() && total > 0 {
                            continue;
                        }
                        let swapped = law.swapped();
                        let key = std::cmp::min(
                            (law.lhs.clone(), law.rhs.clone()),
                            (swapped.lhs.clone(), swapped.rhs.clone()),
                        );
                        if seen.insert(key) {
                            out.push(law);
                        }
                    }
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(i: u8) -> Term {
        Term::Var(i)
    }

    #[test]
    fn parses_associativity_with_nested_parentheses() {
        let law = parse_law("x ◇ (y ◇ z) = (x ◇ y) ◇ z").unwrap();
        assert_eq!(law.lhs, Term::op(v(0), Term::op(v(1), v(2))));
        assert_eq!(law.rhs, Term::op(Term::op(v(0), v(1)), v(2)));
        assert_eq!(law.nvars, 3);
    }

    #[test]
    fn redundant_parentheses_do_not_change_the_tree() {
        let a = parse_law("((x)) ◇ (((y ◇ z))) = ((x ◇ y))").unwrap();
        let b = parse_law("x ◇ (y ◇ z) = x ◇ y").unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn unparenthesised_chains_associate_left() {
        let a = parse_law("x * y * z = x").unwrap();
        let b = parse_law("(x ◇ y) ◇ z = x").unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn repeated_variables_share_an_index() {
        let law = parse_law("x ◇ x = (x ◇ y) ◇ x").unwrap();
        assert_eq!(law.nvars, 2);
        assert_eq!(law.lhs, Term::op(v(0), v(0)));
        assert_eq!(law.rhs, Term::op(Term::op(v(0), v(1)), v(0)));
    }

    #[test]
    fn bare_variable_on_either_side() {
        let left = parse_law("x = y ◇ (x ◇ z)").unwrap();
        assert_eq!(left.lhs, v(0));
        assert_eq!(left.rhs.ops(), 2);
        let right = parse_law("y ◇ y = y").unwrap();
        assert_eq!(right.rhs, v(0));
        let both = parse_law("x = y").unwrap();
        assert_eq!((both.lhs, both.rhs, both.nvars), (v(0), v(1), 2));
    }

    #[test]
    fn variable_names_are_irrelevant_but_preserved_for_display() {
        let a = parse_law("a*b = b*a").unwrap();
        let b = parse_law("x ◇ y = y ◇ x").unwrap();
        assert_eq!(a, b);
        assert_eq!(a.to_string(), "a ◇ b = b ◇ a");
    }

    #[test]
    fn display_round_trips() {
        for src in [
            "x ◇ (y ◇ z) = (x ◇ y) ◇ z",
            "x = x ◇ x",
            "x = y",
            "((x ◇ y) ◇ z) ◇ w = x ◇ w",
        ] {
            let law = parse_law(src).unwrap();
            assert_eq!(law.to_string(), src);
            assert_eq!(parse_law(&law.to_string()).unwrap(), law);
        }
    }

    #[test]
    fn rejects_malformed_input_with_positions() {
        let cases = [
            ("x ◇ y", "expected '='"),
            ("x ◇ (y = x", "expected ')'"),
            ("= x", "missing a term on its left"),
            ("x = ", "unexpected end of input"),
            ("x = y = z", "trailing input"),
            ("x ◇ ◇ y = x", "missing its left operand"),
            ("x + y = y", "unexpected character '+'"),
            ("x = y)", "trailing input"),
            ("", "unexpected end of input"),
        ];
        for (src, needle) in cases {
            let err = parse_law(src).unwrap_err();
            assert!(err.message.contains(needle), "{src:?}: got {err}");
            assert!(err.offset <= src.len());
        }
        assert_eq!(parse_law("x + y = y").unwrap_err().offset, 2);
    }

    #[test]
    fn rejects_too_many_variables() {
        let err = parse_law("a◇b◇c◇d◇e◇f◇g◇h = i").unwrap_err();
        assert!(err.message.contains("distinct variables"));
        assert!(parse_law("a◇b◇c◇d◇e◇f◇g = h").is_ok());
    }

    #[test]
    fn law_list_skips_comments_and_reports_line_numbers() {
        let laws = parse_law_list("# header\nx = x\n\n  x◇y = y◇x  # commutativity\n").unwrap();
        assert_eq!(laws.len(), 2);
        let err = parse_law_list("x = x\nx ◇ = y\n").unwrap_err();
        assert!(err.starts_with("line 2:"), "{err}");
    }

    #[test]
    fn generator_starts_like_the_etp_list() {
        let laws = generate_laws(2);
        let text: Vec<String> = laws.iter().take(9).map(|l| l.to_string()).collect();
        assert_eq!(
            text,
            [
                "x = x",
                "x = y",
                "x = x ◇ x",
                "x = x ◇ y",
                "x = y ◇ x",
                "x = y ◇ y",
                "x = y ◇ z",
                "x = x ◇ (x ◇ x)",
                "x = x ◇ (x ◇ y)",
            ]
        );
        assert!(laws.contains(&parse_law("x ◇ y = y ◇ x").unwrap()));
    }

    #[test]
    fn generator_has_no_duplicates_up_to_renaming_and_swap() {
        let laws = generate_laws(3);
        for (i, a) in laws.iter().enumerate() {
            assert!(i == 0 || !a.is_trivial());
            for b in &laws[..i] {
                assert!(a != b && a.swapped() != *b, "{a} duplicates {b}");
            }
        }
        // 0 ops: 2 laws; 1 op: 5 laws; 2 ops: 30 with a bare side plus the
        // x◇y = z◇w patterns that survive swap/trivial removal.
        assert_eq!(laws.iter().filter(|l| l.ops() == 1).count(), 5);
        assert_eq!(
            laws.iter()
                .filter(|l| l.ops() == 2 && l.lhs.ops() == 0)
                .count(),
            30
        );
    }
}

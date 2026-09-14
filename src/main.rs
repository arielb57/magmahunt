use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use magmahunt::matrix::{Cell, Matrix};
use magmahunt::{
    count_models, generate_laws, parse_law, parse_law_list, refute, CompiledLaw, Options,
};

const USAGE: &str = "\
magmahunt: finite counterexamples for implications between magma laws

USAGE:
  magmahunt refute '<hypothesis>' '<conclusion>' [--max-size N] [--no-symmetry]
  magmahunt matrix <laws.txt> [--max-size N] [--out-dir DIR] [--no-symmetry]
  magmahunt count '<law>' --size N [--no-symmetry]
  magmahunt laws [--max-ops K] [--limit N]

Laws use ETP notation: x ◇ (y ◇ z) = (x ◇ y) ◇ z  (`*` also works for ◇).

EXIT STATUS (refute): 0 counterexample found, 1 none up to N, 2 error.";

struct Args {
    positional: Vec<String>,
    max_size: Option<usize>,
    size: Option<usize>,
    max_ops: Option<usize>,
    limit: Option<usize>,
    out_dir: Option<PathBuf>,
    symmetry: bool,
}

fn parse_args(raw: &[String]) -> Result<Args, String> {
    let mut args = Args {
        positional: Vec::new(),
        max_size: None,
        size: None,
        max_ops: None,
        limit: None,
        out_dir: None,
        symmetry: true,
    };
    let mut it = raw.iter();
    while let Some(a) = it.next() {
        let mut number = |name: &str| -> Result<usize, String> {
            let v = it.next().ok_or_else(|| format!("{name} needs a value"))?;
            v.parse()
                .map_err(|_| format!("{name} expects a non-negative integer, got '{v}'"))
        };
        match a.as_str() {
            "--max-size" => args.max_size = Some(number("--max-size")?),
            "--size" => args.size = Some(number("--size")?),
            "--max-ops" => args.max_ops = Some(number("--max-ops")?),
            "--limit" => args.limit = Some(number("--limit")?),
            "--out-dir" => {
                args.out_dir = Some(PathBuf::from(it.next().ok_or("--out-dir needs a value")?));
            }
            "--no-symmetry" => args.symmetry = false,
            flag if flag.starts_with("--") => return Err(format!("unknown option {flag}")),
            _ => args.positional.push(a.clone()),
        }
    }
    Ok(args)
}

fn expect_positional(args: &Args, count: usize, what: &str) -> Result<(), String> {
    if args.positional.len() != count {
        return Err(format!("expected {what}"));
    }
    Ok(())
}

fn options(args: &Args) -> Options {
    Options {
        symmetry: args.symmetry,
        ..Options::default()
    }
}

fn cmd_refute(args: &Args) -> Result<ExitCode, String> {
    expect_positional(args, 2, "a hypothesis and a conclusion")?;
    let h = parse_law(&args.positional[0]).map_err(|e| format!("hypothesis: {e}"))?;
    let c = parse_law(&args.positional[1]).map_err(|e| format!("conclusion: {e}"))?;
    let max = args.max_size.unwrap_or(4);
    if max == 0 {
        return Err("--max-size must be at least 1".into());
    }
    let start = Instant::now();
    let result = refute(&h, &c, max, options(args))?;
    let elapsed = start.elapsed();
    println!("hypothesis: {h}");
    println!("conclusion: {c}");
    let code = match &result.witness {
        Some(w) => {
            println!(
                "counterexample of size {} (re-verified by the brute-force checker):",
                w.size()
            );
            print!("{w}");
            ExitCode::SUCCESS
        }
        None => {
            println!("none up to size {max}");
            ExitCode::from(1)
        }
    };
    println!("nodes explored: {}, time: {:.3?}", result.nodes, elapsed);
    Ok(code)
}

fn cmd_count(args: &Args) -> Result<ExitCode, String> {
    expect_positional(args, 1, "one law")?;
    let law = parse_law(&args.positional[0]).map_err(|e| e.to_string())?;
    let n = args.size.ok_or("count needs --size N")?;
    let compiled = CompiledLaw::new(&law);
    magmahunt::search::check_size(&compiled, n)?;
    let start = Instant::now();
    let stats = count_models(&compiled, n, options(args));
    let what = if args.symmetry {
        "isomorphism classes of models"
    } else {
        "labelled models"
    };
    println!("{law}");
    println!("size {n}: {} {what}", stats.leaves);
    println!(
        "nodes explored: {}, time: {:.3?}",
        stats.nodes,
        start.elapsed()
    );
    Ok(ExitCode::SUCCESS)
}

fn cmd_matrix(args: &Args) -> Result<ExitCode, String> {
    expect_positional(args, 1, "a laws file")?;
    let path = &args.positional[0];
    let text = std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
    let laws = parse_law_list(&text).map_err(|e| format!("{path}: {e}"))?;
    if laws.is_empty() {
        return Err(format!("{path}: no laws found"));
    }
    let max = args.max_size.unwrap_or(4);
    let out_dir = args.out_dir.clone().unwrap_or_else(|| PathBuf::from("."));
    let start = Instant::now();
    let matrix = Matrix::build(laws, max, options(args));
    let elapsed = start.elapsed();
    let verified = matrix.verify()?;
    std::fs::create_dir_all(&out_dir).map_err(|e| format!("{}: {e}", out_dir.display()))?;
    let csv = out_dir.join("matrix.csv");
    let wit = out_dir.join("witnesses.txt");
    std::fs::write(&csv, matrix.to_csv()).map_err(|e| format!("{}: {e}", csv.display()))?;
    std::fs::write(&wit, matrix.witnesses_text()).map_err(|e| format!("{}: {e}", wit.display()))?;

    let m = matrix.laws.len();
    println!("{m} laws, {} ordered pairs, sizes 1..={max}", m * m);
    println!(
        "  implied (syntactic proof): {}",
        matrix.count(|c| matches!(c, Cell::Implied(_)))
    );
    println!(
        "  refuted by a witness:      {}",
        matrix.count(|c| matches!(c, Cell::Refuted(_)))
    );
    println!(
        "  open (none up to size {max}): {}",
        matrix.count(|c| *c == Cell::Open)
    );
    println!(
        "{} witnesses, {verified} refutations re-verified by the brute-force checker",
        matrix.witnesses.len()
    );
    if matrix.stats.skipped_too_large > 0 {
        println!(
            "{} searches skipped: too many ground instances",
            matrix.stats.skipped_too_large
        );
    }
    println!(
        "{} searches, {} nodes, {:.3?}",
        matrix.stats.searches, matrix.stats.nodes, elapsed
    );
    println!("wrote {} and {}", csv.display(), wit.display());
    Ok(ExitCode::SUCCESS)
}

fn cmd_laws(args: &Args) -> Result<ExitCode, String> {
    expect_positional(args, 0, "no positional arguments")?;
    let laws = generate_laws(args.max_ops.unwrap_or(2));
    for law in laws.iter().take(args.limit.unwrap_or(usize::MAX)) {
        println!("{law}");
    }
    Ok(ExitCode::SUCCESS)
}

fn main() -> ExitCode {
    let raw: Vec<String> = std::env::args().skip(1).collect();
    let Some(command) = raw.first() else {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    };
    if matches!(command.as_str(), "help" | "--help" | "-h") {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    let result = parse_args(&raw[1..]).and_then(|args| match command.as_str() {
        "refute" => cmd_refute(&args),
        "matrix" => cmd_matrix(&args),
        "count" => cmd_count(&args),
        "laws" => cmd_laws(&args),
        other => Err(format!("unknown command '{other}'\n\n{USAGE}")),
    });
    match result {
        Ok(code) => code,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(2)
        }
    }
}

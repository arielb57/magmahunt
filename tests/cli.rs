use std::process::Command;

fn magmahunt(args: &[&str]) -> (i32, String, String) {
    let out = Command::new(env!("CARGO_BIN_EXE_magmahunt"))
        .args(args)
        .output()
        .expect("binary runs");
    (
        out.status.code().unwrap_or(-1),
        String::from_utf8(out.stdout).unwrap(),
        String::from_utf8(out.stderr).unwrap(),
    )
}

#[test]
fn refute_prints_a_counterexample_table() {
    let (code, out, _) = magmahunt(&[
        "refute",
        "x ◇ y = y ◇ x",
        "x ◇ (y ◇ z) = (x ◇ y) ◇ z",
        "--max-size",
        "5",
    ]);
    assert_eq!(code, 0);
    assert!(out.contains("counterexample of size 2"), "{out}");
    assert!(out.contains("◇ | 0 1\n--+----\n0 |"), "{out}");
}

#[test]
fn refute_reports_none_with_exit_status_1() {
    let (code, out, _) = magmahunt(&["refute", "x*y = x", "x*(y*z) = (x*y)*z", "--max-size", "3"]);
    assert_eq!(code, 1);
    assert!(out.contains("none up to size 3"), "{out}");
}

#[test]
fn bad_input_exits_2_with_a_message() {
    let (code, _, err) = magmahunt(&["refute", "x ◇ = y", "x = x"]);
    assert_eq!(code, 2);
    assert!(err.contains("hypothesis:"), "{err}");
    let (code, _, err) = magmahunt(&["refute", "x = y", "x = x", "--max-size", "lots"]);
    assert_eq!(code, 2);
    assert!(err.contains("non-negative integer"), "{err}");
    let (code, _, err) = magmahunt(&["frobnicate"]);
    assert_eq!(code, 2);
    assert!(err.contains("unknown command"), "{err}");
    let (code, _, err) = magmahunt(&["count", "x = x"]);
    assert_eq!(code, 2);
    assert!(err.contains("--size"), "{err}");
}

#[test]
fn count_reports_labelled_and_isomorphism_counts() {
    let (_, out, _) = magmahunt(&["count", "x◇(y◇z) = (x◇y)◇z", "--size", "3", "--no-symmetry"]);
    assert!(out.contains("size 3: 113 labelled models"), "{out}");
    let (_, out, _) = magmahunt(&["count", "x◇(y◇z) = (x◇y)◇z", "--size", "3"]);
    assert!(out.contains("size 3: 24 isomorphism classes"), "{out}");
}

#[test]
fn matrix_writes_csv_and_witnesses() {
    let dir = std::env::temp_dir().join(format!("magmahunt-cli-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let laws = dir.join("laws.txt");
    std::fs::write(
        &laws,
        "# test laws\nx ◇ y = y ◇ x\nx ◇ (y ◇ z) = (x ◇ y) ◇ z\nx ◇ y = x\n",
    )
    .unwrap();
    let out_dir = dir.join("out");
    let (code, out, err) = magmahunt(&[
        "matrix",
        laws.to_str().unwrap(),
        "--max-size",
        "3",
        "--out-dir",
        out_dir.to_str().unwrap(),
    ]);
    assert_eq!(code, 0, "{err}");
    assert!(out.contains("3 laws, 9 ordered pairs"), "{out}");
    let csv = std::fs::read_to_string(out_dir.join("matrix.csv")).unwrap();
    let rows: Vec<&str> = csv.lines().collect();
    assert_eq!(rows.len(), 4);
    // commutativity row: implied itself, refuted associativity and x◇y = x.
    assert!(rows[1].starts_with("\"x ◇ y = y ◇ x\",implied,w"), "{csv}");
    // x◇y = x row: associativity is open (it is in fact implied).
    assert!(rows[3].ends_with(",open,implied"), "{csv}");
    let witnesses = std::fs::read_to_string(out_dir.join("witnesses.txt")).unwrap();
    assert!(witnesses.starts_with("w0: size 2"), "{witnesses}");
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn laws_generates_the_etp_style_list() {
    let (code, out, _) = magmahunt(&["laws", "--max-ops", "2", "--limit", "3"]);
    assert_eq!(code, 0);
    assert_eq!(out, "x = x\nx = y\nx = x ◇ x\n");
}

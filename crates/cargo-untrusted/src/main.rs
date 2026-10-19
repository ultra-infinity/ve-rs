//! `cargo untrusted verify -p <package>`: formally verifies every `Decode` impl
//! of a crate that depends on `untrusted`.
//!
//! This tool only orchestrates; it is not trusted. Everything it produces is
//! checked by Lean: the extracted model must build against the verified
//! `Untrusted` Lean library, every `Decode` impl needs a proved spec, and the
//! audit rejects `sorry` and unexpected axioms.
//!
//! Steps:
//! 1. Charon translates only the crate's `Decode` impls (`--start-from`), with
//!    `untrusted` opaque, so its items become references to our model.
//! 2. Aeneas generates `Types.lean`/`Funs.lean` in the Lean project.
//! 3. Declarations duplicated from `untrusted` are dropped, and the external
//!    templates replaced by imports of the verified `Untrusted` library.
//! 4. One `derive_decode_spec` file per `Decode` impl is generated and built; an
//!    impl whose automatic proof fails (e.g. a hand-written one) is reported,
//!    and must be given a spec by hand in `<Module>/Manual.lean`.
//! 5. `untrusted_audit` checks coverage and axioms.
//!
//! Requires `charon`, `aeneas` and `lake` on `PATH` (the `untrusted` flake's dev
//! shell provides them).

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{exit, Command};

struct Args {
    package: String,
    lean_dir: PathBuf,
    untrusted_lean: Option<PathBuf>,
    extract_only: bool,
}

fn usage() -> ! {
    eprintln!(
        "usage: cargo untrusted verify -p <package> [--lean-dir <dir>] [--untrusted-lean <dir>]\n\
         \x20                          [--extract-only]\n\
         \n\
         --lean-dir        Lean project to generate into (default: proofs)\n\
         --untrusted-lean  path to the `untrusted` Lean package, used when a new\n\
         \x20                 Lean project has to be created\n\
         --extract-only    only regenerate the Lean model (steps 1-3), e.g. to\n\
         \x20                 check that a committed model is up to date"
    );
    exit(2)
}

fn parse_args() -> Args {
    // Invoked as `cargo untrusted verify …` (argv[1] = "untrusted") or directly.
    let mut args = std::env::args().skip(1).peekable();
    if args.peek().map(String::as_str) == Some("untrusted") {
        args.next();
    }
    if args.next().as_deref() != Some("verify") {
        usage();
    }
    let (mut package, mut lean_dir, mut untrusted_lean) = (None, None, None);
    let mut extract_only = false;
    while let Some(a) = args.next() {
        match a.as_str() {
            "-p" | "--package" => package = args.next(),
            "--lean-dir" => lean_dir = args.next().map(PathBuf::from),
            "--untrusted-lean" => untrusted_lean = args.next().map(PathBuf::from),
            "--extract-only" => extract_only = true,
            _ => usage(),
        }
    }
    Args {
        package: package.unwrap_or_else(|| usage()),
        lean_dir: lean_dir.unwrap_or_else(|| PathBuf::from("proofs")),
        untrusted_lean,
        extract_only,
    }
}

fn run(cmd: &mut Command) -> bool {
    eprintln!("$ {cmd:?}");
    cmd.status().map(|s| s.success()).unwrap_or_else(|e| {
        eprintln!("error: could not run {:?}: {e}", cmd.get_program());
        false
    })
}

fn require(ok: bool, what: &str) {
    if !ok {
        eprintln!("error: {what} failed");
        exit(1);
    }
}

/// `derive-demo` → `DeriveDemo`, the Lean module name.
fn module_name(package: &str) -> String {
    package
        .split(['-', '_'])
        .map(|w| {
            let mut c = w.chars();
            c.next()
                .map(|f| f.to_uppercase().chain(c).collect::<String>())
                .unwrap_or_default()
        })
        .collect()
}

/// Drops the paragraphs (Aeneas emits one declaration per paragraph) that
/// declare items of the `untrusted` crate: they are taken from the verified
/// `Untrusted` library instead.
fn drop_untrusted_decls(path: &Path) {
    let text = fs::read_to_string(path).expect("read generated Lean file");
    let kept: Vec<&str> = text
        .split("\n\n")
        .filter(|p| {
            let flat = p.split_whitespace().collect::<Vec<_>>().join(" ");
            !["rust_trait ", "rust_trait_impl ", "rust_type ", "rust_fun "]
                .iter()
                .any(|attr| flat.contains(&format!("{attr}\"untrusted::")))
        })
        .collect();
    fs::write(path, kept.join("\n\n")).expect("write generated Lean file");
}

/// The Lean types that have a `Decode` impl in the generated `Funs.lean`.
fn decode_impl_types(funs: &str, namespace: &str) -> Vec<String> {
    funs.lines()
        .filter_map(|l| {
            let rest = l.strip_prefix("def ")?;
            let name = rest.split_whitespace().next()?;
            let ty = name.strip_suffix(".Insts.UntrustedReaderDecode")?;
            Some(format!("{namespace}.{ty}"))
        })
        .collect()
}

fn ensure_lean_project(dir: &Path, module: &str, untrusted_lean: Option<&Path>) {
    let lakefile = dir.join("lakefile.toml");
    if !lakefile.exists() {
        let Some(src) = untrusted_lean else {
            eprintln!(
                "error: {} has no lakefile.toml; pass --untrusted-lean",
                dir.display()
            );
            exit(2);
        };
        let src = fs::canonicalize(src).expect("--untrusted-lean must exist");
        fs::create_dir_all(dir).expect("create Lean project");
        fs::copy(src.join("lean-toolchain"), dir.join("lean-toolchain"))
            .expect("copy lean-toolchain from the untrusted Lean package");
        fs::write(
            &lakefile,
            format!(
                "name = \"{}\"\n\n[[require]]\nname = \"untrusted\"\npath = \"{}\"\n",
                module.to_lowercase(),
                src.display()
            ),
        )
        .expect("write lakefile.toml");
    }
    let text = fs::read_to_string(&lakefile).expect("read lakefile.toml");
    if !text.contains(&format!("name = \"{module}\"")) {
        fs::write(
            &lakefile,
            format!("{text}\n[[lean_lib]]\nname = \"{module}\"\n"),
        )
        .expect("update lakefile.toml");
    }
}

fn main() {
    let args = parse_args();
    let module = module_name(&args.package);
    let namespace = args.package.replace('-', "_");
    let llbc = PathBuf::from("target/charon").join(format!("{namespace}.llbc"));

    // 1. Charon: only the `Decode` impls, with `untrusted` opaque.
    require(
        run(Command::new("charon").args([
            "cargo",
            "--preset=aeneas",
            "--opaque",
            "untrusted",
            "--start-from",
            "{impl untrusted::reader::Decode for _}",
            "--dest-file",
            llbc.to_str().unwrap(),
            "--",
            "-p",
            &args.package,
        ])),
        "charon",
    );

    // 2. Aeneas.
    ensure_lean_project(&args.lean_dir, &module, args.untrusted_lean.as_deref());
    let out = args.lean_dir.join(&module);
    for f in ["Types.lean", "Funs.lean"] {
        let _ = fs::remove_file(out.join(f));
    }
    require(
        run(Command::new("aeneas").args([
            "-backend",
            "lean",
            "-split-files",
            "-loops-to-rec",
            "-use-lean-modules",
            "false",
            "-subdir",
            &module,
            "-dest",
            args.lean_dir.to_str().unwrap(),
            llbc.to_str().unwrap(),
        ])),
        "aeneas",
    );

    // 3. Link against the verified `Untrusted` library.
    drop_untrusted_decls(&out.join("Types.lean"));
    drop_untrusted_decls(&out.join("Funs.lean"));
    for t in ["TypesExternal_Template.lean", "FunsExternal_Template.lean"] {
        let _ = fs::remove_file(out.join(t));
    }
    fs::write(out.join("TypesExternal.lean"), "import Untrusted.Types\n").unwrap();
    fs::write(out.join("FunsExternal.lean"), "import Untrusted.Funs\n").unwrap();
    if args.extract_only {
        return;
    }

    // 4. One automatic spec per `Decode` impl.
    let funs = fs::read_to_string(out.join("Funs.lean")).unwrap();
    let types = decode_impl_types(&funs, &namespace);
    let specs = out.join("Specs");
    let _ = fs::remove_dir_all(&specs);
    fs::create_dir_all(&specs).unwrap();
    // A struct's spec needs the specs of its field types (nested structs), so
    // each attempt imports everything proved so far, and failed impls are
    // retried until a pass makes no progress.
    let mut proved: Vec<String> = Vec::new();
    let mut manual = types.clone();
    loop {
        let mut progress = false;
        for ty in std::mem::take(&mut manual) {
            let short = ty.rsplit('.').next().unwrap().to_string();
            let mut src = format!("import {module}.Funs\nimport Untrusted\n");
            for p in &proved {
                writeln!(src, "import {p}").unwrap();
            }
            writeln!(src, "\nderive_decode_spec {ty}").unwrap();
            fs::write(specs.join(format!("{short}.lean")), src).unwrap();
            let target = format!("{module}.Specs.{short}");
            if run(Command::new("lake")
                .arg("build")
                .arg(&target)
                .current_dir(&args.lean_dir))
            {
                proved.push(target);
                progress = true;
            } else {
                let _ = fs::remove_file(specs.join(format!("{short}.lean")));
                manual.push(ty);
            }
        }
        if !progress || manual.is_empty() {
            break;
        }
    }

    // 5. Audit everything, including hand-written specs in `Manual.lean`.
    let mut audit = format!("import {module}.Funs\nimport Untrusted\n");
    for p in &proved {
        writeln!(audit, "import {p}").unwrap();
    }
    if out.join("Manual.lean").exists() {
        writeln!(audit, "import {module}.Manual").unwrap();
    }
    writeln!(audit, "\nuntrusted_audit {module}.Funs {module}").unwrap();
    fs::write(out.join("Audit.lean"), audit).unwrap();
    let audited = run(Command::new("lake")
        .args(["env", "lean", &format!("{module}/Audit.lean")])
        .current_dir(&args.lean_dir));

    eprintln!();
    eprintln!("{} `Decode` impls proved automatically", proved.len());
    for ty in &manual {
        eprintln!(
            "needs a manual spec (`{ty}.Insts.UntrustedReaderDecode.decode.spec`) in {}/Manual.lean: {ty}",
            module
        );
    }
    if !audited {
        eprintln!("verification FAILED");
        exit(1);
    }
    eprintln!("verification succeeded");
}

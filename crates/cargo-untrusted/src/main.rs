//! `cargo untrusted verify -p <package>`: formally verifies every `Decode` impl
//! of a crate that depends on `untrusted`.
//!
//! This tool only orchestrates; it is not trusted. Everything it produces is
//! checked by Lean: the extracted model must build against the verified
//! `Untrusted` Lean library, every `Decode` impl needs a proved spec, and the
//! audit rejects `sorry` and unexpected axioms.
//!
//! Steps:
//! 1. Charon translates only the crate's `Decode` and `Validate` impls
//!    (`--start-from`), or every item with `--extract-all`. Items of
//!    `untrusted` (and of `--link`ed crates) are foreign: their functions stay
//!    references to their models, and their public types are re-translated
//!    (and dropped again in step 3).
//! 2. Aeneas generates `Types.lean`/`Funs.lean` in the Lean project.
//! 3. Declarations duplicated from `untrusted` and `--link`ed crates are
//!    dropped, and the external templates replaced by imports of their
//!    verified Lean libraries.
//! 4. One `derive_decode_spec` file per `Decode` impl is generated and built; an
//!    impl whose automatic proof fails (e.g. a hand-written one) is reported,
//!    and must be given a spec by hand in `<Module>/Manual.lean` (if derived
//!    types build on it) or `<Module>/ManualTop.lean` (if it builds on them,
//!    like a `Validate` impl), which are left untouched.
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
    /// Extract every item of the crate, not only its `Decode`/`Validate` impls.
    extract_all: bool,
    /// Verified crates this one depends on, with their Lean library names.
    links: Vec<(String, String)>,
}

fn usage() -> ! {
    eprintln!(
        "usage: cargo untrusted verify -p <package> [--lean-dir <dir>] [--untrusted-lean <dir>]\n\
         \x20                          [--extract-only] [--extract-all] [--link <crate>=<Lib>]...\n\
         \n\
         --lean-dir        Lean project to generate into (default: proofs)\n\
         --untrusted-lean  path to the `untrusted` Lean package, used when a new\n\
         \x20                 Lean project has to be created\n\
         --extract-only    only regenerate the Lean model (steps 1-3), e.g. to\n\
         \x20                 check that a committed model is up to date\n\
         --extract-all     extract every item of the crate, not only its `Decode`\n\
         \x20                 and `Validate` impls; all of them then need specs\n\
         --link            a verified crate this one uses, and its Lean library in\n\
         \x20                 the same Lean project (e.g. `net=Net`): its items are\n\
         \x20                 taken from that library instead of re-translated"
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
    let mut extract_all = false;
    let mut links = Vec::new();
    while let Some(a) = args.next() {
        match a.as_str() {
            "-p" | "--package" => package = args.next(),
            "--lean-dir" => lean_dir = args.next().map(PathBuf::from),
            "--untrusted-lean" => untrusted_lean = args.next().map(PathBuf::from),
            "--extract-only" => extract_only = true,
            "--extract-all" => extract_all = true,
            "--link" => {
                let Some((krate, lib)) = args.next().and_then(|l| {
                    let (c, m) = l.split_once('=')?;
                    Some((c.replace('-', "_"), m.to_string()))
                }) else {
                    usage()
                };
                links.push((krate, lib));
            }
            _ => usage(),
        }
    }
    Args {
        package: package.unwrap_or_else(|| usage()),
        lean_dir: lean_dir.unwrap_or_else(|| PathBuf::from("proofs")),
        untrusted_lean,
        extract_only,
        extract_all,
        links,
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
/// declare items of the already-verified `crates` (`untrusted`, and any
/// `--link`ed crate): they are taken from those crates' Lean libraries
/// instead.
///
/// Returns, per crate, the names those paragraphs declared outside the crate's
/// own prefix. Impls for built-in types, such as `Decode for [u8; N]`, are
/// named after the type (`ArrayU8N.…`), so the generated code refers to them
/// unqualified; they are re-exported into this crate's namespace.
fn drop_verified_decls(path: &Path, crates: &[&str]) -> Vec<(String, String)> {
    let text = fs::read_to_string(path).expect("read generated Lean file");
    let mut unqualified = Vec::new();
    let kept: Vec<&str> = text
        .split("\n\n")
        .filter(|p| {
            let flat = p.split_whitespace().collect::<Vec<_>>().join(" ");
            // An item of a verified crate: its Rust path starts with the
            // crate, or (e.g. a `core` trait impl for one of its types) its
            // Lean name does.
            let from = crates.iter().find(|c| {
                ["rust_trait ", "rust_trait_impl ", "rust_type ", "rust_fun "]
                    .iter()
                    .any(|attr| flat.contains(&format!("{attr}\"{c}::")))
                    || p.lines().any(|l| {
                        ["def ", "structure ", "inductive "].iter().any(|kw| {
                            l.strip_prefix(kw)
                                .is_some_and(|rest| rest.starts_with(&format!("{c}.")))
                        })
                    })
            });
            if let Some(c) = from {
                let names = p.lines().filter_map(|l| {
                    let name = l.strip_prefix("def ")?.split_whitespace().next()?;
                    (!crates.iter().any(|k| name.starts_with(&format!("{k}."))))
                        .then(|| (c.to_string(), name.to_string()))
                });
                unqualified.extend(names);
            }
            from.is_none()
        })
        .collect();
    fs::write(path, kept.join("\n\n")).expect("write generated Lean file");
    unqualified
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

    // 1. Charon: only the `Decode` and `Validate` impls, unless asked for the
    //    whole crate.
    let mut charon = Command::new("charon");
    charon.args(["cargo", "--preset=aeneas"]);
    if args.extract_all {
        // Derived standard impls are for tests and printing; they would each
        // need a spec, and verified code must not rely on them.
        for t in [
            "core::fmt::Debug",
            "core::clone::Clone",
            "core::marker::Copy",
            "core::cmp::PartialEq<_>",
            "core::cmp::Eq",
            "core::marker::StructuralPartialEq",
        ] {
            charon.args(["--exclude", &format!("{{impl {t} for _}}")]);
        }
    } else {
        charon.args([
            "--start-from",
            "{impl untrusted::reader::Decode for _}",
            "--start-from",
            "{impl untrusted::Validate for _}",
        ]);
    }
    charon.args(["--dest-file", llbc.to_str().unwrap(), "--", "-p", &args.package]);
    require(run(&mut charon), "charon");

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

    // 3. Link against the verified `Untrusted` library, and the libraries of
    //    any `--link`ed crates.
    let mut libs = vec![("untrusted", "Untrusted")];
    libs.extend(args.links.iter().map(|(c, l)| (c.as_str(), l.as_str())));
    let crates: Vec<&str> = libs.iter().map(|(c, _)| *c).collect();
    drop_verified_decls(&out.join("Types.lean"), &crates);
    let reexports = drop_verified_decls(&out.join("Funs.lean"), &crates);
    for t in ["TypesExternal_Template.lean", "FunsExternal_Template.lean"] {
        let _ = fs::remove_file(out.join(t));
    }
    let mut types_external = String::new();
    let mut funs_external = String::new();
    for (_, lib) in &libs {
        writeln!(types_external, "import {lib}.Types").unwrap();
        writeln!(funs_external, "import {lib}.Funs").unwrap();
    }
    for (krate, _) in &libs {
        let names: Vec<&str> = reexports
            .iter()
            .filter(|(c, _)| c == krate)
            .map(|(_, n)| n.as_str())
            .collect();
        if !names.is_empty() {
            writeln!(
                funs_external,
                "\nnamespace {namespace}\nexport {krate} ({})\nend {namespace}",
                names.join(" ")
            )
            .unwrap();
        }
    }
    fs::write(out.join("TypesExternal.lean"), types_external).unwrap();
    fs::write(out.join("FunsExternal.lean"), funs_external).unwrap();
    if args.extract_only {
        return;
    }

    // 4. One automatic spec per `Decode` impl, except those given by hand.
    //    Hand-written specs live in `Manual.lean` (specs that derived types
    //    build on; imported by every attempt) and `ManualTop.lean` (specs that
    //    build on derived types, e.g. a `Validate` impl; imported by the audit).
    let funs = fs::read_to_string(out.join("Funs.lean")).unwrap();
    // All hand-written Lean files of the module (they may import each other).
    let generated = [
        "Types.lean",
        "Funs.lean",
        "TypesExternal.lean",
        "FunsExternal.lean",
        "Audit.lean",
    ];
    let manual_src: String = fs::read_dir(&out)
        .into_iter()
        .flatten()
        .flatten()
        .filter(|e| {
            let name = e.file_name().to_string_lossy().into_owned();
            name.ends_with(".lean") && !generated.contains(&name.as_str())
        })
        .filter_map(|e| fs::read_to_string(e.path()).ok())
        .collect();
    let has_manual = out.join("Manual.lean").exists();
    let all_types = decode_impl_types(&funs, &namespace);
    let types: Vec<String> = all_types
        .iter()
        .filter(|ty| !manual_src.contains(&format!("{ty}.Insts.UntrustedReaderDecode.decode.spec")))
        .cloned()
        .collect();
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
            if has_manual {
                writeln!(src, "import {module}.Manual").unwrap();
            }
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

    // 5. Audit everything, including the hand-written specs.
    let mut audit = format!("import {module}.Funs\nimport Untrusted\n");
    if has_manual {
        writeln!(audit, "import {module}.Manual").unwrap();
    }
    for p in &proved {
        writeln!(audit, "import {p}").unwrap();
    }
    if out.join("ManualTop.lean").exists() {
        writeln!(audit, "import {module}.ManualTop").unwrap();
    }
    writeln!(audit, "\nuntrusted_audit {module}.Funs {module}").unwrap();
    fs::write(out.join("Audit.lean"), audit).unwrap();
    // Built as a module, so that Lake first builds everything it imports
    // (including the hand-written specs); a failing audit fails the build.
    let audited = run(Command::new("lake")
        .args(["build", &format!("{module}.Audit")])
        .current_dir(&args.lean_dir));

    eprintln!();
    eprintln!(
        "{} `Decode` impls proved automatically, {} by hand-written specs",
        proved.len(),
        all_types.len() - types.len()
    );
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

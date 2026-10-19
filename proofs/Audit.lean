/- Proof audit, run by `make audit`:
   1. every function of the generated model that returns `Result` has a
      `<function>.spec` theorem;
   2. no theorem of the project depends on `sorryAx` or on an axiom other than
      Lean's standard ones and the abstract `core::fmt::Formatter` type. -/
import Untrusted

open Lean Elab Command

/-- Axioms a project theorem may depend on. `core.fmt.Formatter` is how Aeneas
    declares the (opaque) formatter type; it postulates a type, not a fact. -/
def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound, ``Aeneas.Std.core.fmt.Formatter]

def returnsResult (ty : Expr) : Bool :=
  ty.getForallBody.getAppFn.constName? == some ``Aeneas.Std.Result

#eval show CommandElabM Unit from do
  let env ← getEnv
  let inModule (pre : Name) (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => pre.isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  let consts := env.constants.map₁.toList
  -- 1. Coverage.
  let funs := consts.filterMap fun (n, info) =>
    match info with
    | .defnInfo d =>
      if inModule `Untrusted.Funs n && returnsResult d.type && !n.isInternal then some n else none
    | _ => none
  let missing := funs.filter fun n => !env.contains (n ++ `spec)
  -- 2. Axioms.
  let thms := consts.filterMap fun (n, info) =>
    if info matches .thmInfo _ && inModule `Untrusted n then some n else none
  let mut bad : Array (Name × Array Name) := #[]
  for n in thms do
    let axs ← liftCoreM (collectAxioms n)
    let extra := axs.filter (!allowedAxioms.contains ·)
    unless extra.isEmpty do bad := bad.push (n, extra)
  logInfo m!"{funs.length} model functions, {missing.length} without a spec; \
    {thms.length} theorems, {bad.size} with disallowed axioms"
  for n in missing do logError m!"no spec: {n}"
  for (n, a) in bad do logError m!"disallowed axioms in {n}: {a}"

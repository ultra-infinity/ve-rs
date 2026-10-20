/- `untrusted_audit Model Proofs`:
   1. every function of the generated model (modules under `Model`) that returns
      `Result` has a `<function>.spec`;
   2. no proof in the modules under `Proofs` depends on `sorryAx` or on an
      axiom other than Lean's standard ones and the abstract
      `core::fmt::Formatter` type.
   It fails, with an error per problem, if either check does. -/
import Untrusted.Proofs

open Lean Elab Command Meta

namespace untrusted.audit

/-- Axioms a proof may depend on. `core.fmt.Formatter` is how Aeneas declares
    the (opaque) formatter type; it postulates a type, not a fact. -/
def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound, ``Aeneas.Std.core.fmt.Formatter]

def returnsResult (ty : Expr) : Bool :=
  ty.getForallBody.getAppFn.constName? == some ``Aeneas.Std.Result

/-- `f.mutual`, the auxiliary that `partial_fixpoint` defines `f` through when
    `f`'s fixed parameters are not a prefix of its parameters. It is not a
    function of the Rust code: the spec of `f` covers it. -/
def isFixpointAux (env : Environment) (n : Name) : Bool :=
  match n with
  | .str f "mutual" => env.contains f
  | _ => false

elab "untrusted_audit " model:ident proofs:ident : command => do
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
      if inModule model.getId n && returnsResult d.type && !n.isInternal &&
          !isFixpointAux env n then some n else none
    | _ => none
  let missing := funs.filter fun n => !env.contains (n ++ `spec)
  -- 2. Axioms, for every proof (theorem or Prop-valued instance).
  let proofs ← liftTermElabM <| consts.filterMapM fun (n, info) => do
    if !inModule proofs.getId n then return none
    match info with
    | .thmInfo _ => return some n
    | .defnInfo d => return if ← isProp d.type then some n else none
    | _ => return none
  let mut bad : Array (Name × Array Name) := #[]
  for n in proofs do
    let axs ← liftCoreM (collectAxioms n)
    let extra := axs.filter (!allowedAxioms.contains ·)
    unless extra.isEmpty do bad := bad.push (n, extra)
  logInfo m!"{funs.length} model functions, {missing.length} without a spec; \
    {proofs.length} proofs, {bad.size} with disallowed axioms"
  for n in missing do logError m!"no spec: {n}"
  for (n, a) in bad do logError m!"disallowed axioms in {n}: {a}"

end untrusted.audit

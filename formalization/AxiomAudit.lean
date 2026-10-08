import ExactSampling

/-!
Axiom audit for the whole `ExactSampling` library.

The command below enumerates every constant declared in a module whose name starts with
`ExactSampling`, so no theorem can be left out of the audit by accident. For each constant it
prints one line

    AUDIT <name> | <kind> | <user> | <axioms> | <docstring>

where `<user>` is `user` for declarations written in the source (those with a declaration
range) and `aux` for compiler-generated ones such as `injEq`. `verify.py` parses this output.
-/

open Lean Elab Command

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quot"

elab "#audit_exact_sampling" : command => do
  let env ← getEnv
  let mut decls : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    if (`ExactSampling).isPrefixOf mod then
      decls := decls.push (n, ci)
  decls := decls.qsort (fun a b => a.1.toString < b.1.toString)
  for (n, ci) in decls do
    let axs ← liftCoreM <| collectAxioms n
    let axs := (axs.qsort (fun a b => a.toString < b.toString)).toList.map toString
    let user := (← liftCoreM <| findDeclarationRanges? n).isSome
    let doc := ((← findDocString? env n).getD "").replace "\n" " "
    logInfo m!"AUDIT {n} | {kindOf ci} | {if user then "user" else "aux"} | \
      {", ".intercalate axs} | {doc}"
  logInfo m!"AUDIT-TOTAL {decls.size}"

#audit_exact_sampling

import IsogenyAttack
import Lean.Util.CollectAxioms

/-!
Reject any nonstandard axiom in the transitive dependency closure of ANY
declaration imported from this project's modules, including vendored sources.
This is a diagnostic check; the mathematical proofs are checked by Lean's
kernel when each source module is built.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut used : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if (`IsogenyAttack).isPrefixOf moduleName || (`TauCeti).isPrefixOf moduleName then
        checked := checked + 1
        for axiomName in ← collectAxioms name do
          unless allowed.contains axiomName do
            throwError "Nonstandard axiom {axiomName} in {name}"
          unless used.contains axiomName do
            used := used.push axiomName
  logInfo m!"Audited {checked} project and imported TauCeti declarations. Axioms: {used}"

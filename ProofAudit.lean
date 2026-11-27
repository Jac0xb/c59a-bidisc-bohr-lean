import C59a
import Lean

/-!
# Hard-Fail Kernel Axiom & Sorry Audit Gate (`C_59a`)

Run via:
```bash
lake env lean ProofAudit.lean
```

Verifies that both headline theorems in `Optim.BohrRadius`:
1. exist in the environment as theorems (`ConstantInfo.thmInfo`),
2. have zero `sorry` in their kernel proof terms (`ConstantInfo.value?`),
3. depend strictly on `{propext, Classical.choice, Quot.sound}` — rejecting `sorryAx`,
   `Lean.ofReduceBool`, `Lean.trustCompiler`, or any custom/non-standard axiom,
4. and that all six core `Optim.BohrRadius` definitions have `DefinitionSafety.safe`.
-/

#print axioms Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16
#print axioms Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21

open Lean in
#eval show CoreM Unit from do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let forbidden : List Name := [`sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler]
  let thms : List Name := [
    `Optim.BohrRadius.bohrRadius_lt_3028252794909876_div_10pow16,
    `Optim.BohrRadius.bohrRadius_lt_302825279490987594822_div_10pow21
  ]
  let env ← getEnv
  for nm in thms do
    let some ci := env.find? nm
      | throwError s!"AUDIT FAIL: {nm} not found in environment"
    let .thmInfo info := ci
      | throwError s!"AUDIT FAIL: {nm} is not a theorem"
    let some val := ci.value? (allowOpaque := true)
      | throwError s!"AUDIT FAIL: {nm} has no proof term"
    if val.hasSorry || info.value.hasSorry then
      throwError s!"AUDIT FAIL: {nm} contains sorry in proof term"
    let axs := (← collectAxioms nm).toList
    for ax in axs do
      if forbidden.contains ax then
        throwError s!"AUDIT FAIL: {nm} depends on forbidden axiom {ax}"
      if !allowed.contains ax then
        throwError s!"AUDIT FAIL: {nm} depends on non-standard axiom {ax}"
    IO.println s!"OK THM {nm}: axioms={axs}, hasSorry=false"
  let defs : List Name := [
    `Optim.BohrRadius.unitBidisc,
    `Optim.BohrRadius.IsSchur,
    `Optim.BohrRadius.HasBidiscCoefficients,
    `Optim.BohrRadius.finiteMajorant,
    `Optim.BohrRadius.IsBohrAdmissible,
    `Optim.BohrRadius.bohrRadius
  ]
  for nm in defs do
    let some (.defnInfo info) := env.find? nm
      | throwError s!"AUDIT FAIL: {nm} is not a definition"
    if info.safety != .safe then
      throwError s!"AUDIT FAIL: {nm} is not DefinitionSafety.safe"
    IO.println s!"OK DEF {nm}: DefinitionSafety.safe"
  IO.println "C59A_PROOF_AUDIT_PASS"

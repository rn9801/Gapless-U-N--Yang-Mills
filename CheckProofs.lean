module

import GaplessYangMills
import all GaplessYangMills.Action
import all GaplessYangMills.Decay
import all GaplessYangMills.DirectionalMean
import all GaplessYangMills.FiniteFilling
import all GaplessYangMills.Flux
import all GaplessYangMills.Lattice
import all GaplessYangMills.Marginal
import all GaplessYangMills.MarkedEdges
import all GaplessYangMills.Spectral
import all GaplessYangMills.Ward
import all GaplessYangMills.WeakCoupling
import all GaplessYangMills.Wilson
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

/-! Check the project's declarations against Lean and Mathlib's standard foundations. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let foundations : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in env.constants do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[index.toNat]!
    unless (`GaplessYangMills).isPrefixOf moduleName do continue
    -- Lean generates these executable helpers for inductive types.
    if let .str (.str typeName "ctorIdx") "_impl" := name then
      if let some (.inductInfo _) := env.find? typeName then continue
    audited := audited + 1
    if info.isUnsafe || info.isPartial then
      throwError "{name} is an unsafe or partial declaration"
    for dependency in ← Lean.collectAxioms name do
      unless foundations.contains dependency do
        throwError "{name} depends on {dependency}"
  if audited == 0 then
    throwError "No project declarations were found"
  logInfo m!"Checked {audited} declarations against the standard Lean foundations"

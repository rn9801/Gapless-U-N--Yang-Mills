module

import GaplessYangMills
import all GaplessYangMills.Action
import all GaplessYangMills.BadEvents
import all GaplessYangMills.BadPlaquetteEstimate
import all GaplessYangMills.CapGain
import all GaplessYangMills.CapVector
import all GaplessYangMills.CapVolume
import all GaplessYangMills.ComponentFlux
import all GaplessYangMills.Components
import all GaplessYangMills.ConnectedSetCounting
import all GaplessYangMills.ContinuumSplit
import all GaplessYangMills.CubeHolonomy
import all GaplessYangMills.CutFluxApproximation
import all GaplessYangMills.CutFluxBounds
import all GaplessYangMills.CutFluxMeasurability
import all GaplessYangMills.Decay
import all GaplessYangMills.DefectBounds
import all GaplessYangMills.DirectionalMean
import all GaplessYangMills.Duality
import all GaplessYangMills.Eigenangles
import all GaplessYangMills.FillingTranslations
import all GaplessYangMills.FiniteFilling
import all GaplessYangMills.FiniteGibbs
import all GaplessYangMills.FiniteWilson
import all GaplessYangMills.Flux
import all GaplessYangMills.GaugeAveraging
import all GaplessYangMills.Gluing
import all GaplessYangMills.GoodCubes
import all GaplessYangMills.GramTwist
import all GaplessYangMills.KernelCycleEstimate
import all GaplessYangMills.KernelQuadrature
import all GaplessYangMills.Lattice
import all GaplessYangMills.Marginal
import all GaplessYangMills.MarkedBoxes
import all GaplessYangMills.MarkedComponents
import all GaplessYangMills.MarkedEdges
import all GaplessYangMills.MeasurableRepair
import all GaplessYangMills.PeriodicKernelCycle
import all GaplessYangMills.PeriodicWilsonComparison
import all GaplessYangMills.RankOneTwist
import all GaplessYangMills.RankOneTwistLaw
import all GaplessYangMills.ShiftMeans
import all GaplessYangMills.ShortUnitaryProducts
import all GaplessYangMills.Spectral
import all GaplessYangMills.SphericalCap
import all GaplessYangMills.TorusSlices
import all GaplessYangMills.TraceCycle
import all GaplessYangMills.TracePowerOrder
import all GaplessYangMills.TransferForm
import all GaplessYangMills.UnitaryLog
import all GaplessYangMills.UnitarySphere
import all GaplessYangMills.Ward
import all GaplessYangMills.WeakCoupling
import all GaplessYangMills.Wilson
import all GaplessYangMills.WilsonBadPlaquettes
import all GaplessYangMills.WilsonKernel
import all GaplessYangMills.WilsonLimits
import all GaplessYangMills.WilsonSliceKernel
import all GaplessYangMills.WilsonTranslations
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

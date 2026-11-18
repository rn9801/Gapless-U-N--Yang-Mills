module

public import GaplessYangMills.FiniteWilson
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Compactness.CountablyCompact

/-!
# Periodic thermodynamic subsequences

Periodic configurations are mapped to the full product of unitary positive
links. Compactness and metrizability of probability convergence give a
subsequence along even side lengths.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal

noncomputable section

abbrev InfiniteConfig (N : ℕ) := (Axis × Site) → UnitaryMatrix N

def extendPeriodic {L N : ℕ} (U : TorusConfig L N) : InfiniteConfig N :=
  fun (i, x) => U (i, fun j => (x j : ZMod L))

theorem continuous_extendPeriodic (L N : ℕ) :
    Continuous (extendPeriodic : TorusConfig L N → InfiniteConfig N) := by
  apply continuous_pi
  rintro ⟨i, x⟩
  exact continuous_apply (i, fun j => (x j : ZMod L))

def extendedWilson (L N : ℕ) [NeZero L] (β : ℝ) : ProbabilityMeasure (InfiniteConfig N) :=
  ProbabilityMeasure.map (⟨periodicWilson L N β, inferInstance⟩ :
    ProbabilityMeasure (TorusConfig L N)) extendPeriodic

def evenLength (n : ℕ) : ℕ := 2 * (n + 2)

instance evenLength_neZero (n : ℕ) : NeZero (evenLength n) :=
  ⟨by unfold evenLength; omega⟩

/-- Periodic Wilson measures at even side lengths (L\ge4) have a weakly
convergent subsequence in the full configuration space. -/
theorem exists_periodicWilson_limit (N : ℕ) (β : ℝ) :
    ∃ (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ), StrictMono l ∧
      Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ) := by
  have : MetrizableSpace (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (MetrizableSpace (Fin N → Fin N → ℂ))
  have : MetrizableSpace (UnitaryMatrix N) :=
    (Topology.IsEmbedding.subtypeVal (p := fun U : Matrix (Fin N) (Fin N) ℂ =>
      U ∈ unitary (Matrix (Fin N) (Fin N) ℂ))).metrizableSpace
  have h : IsSeqCompact (Set.univ : Set (ProbabilityMeasure (InfiniteConfig N))) :=
    isCompact_univ.isSeqCompact
  obtain ⟨μ, _, l, hl, hμ⟩ := h
    (x := fun n => extendedWilson (evenLength n) N β) (fun _ => Set.mem_univ _)
  exact ⟨μ, l, hl, hμ⟩

/-- An upper bound on an open cylinder event passes to the weak limit. -/
theorem weakLimit_open_bound {N : ℕ} (μs : ℕ → ProbabilityMeasure (InfiniteConfig N))
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hμ : Tendsto μs atTop (𝓝 μ))
    (E : Set (InfiniteConfig N)) (hE : IsOpen E) (C : ℝ≥0∞)
    (hC : ∀ n, (μs n : Measure (InfiniteConfig N)) E ≤ C) :
    (μ : Measure (InfiniteConfig N)) E ≤ C := by
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hE).trans ?_
  apply liminf_le_of_le
  · use 0
    simp
  · intro c hc
    obtain ⟨n, hn⟩ := hc.exists
    exact hn.trans (hC n)

end

end GaplessYangMills

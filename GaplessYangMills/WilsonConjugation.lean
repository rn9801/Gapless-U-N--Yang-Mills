module

public import GaplessYangMills.WilsonTranslations
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Complex conjugation of Wilson laws

Entrywise conjugation preserves Haar probability and the real
plaquette trace. This symmetry passes to periodic weak limits.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped Topology

noncomputable section

def unitaryConjugate (N : ℕ) : UnitaryMatrix N →* UnitaryMatrix N where
  toFun := Matrix.UnitaryGroup.map_star
  map_one' := by
    apply Subtype.ext
    exact Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)
  map_mul' U V := by
    apply Subtype.ext
    change (U.val * V.val).map (starRingEnd ℂ) = U.val.map (starRingEnd ℂ) * V.val.map (starRingEnd ℂ)
    exact Matrix.map_mul

theorem unitaryConjugate_involutive (N : ℕ) : Function.Involutive (unitaryConjugate N) := by
  intro U
  apply Matrix.UnitaryGroup.ext
  intro i j
  change star (star (U i j)) = U i j
  exact star_star _

theorem continuous_unitaryConjugate (N : ℕ) : Continuous (unitaryConjugate N) := by
  apply Continuous.subtype_mk
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact Complex.continuous_conj.comp ((continuous_apply j).comp
    ((continuous_apply i).comp continuous_subtype_val))

theorem unitaryHaar_conjugate_preserving (N : ℕ) :
    MeasurePreserving (unitaryConjugate N) (unitaryHaar N) (unitaryHaar N) := by
  let : (unitaryHaar N).IsHaarMeasure := by unfold unitaryHaar; infer_instance
  exact MonoidHom.measurePreserving (continuous_unitaryConjugate N) (unitaryConjugate_involutive N).surjective rfl

def conjugateLinks {P : Type*} {N : ℕ} (U : P → UnitaryMatrix N) : P → UnitaryMatrix N :=
  fun p => unitaryConjugate N (U p)

theorem continuous_conjugateLinks (P : Type*) (N : ℕ) :
    Continuous (conjugateLinks : (P → UnitaryMatrix N) → P → UnitaryMatrix N) :=
  continuous_pi fun p => (continuous_unitaryConjugate N).comp (continuous_apply p)

theorem unitaryConjugate_trace {N : ℕ} (U : UnitaryMatrix N) :
    (unitaryConjugate N U).val.trace = star U.val.trace := by
  change ∑ i : Fin N, (starRingEnd ℂ) (U i i) = (starRingEnd ℂ) (∑ i : Fin N, U i i)
  exact (map_sum (starRingEnd ℂ) _ _).symm

theorem periodicLogWeight_conjugate {L N : ℕ} [NeZero L] (β : ℝ) (U : TorusConfig L N) :
    periodicLogWeight β (conjugateLinks U) = periodicLogWeight β U := by
  have hh (I : Face) (x : TorusSite L) :
      periodicHolonomy (conjugateLinks U) I x = unitaryConjugate N (periodicHolonomy U I x) := by
    cases I <;> simp only [conjugateLinks, periodicHolonomy, Face.axes, map_mul, map_inv]
  simp only [periodicLogWeight, hh, unitaryConjugate_trace, Complex.star_def, Complex.conj_re]

theorem periodicWilson_conjugate_preserving {L N : ℕ} [NeZero L] (β : ℝ) :
    MeasurePreserving (conjugateLinks : TorusConfig L N → TorusConfig L N)
      (periodicWilson L N β) (periodicWilson L N β) :=
  periodicWilson_preserving_of_logWeight β _ (measurePreserving_pi (fun _ => unitaryHaar N)
    (fun _ => unitaryHaar N) (fun _ => unitaryHaar_conjugate_preserving N)) (periodicLogWeight_conjugate β)

theorem extendedWilson_conjugate {L N : ℕ} [NeZero L] (β : ℝ) :
    ProbabilityMeasure.map (extendedWilson L N β) conjugateLinks = extendedWilson L N β := by
  apply Subtype.ext
  change Measure.map conjugateLinks (Measure.map extendPeriodic (periodicWilson L N β)) =
    Measure.map extendPeriodic (periodicWilson L N β)
  have he := (continuous_extendPeriodic L N).measurable
  have hc := periodicWilson_conjugate_preserving (L := L) (N := N) β
  have hf : (conjugateLinks : InfiniteConfig N → InfiniteConfig N) ∘ (extendPeriodic (L := L)) =
      extendPeriodic ∘ conjugateLinks := rfl
  rw [Measure.map_map (continuous_conjugateLinks (Axis × Site) N).measurable he, hf,
    ← Measure.map_map he hc.measurable, hc.map_eq]

theorem periodicWilson_limit_conjugate {N : ℕ} (β : ℝ) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ProbabilityMeasure.map μ conjugateLinks = μ := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ
    (continuous_conjugateLinks (Axis × Site) N)
  simp only [extendedWilson_conjugate] at h
  exact tendsto_nhds_unique h hμ

end

end GaplessYangMills

module

public import GaplessYangMills.MarkedEdges
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# From the modified partition-function bound to the bad-face estimate

A positive product weight exceeding an exponential threshold on the all-bad
event gives a probability estimate by integration. It suffices to have the
modified partition-function bound for sets of one orientation.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped ENNReal

theorem largest_orientation (S : Finset Plaquette) :
    ∃ I : Face, S.card ≤ 6 * (S.filter fun p => p.1 = I).card := by
  classical
  have hcard : Fintype.card Face = 6 := by decide
  have hcount : S.card = ∑ I : Face, (S.filter fun p => p.1 = I).card :=
    Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _
  by_contra! h
  have hlt : (∑ I : Face, 6 * (S.filter fun p => p.1 = I).card) <
      ∑ _I : Face, S.card := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨.xy, Finset.mem_univ _⟩
    · intro I _
      exact h I
  rw [← Finset.mul_sum, ← hcount] at hlt
  simp [hcard] at hlt

theorem measurable_allBad {Ω : Type*} [MeasurableSpace Ω] (bad : Plaquette → Set Ω)
    (hbad : ∀ p, MeasurableSet (bad p)) (S : Finset Plaquette) :
    MeasurableSet (allBad bad S) := by
  have h : allBad bad S = ⋂ p ∈ S, bad p := by
    ext ω
    simp [allBad]
  rw [h]
  exact MeasurableSet.biInter S.finite_toSet.countable fun p _ => hbad p

theorem badEvent_le_of_productExpectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad : Plaquette → Set Ω) (hbad : ∀ p, MeasurableSet (bad p))
    (M : Plaquette → Ω → ℝ≥0∞) (a : ℝ)
    (hM : ∀ p ω, ω ∈ bad p → ENNReal.ofReal (Real.exp a) ≤ M p ω)
    (S : Finset Plaquette)
    (hExpectation : (∫⁻ ω, (∏ p ∈ S, M p ω) ∂μ) ≤ 1) :
    μ (allBad bad S) ≤ ENNReal.ofReal (Real.exp (-a * S.card)) := by
  let threshold := ENNReal.ofReal (Real.exp (a * S.card))
  have htest : (allBad bad S).indicator (fun _ => threshold) ≤ (fun ω => ∏ p ∈ S, M p ω) := by
    intro ω
    by_cases hω : ω ∈ allBad bad S
    · rw [Set.indicator_of_mem hω]
      calc
        threshold = ∏ _p ∈ S, ENNReal.ofReal (Real.exp a) := by
          unfold threshold
          rw [Finset.prod_const, mul_comm a, Real.exp_nat_mul,
            ENNReal.ofReal_pow (Real.exp_nonneg _)]
        _ ≤ _ := Finset.prod_le_prod fun p hp => hM p ω (hω p hp)
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have hmul := (lintegral_mono htest).trans hExpectation
  rw [lintegral_indicator_const (measurable_allBad bad hbad S), mul_comm] at hmul
  have hle := ENNReal.le_inv_iff_mul_le.mpr hmul
  change μ (allBad bad S) ≤ (ENNReal.ofReal (Real.exp (a * S.card)))⁻¹ at hle
  rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg] at hle
  simpa only [neg_mul] using hle

/-- The full joint estimate follows from one-orientation expectations and
the pointwise lower bound of the modified weight on bad faces. -/
theorem badEvent_le_of_orientationExpectations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (bad : Plaquette → Set Ω) (hbad : ∀ p, MeasurableSet (bad p))
    (M : Plaquette → Ω → ℝ≥0∞) (a : ℝ) (ha : 0 ≤ a)
    (hM : ∀ p ω, ω ∈ bad p → ENNReal.ofReal (Real.exp a) ≤ M p ω)
    (hExpectation : ∀ (I : Face) (S : Finset Plaquette), (∀ p ∈ S, p.1 = I) →
      (∫⁻ ω, (∏ p ∈ S, M p ω) ∂μ) ≤ 1) (S : Finset Plaquette) :
    μ (allBad bad S) ≤ ENNReal.ofReal (Real.exp (-(a / 6) * S.card)) := by
  classical
  obtain ⟨I, hI⟩ := largest_orientation S
  let T := S.filter fun p => p.1 = I
  have hT : ∀ p ∈ T, p.1 = I := fun _ hp => (Finset.mem_filter.mp hp).2
  have hsub : allBad bad S ⊆ allBad bad T :=
    fun _ hω p hp => hω p (Finset.mem_filter.mp hp).1
  refine (measure_mono hsub).trans
    ((badEvent_le_of_productExpectation μ bad hbad M a hM T (hExpectation I T hT)).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hIR : (S.card : ℝ) ≤ 6 * (T.card : ℝ) := by exact_mod_cast hI
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hIR)]

end GaplessYangMills

module

public import GaplessYangMills.CutFluxBounds
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Averaging the repaired flux

The cut average is defined for any probability law concentrated on the
allowed cuts. The cut-independent error bound survives this averaging.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

private theorem add_step_coordinate_bounds (y : Site) (j i : Axis) :
    y i ≤ (y + step j) i ∧ (y + step j) i ≤ y i + 1 := by
  simp only [Pi.add_apply, step]
  split <;> omega

private theorem plaquetteHolonomy_congr_box {N : ℕ} (U V : InfiniteConfig N)
    (x y : Site) (r : ℕ) (I : Face)
    (hy : ∀ i, x i - (r : ℤ) ≤ y i ∧ y i ≤ x i + r)
    (h : ∀ e ∈ edgesNearVertex x (r + 1), U (e.2, e.1) = V (e.2, e.1)) :
    plaquetteHolonomy (fun j z => U (j, z)) I y = plaquetteHolonomy (fun j z => V (j, z)) I y := by
  have h₀ (j : Axis) : U (j, y) = V (j, y) := by
    apply h (y, j) ((mem_edgesNearVertex_iff _ _ _).mpr ?_)
    intro i
    have hi := hy i
    simp only [Nat.cast_add, Nat.cast_one]
    omega
  have h₁ (j k : Axis) : U (j, y + step k) = V (j, y + step k) := by
    apply h (y + step k, j) ((mem_edgesNearVertex_iff _ _ _).mpr ?_)
    intro i
    have hi := hy i
    have hb := add_step_coordinate_bounds y k i
    simp only [Nat.cast_add, Nat.cast_one]
    omega
  cases I <;> simp [plaquetteHolonomy, Face.axes, h₀, h₁]

/-- The truncation is local in the original link variables. -/
theorem repairedCutFluxApprox_congr_box {N : ℕ} (R : ℕ) (I : Face) (x : Site)
    (U V : InfiniteConfig N) (η : TwoForm ℝ)
    (h : ∀ e ∈ edgesNearVertex x (4 * R + 4), U (e.2, e.1) = V (e.2, e.1)) :
    repairedCutFluxApprox R (fun j y => U (j, y)) η I x =
      repairedCutFluxApprox R (fun j y => V (j, y)) η I x := by
  let a (A : InfiniteConfig N) := liftFlux η (plaquetteEigenangles (fun j y => A (j, y)))
  let r := 4 * R + 2
  have hplaquette (J : Face) (y : Site)
      (hy : ∀ i, x i - ((r + 1 : ℕ) : ℤ) ≤ y i ∧ y i ≤ x i + (r + 1 : ℕ)) :
      a U J y = a V J y := by
    have hb : ∀ e ∈ edgesNearVertex x (r + 1 + 1), U (e.2, e.1) = V (e.2, e.1) := h
    simp only [a, liftFlux_eq_eigenAngleLift, plaquetteHolonomy_congr_box U V x y (r + 1) J hy hb]
  have hc (c : Cube) (y : Site)
      (hy : ∀ i, x i - (r : ℤ) ≤ y i ∧ y i ≤ x i + r) :
      defect (a U) c y = defect (a V) c y := by
    have h₀ (J : Face) : a U J y = a V J y := hplaquette J y fun i => by
      have hi := hy i
      push_cast
      omega
    have h₁ (J : Face) (j : Axis) : a U J (y + step j) = a V J (y + step j) :=
      hplaquette J (y + step j) fun i => by
        have hi := hy i
        have hb := add_step_coordinate_bounds y j i
        push_cast
        omega
    have hd : d₂ (a U) c y = d₂ (a V) c y := by
      cases c <;> simp only [d₂, diff, Pi.add_apply, Pi.sub_apply, h₀, h₁]
    simp only [defect, hd]
  have hfill : fillDefectApprox (defect (a U)) R I x = fillDefectApprox (defect (a V)) R I x := by
    apply fillDefectApprox_congr_on
    intro e he
    obtain ⟨y, j⟩ := e
    have hy : ∀ i, x i - (r : ℤ) ≤ (-y) i ∧ (-y) i ≤ x i + r := by
      intro i
      have hi := (mem_edgesNearVertex_iff _ _ _).mp he i
      simp only [Pi.neg_apply] at hi ⊢
      omega
    simp only [dualCurrent, hc _ _ hy]
  have hbase : a U I x = a V I x := hplaquette I x fun i => by omega
  change a U I x - 2 * Real.pi * (fillDefectApprox (defect (a U)) R I x : ℝ) =
    a V I x - 2 * Real.pi * (fillDefectApprox (defect (a V)) R I x : ℝ)
  rw [hbase, hfill]

theorem measurable_repairedCutFluxApprox_coordinate {N : ℕ} (R : ℕ) (I : Face) (x : Site) :
    Measurable (fun p : InfiniteConfig N × TwoForm ℝ =>
      repairedCutFluxApprox R (fun j y => p.1 (j, y)) p.2 I x) := by
  let a (p : InfiniteConfig N × TwoForm ℝ) :=
    liftFlux p.2 (plaquetteEigenangles (fun j y => p.1 (j, y)))
  let q (p : InfiniteConfig N × TwoForm ℝ) := defect (a p)
  have hf : Measurable (fun p => fillDefectApprox (q p) R I x) := by
    unfold fillDefectApprox
    exact Finset.measurable_sum _ fun S _ => measurable_certifiedFillValue _
      (measurable_dualCurrent_coordinate q measurable_cutDefect_coordinate) S I x
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  exact (measurable_cutFlux_coordinate I x).sub (measurable_const.mul (hcast.comp hf))

theorem repairedCutFluxApprox_bounded (N R : ℕ) (I : Face) (x : Site) :
    ∃ M : ℝ, ∀ (U : InfiniteConfig N) (η : TwoForm ℝ), (∀ J y, |η J y| ≤ Real.pi / 16) →
      |repairedCutFluxApprox R (fun j y => U (j, y)) η I x| ≤ M := by
  let C := boundedBoxCover (-x) R
  let b (S : Finset OrientedEdge) := 20 * (4 * (N : ℝ)) * ((S.card : ℝ) + 1) ^ 2
  refine ⟨N * (17 * Real.pi / 16) + (2 * Real.pi) * ∑ S ∈ C, b S, fun U η hη => ?_⟩
  let V : OneForm (UnitaryMatrix N) := fun j y => U (j, y)
  let a := liftFlux η (plaquetteEigenangles V)
  let q := defect a
  have hdiv (y : Site) : currentDivergence (dualCurrent q) y = 0 := by
    rw [currentDivergence_dualCurrent, plaquetteDefect_closed V η, Pi.zero_apply]
  have hfill : |(fillDefectApprox q R I x : ℝ)| ≤ ∑ S ∈ C, b S := by
    unfold fillDefectApprox
    push_cast
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
    have hB := natAbs_certifiedFillValue_le (dualCurrent q) S I x hdiv (4 * N) (natAbs_cutDefect_le V η hη)
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    simpa only [b, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
      (Nat.cast_le (α := ℝ)).mpr hB
  change |a I x - (2 * Real.pi) * (fillDefectApprox q R I x : ℝ)| ≤ _
  rw [sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul, abs_of_nonneg Real.two_pi_pos.le]
  exact add_le_add (abs_liftFlux_le η _ I x (hη I x)) (mul_le_mul_of_nonneg_left hfill Real.two_pi_pos.le)

section Average

variable {N : ℕ} (ν : Measure (TwoForm ℝ))

def averagedFlux (U : InfiniteConfig N) (I : Face) (x : Site) : ℝ :=
  ∫ η, repairedCutFlux (fun j y => U (j, y)) η I x ∂ν

def averagedFluxApprox (R : ℕ) (U : InfiniteConfig N) (I : Face) (x : Site) : ℝ :=
  ∫ η, repairedCutFluxApprox R (fun j y => U (j, y)) η I x ∂ν

theorem measurable_averagedFlux [SFinite ν] (I : Face) (x : Site) :
    Measurable (fun U : InfiniteConfig N => averagedFlux ν U I x) :=
  (measurable_repairedCutFlux_coordinate I x).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_averagedFluxApprox [SFinite ν] (R : ℕ) (I : Face) (x : Site) :
    Measurable (fun U : InfiniteConfig N => averagedFluxApprox ν R U I x) :=
  (measurable_repairedCutFluxApprox_coordinate R I x).stronglyMeasurable.integral_prod_right'.measurable

variable [IsProbabilityMeasure ν] (hν : ∀ᵐ η ∂ν, ∀ J y, |η J y| ≤ Real.pi / 16)

include hν in
theorem integrable_cutFluxApprox (R : ℕ) (U : InfiniteConfig N) (I : Face) (x : Site) :
    Integrable (fun η => repairedCutFluxApprox R (fun j y => U (j, y)) η I x) ν := by
  obtain ⟨M, hM⟩ := repairedCutFluxApprox_bounded N R I x
  have hm := (measurable_repairedCutFluxApprox_coordinate (N := N) R I x).comp
    (measurable_prodMk_left (x := U))
  exact Integrable.of_bound hm.aestronglyMeasurable M
    (hν.mono fun η hη => by simpa only [Real.norm_eq_abs] using hM U η hη)

include hν in
theorem averagedFluxApprox_bounded (R : ℕ) (I : Face) (x : Site) :
    ∃ M : ℝ, ∀ U : InfiniteConfig N, |averagedFluxApprox ν R U I x| ≤ M := by
  obtain ⟨M, hM⟩ := repairedCutFluxApprox_bounded N R I x
  refine ⟨M, fun U => ?_⟩
  unfold averagedFluxApprox
  refine abs_integral_le_integral_abs.trans ?_
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using
    integral_mono_ae (integrable_cutFluxApprox ν hν R U I x).abs (integrable_const M)
      (hν.mono fun η hη => hM U η hη)

omit [IsProbabilityMeasure ν] in
theorem averagedFluxApprox_congr_box (R : ℕ) (I : Face) (x : Site) (U V : InfiniteConfig N)
    (h : ∀ e ∈ edgesNearVertex x (4 * R + 4), U (e.2, e.1) = V (e.2, e.1)) :
    averagedFluxApprox ν R U I x = averagedFluxApprox ν R V I x :=
  integral_congr_ae (ae_of_all _ fun η => repairedCutFluxApprox_congr_box R I x U V η h)

include hν in
theorem integrable_cutFlux_periodicLimit_ae (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂μ.toMeasure, ∀ I x, Integrable (fun η => repairedCutFlux (fun j y => U (j, y)) η I x) ν := by
  filter_upwards [repairedCutFluxApprox_eventually_eq_periodicLimit hN hβ μ l hl hμ] with U hU
  intro I x
  obtain ⟨R, hR⟩ := hU I x
  exact (integrable_cutFluxApprox ν hν R U I x).congr
    (hν.mono fun η hη => hR R le_rfl η hη)

theorem d₂_integral {Ω : Type*} [MeasurableSpace Ω] (m : Measure Ω)
    (f : Ω → TwoForm ℝ) (hf : ∀ J y, Integrable (fun ω => f ω J y) m) (c : Cube) (x : Site) :
    d₂ (fun J y => ∫ ω, f ω J y ∂m) c x = ∫ ω, d₂ (f ω) c x ∂m := by
  have hdiff (i : Axis) (I : Face) : Integrable (fun ω => diff i (f ω I) x) m :=
    (hf I (x + step i)).sub (hf I x)
  have hd (i : Axis) (I : Face) :
      (∫ ω, diff i (f ω I) x ∂m) = diff i (fun y => ∫ ω, f ω I y ∂m) x :=
    integral_sub (hf I (x + step i)) (hf I x)
  have h (i : Axis) (I : Face) (j : Axis) (J : Face) (k : Axis) (K : Face) :
      (∫ ω, diff i (f ω I) x - diff j (f ω J) x + diff k (f ω K) x ∂m) =
        diff i (fun y => ∫ ω, f ω I y ∂m) x - diff j (fun y => ∫ ω, f ω J y ∂m) x +
          diff k (fun y => ∫ ω, f ω K y ∂m) x := by
    have hij : Integrable (fun ω => diff i (f ω I) x - diff j (f ω J) x) m :=
      (hdiff i I).sub (hdiff j J)
    rw [integral_add hij (hdiff k K), integral_sub (hdiff i I) (hdiff j J), hd, hd, hd]
  cases c <;> exact (h _ _ _ _ _ _).symm

include hν in
theorem averagedFlux_closed_periodicLimit_ae (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂μ.toMeasure, d₂ (averagedFlux ν U) = 0 := by
  filter_upwards [repairedCutFlux_closed_periodicLimit_ae hN hβ μ l hl hμ,
    integrable_cutFlux_periodicLimit_ae ν hν hN hβ μ l hl hμ] with U hU hi
  funext c x
  unfold averagedFlux
  rw [d₂_integral ν _ hi]
  have hz : (fun η => d₂ (repairedCutFlux (fun j y => U (j, y)) η) c x) =ᵐ[ν] 0 :=
    hν.mono fun η hη => congrFun (congrFun (hU η hη).2 c) x
  rw [integral_congr_ae hz, Pi.zero_apply, Pi.zero_apply]
  exact integral_zero _ _

include hν in
theorem abs_averagedFlux_sub_approx_le_periodicLimit_ae (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂μ.toMeasure, ∀ I x R,
      |averagedFlux ν U I x - averagedFluxApprox ν R U I x| ≤ cutFluxErrorBound R x U := by
  filter_upwards [abs_repairedCutFlux_sub_approx_le_periodicLimit_ae hN hβ μ l hl hμ,
    integrable_cutFlux_periodicLimit_ae ν hν hN hβ μ l hl hμ] with U hU hi
  intro I x R
  have ha := integrable_cutFluxApprox ν hν R U I x
  unfold averagedFlux averagedFluxApprox
  rw [← integral_sub (hi I x) ha]
  refine abs_integral_le_integral_abs.trans ?_
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, Pi.sub_apply] using
    integral_mono_ae ((hi I x).sub ha).abs (integrable_const (cutFluxErrorBound R x U))
      (hν.mono fun η hη => hU I x R η hη)

include hν in
/-- Equation (4), using radius `4 * R + 4` in the original link lattice. -/
theorem averagedFlux_exponential_approximation_periodicLimit (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    (∃ C : ℝ, 0 < C ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ I x R,
      eLpNorm ((fun U => averagedFlux ν U I x) - (fun U => averagedFluxApprox ν R U I x)) 2 μ.toMeasure ≤
        ENNReal.ofReal (C * t ^ R)) ∧
    ∀ I x, MemLp (fun U => averagedFlux ν U I x) 2 μ.toMeasure ∧
      ∃ M : ℝ, ∀ R, eLpNorm (fun U => averagedFluxApprox ν R U I x) 2 μ.toMeasure ≤ ENNReal.ofReal M := by
  obtain ⟨C, hC, t, ht₀, ht, hbound⟩ := eLpNorm_cutFluxErrorBound_periodicLimit_le hN hβ μ l hl hμ
  have he (I : Face) (x : Site) (R : ℕ) :
      eLpNorm ((fun U => averagedFlux ν U I x) - (fun U => averagedFluxApprox ν R U I x)) 2 μ.toMeasure ≤
        ENNReal.ofReal (C * t ^ R) := by
    refine (eLpNorm_mono_ae ((measurable_averagedFlux ν I x).sub
      (measurable_averagedFluxApprox ν R I x)).aestronglyMeasurable ?_).trans (hbound x R)
    filter_upwards [abs_averagedFlux_sub_approx_le_periodicLimit_ae ν hν hN hβ μ l hl hμ] with U hU
    rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_of_nonneg (cutFluxErrorBound_nonneg R x U)]
    exact hU I x R
  refine ⟨⟨C, hC, t, ht₀, ht, he⟩, fun I x => ?_⟩
  let F (U : InfiniteConfig N) := averagedFlux ν U I x
  let A (R : ℕ) (U : InfiniteConfig N) := averagedFluxApprox ν R U I x
  have hA (R : ℕ) : Measurable (A R) := measurable_averagedFluxApprox ν R I x
  have hE : MemLp (F - A 0) 2 μ.toMeasure :=
    (he I x 0).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨M₀, hM₀⟩ := averagedFluxApprox_bounded ν hν 0 I x
  have hA₀ : MemLp (A 0) 2 μ.toMeasure := MemLp.of_bound (hA 0).aestronglyMeasurable M₀
    (ae_of_all _ fun U => by simpa only [Real.norm_eq_abs] using hM₀ U)
  have hF₂ : MemLp F 2 μ.toMeasure := by simpa only [sub_add_cancel] using hE.add hA₀
  refine ⟨hF₂, (eLpNorm F 2 μ.toMeasure).toReal + C, fun R => ?_⟩
  have hAR : A R = F + (A R - F) := by abel
  calc
    _ ≤ eLpNorm F 2 μ.toMeasure + eLpNorm (A R - F) 2 μ.toMeasure := by
      change eLpNorm (A R) 2 μ.toMeasure ≤ _
      exact congrArg (fun g => eLpNorm g 2 μ.toMeasure) hAR ▸
        eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ eLpNorm F 2 μ.toMeasure + ENNReal.ofReal (C * t ^ R) := by
      rw [eLpNorm_sub_comm]
      exact add_le_add_right (he I x R) _
    _ ≤ ENNReal.ofReal ((eLpNorm F 2 μ.toMeasure).toReal + C) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hC.le, ENNReal.ofReal_toReal hF₂.eLpNorm_ne_top]
      apply add_le_add_right (ENNReal.ofReal_le_ofReal ?_) _
      exact mul_le_of_le_one_right hC.le (pow_le_one₀ ht₀ ht.le)

end Average

end

end GaplessYangMills

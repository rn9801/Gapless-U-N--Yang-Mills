module

public import GaplessYangMills.PeriodicKernelCycle
public import GaplessYangMills.TorusSlices
public import GaplessYangMills.WilsonSliceKernel
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Modified Wilson partition functions

Temporal faces carry independent factors from the selected twist law.
Integration over the normal links gives the gauge averages of the slice kernels.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.L2Operator

noncomputable section

abbrev TorusPlaquette (L : ℕ) := Face × TorusSite L
abbrev SpatialFace (τ : Axis) := {I : Face // I.axes.1 ≠ τ ∧ I.axes.2 ≠ τ}
abbrev TemporalFace (τ : Axis) := {I : Face // ¬ (I.axes.1 ≠ τ ∧ I.axes.2 ≠ τ)}

private def temporalFaceAxis {τ : Axis} (I : TemporalFace τ) : SpatialAxis τ :=
  if h : I.val.axes.1 = τ then ⟨I.val.axes.2, fun h' => by
    have hne : I.val.axes.1 ≠ I.val.axes.2 := by cases I.val <;> decide
    exact hne (h.trans h'.symm)⟩
  else ⟨I.val.axes.1, h⟩

/-- Each spatial direction determines one temporal plaquette orientation. -/
private def temporalFaceEquiv (τ : Axis) : TemporalFace τ ≃ SpatialAxis τ :=
  Equiv.ofBijective temporalFaceAxis (by fin_cases τ <;> decide)

private def torusPlaquetteEquiv (L : ℕ) (τ : Axis) :
    ZMod L × Face × SpatialSite L τ ≃ TorusPlaquette L where
  toFun p := (p.2.1, torusSliceSite τ p.1 p.2.2)
  invFun p := (p.2 τ, p.1, fun i => p.2 i)
  left_inv p := by simp
  right_inv p := by
    refine Prod.ext rfl ?_
    exact (torusSliceSiteEquiv L τ).right_inv p.2

private def slicePlaquetteEquiv (L : ℕ) (τ : Axis) :
    ((SpatialFace τ × SpatialSite L τ) ⊕ SpatialLink L τ) ≃ Face × SpatialSite L τ :=
  (Equiv.sumProdDistrib _ _ _).symm.trans
    (((Equiv.sumCongr (Equiv.refl _) (temporalFaceEquiv τ).symm).trans
      (Equiv.sumCompl (fun I : Face => I.axes.1 ≠ τ ∧ I.axes.2 ≠ τ))).prodCongr (Equiv.refl _))

private theorem fundamentalKernel_one_inv {N : ℕ} (β : ℝ) (P : UnitaryMatrix N) :
    fundamentalKernel β P⁻¹ 1 = fundamentalKernel β P 1 := by
  have h := fundamentalKernel_rightInvariant β P P⁻¹ 1
  simpa only [inv_mul_cancel, one_mul, fundamentalKernel_symm β 1 P] using h.symm

private theorem fundamentalKernel_one_conj {N : ℕ} (β : ℝ) (P Q : UnitaryMatrix N) :
    fundamentalKernel β (Q * P * Q⁻¹) 1 = fundamentalKernel β P 1 := by
  calc
    _ = fundamentalKernel β (Q * P) (Q * 1) := by
      simpa only [mul_inv_cancel, mul_one] using fundamentalKernel_rightInvariant β Q⁻¹ (Q * P) Q
    _ = _ := fundamentalKernel_leftInvariant β Q P 1

private theorem fundamentalKernel_mulInv_one {N : ℕ} (β : ℝ) (A B : UnitaryMatrix N) :
    fundamentalKernel β (A * B⁻¹) 1 = fundamentalKernel β A B := by
  simpa only [mul_inv_cancel] using fundamentalKernel_rightInvariant β B⁻¹ A B

private theorem periodicHolonomy_assembly_temporal {L N : ℕ} {τ : Axis}
    (A : TorusSliceCoords L N τ) (t : ZMod L) (i : SpatialAxis τ) (x : SpatialSite L τ)
    (F : UnitaryMatrix N → ℝ) (hF : ∀ P, F P⁻¹ = F P) :
    F (periodicHolonomy (periodicSliceAssembly L N τ A)
      ((temporalFaceEquiv τ).symm i).val (torusSliceSite τ t x)) =
        F (A.1 t (i, x) * ((A.2 t • A.1 (t + 1)) (i, x))⁻¹) := by
  let I := (temporalFaceEquiv τ).symm i
  have haxis : temporalFaceAxis I = i := (temporalFaceEquiv τ).apply_symm_apply i
  change F (periodicHolonomy (periodicSliceAssembly L N τ A) I.val (torusSliceSite τ t x)) = _
  by_cases hi : I.val.axes.1 = τ
  · have hj : I.val.axes.2 ≠ τ := by
      intro hj
      have hne : I.val.axes.1 ≠ I.val.axes.2 := by cases I.val <;> decide
      exact hne (hi.trans hj.symm)
    rw [periodicHolonomy_assembly_timeFirst A t I.val x hi hj, hF]
    simp only [temporalFaceAxis, dite_eq_left hi] at haxis
    rw [haxis]
  · have hj : I.val.axes.2 = τ := by by_contra hn; exact I.property ⟨hi, hn⟩
    rw [periodicHolonomy_assembly_timeSecond A t I.val x hi hj]
    simp only [temporalFaceAxis, dite_eq_right hi] at haxis
    rw [haxis]

private def spatialPlaquetteKernel {L N : ℕ} {τ : Axis} (β : ℝ) (A : SliceConfig L N τ)
    (p : SpatialFace τ × SpatialSite L τ) : ℝ :=
  fundamentalKernel β
    (sliceHolonomy A ⟨p.1.val.axes.1, p.1.property.1⟩ ⟨p.1.val.axes.2, p.1.property.2⟩ p.2) 1

private theorem continuous_spatialPlaquetteKernel {L N : ℕ} {τ : Axis} (β : ℝ)
    (p : SpatialFace τ × SpatialSite L τ) :
    Continuous (fun A : SliceConfig L N τ => spatialPlaquetteKernel β A p) := by
  let i : SpatialAxis τ := ⟨p.1.val.axes.1, p.1.property.1⟩
  let j : SpatialAxis τ := ⟨p.1.val.axes.2, p.1.property.2⟩
  let x := p.2
  have h : Continuous (fun A : SliceConfig L N τ => sliceHolonomy A i j x) :=
    (((continuous_apply (i, x)).mul (continuous_apply (j, x + spatialStep L i))).mul
      (continuous_apply (i, x + spatialStep L j)).inv).mul (continuous_apply (j, x)).inv
  have hp : Continuous (fun A : SliceConfig L N τ => (sliceHolonomy A i j x, (1 : UnitaryMatrix N))) :=
    h.prodMk continuous_const
  simpa only [Function.comp_def, spatialPlaquetteKernel, i, j, x] using
    (continuous_fundamentalKernel (N := N) β).comp hp

/-- Half of the spatial Boltzmann weight, assigned to each adjacent step. -/
private def sliceHalfWeight {L N : ℕ} {τ : Axis} [NeZero L] (β : ℝ) (A : SliceConfig L N τ) : ℝ :=
  ∏ p : SpatialFace τ × SpatialSite L τ, Real.sqrt (spatialPlaquetteKernel β A p)

private theorem continuous_sliceHalfWeight {L N : ℕ} {τ : Axis} [NeZero L] (β : ℝ) :
    Continuous (sliceHalfWeight (L := L) (N := N) (τ := τ) β) :=
  continuous_finsetProd _ fun p _ => (continuous_spatialPlaquetteKernel β p).sqrt

private theorem sliceHalfWeight_mul_self {L N : ℕ} {τ : Axis} [NeZero L]
    (β : ℝ) (A : SliceConfig L N τ) :
    sliceHalfWeight β A * sliceHalfWeight β A =
      ∏ p : SpatialFace τ × SpatialSite L τ, spatialPlaquetteKernel β A p := by
  unfold sliceHalfWeight
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun _ _ => Real.mul_self_sqrt (fundamentalKernel_pos β _ _).le

private theorem sliceHalfWeight_gauge {L N : ℕ} {τ : Axis} [NeZero L]
    (β : ℝ) (g : SliceGauge L N τ) (A : SliceConfig L N τ) :
    sliceHalfWeight β (applySliceGauge g A) = sliceHalfWeight β A := by
  unfold sliceHalfWeight
  apply Finset.prod_congr rfl
  intro p _
  have h := sliceHolonomy_gauge A g ⟨p.1.val.axes.1, p.1.property.1⟩
    ⟨p.1.val.axes.2, p.1.property.2⟩ p.2
  rw [sliceGauge_smul_eq] at h
  simp only [spatialPlaquetteKernel, h, fundamentalKernel_one_conj]

/-- The real Boltzmann weight multiplied by the chosen face factors. -/
def periodicModifiedWeight {L N : ℕ} [NeZero L] (ν : Measure (UnitaryMatrix N))
    (β : ℝ) (S : Finset (TorusPlaquette L)) (U : TorusConfig L N) : ℝ :=
  Real.exp (periodicLogWeight β U) *
    ∏ p ∈ S, wilsonTwistMultiplier ν β (periodicHolonomy U p.1 p.2)

theorem continuous_periodicModifiedWeight {L N : ℕ} [NeZero L] (ν : Measure (UnitaryMatrix N))
    [IsProbabilityMeasure ν] (β : ℝ) (S : Finset (TorusPlaquette L)) :
    Continuous (periodicModifiedWeight ν β S) :=
  (Real.continuous_exp.comp (continuous_periodicLogWeight β)).mul (continuous_finsetProd S fun p _ =>
    (continuous_wilsonTwistMultiplier ν β).comp (continuous_periodicHolonomy p.1 p.2))

private theorem periodicModifiedWeight_prod {L N : ℕ} [NeZero L]
    (ν : Measure (UnitaryMatrix N)) (β : ℝ) (S : Finset (TorusPlaquette L))
    (U : TorusConfig L N) :
    periodicModifiedWeight ν β S U =
      ∏ p : TorusPlaquette L, fundamentalKernel β (periodicHolonomy U p.1 p.2) 1 *
        (if p ∈ S then wilsonTwistMultiplier ν β (periodicHolonomy U p.1 p.2) else 1) := by
  classical
  have hs : Finset.univ.filter (fun p => p ∈ S) = S := by ext p; simp
  have h (p : TorusPlaquette L) :
      Real.exp ((N : ℝ) * β * (periodicHolonomy U p.1 p.2).val.trace.re) =
        fundamentalKernel β (periodicHolonomy U p.1 p.2) 1 := by
    change Real.exp ((N : ℝ) * β * (periodicHolonomy U p.1 p.2).val.trace.re) =
      Real.exp ((N : ℝ) * β * ((periodicHolonomy U p.1 p.2).val *
        (1 : Matrix (Fin N) (Fin N) ℂ)ᴴ).trace.re)
    simp
  unfold periodicModifiedWeight periodicLogWeight
  rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib, ← Finset.prod_filter, hs]
  simp_rw [h]

private def sliceMarks {L : ℕ} [NeZero L] (τ : Axis) (S : Finset (TorusPlaquette L))
    (t : ZMod L) : Finset (SpatialLink L τ) :=
  Finset.univ.filter fun e =>
    (((temporalFaceEquiv τ).symm e.1).val, torusSliceSite τ t e.2) ∈ S

private theorem periodicModifiedWeight_assembly {L N : ℕ} [NeZero L]
    (ν : Measure (UnitaryMatrix N)) (β : ℝ) (S : Finset (TorusPlaquette L)) (τ : Axis)
    (hS : ∀ p ∈ S, p.1.axes.1 = τ ∨ p.1.axes.2 = τ) (A : TorusSliceCoords L N τ) :
    periodicModifiedWeight ν β S (periodicSliceAssembly L N τ A) =
      ∏ t, weightedKernel (sliceHalfWeight β)
        (averagedWilsonSlice ν β Finset.univ (sliceMarks τ S t))
        (A.1 t) (applySliceGauge (A.2 t) (A.1 (t + 1))) := by
  let U := periodicSliceAssembly L N τ A
  let W (p : TorusPlaquette L) := fundamentalKernel β (periodicHolonomy U p.1 p.2) 1 *
    (if p ∈ S then wilsonTwistMultiplier ν β (periodicHolonomy U p.1 p.2) else 1)
  rw [periodicModifiedWeight_prod]
  change (∏ p : TorusPlaquette L, W p) = _
  rw [← (torusPlaquetteEquiv L τ).prod_comp W, Fintype.prod_prod_type]
  have hproduct (t : ZMod L) :
      (∏ p : Face × SpatialSite L τ, W (torusPlaquetteEquiv L τ (t, p))) =
        (sliceHalfWeight β (A.1 t) * sliceHalfWeight β (A.1 t)) *
          averagedWilsonSlice ν β Finset.univ (sliceMarks τ S t) (A.1 t)
            (applySliceGauge (A.2 t) (A.1 (t + 1))) := by
    rw [← (slicePlaquetteEquiv L τ).prod_comp (fun p => W (torusPlaquetteEquiv L τ (t, p))),
      Fintype.prod_sum_type, sliceHalfWeight_mul_self]
    congr 1
    · apply Finset.prod_congr rfl
      intro p _
      have hp : (p.1.val, torusSliceSite τ t p.2) ∉ S := fun hp =>
        (hS _ hp).elim p.1.property.1 p.1.property.2
      change W (p.1.val, torusSliceSite τ t p.2) = spatialPlaquetteKernel β (A.1 t) p
      simp only [W, hp, ite_false, mul_one, spatialPlaquetteKernel, U,
        periodicHolonomy_assembly_spatial A t p.1.val p.2 p.1.property.1 p.1.property.2]
    · apply Finset.prod_congr rfl
      intro e _
      let I := ((temporalFaceEquiv τ).symm e.1).val
      let p : TorusPlaquette L := (I, torusSliceSite τ t e.2)
      let a := A.1 t e
      let b := applySliceGauge (A.2 t) (A.1 (t + 1)) e
      have hk := periodicHolonomy_assembly_temporal A t e.1 e.2
        (fun P => fundamentalKernel β P 1) (fundamentalKernel_one_inv β)
      have hm := periodicHolonomy_assembly_temporal A t e.1 e.2
        (wilsonTwistMultiplier ν β) (wilsonTwistMultiplier_inv ν β)
      change fundamentalKernel β (periodicHolonomy U p.1 p.2) 1 =
        fundamentalKernel β (a * b⁻¹) 1 at hk
      change wilsonTwistMultiplier ν β (periodicHolonomy U p.1 p.2) =
        wilsonTwistMultiplier ν β (a * b⁻¹) at hm
      change W p = if e ∈ sliceMarks τ S t then averagedFundamentalKernel ν β a b
        else fundamentalKernel β a b
      have hmem : e ∈ sliceMarks τ S t ↔ p ∈ S := by simp [sliceMarks, p, I]
      simp only [W, hmem, hk, hm, fundamentalKernel_mulInv_one]
      split
      · exact fundamentalKernel_mul_wilsonTwistMultiplier ν β a b
      · exact mul_one _
  simp_rw [hproduct]
  have hshift : (∏ t : ZMod L, sliceHalfWeight β (A.1 (t + 1))) =
      ∏ t : ZMod L, sliceHalfWeight β (A.1 t) :=
    Equiv.prod_comp (Equiv.addRight (1 : ZMod L)) fun t => sliceHalfWeight β (A.1 t)
  -- The endpoint gauge preserves the spatial plaquette weights.
  have hweight (t : ZMod L) :
      sliceHalfWeight β (applySliceGauge (A.2 t) (A.1 (t + 1))) =
        sliceHalfWeight β (A.1 (t + 1)) :=
    sliceHalfWeight_gauge β (A.2 t) (A.1 (t + 1))
  simp only [weightedKernel, hweight, Finset.prod_mul_distrib, hshift]
  ring

private def periodicSliceKernel {L N : ℕ} {τ : Axis} [NeZero L]
    (ν : Measure (UnitaryMatrix N)) (β : ℝ) (marked : Finset (SpatialLink L τ)) :
    SliceConfig L N τ → SliceConfig L N τ → ℝ :=
  weightedKernel (sliceHalfWeight β) (averagedWilsonSlice ν β Finset.univ marked)

private theorem continuous_periodicSliceKernel {L N : ℕ} {τ : Axis} [NeZero L]
    (ν : Measure (UnitaryMatrix N)) [IsProbabilityMeasure ν] (β : ℝ)
    (marked : Finset (SpatialLink L τ)) :
    Continuous (fun p : SliceConfig L N τ × SliceConfig L N τ =>
      periodicSliceKernel ν β marked p.1 p.2) :=
  continuous_weightedKernel (continuous_sliceHalfWeight β)
    (continuous_averagedWilsonSlice ν β Finset.univ marked)

private theorem periodicSliceKernel_gauge {L N : ℕ} {τ : Axis} [NeZero L]
    (ν : Measure (UnitaryMatrix N))
    (hν : ∀ Q : UnitaryMatrix N, MeasurePreserving (fun Z => Q * Z * Q⁻¹) ν ν)
    (β : ℝ) (marked : Finset (SpatialLink L τ)) (g : SliceGauge L N τ)
    (a b : SliceConfig L N τ) :
    periodicSliceKernel ν β marked (applySliceGauge g a) (applySliceGauge g b) =
      periodicSliceKernel ν β marked a b := by
  unfold periodicSliceKernel weightedKernel
  have he : averagedWilsonSlice ν β Finset.univ marked (applySliceGauge g a) (applySliceGauge g b) =
      averagedWilsonSlice ν β Finset.univ marked a b := by
    unfold averagedWilsonSlice
    apply Finset.prod_congr rfl
    intro e _
    simp only [applySliceGauge, averagedFundamentalKernel_rightInvariant,
      averagedFundamentalKernel_leftInvariant ν hν, fundamentalKernel_rightInvariant,
      fundamentalKernel_leftInvariant]
  rw [he, sliceHalfWeight_gauge β g a, sliceHalfWeight_gauge β g b]

set_option maxHeartbeats 600000 in
private theorem integral_periodicModifiedWeight_eq {L N : ℕ} [NeZero L]
    (ν : Measure (UnitaryMatrix N)) [IsProbabilityMeasure ν] (β : ℝ)
    (S : Finset (TorusPlaquette L)) (τ : Axis)
    (hS : ∀ p ∈ S, p.1.axes.1 = τ ∨ p.1.axes.2 = τ) :
    (∫ U, periodicModifiedWeight ν β S U ∂periodicHaar L N) =
      ∫ a : ZMod L → SliceConfig L N τ, ∏ t, gaugeAverageKernel (sliceGaugeHaar L N τ)
        (periodicSliceKernel ν β (sliceMarks τ S t)) (a t) (a (t + 1))
        ∂Measure.pi (fun _ => sliceHaar L N τ) := by
  let X := SliceConfig L N τ
  let G := SliceGauge L N τ
  let K (t : ZMod L) := periodicSliceKernel ν β (sliceMarks τ S t)
  let f (p : TorusSliceCoords L N τ) := ∏ t, K t (p.1 t) (p.2 t • p.1 (t + 1))
  have hf : Continuous f := by
    apply continuous_finsetProd
    intro t _
    let g (p : TorusSliceCoords L N τ) := (p.1 t, p.2 t • p.1 (t + 1))
    have hg : Continuous g := ((continuous_apply t).comp continuous_fst).prodMk
      (((continuous_apply t).comp continuous_snd).smul
        ((continuous_apply (t + 1)).comp continuous_fst))
    simpa only [K, Function.comp_def, g] using
      (continuous_periodicSliceKernel ν β (sliceMarks τ S t)).comp hg
  let μa : Measure (ZMod L → X) := Measure.pi fun _ => sliceHaar L N τ
  let μg : Measure (ZMod L → G) := Measure.pi fun _ => sliceGaugeHaar L N τ
  have hi : Integrable f (μa.prod μg) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← (periodicSliceAssembly_preserving L N τ).integral_comp' (periodicModifiedWeight ν β S)]
  have he : (fun p => periodicModifiedWeight ν β S (periodicSliceAssembly L N τ p)) = f :=
    funext fun p => by simpa only [f, K, sliceGauge_smul_eq, periodicSliceKernel] using
      periodicModifiedWeight_assembly ν β S τ hS p
  rw [he, integral_prod f hi]
  apply integral_congr_ae
  filter_upwards [] with a
  exact integral_fintype_prod_eq_prod (fun t (g : G) => K t (a t) (g • a (t + 1)))

set_option maxHeartbeats 600000 in
/-- On an even torus, modifying any specified temporal faces decreases the
partition function for a conjugation-invariant probability law of twists. -/
theorem integral_periodicModifiedWeight_le {L N : ℕ} [NeZero L] (hL : Even L)
    (ν : Measure (UnitaryMatrix N)) [IsProbabilityMeasure ν]
    (hν : ∀ Q : UnitaryMatrix N, MeasurePreserving (fun Z => Q * Z * Q⁻¹) ν ν)
    (β : ℝ) (hβ : 0 ≤ β) (S : Finset (TorusPlaquette L)) (τ : Axis)
    (hS : ∀ p ∈ S, p.1.axes.1 = τ ∨ p.1.axes.2 = τ) :
    (∫ U, periodicModifiedWeight ν β S U ∂periodicHaar L N) ≤
      ∫ U, Real.exp (periodicLogWeight β U) ∂periodicHaar L N := by
  have hnone : (periodicModifiedWeight ν β (∅ : Finset (TorusPlaquette L))) =
      fun U => Real.exp (periodicLogWeight β U) := by
    funext U
    simp [periodicModifiedWeight]
  rw [← hnone, integral_periodicModifiedWeight_eq ν β S τ hS,
    integral_periodicModifiedWeight_eq ν β ∅ τ (by simp)]
  have hm (t : ZMod L) : sliceMarks τ ∅ t = ∅ := by simp [sliceMarks]
  simp_rw [hm]
  let H (B : Finset (SpatialLink L τ)) := periodicSliceKernel (L := L) (τ := τ) ν β B
  let γ := sliceGaugeHaar L N τ
  have hc (B : Finset (SpatialLink L τ)) :
      Continuous (fun p : SliceConfig L N τ × SliceConfig L N τ => H B p.1 p.2) :=
    continuous_periodicSliceKernel ν β B
  have hg (B : Finset (SpatialLink L τ)) (g : SliceGauge L N τ) (a b : SliceConfig L N τ) :
      H B (g • a) (g • b) = H B a b :=
    periodicSliceKernel_gauge ν hν β B g a b
  have hpos (B : Finset (SpatialLink L τ)) : PositiveKernel (H B) :=
    (averagedWilsonSlice_positive_order ν β hβ Finset.univ B).1.weighted _
  have hd (B : Finset (SpatialLink L τ)) : PositiveKernel (fun a b => H ∅ a b - H B a b) := by
    let K : Finset (SpatialLink L τ) → SliceConfig L N τ → SliceConfig L N τ → ℝ :=
      averagedWilsonSlice ν β Finset.univ
    have he : weightedKernel (sliceHalfWeight β) (fun a b => K ∅ a b - K B a b) =
        (fun a b => H ∅ a b - H B a b) := by
      funext a b
      exact weightedKernel_sub (sliceHalfWeight β) (K ∅) (K B) a b
    rw [← he]
    exact (averagedWilsonSlice_positive_order ν β hβ Finset.univ B).2.weighted (sliceHalfWeight β)
  refine integral_zmodCycle_le_of_sampleOrder (sliceHaar L N τ) hL
    (fun t => gaugeAverageKernel γ (H (sliceMarks τ S t))) (gaugeAverageKernel γ (H ∅))
    (fun t => continuous_gaugeAverage γ (hc (sliceMarks τ S t))) (continuous_gaugeAverage γ (hc ∅))
    (fun m v t => (hpos _).gaugeAverage γ (hc _) (hg _) m v) (fun m v t => ?_)
  let B := sliceMarks τ S t
  have h := (hd B).gaugeAverage γ ((hc ∅).sub (hc B)) (fun g a b => by rw [hg ∅, hg B]) m v
  convert h using 1
  ext a b
  simp only [Matrix.sub_apply, Matrix.of_apply, gaugeAverageKernel_sub γ (hc B) (hc ∅), B]

/-- The product of the modified face factors has Wilson expectation at most
one when all the selected plaquettes cross the chosen time direction. -/
theorem lintegral_periodicWilson_twistMultiplier_le_one {L N : ℕ} [NeZero L] (hL : Even L)
    (ν : Measure (UnitaryMatrix N)) [IsProbabilityMeasure ν]
    (hν : ∀ Q : UnitaryMatrix N, MeasurePreserving (fun Z => Q * Z * Q⁻¹) ν ν)
    (β : ℝ) (hβ : 0 ≤ β) (S : Finset (TorusPlaquette L)) (τ : Axis)
    (hS : ∀ p ∈ S, p.1.axes.1 = τ ∨ p.1.axes.2 = τ) :
    (∫⁻ U, ∏ p ∈ S, ENNReal.ofReal (wilsonTwistMultiplier ν β (periodicHolonomy U p.1 p.2))
        ∂periodicWilson L N β) ≤ 1 := by
  let f := periodicModifiedWeight ν β S
  let g (U : TorusConfig L N) := Real.exp (periodicLogWeight β U)
  have hf : Integrable f (periodicHaar L N) :=
    (continuous_periodicModifiedWeight ν β S).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : Integrable g (periodicHaar L N) :=
    (Real.continuous_exp.comp (continuous_periodicLogWeight β)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hf₀ (U : TorusConfig L N) : 0 ≤ f U :=
    mul_nonneg (Real.exp_nonneg _) (Finset.prod_nonneg fun p _ =>
      (wilsonTwistMultiplier_pos ν β (periodicHolonomy U p.1 p.2)).le)
  have he (U : TorusConfig L N) :
      periodicWeight β U *
        (∏ p ∈ S, ENNReal.ofReal (wilsonTwistMultiplier ν β (periodicHolonomy U p.1 p.2))) =
      ENNReal.ofReal (f U) := by
    simp only [f, periodicModifiedWeight, periodicWeight, ENNReal.ofReal_mul (Real.exp_nonneg _)]
    rw [ENNReal.ofReal_prod_of_nonneg fun p _ => (wilsonTwistMultiplier_pos ν β
      (periodicHolonomy U p.1 p.2)).le]
  have hmeas : Measurable (fun U : TorusConfig L N => ∏ p ∈ S,
      ENNReal.ofReal (wilsonTwistMultiplier ν β (periodicHolonomy U p.1 p.2))) :=
    Finset.measurable_prod S fun p _ => ENNReal.measurable_ofReal.comp
      ((continuous_wilsonTwistMultiplier ν β).comp (continuous_periodicHolonomy p.1 p.2)).measurable
  have hF : (∫⁻ U, ENNReal.ofReal (f U) ∂periodicHaar L N) ≤ periodicPartition L N β := by
    unfold periodicPartition periodicWeight
    rw [← ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf₀),
      ← ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (integral_periodicModifiedWeight_le hL ν hν β hβ S τ hS)
  rw [periodicWilson, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (periodicWeight_measurable β) hmeas]
  simp_rw [Pi.mul_apply, he]
  calc
    _ ≤ (periodicPartition L N β)⁻¹ * periodicPartition L N β :=
      mul_le_mul_of_nonneg_left hF zero_le
    _ = 1 := ENNReal.inv_mul_cancel (periodicPartition_pos L N β).ne'
      (periodicPartition_lt_top L N β).ne

end

end GaplessYangMills

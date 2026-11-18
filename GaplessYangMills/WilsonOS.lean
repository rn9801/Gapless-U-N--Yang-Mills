module

public import GaplessYangMills.ReflectionHilbert
public import GaplessYangMills.WilsonHalfSpace

/-!
# The Wilson reflection Hilbert space and transfer

Site and bond reflection positivity extend to the Euclidean L² closure
of the continuous gauge-invariant half-space cylinders. The site form and
the inward shift then construct the physical transfer.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace Topology

noncomputable section

theorem measurePreserving_reflectConfig {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) (c : ℤ) :
    MeasurePreserving (reflectConfig τ c) μ.toMeasure μ.toMeasure :=
  ⟨(continuous_reflectConfig τ c).measurable,
    congrArg ProbabilityMeasure.toMeasure (periodicWilson_limit_reflect β μ hμ τ c)⟩

def wilsonReflectL2Isometry {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (c : ℤ) : WilsonL2 μ →ₗᵢ[ℝ] WilsonL2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (reflectConfig τ c) (measurePreserving_reflectConfig μ hμ τ c)

def wilsonReflectL2 {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (c : ℤ) : WilsonL2 μ →L[ℝ] WilsonL2 μ :=
  (wilsonReflectL2Isometry μ hμ τ c).toContinuousLinearMap

private theorem lpComposition_congr {Ω : Type*} [MeasurableSpace Ω] {m : Measure Ω}
    {f g : Ω → Ω} (h : f = g) (hf : MeasurePreserving f m m) (hg : MeasurePreserving g m m)
    (u : Lp ℝ 2 m) : Lp.compMeasurePreserving f hf u = Lp.compMeasurePreserving g hg u := by
  subst g
  rfl

theorem wilsonTranslateL2_zero {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (u : WilsonL2 μ) :
    wilsonTranslateL2 μ hμ 0 u = u := by
  change Lp.compMeasurePreserving _ (measurePreserving_translateConfig μ hμ 0) u = u
  have h : (translateConfig (N := N) 0) = id := by
    funext U e
    obtain ⟨i, x⟩ := e
    simp [translateConfig]
  exact (lpComposition_congr h _ (MeasurePreserving.id μ.toMeasure) u).trans
    (Lp.compMeasurePreserving_id_apply u)

theorem wilsonReflectL2_involutive {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) (c : ℤ) :
    Function.Involutive (wilsonReflectL2 μ hμ τ c) := by
  intro u
  let hR := measurePreserving_reflectConfig μ hμ τ c
  change Lp.compMeasurePreserving _ hR (Lp.compMeasurePreserving _ hR u) = u
  rw [← Lp.compMeasurePreserving_comp_apply]
  exact (lpComposition_congr (funext (reflectConfig_involutive τ c)) _ (MeasurePreserving.id μ.toMeasure) u).trans
    (Lp.compMeasurePreserving_id_apply u)

theorem wilsonReflectL2_symmetric {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) (c : ℤ)
    (u v : WilsonL2 μ) :
    ⟪wilsonReflectL2 μ hμ τ c u, v⟫_ℝ = ⟪u, wilsonReflectL2 μ hμ τ c v⟫_ℝ := by
  let R := wilsonReflectL2 μ hμ τ c
  calc
    _ = ⟪R (R u), R v⟫_ℝ := ((wilsonReflectL2Isometry μ hμ τ c).inner_map_map (R u) v).symm
    _ = _ := by rw [wilsonReflectL2_involutive μ hμ τ c u]

theorem wilsonReflectL2_shift {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) (c : ℤ)
    (u : WilsonL2 μ) :
    wilsonReflectL2 μ hμ τ c (wilsonTranslateL2 μ hμ (step τ) u) = wilsonReflectL2 μ hμ τ (c - 1) u := by
  let hR := measurePreserving_reflectConfig μ hμ τ c
  let hS := measurePreserving_translateConfig μ hμ (step τ)
  change Lp.compMeasurePreserving _ hR (Lp.compMeasurePreserving _ hS u) =
    Lp.compMeasurePreserving _ (measurePreserving_reflectConfig μ hμ τ (c - 1)) u
  rw [← Lp.compMeasurePreserving_comp_apply]
  exact lpComposition_congr (funext (translateConfig_reflect_step τ c)) _ _ u

theorem wilsonReflectL2_inner_toLp {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) (c : ℤ)
    (f g : InfiniteConfig N →ᵇ ℝ) :
    ⟪wilsonReflectL2 μ hμ τ c (BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ f),
      BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ g⟫_ℝ =
      ∫ U, f (reflectConfig τ c U) * g U ∂μ.toMeasure := by
  let hR := measurePreserving_reflectConfig μ hμ τ c
  let A : (InfiniteConfig N →ᵇ ℝ) →L[ℝ] WilsonL2 μ := BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_compMeasurePreserving (A f) hR,
    hR.quasiMeasurePreserving.ae (BoundedContinuousFunction.coeFn_toLp 2 μ.toMeasure ℝ f),
    BoundedContinuousFunction.coeFn_toLp 2 μ.toMeasure ℝ g] with U h₁ h₂ h₃
  rw [Real.inner_apply]
  exact congrArg₂ (· * ·) (h₁.trans h₂) h₃

private theorem wilsonReflectL2_nonneg_of_core {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) (c : ℤ)
    (hc : ∀ f : wilsonHalfSpaceCore N τ, 0 ≤ ∫ U, f.val (reflectConfig τ c U) * f.val U ∂μ.toMeasure)
    (u : wilsonHalfSpace μ τ) :
    0 ≤ ⟪wilsonReflectL2 μ hμ τ c u.val, u.val⟫_ℝ := by
  let R := wilsonReflectL2 μ hμ τ c
  have hclosed : IsClosed {u : WilsonL2 μ | 0 ≤ ⟪R u, u⟫_ℝ} :=
    isClosed_le continuous_const (R.continuous.inner continuous_id)
  have hsub : ((wilsonHalfSpaceCoreL2 μ τ).range : Set (WilsonL2 μ)) ⊆ {u | 0 ≤ ⟪R u, u⟫_ℝ} := by
    rintro _ ⟨f, rfl⟩
    change 0 ≤ ⟪R (BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ f.val),
      BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ f.val⟫_ℝ
    rw [wilsonReflectL2_inner_toLp]
    exact hc f
  exact closure_minimal hsub hclosed u.property

theorem wilsonReflectL2_site_nonneg {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (u : wilsonHalfSpace μ τ) : 0 ≤ ⟪wilsonReflectL2 μ hμ τ 0 u.val, u.val⟫_ℝ :=
  wilsonReflectL2_nonneg_of_core μ hμ τ 0 (fun f =>
    periodicLimit_siteReflection_nonneg β μ hl hμ τ f.val f.val.continuous f.property.1) u

theorem wilsonReflectL2_bond_nonneg {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (u : wilsonHalfSpace μ τ) : 0 ≤ ⟪wilsonReflectL2 μ hμ τ (-1) u.val, u.val⟫_ℝ :=
  wilsonReflectL2_nonneg_of_core μ hμ τ (-1) (fun f =>
    periodicLimit_bondReflection_nonneg β hβ μ hl hμ τ f.val f.val.continuous f.property.2 f.property.1) u

def wilsonOSForm {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) :
    PositiveReflectionForm (wilsonHalfSpace μ τ) where
  form := (innerₗ (WilsonL2 μ)).compl₁₂ ((wilsonReflectL2 μ hμ τ 0).toLinearMap.comp (wilsonHalfSpace μ τ).subtype)
    (wilsonHalfSpace μ τ).subtype
  symmetric := ⟨fun u v => (wilsonReflectL2_symmetric μ hμ τ 0 u.val v.val).trans (real_inner_comm _ _)⟩
  nonnegative := wilsonReflectL2_site_nonneg μ hl hμ τ

theorem wilsonOSForm_apply {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (u v : wilsonHalfSpace μ τ) :
    (wilsonOSForm μ hl hμ τ).form u v = ⟪wilsonReflectL2 μ hμ τ 0 u.val, v.val⟫_ℝ := rfl

theorem wilsonOSVector_norm_le {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (u : wilsonHalfSpace μ τ) : ‖(wilsonOSForm μ hl hμ τ).ofVector u‖ ≤ ‖u.val‖ := by
  rw [PositiveReflectionForm.norm_ofVector]
  calc
    _ ≤ Real.sqrt (‖u.val‖ * ‖u.val‖) := by
      apply Real.sqrt_le_sqrt
      rw [wilsonOSForm_apply]
      have h := real_inner_le_norm (wilsonReflectL2 μ hμ τ 0 u.val) u.val
      rw [show ‖wilsonReflectL2 μ hμ τ 0 u.val‖ = ‖u.val‖ from
        (wilsonReflectL2Isometry μ hμ τ 0).norm_map u.val] at h
      exact h
    _ = _ := by rw [← sq, Real.sqrt_sq (norm_nonneg _)]

def wilsonInwardShift {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) :
    wilsonHalfSpace μ τ →ₗ[ℝ] wilsonHalfSpace μ τ :=
  ((wilsonTranslateL2 μ hμ (step τ)).toLinearMap.comp (wilsonHalfSpace μ τ).subtype).codRestrict
    (wilsonHalfSpace μ τ) (fun u => wilsonTranslateL2_halfSpace μ hμ τ (step τ) (by simp [step_same]) u.property)

theorem wilsonInwardShift_pow {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (n : ℕ) (u : wilsonHalfSpace μ τ) :
    ((wilsonInwardShift μ hμ τ ^ n) u).val = wilsonTranslateL2 μ hμ (n • step τ) u.val := by
  induction n with
  | zero =>
    rw [zero_nsmul, wilsonTranslateL2_zero, pow_zero, one_apply_eq_self]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    change wilsonTranslateL2 μ hμ (step τ) ((wilsonInwardShift μ hμ τ ^ n) u).val = _
    rw [ih, ← mul_apply_eq_comp, wilsonTranslateL2_mul, succ_nsmul, add_comm]

def wilsonOSShift {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) :
    (wilsonOSForm μ hl hμ τ).Shift where
  operator := wilsonInwardShift μ hμ τ
  symmetric u v := by
    simp only [wilsonOSForm_apply]
    change ⟪wilsonReflectL2 μ hμ τ 0 (wilsonTranslateL2 μ hμ (step τ) u.val), v.val⟫_ℝ =
      ⟪wilsonReflectL2 μ hμ τ 0 u.val, wilsonTranslateL2 μ hμ (step τ) v.val⟫_ℝ
    calc
      _ = ⟪wilsonReflectL2 μ hμ τ (-1) u.val, v.val⟫_ℝ := by
        rw [wilsonReflectL2_shift]
        rfl
      _ = ⟪u.val, wilsonReflectL2 μ hμ τ (-1) v.val⟫_ℝ :=
        wilsonReflectL2_symmetric μ hμ τ (-1) u.val v.val
      _ = _ := by
        rw [wilsonReflectL2_symmetric μ hμ τ 0 u.val, wilsonReflectL2_shift]
        rfl
  nonnegative u := by
    rw [wilsonOSForm_apply]
    change 0 ≤ ⟪wilsonReflectL2 μ hμ τ 0 (wilsonTranslateL2 μ hμ (step τ) u.val), u.val⟫_ℝ
    rw [wilsonReflectL2_shift]
    exact wilsonReflectL2_bond_nonneg hβ μ hl hμ τ u
  boundedOrbit u := by
    refine ⟨‖u.val‖ * ‖u.val‖, fun n => ?_⟩
    rw [wilsonOSForm_apply, wilsonInwardShift_pow]
    have h := real_inner_le_norm (wilsonReflectL2 μ hμ τ 0 (wilsonTranslateL2 μ hμ (n • step τ) u.val))
      (wilsonTranslateL2 μ hμ (n • step τ) u.val)
    have hnorm : ‖wilsonReflectL2 μ hμ τ 0 (wilsonTranslateL2 μ hμ (n • step τ) u.val)‖ =
        ‖wilsonTranslateL2 μ hμ (n • step τ) u.val‖ :=
      (wilsonReflectL2Isometry μ hμ τ 0).norm_map _
    rwa [hnorm, norm_wilsonTranslateL2_apply] at h

def wilsonTransfer {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) :
    (wilsonOSForm μ hl hμ τ).Hilbert →L[ℝ] (wilsonOSForm μ hl hμ τ).Hilbert :=
  (wilsonOSShift hβ μ hl hμ τ).transfer

theorem wilsonTransfer_positive {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) :
    (wilsonTransfer hβ μ hl hμ τ).IsPositive :=
  (wilsonOSShift hβ μ hl hμ τ).transfer_positive

theorem wilsonTransfer_norm_le_one {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) :
    ‖wilsonTransfer hβ μ hl hμ τ‖ ≤ 1 :=
  (wilsonOSShift hβ μ hl hμ τ).transfer_norm_le_one

theorem wilsonTransfer_matrixElement {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (n : ℕ) (u v : wilsonHalfSpace μ τ) :
    ⟪(wilsonOSForm μ hl hμ τ).ofVector u,
      (wilsonTransfer hβ μ hl hμ τ ^ n) ((wilsonOSForm μ hl hμ τ).ofVector v)⟫_ℝ =
      ⟪wilsonReflectL2 μ hμ τ 0 u.val, wilsonTranslateL2 μ hμ (n • step τ) v.val⟫_ℝ := by
  rw [show wilsonTransfer hβ μ hl hμ τ = (wilsonOSShift hβ μ hl hμ τ).transfer from rfl,
    PositiveReflectionForm.Shift.inner_transfer_pow, wilsonOSForm_apply]
  change ⟪wilsonReflectL2 μ hμ τ 0 u.val, ((wilsonInwardShift μ hμ τ ^ n) v).val⟫_ℝ = _
  rw [wilsonInwardShift_pow]

end

end GaplessYangMills

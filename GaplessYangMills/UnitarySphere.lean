module

public import GaplessYangMills.SphericalCap
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Uniform measure and caps on the unit sphere

Normalize the spherical measure induced by real Lebesgue measure. An
orthogonal decomposition along the cap's axis identifies its measure with
the complex product-coordinate calculation.
-/

@[expose] public section

namespace GaplessYangMills

open Metric MeasureTheory
open scoped ENNReal InnerProductSpace Pointwise

noncomputable section

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := sphere (0 : E) 1

section Real

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def uniformSphere : Measure (UnitSphere E) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

instance uniformSphere_probability [Nontrivial E] : IsProbabilityMeasure (uniformSphere E) where
  measure_univ := by
    let σ := (volume : Measure E).toSphere
    have h₀ : σ Set.univ ≠ 0 := fun h => Measure.toSphere_ne_zero _ (Measure.measure_univ_eq_zero.mp h)
    change (σ Set.univ)⁻¹ * σ Set.univ = 1
    exact ENNReal.inv_mul_cancel h₀ (measure_ne_top _ _)

end Real

section Isometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F]
  [BorelSpace E] [BorelSpace F]

def sphereIsometry (e : E ≃ₗᵢ[ℝ] F) : UnitSphere E ≃ᵐ UnitSphere F where
  toEquiv := e.toEquiv.subtypeEquiv fun x => by simp
  measurable_toFun := (e.continuous.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (e.symm.continuous.measurable.comp measurable_subtype_coe).subtype_mk

@[simp] theorem sphereIsometry_apply_val (e : E ≃ₗᵢ[ℝ] F) (x : UnitSphere E) :
    (sphereIsometry e x).val = e x.val := rfl

private theorem sphereCone_preimage (e : E ≃ₗᵢ[ℝ] F) (s : Set (UnitSphere F)) :
    e ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereIsometry e ⁻¹' s)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr, _, ⟨v, hv, rfl⟩, hrv⟩ := Set.mem_smul.mp hx
    let u := (sphereIsometry e).symm v
    have hu : sphereIsometry e u = v := (sphereIsometry e).apply_symm_apply v
    have hxu : r • u.val = x := e.injective (by
      rw [map_smul]
      exact (congrArg (fun y : UnitSphere F => r • y.val) hu).trans hrv)
    have hm : u ∈ sphereIsometry e ⁻¹' s := by change sphereIsometry e u ∈ s; rwa [hu]
    exact Set.mem_smul.mpr ⟨r, hr, u.val, ⟨u, hm, rfl⟩, hxu⟩
  · intro hx
    obtain ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩ := Set.mem_smul.mp hx
    exact Set.mem_smul.mpr ⟨r, hr, (sphereIsometry e u).val, ⟨_, hu, rfl⟩, (map_smul e r u.val).symm⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

private theorem sphereIsometry_toSphere_preserving (e : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (sphereIsometry e) (volume : Measure E).toSphere
      (volume : Measure F).toSphere := by
  refine ⟨(sphereIsometry e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [(sphereIsometry e).map_apply, Measure.toSphere_apply' _
    ((sphereIsometry e).measurable hs), Measure.toSphere_apply' _ hs,
    e.toLinearEquiv.finrank_eq, ← sphereCone_preimage e s]
  change (_ : ℝ≥0∞) * (volume : Measure E) (e.toMeasurableEquiv ⁻¹' _) = _
  rw [← e.toMeasurableEquiv.map_apply, LinearIsometryEquiv.coe_toMeasurableEquiv,
    e.measurePreserving.map_eq]

theorem sphereIsometry_preserving (e : E ≃ₗᵢ[ℝ] F) :
    MeasurePreserving (sphereIsometry e) (uniformSphere E) (uniformSphere F) := by
  have h := sphereIsometry_toSphere_preserving e
  refine ⟨h.measurable, ?_⟩
  have hu : (volume : Measure E).toSphere Set.univ = (volume : Measure F).toSphere Set.univ :=
    h.measure_preimage MeasurableSet.univ.nullMeasurableSet
  dsimp only [uniformSphere]
  rw [Measure.map_smul _ h.measurable.aemeasurable, h.map_eq, hu]

end Isometry

section Cap

/-- Restriction of scalars for an isometry of complex inner product spaces. -/
def realLinearIsometry {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [Module ℂ E] [Module ℂ F]
    [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] (e : E ≃ₗᵢ[ℂ] F) : E ≃ₗᵢ[ℝ] F :=
  ⟨e.toLinearEquiv.restrictScalars ℝ, e.norm_map⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option backward.isDefEq.respectTransparency false in
/-- The fraction of the complex unit sphere in the cap of squared overlap
at least fifteen sixteenths. -/
theorem uniformSphere_cap (n : ℕ) (hdim : Module.finrank ℂ E = n + 1) (v₀ : UnitSphere E) :
    uniformSphere E {v : UnitSphere E | (15 : ℝ) / 16 ≤ ‖⟪v₀.val, v.val⟫_ℂ‖ ^ 2} =
      ENNReal.ofReal ((1 / 16 : ℝ) ^ n) := by
  let u := v₀.val
  have hu : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp v₀.property
  have hu₀ : u ≠ 0 := by intro h; simp [h] at hu
  let K := ℂ ∙ u
  let V := ↥Kᗮ
  let : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  let H := WithLp 2 (ℂ × V)
  let d : ℂ ≃ₗᵢ[ℂ] ↥K :=
    { toLinearEquiv := LinearEquiv.toSpanNonzeroSingleton ℂ E u hu₀
      norm_map' := fun z => by
        change ‖(LinearEquiv.toSpanNonzeroSingleton ℂ E u hu₀ z).val‖ = ‖z‖
        simp [norm_smul, hu] }
  let e₀ : E ≃ₗᵢ[ℂ] H := K.orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2 d.symm (LinearIsometryEquiv.refl ℂ V))
  let e := realLinearIsometry e₀
  have hc (x : E) : (complexProductCoordinates (e x)).1 = ⟪u, x⟫_ℂ := by
    change (complexProductCoordinates (e₀ x)).1 = _
    simp only [e₀, LinearIsometryEquiv.trans_apply, Submodule.orthogonalDecomposition_apply]
    change d.symm (K.orthogonalProjectionOnto x) = _
    apply d.injective
    rw [d.apply_symm_apply]
    apply Subtype.ext
    change K.starProjection x = ⟪u, x⟫_ℂ • u
    rw [Submodule.starProjection_singleton]
    simp [hu]
  let s : Set (UnitSphere H) := complexSphericalCap (1 / 4)
  have hs : MeasurableSet s := measurableSet_le measurable_const
    (((complexProductCoordinates (E := V)).continuous.comp continuous_subtype_val).fst.norm.pow 2).measurable
  have hpre : sphereIsometry e ⁻¹' s =
      {v : UnitSphere E | (15 : ℝ) / 16 ≤ ‖⟪v₀.val, v.val⟫_ℂ‖ ^ 2} := by
    ext v
    change 1 - (1 / 4 : ℝ) ^ 2 ≤ ‖(complexProductCoordinates (e v.val)).1‖ ^ 2 ↔ _
    rw [hc]
    norm_num [u]
  have hvolume : complexProductMeasure (volume : Measure V) = (volume : Measure H) :=
    (WithLp.volume_preserving_toLp ℂ V).map_eq
  let : Fact (Module.finrank ℂ E = n + 1) := ⟨hdim⟩
  have hV : Module.finrank ℂ V = n := Submodule.finrank_orthogonal_span_singleton hu₀
  rw [← hpre, (sphereIsometry_preserving e).measure_preimage hs.nullMeasurableSet]
  have h := complexSphericalCap_probability (E := V) volume
  rw [hvolume, hV] at h
  have hspace : (inferInstance : InnerProductSpace ℝ H).toNormedSpace =
      WithLp.instProdNormedSpace 2 ℝ ℂ V := by
    ext r x
    apply WithLp.ofLp_injective
    apply Prod.ext
    · rfl
    · change (r : ℂ) • x.snd = r • x.snd
      exact algebraMap_smul ℂ r x.snd
  let toSphere (inst : NormedSpace ℝ H) : Measure (UnitSphere H) :=
    @Measure.toSphere H _ inst _ (volume : Measure H)
  let σ₁ := toSphere (inferInstance : InnerProductSpace ℝ H).toNormedSpace
  let σ₂ := toSphere (WithLp.instProdNormedSpace 2 ℝ ℂ V)
  have hσ : σ₁ = σ₂ := congrArg toSphere hspace
  change (σ₁ Set.univ)⁻¹ * σ₁ s = _
  rw [hσ]
  simpa only [σ₂, toSphere, s, smul_eq_mul] using h

end Cap

end

end GaplessYangMills

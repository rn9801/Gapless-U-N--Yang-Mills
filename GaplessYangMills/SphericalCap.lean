module

public import GaplessYangMills.CapVolume
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The complex spherical cap ratio

Passing from a solid cone to its section on the unit sphere keeps the
relative measure. The squared overlap with the complex coordinate is one
minus the squared norm in the remaining coordinates.
-/

@[expose] public section

namespace GaplessYangMills

open Metric MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev ComplexSphere (E : Type*) [NormedAddCommGroup E] :=
  sphere (0 : WithLp 2 (ℂ × E)) 1

/-- Coordinate map from the Hilbert product to its two factors. -/
def complexProductCoordinates : WithLp 2 (ℂ × E) ≃L[ℝ] ℂ × E :=
  WithLp.prodContinuousLinearEquiv 2 ℝ ℂ E

private theorem sq_norm_complexProductCoordinates (x : WithLp 2 (ℂ × E)) :
    ‖x‖ ^ 2 = ‖(complexProductCoordinates x).1‖ ^ 2 + ‖(complexProductCoordinates x).2‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 x

def complexSphericalCap (s : ℝ) : Set (ComplexSphere E) :=
  {z | 1 - s ^ 2 ≤ ‖(complexProductCoordinates z.val).1‖ ^ 2}

private theorem complexSphericalCap_iff {s : ℝ} (z : ComplexSphere E) :
    z ∈ complexSphericalCap s ↔ ‖(complexProductCoordinates z.val).2‖ ^ 2 ≤ s ^ 2 := by
  have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.prop
  have h := sq_norm_complexProductCoordinates z.val
  change 1 - s ^ 2 ≤ ‖(complexProductCoordinates z.val).1‖ ^ 2 ↔ _
  rw [hz, one_pow] at h
  constructor <;> intro h₀ <;> linarith only [h₀, h]

private theorem image_radial_complexCap (s : ℝ) :
    complexProductCoordinates (E := E) '' (Set.Ioo (0 : ℝ) 1 •
      (Subtype.val '' (complexSphericalCap s : Set (ComplexSphere E)))) =
      complexCapSet s \ {0} := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨r, hr, _, ⟨u, hu, rfl⟩, rfl⟩ := Set.mem_smul.mp hp
    have huNorm : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.prop
    have hn : ‖r • u.val‖ = r := by simp [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, huNorm]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change ‖(complexProductCoordinates (r • u.val)).1‖ ^ 2 +
        ‖(complexProductCoordinates (r • u.val)).2‖ ^ 2 < 1
      rw [← sq_norm_complexProductCoordinates, hn]
      simpa only [one_pow] using (sq_lt_sq₀ hr.1.le zero_le_one).mpr hr.2
    · change ‖(complexProductCoordinates (r • u.val)).2‖ ^ 2 ≤ s ^ 2 *
        (‖(complexProductCoordinates (r • u.val)).1‖ ^ 2 + ‖(complexProductCoordinates (r • u.val)).2‖ ^ 2)
      rw [← sq_norm_complexProductCoordinates, hn, map_smul]
      change ‖r • (complexProductCoordinates u.val).2‖ ^ 2 ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, mul_pow, mul_comm (s ^ 2)]
      exact mul_le_mul_of_nonneg_left ((complexSphericalCap_iff u).mp hu) (sq_nonneg r)
    · intro hz
      have he : complexProductCoordinates (r • u.val) = 0 := hz
      have hzero : r • u.val = 0 := complexProductCoordinates.injective (he.trans (map_zero _).symm)
      rw [hzero, norm_zero] at hn
      exact hr.1.ne' hn.symm
  · rintro ⟨⟨hu, hc⟩, hz⟩
    let p := (complexProductCoordinates (E := E)).symm z
    have hp : complexProductCoordinates p = z := complexProductCoordinates.apply_symm_apply z
    let r := ‖p‖
    have hr₀ : 0 < r := by
      apply norm_pos_iff.mpr
      intro he
      apply hz
      rw [← hp, he, map_zero]
      rfl
    have hsum : r ^ 2 = ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
      rw [← hp]
      exact sq_norm_complexProductCoordinates p
    have hr₁ : r < 1 := by
      apply (sq_lt_sq₀ hr₀.le zero_le_one).mp
      rw [hsum, one_pow]
      exact hu
    let v : WithLp 2 (ℂ × E) := r⁻¹ • p
    have hvNorm : ‖v‖ = 1 := by
      change ‖r⁻¹ • p‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr₀)]
      exact inv_mul_cancel₀ hr₀.ne'
    let u : ComplexSphere E := ⟨v, mem_sphere_zero_iff_norm.mpr hvNorm⟩
    have hv : r • v = p := by simp [v, smul_smul, mul_inv_cancel₀ hr₀.ne']
    have he : r • (complexProductCoordinates v).2 = z.2 := by
      have h := congrArg (fun a : WithLp 2 (ℂ × E) => (complexProductCoordinates a).2) hv
      rw [map_smul, hp] at h
      exact h
    have hvCap : u ∈ complexSphericalCap s := by
      apply (complexSphericalCap_iff u).mpr
      change ‖z.2‖ ^ 2 ≤ s ^ 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) at hc
      rw [← hsum, ← he, norm_smul, Real.norm_eq_abs, abs_of_pos hr₀, mul_pow,
        mul_comm (s ^ 2)] at hc
      exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hr₀)).mp hc
    exact ⟨p, Set.mem_smul.mpr ⟨r, ⟨hr₀, hr₁⟩, v, ⟨u, hvCap, rfl⟩, hv⟩, hp⟩

section Measure

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def complexProductMeasure [MeasurableSpace (WithLp 2 (ℂ × E))] (ν : Measure E) :
    Measure (WithLp 2 (ℂ × E)) :=
  Measure.map (complexProductCoordinates (E := E)).symm ((volume : Measure ℂ).prod ν)

theorem complexSphericalCap_measure [MeasurableSpace (WithLp 2 (ℂ × E))]
    [BorelSpace (WithLp 2 (ℂ × E))] (ν : Measure E) [ν.IsAddHaarMeasure]
    (s : ℝ) (hs : 0 < s) (hs' : s ≤ 1) :
    (complexProductMeasure ν).toSphere (complexSphericalCap s) =
      ENNReal.ofReal (s ^ Module.finrank ℝ E) *
        (complexProductMeasure ν).toSphere Set.univ := by
  let κ := (volume : Measure ℂ).prod ν
  let L := complexProductCoordinates (E := E)
  have himage (A : Set (WithLp 2 (ℂ × E))) : L.symm ⁻¹' A = L '' A := by
    ext z
    constructor
    · intro hz
      exact ⟨L.symm z, hz, L.apply_symm_apply z⟩
    · rintro ⟨a, ha, rfl⟩
      change L.symm (L a) ∈ A
      rw [L.symm_apply_apply]
      exact ha
  have hmap (A : Set (WithLp 2 (ℂ × E))) :
      complexProductMeasure ν A = κ (L '' A) := by
    unfold complexProductMeasure
    have h := L.symm.toHomeomorph.toMeasurableEquiv.map_apply (μ := κ) A
    change Measure.map L.symm κ A = κ (L.symm ⁻¹' A) at h
    rw [himage] at h
    exact h
  have hc : MeasurableSet (complexSphericalCap s : Set (ComplexSphere E)) :=
    measurableSet_le measurable_const
      (((L.continuous.comp continuous_subtype_val).fst.norm.pow 2).measurable)
  have hball : L '' ball (0 : WithLp 2 (ℂ × E)) 1 = complexUnitSet := by
    ext z
    rw [← himage]
    simp only [Set.mem_preimage, mem_ball_zero_iff]
    change ‖L.symm z‖ < 1 ↔ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < 1
    rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one, one_pow,
      sq_norm_complexProductCoordinates (L.symm z)]
    simp [L]
  have hzero : κ ({0} : Set (ℂ × E)) = 0 := by
    have hprod : ({0} : Set (ℂ × E)) = ({0} : Set ℂ) ×ˢ ({0} : Set E) := by
      ext z
      rcases z with ⟨a, b⟩
      change ((a, b) = (0, 0)) ↔ _
      simp
    rw [hprod, Measure.prod_prod]
    simp
  rw [Measure.toSphere_apply' _ hc, Measure.toSphere_apply_univ', hmap, hmap,
    image_radial_complexCap, Set.image_sdiff L.injective, hball, Set.image_singleton, map_zero,
    measure_sdiff_null hzero, measure_sdiff_null hzero, complexCap_volume ν s hs hs']
  ac_rfl

/-- The cap of squared overlap at least fifteen sixteenths occupies a
fraction `16⁻¹` for each complex dimension in the remaining factor. -/
theorem complexSphericalCap_fifteen_sixteenths [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [MeasurableSpace (WithLp 2 (ℂ × E))]
    [BorelSpace (WithLp 2 (ℂ × E))] (ν : Measure E) [ν.IsAddHaarMeasure] :
    (complexProductMeasure ν).toSphere (complexSphericalCap (1 / 4)) =
      ENNReal.ofReal ((1 / 16 : ℝ) ^ Module.finrank ℂ E) *
        (complexProductMeasure ν).toSphere Set.univ := by
  rw [complexSphericalCap_measure ν (1 / 4) (by norm_num) (by norm_num),
    ← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex, pow_mul]
  norm_num

/-- Normalizing the induced sphere measure gives the cap probability in
the complex product coordinates. -/
theorem complexSphericalCap_probability [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [MeasurableSpace (WithLp 2 (ℂ × E))] [BorelSpace (WithLp 2 (ℂ × E))]
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    let σ := (complexProductMeasure ν).toSphere
    (σ Set.univ)⁻¹ • σ (complexSphericalCap (1 / 4)) =
      ENNReal.ofReal ((1 / 16 : ℝ) ^ Module.finrank ℂ E) := by
  let H := WithLp 2 (ℂ × E)
  let L := complexProductCoordinates (E := E)
  let : FiniteDimensional ℝ H := FiniteDimensional.of_injective L.toLinearMap L.injective
  let : Nontrivial H := Function.Injective.nontrivial L.symm.injective
  let μ := complexProductMeasure ν
  let : μ.IsAddHaarMeasure :=
    L.symm.isAddHaarMeasure_map ((volume : Measure ℂ).prod ν)
  have h₀ : μ.toSphere Set.univ ≠ 0 := by
    intro h
    exact Measure.toSphere_ne_zero μ (Measure.measure_univ_eq_zero.mp h)
  have ht : μ.toSphere Set.univ ≠ ⊤ := measure_ne_top _ _
  change (μ.toSphere Set.univ)⁻¹ * μ.toSphere (complexSphericalCap (1 / 4)) = _
  rw [complexSphericalCap_fifteen_sixteenths ν]
  let c := ENNReal.ofReal ((1 / 16 : ℝ) ^ Module.finrank ℂ E)
  change (μ.toSphere Set.univ)⁻¹ * (c * μ.toSphere Set.univ) = c
  calc
    _ = ((μ.toSphere Set.univ)⁻¹ * μ.toSphere Set.univ) * c := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel h₀ ht, one_mul]

end Measure

end

end GaplessYangMills

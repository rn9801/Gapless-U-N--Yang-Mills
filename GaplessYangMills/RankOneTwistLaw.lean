module

public import GaplessYangMills.BadEvents
public import GaplessYangMills.CapVector
public import GaplessYangMills.RankOneTwist
public import GaplessYangMills.UnitarySphere
public import GaplessYangMills.WilsonSliceKernel
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# The uniform rank-one twist law

Push the uniform sphere measure forward by the rank-one twist. Unitary
invariance of the sphere gives conjugation invariance of the resulting law.
-/

@[expose] public section

namespace GaplessYangMills

open Metric MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace ENNReal

noncomputable section

abbrev UnitaryVector (N : ℕ) := EuclideanSpace ℂ (Fin N)

local instance unitaryVector_realFiniteDimensional (N : ℕ) :
    FiniteDimensional ℝ (UnitaryVector N) := FiniteDimensional.trans ℝ ℂ _

def unitaryVectorIsometry {N : ℕ} (Q : UnitaryMatrix N) : UnitaryVector N ≃ₗᵢ[ℂ] UnitaryVector N :=
  let F := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N)
  Unitary.linearIsometryEquiv ⟨F Q.val, Unitary.map_mem F Q.property⟩

theorem unitaryVectorIsometry_apply {N : ℕ} (Q : UnitaryMatrix N) (v : UnitaryVector N) :
    unitaryVectorIsometry Q v = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N) Q.val v := rfl

theorem unitaryVector_dotProduct {N : ℕ} (v : UnitSphere (UnitaryVector N)) :
    star (WithLp.ofLp v.val) ⬝ᵥ WithLp.ofLp v.val = 1 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, mem_sphere_zero_iff_norm.mp v.property]
  norm_num

def sphereRankOneTwist {N : ℕ} (z : Circle) (v : UnitSphere (UnitaryVector N)) : UnitaryMatrix N :=
  rankOneTwist (WithLp.ofLp v.val) (unitaryVector_dotProduct v) z

private theorem continuous_sphereRankOneTwist {N : ℕ} (z : Circle) :
    Continuous (sphereRankOneTwist (N := N) z) :=
  continuous_rankOneTwist _ unitaryVector_dotProduct
    ((PiLp.continuous_ofLp _ _).comp continuous_subtype_val) z

/-- The law of rotation by π/4 on a uniformly sampled complex line. -/
def rankOneTwistLaw (N : ℕ) : Measure (UnitaryMatrix N) :=
  (uniformSphere (UnitaryVector N)).map (sphereRankOneTwist (Circle.exp (Real.pi / 4)))

instance rankOneTwistLaw_probability (N : ℕ) [NeZero N] :
    IsProbabilityMeasure (rankOneTwistLaw N) := by
  unfold rankOneTwistLaw
  infer_instance

/-- Unitary conjugation preserves the law of the twist. -/
theorem rankOneTwistLaw_conjugation {N : ℕ} (Q : UnitaryMatrix N) :
    MeasurePreserving (fun Z => Q * Z * Q⁻¹) (rankOneTwistLaw N) (rankOneTwistLaw N) := by
  let e := realLinearIsometry (unitaryVectorIsometry Q)
  let σ := uniformSphere (UnitaryVector N)
  let z := Circle.exp (Real.pi / 4)
  let f := sphereRankOneTwist (N := N) z
  let c (Z : UnitaryMatrix N) := Q * Z * Q⁻¹
  have hc : Measurable c := ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hf : Measurable f := (continuous_sphereRankOneTwist z).measurable
  have he := sphereIsometry_preserving e
  refine ⟨hc, ?_⟩
  have heq : c ∘ f = f ∘ sphereIsometry e := by
    funext v
    have hv : WithLp.ofLp ((sphereIsometry e) v).val = Q.val *ᵥ WithLp.ofLp v.val := by
      change WithLp.ofLp (unitaryVectorIsometry Q v.val) = _
      rw [unitaryVectorIsometry_apply, Matrix.ofLp_toEuclideanCLM]
    have h := rankOneTwist_mulVec_conj Q (WithLp.ofLp v.val) (unitaryVector_dotProduct v)
      (hv ▸ unitaryVector_dotProduct (sphereIsometry e v)) z
    simpa only [Function.comp_def, c, f, sphereRankOneTwist, hv] using h.symm
  change (σ.map f).map c = σ.map f
  rw [Measure.map_map hc hf, heq, ← Measure.map_map hf he.measurable, he.map_eq]

private theorem badUnitary_eigenvector {N : ℕ} (P : UnitaryMatrix N) (hP : badUnitary P) :
    ∃ (θ : ℝ) (v₀ : UnitSphere (UnitaryVector N)), Real.pi / 4 < |θ| ∧ |θ| ≤ Real.pi ∧
      unitaryVectorIsometry P v₀.val = (Circle.exp θ : ℂ) • v₀.val := by
  obtain ⟨z, hz, hangle⟩ := hP
  let F := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin N)
  have hspec : z ∈ spectrum ℂ ((F P.val : UnitaryVector N →L[ℂ] UnitaryVector N) :
      UnitaryVector N →ₗ[ℂ] UnitaryVector N) := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
      Matrix.spectrum_toLin]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (Polynomial.isRoot_of_mem_roots hz)
  obtain ⟨v, hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hspec).exists_hasEigenvector
  let u := (‖v‖ : ℂ)⁻¹ • v
  have hnorm : ‖u‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv.2)]
  let w : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr (norm_charpoly_root P hz)⟩
  have hζ : (Circle.exp (Complex.arg z) : ℂ) = z :=
    congrArg (fun y : Circle => (y : ℂ)) (Circle.exp_arg w)
  refine ⟨Complex.arg z, ⟨u, mem_sphere_zero_iff_norm.mpr hnorm⟩, hangle,
    Complex.abs_arg_le_pi _, ?_⟩
  change unitaryVectorIsometry P u = (Circle.exp (Complex.arg z) : ℂ) • u
  rw [hζ, unitaryVectorIsometry_apply, map_smul]
  change (‖v‖ : ℂ)⁻¹ • F P.val v = z • ((‖v‖ : ℂ)⁻¹ • v)
  rw [show F P.val v = z • v from hv.apply_eq_smul, smul_smul, smul_smul, mul_comm]

private theorem fundamentalKernel_sphereTwist {N : ℕ} (β : ℝ) (P : UnitaryMatrix N)
    (v : UnitSphere (UnitaryVector N)) (z : Circle) :
    fundamentalKernel β P (sphereRankOneTwist z v) =
      fundamentalKernel β P 1 * Real.exp ((N : ℝ) * β *
        ((((z⁻¹ : Circle) : ℂ) - 1) * ⟪v.val, unitaryVectorIsometry P v.val⟫_ℂ).re) := by
  let Z := sphereRankOneTwist z v
  have h := fundamentalKernel_leftInvariant β Z⁻¹ P Z
  rw [inv_mul_cancel] at h
  rw [← h]
  change fundamentalKernel β ((rankOneTwist (WithLp.ofLp v.val) (unitaryVector_dotProduct v) z)⁻¹ * P)
    1 = _
  rw [rankOneTwist_inv, fundamentalKernel_rankOneTwist, EuclideanSpace.inner_eq_star_dotProduct,
    unitaryVectorIsometry_apply, Matrix.ofLp_toEuclideanCLM, dotProduct_comm,
    show (1 : UnitaryMatrix N).val = 1 from rfl, Matrix.conjTranspose_one, mul_one]

private theorem twistedFundamentalKernel_cap_lower {N : ℕ} (β : ℝ) (hβ : 0 ≤ β)
    (P : UnitaryMatrix N) (v₀ v : UnitSphere (UnitaryVector N)) (θ : ℝ)
    (heig : unitaryVectorIsometry P v₀.val = (Circle.exp θ : ℂ) • v₀.val)
    (hθ : Real.pi / 4 ≤ |θ|) (hπ : |θ| ≤ Real.pi)
    (hcap : (15 : ℝ) / 16 ≤ ‖⟪v₀.val, v.val⟫_ℂ‖ ^ 2) :
    fundamentalKernel β P 1 * Real.exp ((N : ℝ) * β * badPenalty / 2) / 4 ≤
      twistedFundamentalKernel β (sphereRankOneTwist (Circle.exp (Real.pi / 4)) v) P 1 := by
  let δ := Real.pi / 4
  let Z := sphereRankOneTwist (Circle.exp δ) v
  let k := fundamentalKernel β P 1
  let c := Real.exp ((N : ℝ) * β * badPenalty / 2)
  have hv₀ := mem_sphere_zero_iff_norm.mp v₀.property
  have hv := mem_sphere_zero_iff_norm.mp v.property
  obtain ⟨s, hs, hgain⟩ := exists_unitary_cap_gain
    (unitaryVectorIsometry P) v₀.val v.val θ hv₀ hv heig hθ hπ hcap
  have hgain' : c ≤ Real.exp ((N : ℝ) * β *
      (((Circle.exp s : ℂ) - 1) * ⟪v.val, unitaryVectorIsometry P v.val⟫_ℂ).re) := by
    apply Real.exp_le_exp.mpr
    rw [show (N : ℝ) * β * badPenalty / 2 = (N : ℝ) * β * (badPenalty / 2) by ring]
    exact mul_le_mul_of_nonneg_left hgain (mul_nonneg (Nat.cast_nonneg _) hβ)
  change k * c / 4 ≤ twistedFundamentalKernel β Z P 1
  simp only [twistedFundamentalKernel, mul_one]
  have hbase : 0 < k := fundamentalKernel_pos β P 1
  have hplus := fundamentalKernel_sphereTwist β P v (Circle.exp δ)
  have hminus := fundamentalKernel_sphereTwist β P v (Circle.exp δ)⁻¹
  have hinv : sphereRankOneTwist (Circle.exp δ)⁻¹ v = Z⁻¹ :=
    (rankOneTwist_inv _ _ _).symm
  rw [hinv, inv_inv] at hminus
  change fundamentalKernel β P Z = _ at hplus
  have hδ : 0 ≤ Real.pi / 4 := by positivity
  rcases (abs_eq hδ).mp hs with he | he
  · rw [he] at hgain'
    have h := mul_le_mul_of_nonneg_left hgain' hbase.le
    rw [← hminus] at h
    linarith [fundamentalKernel_pos β P Z]
  · rw [he, Circle.exp_neg] at hgain'
    have h := mul_le_mul_of_nonneg_left hgain' hbase.le
    rw [← hplus] at h
    linarith [fundamentalKernel_pos β P Z⁻¹]

/-- The modified factor has the required exponential gain on a bad face. -/
theorem rankOneTwistMultiplier_bad_lower {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 40 ≤ β)
    (P : UnitaryMatrix N) (hP : badUnitary P) :
    Real.exp ((N : ℝ) * β * badPenalty / 4) ≤ wilsonTwistMultiplier (rankOneTwistLaw N) β P := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  let N := n + 1
  let E := UnitaryVector N
  let σ := uniformSphere E
  let k := fundamentalKernel β P 1
  let c := Real.exp ((N : ℝ) * β * badPenalty / 2)
  let z := Circle.exp (Real.pi / 4)
  let f (v : UnitSphere E) := twistedFundamentalKernel β (sphereRankOneTwist z v) P 1
  obtain ⟨θ, v₀, hθ, hπ, heig⟩ := badUnitary_eigenvector P hP
  let S : Set (UnitSphere E) := {v | (15 : ℝ) / 16 ≤ ‖⟪v₀.val, v.val⟫_ℂ‖ ^ 2}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    ((continuous_const.inner continuous_subtype_val).norm.pow 2).measurable
  have hcap : σ.real S = (1 / 16 : ℝ) ^ n := by
    have hdim : Module.finrank ℂ E = n + 1 := finrank_euclideanSpace_fin
    change ((uniformSphere E) S).toReal = _
    rw [uniformSphere_cap n hdim, ENNReal.toReal_ofReal (by positivity)]
  have hf : Integrable f σ := ((continuous_twistedFundamentalKernel β P 1).comp
    (continuous_sphereRankOneTwist z)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbound : (∫ v, S.indicator (fun _ => k * c / 4) v ∂σ) ≤ ∫ v, f v ∂σ := by
    apply integral_mono ((integrable_const _).indicator hS) hf
    intro v
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_mem hv]
      exact twistedFundamentalKernel_cap_lower β (by linarith) P v₀ v θ heig hθ.le hπ hv
    · rw [Set.indicator_of_notMem hv]
      unfold f twistedFundamentalKernel
      linarith [fundamentalKernel_pos β P (sphereRankOneTwist z v * 1),
        fundamentalKernel_pos β P ((sphereRankOneTwist z v)⁻¹ * 1), fundamentalKernel_pos β P 1]
  have hmap : (∫ v, f v ∂σ) = averagedFundamentalKernel (rankOneTwistLaw N) β P 1 :=
    (integral_map (continuous_sphereRankOneTwist z).measurable.aemeasurable
      (continuous_twistedFundamentalKernel β P 1).aestronglyMeasurable).symm
  rw [integral_indicator_const _ hS, smul_eq_mul, hcap, hmap] at hbound
  have hcoeff : (1 / 16 : ℝ) ^ n * (k * c / 4) = (4 / (16 : ℝ) ^ N * c) * k := by
    dsimp only [N]
    rw [div_pow, one_pow, pow_succ]
    field_simp
    ring
  rw [hcoeff] at hbound
  refine (cap_weight_lower_bound N hβ).trans ?_
  change 4 / (16 : ℝ) ^ N * c ≤ averagedFundamentalKernel (rankOneTwistLaw N) β P 1 / k
  exact (le_div_iff₀ (fundamentalKernel_pos β P 1)).mpr hbound

end

end GaplessYangMills

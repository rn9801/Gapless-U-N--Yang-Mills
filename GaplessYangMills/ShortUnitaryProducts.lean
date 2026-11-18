module

public import GaplessYangMills.UnitaryLog
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Determinant phase for short products

Three rotations through angles at most π/4 stay in the domain of the principal
logarithm when scaled simultaneously. Applying this to the two halves of a
six-factor loop gives a vanishing total angle.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix.Norms.L2Operator
open selfAdjoint

private theorem norm_unitary_action {N : ℕ} (U : UnitaryMatrix N)
    (v : EuclideanSpace ℂ (Fin N)) :
    ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) U.val v‖ = ‖v‖ := by
  let F := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (F U.val)).mpr _ v
  suffices h : star (F U.val) * F U.val = 1 by
    exact h
  rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem U.property, map_one]

/-- If three unitary jumps are short, they cannot take a nonzero vector
to its antipode. This gives a branch-cut bound for the matrix product. -/
theorem norm_three_unitaries_sub_one_lt_two {N : ℕ} (A B C : UnitaryMatrix N)
    (hA : ‖A.val - 1‖ ≤ 4 / 5) (hB : ‖B.val - 1‖ ≤ 4 / 5) (hC : ‖C.val - 1‖ ≤ 4 / 5) :
    ‖(A * B * C).val - 1‖ < 2 := by
  apply (Unitary.norm_sub_one_lt_two_iff (A * B * C).property).mpr
  intro h
  let E := EuclideanSpace ℂ (Fin N)
  let F := Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ)
  have hs : (-1 : ℂ) ∈ spectrum ℂ ((F (A * B * C).val : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
      Matrix.spectrum_toLin]
    exact h
  obtain ⟨v, hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hs).exists_hasEigenvector
  let b : E := F C.val v
  let c : E := F B.val b
  have hb : ‖b‖ = ‖v‖ := norm_unitary_action C v
  have hc : ‖c‖ = ‖v‖ := (norm_unitary_action B b).trans hb
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
  have hend : F A.val c = -v := by
    have he := hv.apply_eq_smul
    change F ((A.val * B.val) * C.val) v = (-1 : ℂ) • v at he
    simpa only [map_mul, mul_apply_eq_comp,
      neg_one_smul, b, c] using he
  have hjump (U : UnitaryMatrix N) (w : E) (hU : ‖U.val - 1‖ ≤ 4 / 5) :
      ‖F U.val w - w‖ ≤ (4 / 5) * ‖w‖ := by
    have he : F U.val w - w = F (U.val - 1) w := by
      rw [map_sub, sub_apply, map_one, one_apply_eq_self]
    rw [he]
    exact ((F (U.val - 1)).le_opNorm w).trans <|
      mul_le_mul_of_nonneg_right hU (norm_nonneg w)
  have h₁ : ‖b - v‖ ≤ (4 / 5) * ‖v‖ := hjump C v hC
  have h₂ : ‖c - b‖ ≤ (4 / 5) * ‖v‖ := hb ▸ hjump B b hB
  have h₃ : ‖-v - c‖ ≤ (4 / 5) * ‖v‖ := by
    simpa only [hend, hc] using hjump A c hA
  have hplus : ‖b + v‖ ≤ (8 / 5) * ‖v‖ := by
    have he : (-v - c) + (c - b) = -(b + v) := by abel
    have hi := norm_add_le (-v - c) (c - b)
    rw [he, norm_neg] at hi
    linarith
  have hpara := parallelogram_law_with_norm ℂ b v
  rw [hb] at hpara
  have hl := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h₁
  have hr := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hplus
  nlinarith

private theorem short_expUnitary {N : ℕ} (X : HermitianMatrix N)
    (hX : ‖X‖ ≤ Real.pi / 4) :
    ‖(expUnitary X).val - 1‖ ≤ 4 / 5 := by
  have hπ := Real.pi_pos
  have hn : ‖X‖ ≤ Real.pi := hX.trans (by linarith)
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [norm_sq_expUnitary_sub_one hn]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (norm_nonneg X)
    (show Real.pi / 4 ≤ Real.pi by linarith) hX
  rw [Real.cos_pi_div_four] at hcos
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : (7 : ℝ) / 5 ≤ Real.sqrt 2 := by
    apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg 2)).mp
    rw [hsq]
    norm_num
  linarith

private theorem norm_smul_short {N : ℕ} (X : HermitianMatrix N)
    (hX : ‖X‖ ≤ Real.pi / 4) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖t • X‖ ≤ Real.pi / 4 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg X) ht.2).trans hX

theorem phaseTrace_arg_three {N : ℕ} (X Y Z : HermitianMatrix N)
    (hX : ‖X‖ ≤ Real.pi / 4) (hY : ‖Y‖ ≤ Real.pi / 4) (hZ : ‖Z‖ ≤ Real.pi / 4) :
    phaseTrace (Unitary.argSelfAdjoint (expUnitary X * expUnitary Y * expUnitary Z)) =
      phaseTrace X + phaseTrace Y + phaseTrace Z := by
  let I := Set.Icc (0 : ℝ) 1
  let U (t : ℝ) := expUnitary (t • X) * expUnitary (t • Y) * expUnitary (t • Z)
  let d (t : ℝ) :=
    (phaseTrace (Unitary.argSelfAdjoint (U t)) -
      t * (phaseTrace X + phaseTrace Y + phaseTrace Z)) / (2 * Real.pi)
  have hU (t : ℝ) (ht : t ∈ I) : ‖(U t).val - 1‖ < 2 :=
    norm_three_unitaries_sub_one_lt_two _ _ _
      (short_expUnitary _ (norm_smul_short X hX ht))
      (short_expUnitary _ (norm_smul_short Y hY ht))
      (short_expUnitary _ (norm_smul_short Z hZ ht))
  have hc : ContinuousOn d I := by
    have hu : Continuous U := by unfold U; fun_prop
    have hmap : Set.MapsTo U I (Metric.ball (1 : UnitaryMatrix N) 2) := by
      intro t ht
      simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, OneMemClass.coe_one] using hU t ht
    have harg := Unitary.continuousOn_argSelfAdjoint.comp hu.continuousOn hmap
    exact (continuous_phaseTrace N).comp_continuousOn harg |>.sub
      (continuous_id.mul continuous_const).continuousOn |>.div_const (2 * Real.pi)
  have hint : Set.MapsTo d I (Set.range ((↑) : ℤ → ℝ)) := by
    intro t ht
    have hexp : Circle.exp (phaseTrace (Unitary.argSelfAdjoint (U t))) =
        Circle.exp (t * (phaseTrace X + phaseTrace Y + phaseTrace Z)) := by
      rw [← unitaryDet_expUnitary, expUnitary_argSelfAdjoint (hU t ht)]
      simp only [U, map_mul, unitaryDet_expUnitary, phaseTrace_smul, mul_add, Circle.exp_add]
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
    refine ⟨n, ?_⟩
    dsimp only [d]
    rw [hn, add_sub_cancel_left, mul_div_cancel_right₀ _ Real.two_pi_pos.ne']
  have hdis : IsDiscrete (Set.range ((↑) : ℤ → ℝ)) :=
    Real.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range
  have hconst := (isPreconnected_Icc (α := ℝ)).constant_of_mapsTo hdis hc hint
    (show (1 : ℝ) ∈ I by dsimp [I]; exact ⟨zero_le_one, le_rfl⟩)
    (show (0 : ℝ) ∈ I by dsimp [I]; exact ⟨le_rfl, zero_le_one⟩)
  have hargOne : Unitary.argSelfAdjoint (1 : UnitaryMatrix N) = 0 := by
    rw [← expUnitary_zero, argSelfAdjoint_expUnitary]
    simpa using Real.pi_pos
  have hzero : d 0 = 0 := by simp [d, U, hargOne]
  rw [hzero] at hconst
  simpa [d, U, Real.two_pi_pos.ne', sub_eq_zero] using hconst

theorem phaseTrace_six_eq_zero {N : ℕ} (A B C D E F : HermitianMatrix N)
    (hA : ‖A‖ ≤ Real.pi / 4) (hB : ‖B‖ ≤ Real.pi / 4) (hC : ‖C‖ ≤ Real.pi / 4)
    (hD : ‖D‖ ≤ Real.pi / 4) (hE : ‖E‖ ≤ Real.pi / 4) (hF : ‖F‖ ≤ Real.pi / 4)
    (h : expUnitary A * expUnitary B * expUnitary C *
      expUnitary D * expUnitary E * expUnitary F = 1) :
    phaseTrace A + phaseTrace B + phaseTrace C +
      phaseTrace D + phaseTrace E + phaseTrace F = 0 := by
  have hprod : expUnitary A * expUnitary B * expUnitary C =
      expUnitary (-F) * expUnitary (-E) * expUnitary (-D) := by
    have heq : (expUnitary A * expUnitary B * expUnitary C) *
        (expUnitary D * expUnitary E * expUnitary F) = 1 := by
      simpa only [mul_assoc] using h
    simpa only [expUnitary_neg, mul_inv_rev, mul_assoc] using eq_inv_of_mul_eq_one_left heq
  have h₁ := phaseTrace_arg_three A B C hA hB hC
  have h₂ := phaseTrace_arg_three (-F) (-E) (-D)
    (by simpa only [norm_neg] using hF) (by simpa only [norm_neg] using hE)
    (by simpa only [norm_neg] using hD)
  rw [hprod, h₂, phaseTrace_neg, phaseTrace_neg, phaseTrace_neg] at h₁
  linarith

end GaplessYangMills

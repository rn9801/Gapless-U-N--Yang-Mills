module

public import GaplessYangMills.Eigenangles
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Principal determinant phase of a unitary matrix

The trace of the principal Hermitian logarithm equals the sum of the
multiplicity-counted principal eigenangles whenever the spectrum avoids −1.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix Matrix.Norms.L2Operator
open selfAdjoint

noncomputable section

abbrev HermitianMatrix (N : ℕ) := selfAdjoint (Matrix (Fin N) (Fin N) ℂ)

def principalAngleSum {N : ℕ} (U : UnitaryMatrix N) : ℝ :=
  (U.val.charpoly.roots.map Complex.arg).sum

def phaseTrace {N : ℕ} (X : HermitianMatrix N) : ℝ :=
  X.val.trace.re

@[simp] theorem phaseTrace_zero (N : ℕ) : phaseTrace (0 : HermitianMatrix N) = 0 := by
  simp [phaseTrace]

@[simp] theorem phaseTrace_neg {N : ℕ} (X : HermitianMatrix N) :
    phaseTrace (-X) = -phaseTrace X := by
  simp [phaseTrace]

@[simp] theorem phaseTrace_smul {N : ℕ} (t : ℝ) (X : HermitianMatrix N) :
    phaseTrace (t • X) = t * phaseTrace X := by
  simp [phaseTrace, Matrix.trace_smul, Complex.real_smul, Complex.mul_re]

@[fun_prop] theorem continuous_phaseTrace (N : ℕ) :
    Continuous (phaseTrace (N := N)) :=
  Complex.continuous_re.comp (Continuous.matrix_trace continuous_subtype_val)

private theorem isHermitian_val {N : ℕ} (X : HermitianMatrix N) : X.val.IsHermitian := X.prop

private theorem phaseTrace_eq_sum_eigenvalues {N : ℕ} (X : HermitianMatrix N) :
    phaseTrace X = ∑ j, (isHermitian_val X).eigenvalues j := by
  rw [phaseTrace, (isHermitian_val X).trace_eq_sum_eigenvalues, Complex.re_sum]
  rfl

private theorem expUnitary_diagonalization {N : ℕ} (X : HermitianMatrix N) :
    let h := isHermitian_val X
    let e := h.eigenvectorUnitary
    (expUnitary X).val =
      e.val * Matrix.diagonal (fun j => (Circle.exp (h.eigenvalues j) : ℂ)) * (star e).val := by
  dsimp only
  set h := isHermitian_val X
  let e := h.eigenvectorUnitary
  let d : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun j => (h.eigenvalues j : ℂ))
  have hX : X.val = e.val * d * (star e).val := h.spectral_theorem
  have he : e.val⁻¹ = (star e).val := Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self e)
  have hs : Complex.I • (e.val * d * (star e).val) =
      e.val * (Complex.I • d) * (star e).val := by
    rw [mul_smul_comm, smul_mul_assoc]
  conv_lhs =>
    rw [expUnitary_coe, hX, hs, ← he, Matrix.exp_conj _ _ (Unitary.isUnit_coe (U := e)), he]
    dsimp only [d]
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  have hd : NormedSpace.exp (Complex.I • (fun j : Fin N => (h.eigenvalues j : ℂ))) =
      fun j => (Circle.exp (h.eigenvalues j) : ℂ) := by
    funext j
    rw [Pi.coe_exp, Circle.coe_exp, ← Complex.exp_eq_exp_ℂ]
    change Complex.exp (Complex.I * (h.eigenvalues j : ℂ)) = _
    rw [mul_comm]
  rw [hd]

private theorem roots_expUnitary {N : ℕ} (X : HermitianMatrix N) :
    (expUnitary X).val.charpoly.roots =
      (Finset.univ : Finset (Fin N)).val.map
        (fun j => (Circle.exp ((isHermitian_val X).eigenvalues j) : ℂ)) := by
  rw [expUnitary_diagonalization]
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, Unitary.coe_star, Unitary.coe_star_mul_self, one_mul]
  have hn : (Matrix.diagonal fun j =>
      (Circle.exp ((isHermitian_val X).eigenvalues j) : ℂ)).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  rw [Matrix.charpoly_diagonal] at hn ⊢
  rw [Polynomial.roots_prod _ _ hn]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

theorem unitaryDet_expUnitary {N : ℕ} (X : HermitianMatrix N) :
    unitaryDet N (expUnitary X) = Circle.exp (phaseTrace X) := by
  apply Circle.ext
  change (expUnitary X).val.det = _
  rw [Matrix.det_eq_prod_roots_charpoly, roots_expUnitary, Finset.prod_map_val]
  rw [phaseTrace_eq_sum_eigenvalues]
  change (∏ j, Circle.coeHom (Circle.exp ((isHermitian_val X).eigenvalues j))) = _
  rw [← map_prod]
  exact congrArg Circle.coeHom (map_sum Circle.expHom _ _).symm

theorem principalAngleSum_expUnitary {N : ℕ} (X : HermitianMatrix N) (hX : ‖X‖ < Real.pi) :
    principalAngleSum (expUnitary X) = phaseTrace X := by
  have he (j : Fin N) : |(isHermitian_val X).eigenvalues j| < Real.pi := by
    let : Nonempty (Fin N) := ⟨j⟩
    exact (spectrum.norm_le_norm_of_mem
      ((isHermitian_val X).eigenvalues_mem_spectrum_real j)).trans_lt hX
  have ha (j : Fin N) :
      Complex.arg (Circle.exp ((isHermitian_val X).eigenvalues j) : ℂ) =
        (isHermitian_val X).eigenvalues j :=
    Circle.arg_exp (neg_lt_of_abs_lt (he j)) (lt_of_abs_lt (he j)).le
  rw [principalAngleSum, roots_expUnitary, Multiset.map_map,
    phaseTrace_eq_sum_eigenvalues, Finset.sum_map_val]
  simp only [Function.comp_def, ha]

theorem principalAngleSum_eq_phaseTrace_arg {N : ℕ} (U : UnitaryMatrix N)
    (hU : ‖U.val - 1‖ < 2) :
    principalAngleSum U = phaseTrace (Unitary.argSelfAdjoint U) := by
  have hlog : ‖Unitary.argSelfAdjoint U‖ < Real.pi := by
    rw [Unitary.norm_argSelfAdjoint hU]
    apply Real.arccos_lt_pi.mpr
    nlinarith [sq_lt_sq₀ (norm_nonneg (U.val - 1)) (by norm_num : (0 : ℝ) ≤ 2) |>.mpr hU]
  conv_lhs => rw [← expUnitary_argSelfAdjoint (u := U) hU]
  exact principalAngleSum_expUnitary _ hlog

theorem unitaryCharpoly_conj {N : ℕ} (V U : UnitaryMatrix N) :
    (V * U * V⁻¹).val.charpoly = U.val.charpoly := by
  change (V.val * U.val * (star V).val).charpoly = _
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, Unitary.coe_star, Unitary.coe_star_mul_self, one_mul]

theorem principalAngleSum_conj {N : ℕ} (V U : UnitaryMatrix N) :
    principalAngleSum (V * U * V⁻¹) = principalAngleSum U := by
  simp only [principalAngleSum, unitaryCharpoly_conj]

theorem expUnitary_neg {N : ℕ} (X : HermitianMatrix N) :
    expUnitary (-X) = (expUnitary X)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← (Commute.refl X.val).neg_left.expUnitary_add, neg_add_cancel, expUnitary_zero]

end

end GaplessYangMills

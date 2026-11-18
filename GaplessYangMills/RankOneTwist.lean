module

public import GaplessYangMills.WilsonKernel

/-!
# Rank-one unitary twists

Rotating the line spanned by a unit vector changes the Wilson trace by
one scalar matrix expectation.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix

/-- The outer product of a vector and its adjoint. -/
def lineProjection {N : ℕ} (v : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.vecMulVec v (star v)

theorem lineProjection_star {N : ℕ} (v : Fin N → ℂ) :
    (lineProjection v)ᴴ = lineProjection v := by
  simp [lineProjection]

theorem lineProjection_mul_self {N : ℕ} (v : Fin N → ℂ) (hv : star v ⬝ᵥ v = 1) :
    lineProjection v * lineProjection v = lineProjection v := by
  simp [lineProjection, Matrix.vecMulVec_mul_vecMulVec, hv]

private theorem trace_lineProjection_mul {N : ℕ} (v : Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ) :
    (lineProjection v * A).trace = star v ⬝ᵥ (A *ᵥ v) := by
  rw [Matrix.trace_mul_comm, lineProjection, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm]

/-- The twist is multiplication by a circle element on the given line
and the identity on its orthogonal complement. -/
noncomputable def rankOneTwist {N : ℕ} (v : Fin N → ℂ) (hv : star v ⬝ᵥ v = 1)
    (z : Circle) : UnitaryMatrix N := by
  let P := lineProjection v
  let c := (z : ℂ) - 1
  have hp : P * P = P := lineProjection_mul_self v hv
  have hstar : star (1 + c • P) = 1 + star c • P := by
    rw [star_add, star_one, star_smul]
    exact congrArg (fun M => 1 + star c • M) (lineProjection_star v)
  have hcircle : (z : ℂ) * star (z : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
  have hcoeff : c + star c + c * star c = 0 := by
    simp only [c, star_sub, star_one]
    linear_combination hcircle
  have hproduct (a b : ℂ) (h : a + b + a * b = 0) :
      (1 + a • P) * (1 + b • P) = 1 := by
    calc
      _ = 1 + (a + b + b * a) • P := by
        simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
          mul_smul_comm, smul_add, smul_smul, hp, add_smul]
        abel
      _ = 1 := by rw [mul_comm b a, h, zero_smul, add_zero]
  refine ⟨1 + c • P, Unitary.mem_iff.mpr ⟨?_, ?_⟩⟩
  · rw [hstar]
    apply hproduct
    simpa only [add_comm (star c) c, mul_comm (star c) c] using hcoeff
  · rw [hstar]
    exact hproduct _ _ hcoeff

theorem trace_rankOneTwist_mul {N : ℕ} (v : Fin N → ℂ) (hv : star v ⬝ᵥ v = 1)
    (z : Circle) (A : Matrix (Fin N) (Fin N) ℂ) :
    ((rankOneTwist v hv z).val * A).trace =
      A.trace + ((z : ℂ) - 1) * (star v ⬝ᵥ (A *ᵥ v)) := by
  change ((1 + ((z : ℂ) - 1) • lineProjection v) * A).trace = _
  rw [add_mul, one_mul, smul_mul_assoc, Matrix.trace_add, Matrix.trace_smul,
    trace_lineProjection_mul, smul_eq_mul]

/-- The kernel ratio is the exponential gain evaluated at the real part of
the rank-one expectation for the unmodified face. -/
theorem fundamentalKernel_rankOneTwist {N : ℕ} (β : ℝ) (A B : UnitaryMatrix N)
    (v : Fin N → ℂ) (hv : star v ⬝ᵥ v = 1) (z : Circle) :
    fundamentalKernel β (rankOneTwist v hv z * A) B =
      fundamentalKernel β A B *
        Real.exp ((N : ℝ) * β *
          (((z : ℂ) - 1) * (star v ⬝ᵥ ((A.val * B.valᴴ) *ᵥ v))).re) := by
  unfold fundamentalKernel
  change Real.exp ((N : ℝ) * β * (((rankOneTwist v hv z).val * A.val) * B.valᴴ).trace.re) = _
  rw [Matrix.mul_assoc, trace_rankOneTwist_mul, Complex.add_re, mul_add, Real.exp_add]

end GaplessYangMills

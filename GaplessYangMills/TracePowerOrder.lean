module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Trace powers in positive matrix order

This is the finite-dimensional trace comparison for an ordered pair of
sampled transfer kernels. The derivative along the positive segment has
nonnegative trace by cyclicity.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_mul_nonneg_of_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  let S := CFC.sqrt A
  have hS : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hSq : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  calc
    0 ≤ (S * B * Sᴴ).trace := (hB.mul_mul_conjTranspose_same S).trace_nonneg
    _ = (A * B).trace := by rw [Matrix.trace_mul_comm, hS, ← mul_assoc, hSq]

noncomputable section

private def powerDerivative (M D : Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  Nat.rec 0 (fun k prev => prev * M + M ^ k * D) n

private theorem powerDerivative_succ (M D : Matrix ι ι ℝ) (n : ℕ) :
    powerDerivative M D (n + 1) = powerDerivative M D n * M + M ^ n * D := rfl

private theorem trace_powerDerivative_mul (M D : Matrix ι ι ℝ) (n k : ℕ) :
    (powerDerivative M D (n + 1) * M ^ k).trace =
      ((n + 1 : ℕ) : ℝ) * (D * M ^ (n + k)).trace := by
  induction n generalizing k with
  | zero => simp [powerDerivative]
  | succ n ih =>
    have hc : (M ^ (n + 1) * D * M ^ k).trace = (D * M ^ (n + 1 + k)).trace := by
      rw [mul_assoc, Matrix.trace_mul_comm (M ^ (n + 1)), mul_assoc, ← pow_add, Nat.add_comm k]
    rw [powerDerivative_succ, add_mul, Matrix.trace_add, hc, mul_assoc, ← pow_succ', ih]
    rw [show n + (k + 1) = n + 1 + k by omega]
    push_cast
    ring

private theorem hasDerivAt_matrix_power {M : ℝ → Matrix ι ι ℝ}
    {D : Matrix ι ι ℝ} {t : ℝ} (hM : HasDerivAt M D t) (n : ℕ) :
    HasDerivAt (fun x => M x ^ n) (powerDerivative (M t) D n) t := by
  induction n with
  | zero =>
    change HasDerivAt (fun _ => (1 : Matrix ι ι ℝ)) 0 t
    exact hasDerivAt_const t 1
  | succ n ih =>
    have h := ih.mul hM
    change HasDerivAt (fun x => M x ^ n * M x)
      (powerDerivative (M t) D n * M t + M t ^ n * D) t at h
    simpa only [pow_succ, powerDerivative_succ] using h

/-- Positive matrix order bounds every nonnegative integer trace power. -/
theorem trace_pow_mono_of_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hBA : (B - A).PosSemidef) (n : ℕ) :
    (A ^ n).trace ≤ (B ^ n).trace := by
  cases n with
  | zero => simp
  | succ n =>
    let D := B - A
    let M (t : ℝ) := A + t • D
    let T := (Matrix.traceLinearMap ι ℝ ℝ).toContinuousLinearMap
    let F (t : ℝ) := (M t ^ (n + 1)).trace
    let G (t : ℝ) := ((n + 1 : ℕ) : ℝ) * (D * M t ^ n).trace
    have hderiv (t : ℝ) : HasDerivAt F (G t) t := by
      have hm : HasDerivAt M D t := by
        simpa only [M, one_smul] using ((hasDerivAt_id' t).smul_const D).const_add A
      have ht := T.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_matrix_power hm (n + 1))
      change HasDerivAt F (powerDerivative (M t) D (n + 1)).trace t at ht
      have he : (powerDerivative (M t) D (n + 1)).trace = G t := by
        simpa only [pow_zero, mul_one, add_zero, G] using trace_powerDerivative_mul (M t) D n 0
      rwa [he] at ht
    have hG (t : ℝ) (ht : t ∈ interior (Set.Icc (0 : ℝ) 1)) : 0 ≤ G t := by
      have ht₀ : 0 ≤ t := (interior_subset ht).1
      have hp : (M t).PosSemidef := hA.add (hBA.smul ht₀)
      exact mul_nonneg (Nat.cast_nonneg _) (trace_mul_nonneg_of_posSemidef hBA (hp.pow n))
    have hcont : Continuous F := continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
    have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
      hcont.continuousOn (fun t _ => (hderiv t).hasDerivWithinAt) hG
    have hend := hm (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) (by norm_num : (0 : ℝ) ≤ 1)
    simpa [F, M, D, add_comm A] using hend

end

end GaplessYangMills

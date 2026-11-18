module

public import GaplessYangMills.Lattice
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Central curvature in a local continuum trivialization

The scalar part of the connection commutes with all matrices. The trace
inner product splits orthogonally once the other curvature is traceless.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix Matrix.Norms.Elementwise

noncomputable section

abbrev LocalConnection (N : ℕ) := Axis → (Axis → ℝ) → Matrix (Fin N) (Fin N) ℂ

def continuumCentral (N : ℕ) (a : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  a • (Complex.I • (1 : Matrix (Fin N) (Fin N) ℂ))

def continuumCurvature {N : ℕ} (A : LocalConnection N) (i j : Axis) (x : Axis → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fderiv ℝ (A j) x (Pi.single i 1) - fderiv ℝ (A i) x (Pi.single j 1) +
    (A i x * A j x - A j x * A i x)

private theorem continuumCentral_comm {N : ℕ} (a : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    continuumCentral N a * M = M * continuumCentral N a := by
  simp [continuumCentral]

theorem continuumCurvature_add_central {N : ℕ} (A : LocalConnection N)
    (a : Axis → (Axis → ℝ) → ℝ) (i j : Axis) (x : Axis → ℝ)
    (hA : ∀ k, DifferentiableAt ℝ (A k) x) (ha : ∀ k, DifferentiableAt ℝ (a k) x) :
    continuumCurvature (fun k y => A k y + continuumCentral N (a k y)) i j x =
      continuumCurvature A i j x +
        continuumCentral N (fderiv ℝ (a j) x (Pi.single i 1) -
          fderiv ℝ (a i) x (Pi.single j 1)) := by
  have hdiff (k : Axis) : DifferentiableAt ℝ (fun y => continuumCentral N (a k y)) x :=
    (ha k).smul_const _
  have hderiv (k : Axis) (u : Axis → ℝ) :
      fderiv ℝ (fun y => continuumCentral N (a k y)) x u =
        continuumCentral N (fderiv ℝ (a k) x u) := by
    let C : Matrix (Fin N) (Fin N) ℂ := Complex.I • 1
    have hh : HasFDerivAt (fun y => a k y • C) ((fderiv ℝ (a k) x).smulRight C) x :=
      (ha k).hasFDerivAt.smul_const C
    exact congrArg (fun D : (Axis → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ => D u) hh.fderiv
  have hsum (k : Axis) : fderiv ℝ (fun y => A k y + continuumCentral N (a k y)) x =
      fderiv ℝ (A k) x + fderiv ℝ (fun y => continuumCentral N (a k y)) x :=
    fderiv_add (hA k) (hdiff k)
  have hbracket :
      (A i x + continuumCentral N (a i x)) * (A j x + continuumCentral N (a j x)) -
        (A j x + continuumCentral N (a j x)) * (A i x + continuumCentral N (a i x)) =
          A i x * A j x - A j x * A i x := by
    simp only [add_mul, mul_add]
    rw [continuumCentral_comm (a i x) (A j x), continuumCentral_comm (a j x) (A i x),
      continuumCentral_comm (a j x) (continuumCentral N (a i x))]
    abel
  simp only [continuumCurvature, hsum, add_apply, hderiv, hbracket]
  simp only [continuumCentral, sub_smul]
  abel

def traceNormSquared {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (Mᴴ * M).trace.re

theorem traceNormSquared_add_scalar {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.trace = 0) (z : ℂ) :
    traceNormSquared (M + z • 1) = traceNormSquared M + N * ‖z‖ ^ 2 := by
  simp [traceNormSquared, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, add_mul,
    mul_add, smul_smul, hM, Complex.mul_re]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem traceNormSquared_add_central {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (hM : M.trace = 0) (t : ℝ) :
    traceNormSquared (M + continuumCentral N t) = traceNormSquared M + N * t ^ 2 := by
  rw [continuumCentral, ← smul_assoc, Complex.real_smul, traceNormSquared_add_scalar M hM]
  simp [sq_abs]

theorem traced_central_curvature {N : ℕ} (hN : 0 < N)
    (M : Matrix (Fin N) (Fin N) ℂ) (hM : M.trace = 0) (t : ℝ) :
    (M + continuumCentral N t).trace.im / N = t := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [continuumCentral, Matrix.trace_smul, hM, Complex.real_smul, Complex.mul_im, hn]

end

end GaplessYangMills

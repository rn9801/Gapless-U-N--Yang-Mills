module

public import GaplessYangMills.Lattice
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Linear
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

theorem traced_central_curvature_complex {N : ℕ} (hN : 0 < N)
    (M : Matrix (Fin N) (Fin N) ℂ) (hM : M.trace = 0) (t : ℝ) :
    -Complex.I * (M + continuumCentral N t).trace / (N : ℂ) = (t : ℂ) := by
  have hN₀ : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : -Complex.I * ((t : ℂ) * (Complex.I * (N : ℂ))) = (t : ℂ) * (N : ℂ) := by
    calc
      _ = (-Complex.I * Complex.I) * ((t : ℂ) * (N : ℂ)) := by ring
      _ = _ := by simp
  simp only [continuumCentral, Matrix.trace_add, hM, zero_add, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, Complex.real_smul, smul_eq_mul, he, mul_div_cancel_right₀ _ hN₀]

private def continuumTrace (N : ℕ) : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ :=
  (Matrix.traceLinearMap (Fin N) ℝ ℂ).toContinuousLinearMap

theorem continuumCurvature_trace_zero {N : ℕ} (A : LocalConnection N) (i j : Axis) (x : Axis → ℝ)
    (hA : ∀ k, DifferentiableAt ℝ (A k) x) (htrace : ∀ k y, (A k y).trace = 0) :
    (continuumCurvature A i j x).trace = 0 := by
  let L := continuumTrace N
  have hd (k : Axis) (v : Axis → ℝ) : (fderiv ℝ (A k) x v).trace = 0 := by
    have hzero : L ∘ A k = fun _ => 0 := funext (htrace k)
    have hconst : fderiv ℝ (L ∘ A k) x = 0 :=
      (congrArg (fun f : (Axis → ℝ) → ℂ => fderiv ℝ f x) hzero).trans (fderiv_const_apply 0)
    have h := (L.fderiv_comp_left (hA k)).symm.trans hconst
    exact congrArg (fun D : (Axis → ℝ) →L[ℝ] ℂ => D v) h
  simp only [continuumCurvature, Matrix.trace_add, Matrix.trace_sub, hd, sub_self, zero_add]
  rw [Matrix.trace_mul_comm, sub_self]

def centralPotential {N : ℕ} (A : LocalConnection N) (i : Axis) (x : Axis → ℝ) : ℝ :=
  (A i x).trace.im / N

def tracelessConnection {N : ℕ} (A : LocalConnection N) : LocalConnection N :=
  fun i x => A i x - continuumCentral N (centralPotential A i x)

theorem tracelessConnection_antiHermitian {N : ℕ} (A : LocalConnection N)
    (hskew : ∀ i x, (A i x)ᴴ = -A i x) (i : Axis) (x : Axis → ℝ) :
    (tracelessConnection A i x)ᴴ = -tracelessConnection A i x := by
  have hcentral (s : ℝ) : (continuumCentral N s)ᴴ = -continuumCentral N s := by
    simp [continuumCentral]
  rw [tracelessConnection, Matrix.conjTranspose_sub, hskew, hcentral]
  abel

theorem tracelessConnection_trace_zero {N : ℕ} (hN : 0 < N) (A : LocalConnection N)
    (hskew : ∀ i x, (A i x)ᴴ = -A i x) (i : Axis) (x : Axis → ℝ) :
    (tracelessConnection A i x).trace = 0 := by
  have hN₀ : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hreal : (A i x).trace.re = 0 := by
    have h := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M.trace.re) (hskew i x)
    simp only [Matrix.trace_conjTranspose, Matrix.trace_neg, Complex.star_def, Complex.conj_re, Complex.neg_re] at h
    linarith
  apply Complex.ext
  · simp [tracelessConnection, continuumCentral, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, hreal]
  · simp [tracelessConnection, centralPotential, continuumCentral, Matrix.trace_smul, Complex.real_smul,
      Complex.mul_im, hN₀]

/-- The curvature and trace action of an anti-Hermitian connection split
into the traceless curvature and the ordinary exterior derivative of its
normalized central potential. -/
theorem continuumCurvature_unitary_split {N : ℕ} (hN : 0 < N) (A : LocalConnection N)
    (hskew : ∀ k y, (A k y)ᴴ = -A k y) (i j : Axis) (x : Axis → ℝ)
    (hA : ∀ k, DifferentiableAt ℝ (A k) x) :
    let da := fderiv ℝ (centralPotential A j) x (Pi.single i 1) -
      fderiv ℝ (centralPotential A i) x (Pi.single j 1)
    let F₀ := continuumCurvature (tracelessConnection A) i j x
    continuumCurvature A i j x = F₀ + continuumCentral N da ∧
      traceNormSquared (continuumCurvature A i j x) = traceNormSquared F₀ + N * da ^ 2 ∧
      -Complex.I * (continuumCurvature A i j x).trace / (N : ℂ) = (da : ℂ) := by
  dsimp only
  have ha (k : Axis) : DifferentiableAt ℝ (centralPotential A k) x := by
    have him : DifferentiableAt ℝ (fun y => (A k y).trace.im) x :=
      Complex.imCLM.differentiableAt.comp x ((continuumTrace N).differentiableAt.comp x (hA k))
    change DifferentiableAt ℝ (fun y => (A k y).trace.im / (N : ℝ)) x
    simp only [div_eq_mul_inv]
    exact him.mul (differentiableAt_const _)
  have hA₀ (k : Axis) : DifferentiableAt ℝ (tracelessConnection A k) x :=
    (hA k).sub ((ha k).smul_const _)
  have hsplit : (fun k y => tracelessConnection A k y + continuumCentral N (centralPotential A k y)) = A :=
    funext fun k => funext fun y => sub_add_cancel _ _
  have h := continuumCurvature_add_central (tracelessConnection A) (centralPotential A) i j x hA₀ ha
  rw [hsplit] at h
  have htrace := continuumCurvature_trace_zero (tracelessConnection A) i j x hA₀
    (tracelessConnection_trace_zero hN A hskew)
  rw [h]
  exact ⟨rfl, traceNormSquared_add_central _ htrace _, traced_central_curvature_complex hN _ htrace _⟩

end

end GaplessYangMills

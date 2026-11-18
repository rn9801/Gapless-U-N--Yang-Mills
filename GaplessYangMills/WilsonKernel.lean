module

public import GaplessYangMills.GramTwist
public import GaplessYangMills.Wilson
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Positive definiteness of the fundamental Wilson kernel

The power of a real coordinate Gram kernel is the Gram kernel of finite
coordinate words. The exponential series is a nonnegative combination of
these kernels.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix

def coordinateGram {D ι : Type*} [Fintype D] (v : ι → D → ℝ) (i j : ι) : ℝ :=
  ∑ d, v i d * v j d

theorem coordinateGram_power_nonneg {D ι : Type*} [Fintype D] (v : ι → D → ℝ)
    (s : Finset ι) (w : ι → ℝ) (n : ℕ) :
    0 ≤ kernelQuadratic s w (fun i j => coordinateGram v i j ^ n) := by
  let feature (f : Fin n → D) (i : ι) := ∏ k, v i (f k)
  have h (i j : ι) : coordinateGram v i j ^ n =
      ∑ f : Fin n → D, feature f i * feature f j := by
    rw [coordinateGram, Fintype.sum_pow]
    simp only [feature, Finset.prod_mul_distrib]
  have hex : kernelQuadratic s w (fun i j => coordinateGram v i j ^ n) =
      ∑ f : Fin n → D, (∑ i ∈ s, w i * feature f i) ^ 2 := by
    simp only [kernelQuadratic, h, Finset.mul_sum]
    calc
      _ = ∑ i ∈ s, ∑ f : Fin n → D, ∑ j ∈ s,
          w i * w j * (feature f i * feature f j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro f _
        rw [pow_two, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [hex]
  exact Finset.sum_nonneg fun f _ => sq_nonneg _

theorem exponentialGram_nonneg {D ι : Type*} [Fintype D] (v : ι → D → ℝ)
    (s : Finset ι) (w : ι → ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ kernelQuadratic s w (fun i j => Real.exp (β * coordinateGram v i j)) := by
  have hsum (i j : ι) : HasSum
      (fun n : ℕ => (w i * w j) * ((β * coordinateGram v i j) ^ n / (n.factorial : ℝ)))
      ((w i * w j) * Real.exp (β * coordinateGram v i j)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (β * coordinateGram v i j)).mul_left (w i * w j)
  have htotal : HasSum
      (fun n : ℕ => ∑ i ∈ s, ∑ j ∈ s,
        (w i * w j) * ((β * coordinateGram v i j) ^ n / (n.factorial : ℝ)))
      (kernelQuadratic s w (fun i j => Real.exp (β * coordinateGram v i j))) := by
    exact hasSum_sum fun i _ => hasSum_sum fun j _ => hsum i j
  rw [← htotal.tsum_eq]
  apply tsum_nonneg
  intro n
  have hfactor :
      (∑ i ∈ s, ∑ j ∈ s,
        (w i * w j) * ((β * coordinateGram v i j) ^ n / (n.factorial : ℝ))) =
        (β ^ n / (n.factorial : ℝ)) *
          kernelQuadratic s w (fun i j => coordinateGram v i j ^ n) := by
    simp only [kernelQuadratic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    ring
  rw [hfactor]
  exact mul_nonneg (by positivity) (coordinateGram_power_nonneg v s w n)

def matrixCoordinates {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Fin N × Fin N × Bool → ℝ :=
  fun (i, j, b) => if b then (A i j).re else (A i j).im

theorem gram_matrixCoordinates {N : Type*} [Fintype N] [DecidableEq N]
    (A B : Matrix N N ℂ) :
    (∑ p : N × N × Bool,
      (if p.2.2 then (A p.1 p.2.1).re else (A p.1 p.2.1).im) *
      (if p.2.2 then (B p.1 p.2.1).re else (B p.1 p.2.1).im)) =
      (A * Bᴴ).trace.re := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ite_false,
    ite_true, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    mul_neg, sub_neg_eq_add]

/-- The single-link Wilson transfer kernel is positive definite on every
finite set of test matrices. -/
theorem wilsonKernel_nonneg {N : ℕ} {ι : Type*}
    (A : ι → Matrix (Fin N) (Fin N) ℂ) (s : Finset ι) (w : ι → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) :
    0 ≤ kernelQuadratic s w (fun i j => Real.exp ((N : ℝ) * β * (A i * (A j)ᴴ).trace.re)) := by
  have hg (i j : ι) : coordinateGram (fun i => matrixCoordinates (A i)) i j =
      (A i * (A j)ᴴ).trace.re := by
    simpa only [coordinateGram, matrixCoordinates] using gram_matrixCoordinates (A i) (A j)
  simpa only [hg] using exponentialGram_nonneg (fun i => matrixCoordinates (A i)) s w
    ((N : ℝ) * β) (by positivity)


private theorem kernelQuadratic_swap {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (K : ι → ι → ℝ) :
    kernelQuadratic s w (fun i j => K j i) = kernelQuadratic s w K := by
  unfold kernelQuadratic
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem doubledQuadratic {X ι : Type*} (s : Finset ι) (w : ι → ℝ) (a : ℝ)
    (K : X → X → ℝ) (x y : ι → X) :
    kernelQuadratic (((Finset.univ : Finset Bool) ×ˢ s))
        (fun p => if p.1 then w p.2 else a * w p.2)
        (fun p q => K (if p.1 then x p.2 else y p.2) (if q.1 then x q.2 else y q.2)) =
      kernelQuadratic s w (fun i j => K (x i) (x j)) +
      a * kernelQuadratic s w (fun i j => K (x i) (y j)) +
      a * kernelQuadratic s w (fun i j => K (y i) (x j)) +
      a ^ 2 * kernelQuadratic s w (fun i j => K (y i) (y j)) := by
  simp only [kernelQuadratic, Finset.sum_product, Fintype.sum_bool, Bool.false_eq_true,
    ite_false, ite_true, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

/-- A simultaneous symmetry of a real positive kernel gives the order
inequality for the two inverse twists on a finite sample. -/
theorem finiteKernel_twist_bounds {X ι : Type*} (K : X → X → ℝ)
    (s : Finset ι) (x : ι → X) (w : ι → ℝ) (W : Equiv.Perm X)
    (hsym : ∀ u v, K u v = K v u) (hinv : ∀ u v, K (W u) (W v) = K u v)
    (hpos : ∀ (f : Bool × ι → X) (v : Bool × ι → ℝ),
      0 ≤ kernelQuadratic (((Finset.univ : Finset Bool) ×ˢ s)) v (fun i j => K (f i) (f j))) :
    let K' : ι → ι → ℝ := fun i j =>
      K (x i) (x j) / 2 + K (x i) (W (x j)) / 4 + K (x i) (W.symm (x j)) / 4
    0 ≤ kernelQuadratic s w K' ∧
      kernelQuadratic s w K' ≤ kernelQuadratic s w (fun i j => K (x i) (x j)) := by
  have hcross : kernelQuadratic s w (fun i j => K (W (x i)) (x j)) =
      kernelQuadratic s w (fun i j => K (x i) (W (x j))) := by
    have hf : (fun i j => K (W (x i)) (x j)) = fun i j => K (x j) (W (x i)) := by
      funext i j
      exact hsym _ _
    rw [hf]
    exact kernelQuadratic_swap _ _ _
  have hreverse : kernelQuadratic s w (fun i j => K (x i) (W.symm (x j))) =
      kernelQuadratic s w (fun i j => K (W (x i)) (x j)) := by
    congr 1
    funext i j
    rw [← hinv (x i) (W.symm (x j)), W.apply_symm_apply]
  have htest (a : ℝ) :=
    hpos (fun p => if p.1 then x p.2 else W (x p.2)) (fun p => if p.1 then w p.2 else a * w p.2)
  have hlo := htest 1
  have hhi := htest (-1)
  rw [doubledQuadratic s w 1 K x (fun i => W (x i)), hcross] at hlo
  rw [doubledQuadratic s w (-1) K x (fun i => W (x i)), hcross] at hhi
  simp only [hinv] at hlo hhi
  have hlin : kernelQuadratic s w (fun i j => K (x i) (x j) / 2 +
      K (x i) (W (x j)) / 4 + K (x i) (W.symm (x j)) / 4) =
      kernelQuadratic s w (fun i j => K (x i) (x j)) / 2 +
      kernelQuadratic s w (fun i j => K (x i) (W (x j))) / 4 +
      kernelQuadratic s w (fun i j => K (x i) (W.symm (x j))) / 4 := by
    simp only [kernelQuadratic, div_eq_mul_inv, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    ring_nf
  dsimp
  rw [hlin, hreverse, hcross]
  constructor <;> linarith



noncomputable def fundamentalKernel {N : ℕ} (β : ℝ) (A B : UnitaryMatrix N) : ℝ :=
  Real.exp ((N : ℝ) * β * (A.val * B.valᴴ).trace.re)

theorem fundamentalKernel_pos {N : ℕ} (β : ℝ) (A B : UnitaryMatrix N) :
    0 < fundamentalKernel β A B := Real.exp_pos _

theorem fundamentalKernel_rightInvariant {N : ℕ} (β : ℝ) (Z A B : UnitaryMatrix N) :
    fundamentalKernel β (A * Z) (B * Z) = fundamentalKernel β A B := by
  have h : (A * Z) * (B * Z)⁻¹ = A * B⁻¹ := by simp [mul_assoc]
  exact congrArg (fun U : UnitaryMatrix N => Real.exp ((N : ℝ) * β * U.val.trace.re)) h

theorem fundamentalKernel_symm {N : ℕ} (β : ℝ) (A B : UnitaryMatrix N) :
    fundamentalKernel β A B = fundamentalKernel β B A := by
  have h := Matrix.trace_conjTranspose (A.val * B.valᴴ)
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
  have hre := congrArg Complex.re h
  simp only [Complex.star_def, Complex.conj_re] at hre
  simp only [fundamentalKernel, hre]

theorem fundamentalKernel_leftInvariant {N : ℕ} (β : ℝ) (Z A B : UnitaryMatrix N) :
    fundamentalKernel β (Z * A) (Z * B) = fundamentalKernel β A B := by
  have hz : Z.valᴴ * Z.val = 1 := Z.property.1
  have h : ((Z.val * A.val) * (Z.val * B.val)ᴴ).trace = (A.val * B.valᴴ).trace := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = ((Z.val * (A.val * B.valᴴ)) * Z.valᴴ).trace := by simp only [Matrix.mul_assoc]
      _ = (Z.valᴴ * (Z.val * (A.val * B.valᴴ))).trace := Matrix.trace_mul_comm _ _
      _ = _ := by rw [← Matrix.mul_assoc, hz, one_mul]
  unfold fundamentalKernel
  change Real.exp ((N : ℝ) * β * ((Z.val * A.val) * (Z.val * B.val)ᴴ).trace.re) = _
  rw [h]

/-- Pointwise twist order for the fundamental Wilson kernel and any unitary
twist of the tangential link. -/
theorem fundamentalKernel_twist_bounds {N : ℕ} {ι : Type*} (β : ℝ) (hβ : 0 ≤ β)
    (s : Finset ι) (A : ι → UnitaryMatrix N) (w : ι → ℝ) (Z : UnitaryMatrix N) :
    let K' : ι → ι → ℝ := fun i j =>
      fundamentalKernel β (A i) (A j) / 2 +
      fundamentalKernel β (A i) (Z * A j) / 4 +
      fundamentalKernel β (A i) (Z⁻¹ * A j) / 4
    0 ≤ kernelQuadratic s w K' ∧
      kernelQuadratic s w K' ≤ kernelQuadratic s w (fun i j => fundamentalKernel β (A i) (A j)) := by
  apply finiteKernel_twist_bounds (fundamentalKernel β) s A w (Equiv.mulLeft Z)
    (fundamentalKernel_symm β) (fundamentalKernel_leftInvariant β Z)
  intro f v
  exact wilsonKernel_nonneg (fun i => (f i).val) _ v β hβ

end GaplessYangMills

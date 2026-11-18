module

public import GaplessYangMills.WilsonKernel
public import Mathlib.Analysis.Matrix.Order

/-!
# Product order for Wilson slice kernels

Sampling any finite collection of slices gives positive semidefinite matrices.
Schur products preserve the order as the indicated tangential links are twisted.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix

noncomputable section

def twistedFundamentalKernel {N : ℕ} (β : ℝ) (Z A B : UnitaryMatrix N) : ℝ :=
  fundamentalKernel β A B / 2 + fundamentalKernel β A (Z * B) / 4 +
    fundamentalKernel β A (Z⁻¹ * B) / 4

private theorem twistedFundamentalKernel_symm {N : ℕ} (β : ℝ) (Z A B : UnitaryMatrix N) :
    twistedFundamentalKernel β Z A B = twistedFundamentalKernel β Z B A := by
  have h (W : UnitaryMatrix N) :
      fundamentalKernel β A (W * B) = fundamentalKernel β B (W⁻¹ * A) := by
    have h' := fundamentalKernel_leftInvariant β W⁻¹ A (W * B)
    rw [← mul_assoc, inv_mul_cancel, one_mul, fundamentalKernel_symm β (W⁻¹ * A) B] at h'
    exact h'.symm
  rw [twistedFundamentalKernel, twistedFundamentalKernel, h Z, h Z⁻¹, inv_inv,
    fundamentalKernel_symm β A B]
  ring

private theorem quadratic_eq_sample {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (w : ι → ℝ) :
    star w ⬝ᵥ (M *ᵥ w) = kernelQuadratic Finset.univ w M := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
    kernelQuadratic]
  exact Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

private theorem posSemidef_sample {ι : Type*} [Fintype ι] (K : ι → ι → ℝ)
    (hs : ∀ i j, K i j = K j i)
    (h : ∀ w, 0 ≤ kernelQuadratic Finset.univ w K) : (Matrix.of K).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    exact hs j i
  · intro w
    rw [quadratic_eq_sample]
    exact h w

theorem fundamentalSample_order {N : ℕ} {ι : Type*} [Fintype ι] (β : ℝ) (hβ : 0 ≤ β)
    (A : ι → UnitaryMatrix N) (Z : UnitaryMatrix N) :
    let K := Matrix.of (fun i j => fundamentalKernel β (A i) (A j))
    let K' := Matrix.of (fun i j => twistedFundamentalKernel β Z (A i) (A j))
    K.PosSemidef ∧ K'.PosSemidef ∧ (K - K').PosSemidef := by
  dsimp
  have h (w : ι → ℝ) := fundamentalKernel_twist_bounds β hβ Finset.univ A w Z
  refine ⟨posSemidef_sample _ (fun i j => fundamentalKernel_symm β (A i) (A j))
    (fun w => wilsonKernel_nonneg (fun i => (A i).val) _ w β hβ),
    posSemidef_sample _ (fun i j => twistedFundamentalKernel_symm β Z (A i) (A j))
      (fun w => (h w).1), ?_⟩
  apply posSemidef_sample
  · intro i j
    exact congrArg₂ (· - ·) (fundamentalKernel_symm β (A i) (A j))
      (twistedFundamentalKernel_symm β Z (A i) (A j))
  · intro w
    change 0 ≤ kernelQuadratic Finset.univ w (fun i j =>
      fundamentalKernel β (A i) (A j) - twistedFundamentalKernel β Z (A i) (A j))
    have he : kernelQuadratic Finset.univ w (fun i j =>
        fundamentalKernel β (A i) (A j) - twistedFundamentalKernel β Z (A i) (A j)) =
      kernelQuadratic Finset.univ w (fun i j => fundamentalKernel β (A i) (A j)) -
      kernelQuadratic Finset.univ w (fun i j => twistedFundamentalKernel β Z (A i) (A j)) := by
      simp only [kernelQuadratic, mul_sub, Finset.sum_sub_distrib]
    rw [he]
    exact sub_nonneg.mpr (h w).2

private def sampleProduct {E ι : Type*} (K : E → Matrix ι ι ℝ) (s : Finset E) :
    Matrix ι ι ℝ := Matrix.of fun i j => ∏ e ∈ s, K e i j

private theorem sampleProduct_order {E ι : Type*} (s : Finset E)
    (K K' : E → Matrix ι ι ℝ)
    (h : ∀ e ∈ s, (K e).PosSemidef ∧ (K' e).PosSemidef ∧ (K e - K' e).PosSemidef) :
    (sampleProduct K s).PosSemidef ∧ (sampleProduct K' s).PosSemidef ∧
      (sampleProduct K s - sampleProduct K' s).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h₁ : (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef := by
      let v : ι → ℝ := fun _ => 1
      have he : Matrix.of (fun _ _ : ι => (1 : ℝ)) = Matrix.vecMulVec v (star v) := by
        ext i j
        simp [Matrix.vecMulVec_apply, v]
      exact he ▸ Matrix.posSemidef_vecMulVec_self_star v
    simpa [sampleProduct, Matrix.PosSemidef.zero] using
      (show (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef ∧
        (Matrix.of (fun _ _ : ι => (1 : ℝ))).PosSemidef from ⟨h₁, h₁⟩)
  | insert e s he ih =>
    have hprod (A : E → Matrix ι ι ℝ) :
        sampleProduct A (insert e s) = A e ⊙ sampleProduct A s := by
      ext i j
      exact Finset.prod_insert he
    rw [hprod, hprod]
    obtain ⟨hK, hK', hdiff⟩ := h e (Finset.mem_insert_self e s)
    obtain ⟨hs, hs', hsdiff⟩ := ih (fun f hf => h f (Finset.mem_insert_of_mem hf))
    refine ⟨hK.hadamard hs, hK'.hadamard hs', ?_⟩
    have heq : K e ⊙ sampleProduct K s - K' e ⊙ sampleProduct K' s =
        (K e - K' e) ⊙ sampleProduct K s +
          K' e ⊙ (sampleProduct K s - sampleProduct K' s) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.hadamard_apply, Matrix.add_apply]
      ring
    rw [heq]
    exact (hdiff.hadamard hs).add (hK'.hadamard hsdiff)

/-- Applying twists independently to factors in a slice preserves the
positive order for every finite sample of slice configurations. -/
theorem fundamentalSliceSample_order {N : ℕ} {E ι : Type*} [Fintype ι] [DecidableEq E]
    (β : ℝ) (hβ : 0 ≤ β) (s : Finset E) (marked : Finset E)
    (A : ι → E → UnitaryMatrix N) (Z : E → UnitaryMatrix N) :
    let K := Matrix.of fun i j => ∏ e ∈ s, fundamentalKernel β (A i e) (A j e)
    let K' := Matrix.of fun i j => ∏ e ∈ s, if e ∈ marked then
      twistedFundamentalKernel β (Z e) (A i e) (A j e) else fundamentalKernel β (A i e) (A j e)
    K.PosSemidef ∧ K'.PosSemidef ∧ (K - K').PosSemidef := by
  let U e := Matrix.of fun i j => fundamentalKernel β (A i e) (A j e)
  let V e := if e ∈ marked then Matrix.of (fun i j =>
    twistedFundamentalKernel β (Z e) (A i e) (A j e)) else U e
  have h := sampleProduct_order s U V (fun e _ => by
    have he := fundamentalSample_order β hβ (fun i => A i e) (Z e)
    by_cases hm : e ∈ marked
    · simpa only [U, V, ite_eq_left hm] using he
    · simpa only [V, ite_eq_right hm, sub_self, Matrix.PosSemidef.zero, and_true] using
        (show (U e).PosSemidef ∧ (U e).PosSemidef from ⟨he.1, he.1⟩))
  have hV : sampleProduct V s = Matrix.of (fun i j => ∏ e ∈ s, if e ∈ marked then
      twistedFundamentalKernel β (Z e) (A i e) (A j e) else fundamentalKernel β (A i e) (A j e)) := by
    ext i j
    apply Finset.prod_congr rfl
    intro e _
    by_cases hm : e ∈ marked <;> simp only [V, hm, ite_true, ite_false, U, Matrix.of_apply]
  rw [hV] at h
  exact h

end

end GaplessYangMills

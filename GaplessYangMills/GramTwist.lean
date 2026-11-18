module

public import GaplessYangMills.WeakCoupling
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Order of the symmetrized twisted Gram kernel

The modified kernel of Section 2 inserts the average of the identity and
the two inverse twists into a Gram form. Its order follows from the squares
of the sum and difference of a vector and its transform.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def symmetrizedTwist (W : E ≃ₗ[ℝ] E) (v : E) : E :=
  (1 / 2 : ℝ) • v + (1 / 4 : ℝ) • W v + (1 / 4 : ℝ) • W.symm v

theorem symmetrizedTwist_bounds (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsym : ∀ u v, B u v = B v u) (hpos : ∀ v, 0 ≤ B v v)
    (W : E ≃ₗ[ℝ] E) (hW : ∀ u v, B (W u) (W v) = B u v) (v : E) :
    0 ≤ B v (symmetrizedTwist W v) ∧ B v (symmetrizedTwist W v) ≤ B v v := by
  have hinv : B v (W.symm v) = B v (W v) := by
    rw [← hW v (W.symm v), W.apply_symm_apply, hsym (W v) v]
  have hadd := hpos (v + W v)
  have hsub := hpos (v - W v)
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    hsym (W v) v, hW] at hadd hsub
  simp only [symmetrizedTwist, map_add, map_smul, smul_eq_mul, hinv]
  constructor <;> linarith

def kernelQuadratic {ι : Type*} (s : Finset ι) (w : ι → ℝ) (K : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, w i * w j * K i j

private theorem kernelQuadratic_gram {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (f g : ι → E) :
    kernelQuadratic s w (fun i j => B (f i) (g j)) =
      B (∑ i ∈ s, w i • f i) (∑ j ∈ s, w j • g j) := by
  simp only [kernelQuadratic, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Finite Gram test sums for the twisted kernel lie between zero and the
unmodified Gram test sums. The feature vectors and the number of test points
are arbitrary. -/
theorem twistedGram_bounds {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (f : ι → E)
    (hsym : ∀ u v, B u v = B v u) (hpos : ∀ v, 0 ≤ B v v)
    (W : E ≃ₗ[ℝ] E) (hW : ∀ u v, B (W u) (W v) = B u v) :
    0 ≤ kernelQuadratic s w (fun i j => B (f i) (symmetrizedTwist W (f j))) ∧
    kernelQuadratic s w (fun i j => B (f i) (symmetrizedTwist W (f j))) ≤
      kernelQuadratic s w (fun i j => B (f i) (f j)) := by
  have hsum : (∑ j ∈ s, w j • symmetrizedTwist W (f j)) =
      symmetrizedTwist W (∑ j ∈ s, w j • f j) := by
    simp only [symmetrizedTwist, smul_add, Finset.sum_add_distrib, map_sum, map_smul,
      Finset.smul_sum]
    simp only [smul_comm (1 / 2 : ℝ), smul_comm (1 / 4 : ℝ)]
  rw [kernelQuadratic_gram, kernelQuadratic_gram, hsum]
  exact symmetrizedTwist_bounds B hsym hpos W hW _

end

end GaplessYangMills

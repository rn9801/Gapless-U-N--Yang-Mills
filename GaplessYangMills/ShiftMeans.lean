module

public import GaplessYangMills.DirectionalMean
public import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# Directional means from Hilbert space shifts
-/

@[expose] public section

namespace GaplessYangMills

open Filter
open scoped Topology InnerProductSpace

/-- The directional mean of a translation matrix element is the matrix
element of the orthogonal projection onto the fixed space of the shift. -/
theorem hasDirectionalMean_of_hilbert_shift {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (i : Axis)
    (S : E →L[ℝ] E) (hS : ‖S‖ ≤ 1) (a : E) (b : Site → E)
    (hshift : ∀ x, S (b x) = b (x + step i)) :
    HasDirectionalMean i (fun x => ⟪a, b x⟫_ℝ)
      (fun x => ⟪a, (S.eqLocus (1 : E →L[ℝ] E)).orthogonalProjectionOnto (b x)⟫_ℝ) := by
  intro x
  have hiter (n : ℕ) : S^[n] (b x) = b (x + n • step i) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hshift, succ_nsmul, ← add_assoc]
  have hm := S.tendsto_birkhoffAverage_orthogonalProjection hS (b x)
  have hinner : Continuous (fun z : E => ⟪a, z⟫_ℝ) := continuous_const.inner continuous_id
  have ht := hinner.continuousAt.tendsto.comp hm
  simpa [averageAlong, Function.comp_def, birkhoffAverage, birkhoffSum, hiter,
    real_inner_smul_right, inner_sum] using ht

end GaplessYangMills

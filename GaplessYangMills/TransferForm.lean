module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Contraction for the reflection form

A symmetric shift acting on a positive semidefinite reflection form contracts
its induced seminorm if the squared seminorms of its iterates are bounded.
-/

@[expose] public section

namespace GaplessYangMills

private theorem decreasing_first_of_bounded_logConvex (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hconv : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2))
    (C : ℝ) (hC : ∀ n, a n ≤ C) : a 1 ≤ a 0 := by
  have hmid (n : ℕ) : 2 * a (n + 1) ≤ a n + a (n + 2) := by
    apply (sq_le_sq₀ (mul_nonneg (by norm_num) (ha (n + 1)))
      (add_nonneg (ha n) (ha (n + 2)))).mp
    nlinarith only [hconv n, sq_nonneg (a n - a (n + 2))]
  let d := a 1 - a 0
  have hstep (n : ℕ) : d ≤ a (n + 1) - a n := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      change d ≤ a (n + 2) - a (n + 1)
      linarith only [hmid n, ih]
  have hlin (n : ℕ) : a 0 + (n : ℝ) * d ≤ a n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul]
      linarith only [ih, hstep n]
  by_contra! h
  have hd : 0 < d := sub_pos.mpr h
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - a 0) / d)
  linarith only [(div_lt_iff₀ hd).1 hn, hlin n, hC n]

theorem reflectionShift_contracts {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hB : B.IsSymm) (hpos : ∀ v, 0 ≤ B v v)
    (S : E →ₗ[ℝ] E) (hsym : ∀ u v, B (S u) v = B u (S v))
    (v : E) (C : ℝ) (hbound : ∀ n : ℕ, B ((S ^ n) v) ((S ^ n) v) ≤ C) :
    B (S v) (S v) ≤ B v v := by
  let y (n : ℕ) := (S ^ n) v
  let a (n : ℕ) := B (y n) (y n)
  have hy (n : ℕ) : y (n + 1) = S (y n) := by
    change (S ^ (n + 1)) v = S ((S ^ n) v)
    rw [pow_succ']
    rfl
  have hconv (n : ℕ) : a (n + 1) ^ 2 ≤ a n * a (n + 2) := by
    have h := B.apply_sq_le_of_symm hpos hB (y n) (y (n + 2))
    have he : B (y n) (y (n + 2)) = a (n + 1) := by
      rw [hy (n + 1), ← hsym, ← hy n]
    rw [he] at h
    exact h
  have hm := decreasing_first_of_bounded_logConvex a (fun n => hpos (y n)) hconv C hbound
  simpa [a, y] using hm

/-- Under the same hypotheses the translation preserves the null space of
the reflection form, as required for descent to the quotient. -/
theorem reflectionShift_preserves_null {E : Type*} [AddCommGroup E] [Module ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hB : B.IsSymm) (hpos : ∀ v, 0 ≤ B v v)
    (S : E →ₗ[ℝ] E) (hsym : ∀ u v, B (S u) v = B u (S v))
    (v : E) (C : ℝ) (hbound : ∀ n : ℕ, B ((S ^ n) v) ((S ^ n) v) ≤ C)
    (hv : B v v = 0) : B (S v) (S v) = 0 := by
  have h := reflectionShift_contracts B hB hpos S hsym v C hbound
  exact le_antisymm (h.trans_eq hv) (hpos (S v))

end GaplessYangMills

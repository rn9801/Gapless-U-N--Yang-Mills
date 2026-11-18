module

public import GaplessYangMills.Lattice
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Summation over transverse lattice slices

The proofs in this file use unconditional sums. Taking a transverse sum commutes
with a longitudinal difference and annihilates every transverse difference.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Topology

abbrev Slice (i : Axis) (n : ℤ) := {x : Site // x i = n}

noncomputable def marginal (i : Axis) (f : Site → ℝ) (n : ℤ) : ℝ :=
  ∑' x : Slice i n, f x

private theorem summable_slice {f : Site → ℝ} (hf : Summable f) (i : Axis) (n : ℤ) :
    Summable (fun x : Slice i n => f x) :=
  hf.comp_injective Subtype.val_injective

theorem summable_marginal {f : Site → ℝ} (hf : Summable f) (i : Axis) :
    Summable (marginal i f) :=
  ((Equiv.sigmaFiberEquiv (fun x : Site => x i)).summable_iff.mpr hf).sigma

theorem tsum_marginal {f : Site → ℝ} (hf : Summable f) (i : Axis) :
    ∑' n, marginal i f n = ∑' x, f x := by
  let e := Equiv.sigmaFiberEquiv (fun x : Site => x i)
  have hs : Summable (fun p => f (e p)) := e.summable_iff.mpr hf
  exact hs.tsum_sigma.symm.trans (e.tsum_eq f)

theorem summable_diff {f : Site → ℝ} (hf : Summable f) (i : Axis) :
    Summable (diff i f) :=
  ((Equiv.addRight (step i)).summable_iff.mpr hf).sub hf

theorem marginal_add {f g : Site → ℝ} (hf : Summable f) (hg : Summable g)
    (i : Axis) (n : ℤ) :
    marginal i (f + g) n = marginal i f n + marginal i g n :=
  (summable_slice hf i n).tsum_add (summable_slice hg i n)

theorem marginal_sub {f g : Site → ℝ} (hf : Summable f) (hg : Summable g)
    (i : Axis) (n : ℤ) :
    marginal i (f - g) n = marginal i f n - marginal i g n :=
  (summable_slice hf i n).tsum_sub (summable_slice hg i n)

theorem marginal_diff {f : Site → ℝ} (hf : Summable f) (i j : Axis) (n : ℤ) :
    marginal i (diff j f) n = marginal i f (n + step j i) - marginal i f n := by
  let e : Slice i n ≃ Slice i (n + step j i) :=
    (Equiv.addRight (step j)).subtypeEquiv (fun x => by
      change x i = n ↔ x i + step j i = n + step j i
      exact add_right_cancel_iff.symm)
  have hs : Summable (fun x : Slice i n => f (x.val + step j)) :=
    (summable_slice hf i (n + step j i)).comp_injective e.injective
  unfold marginal diff
  rw [hs.tsum_sub (summable_slice hf i n)]
  exact congrArg (· - ∑' x : Slice i n, f x) (e.tsum_eq (fun x => f x.val))

@[simp]
theorem marginal_zero (i : Axis) (n : ℤ) : marginal i 0 n = 0 := by
  simp [marginal]

theorem marginal_diff_along {f : Site → ℝ} (hf : Summable f) (i : Axis) (n : ℤ) :
    marginal i (diff i f) n = marginal i f (n + 1) - marginal i f n := by
  rw [marginal_diff hf, step_same]

theorem marginal_diff_across {f : Site → ℝ} (hf : Summable f) {i j : Axis}
    (h : j ≠ i) (n : ℤ) : marginal i (diff j f) n = 0 := by
  rw [marginal_diff hf, step_other h, add_zero, sub_self]

/-- A summable sequence on the integers with zero forward difference is zero. -/
private theorem eq_zero_of_summable_period_one {g : ℤ → ℝ} (hg : Summable g)
    (h : ∀ n, g (n + 1) = g n) (n : ℤ) : g n = 0 := by
  have hconst (k : ℕ) : g (n + (k : ℤ)) = g n := by
    induction k with
    | zero => simp
    | succ k ih => simpa only [Nat.cast_succ, ← add_assoc, h] using ih
  have hinj : Function.Injective (fun k : ℕ => n + (k : ℤ)) := by
    intro a b hab
    exact Int.ofNat.inj (add_left_cancel hab)
  have hs : Summable (fun _ : ℕ => g n) := by
    simpa only [Function.comp_def, hconst] using hg.comp_injective hinj
  exact (summable_const_iff (g n)).mp hs

/-- An absolutely summable function whose slice sums have zero difference
has total sum zero. -/
theorem tsum_eq_zero_of_marginal_diff {f : Site → ℝ} (hf : Summable f) (i : Axis)
    (h : ∀ n, marginal i (diff i f) n = 0) : ∑' x, f x = 0 := by
  rw [← tsum_marginal hf i]
  have hs : ∀ n, marginal i f n = 0 :=
    eq_zero_of_summable_period_one (summable_marginal hf i) (fun n =>
      sub_eq_zero.mp ((marginal_diff_along hf i n).symm.trans (h n)))
  simp [hs]

end GaplessYangMills

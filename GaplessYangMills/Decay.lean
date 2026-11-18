module

public import GaplessYangMills.Ward
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Exponential decay implies summability

The bound is in the maximum-coordinate distance on the four-dimensional lattice,
as at the end of Section 5 of the paper.
-/

@[expose] public section

namespace GaplessYangMills

def radius (x : Site) : ℕ :=
  Finset.univ.sup fun i => (x i).natAbs

theorem natAbs_le_radius (x : Site) (i : Axis) : (x i).natAbs ≤ radius x :=
  Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ i)

private theorem summable_exp_natAbs (m : ℝ) (hm : 0 < m) :
    Summable (fun z : ℤ => Real.exp (-m * (z.natAbs : ℝ))) := by
  have hs : Summable (fun n : ℕ => Real.exp (-m * (n : ℝ))) := by
    simpa only [mul_comm (-m)] using Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hm)
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨by simpa using hs, by simpa using hs⟩

private theorem summable_fin_product {α : Type*} (f : α → ℝ)
    (hf : Summable f) (h0 : 0 ≤ f) (d : ℕ) :
    Summable (fun x : Fin d → α => ∏ i, f (x i)) := by
  induction d with
  | zero =>
    let : Subsingleton (Fin 0 → α) := ⟨fun x y => funext fun i => Fin.elim0 i⟩
    exact Summable.of_finite
  | succ d ih =>
    apply (Fin.consEquiv (fun _ : Fin (d + 1) => α)).summable_iff.mp
    simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ] using hf.mul_of_nonneg ih h0 (fun x => Finset.prod_nonneg fun i _ => h0 (x i))

/-- The radial exponential envelope has finite mass in four dimensions. -/
theorem summable_exp_radius (m : ℝ) (hm : 0 < m) :
    Summable (fun x : Site => Real.exp (-m * (radius x : ℝ))) := by
  have hm' : 0 < m / 4 := div_pos hm (by norm_num)
  have hs := summable_fin_product (fun z : ℤ => Real.exp (-(m / 4) * (z.natAbs : ℝ)))
    (summable_exp_natAbs (m / 4) hm') (fun _ => Real.exp_nonneg _) 4
  refine hs.of_nonneg_of_le (fun _ => Real.exp_nonneg _) fun x => ?_
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  calc
    -m * (radius x : ℝ) = ∑ _i : Axis, -(m / 4) * (radius x : ℝ) := by
      simp
      ring
    _ ≤ ∑ i : Axis, -(m / 4) * ((x i).natAbs : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (natAbs_le_radius x i))
        (neg_nonpos.mpr hm'.le)

theorem summable_of_exp_bound (f : Site → ℝ) {C m : ℝ} (hm : 0 < m)
    (hbound : ∀ x, |f x| ≤ C * Real.exp (-m * (radius x : ℝ))) :
    Summable f := by
  apply Summable.of_norm
  exact ((summable_exp_radius m hm).mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun x => by simpa only [Real.norm_eq_abs] using hbound x)

/-- The local approximation estimate and a transfer bound with a linear
support offset imply a global exponential bound. -/
theorem exp_bound_of_local_approximants_linear (f : Site → ℝ) (localApprox : ℕ → Site → ℝ)
    {A B c m width slope : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hm : 0 < m)
    (hslope : slope ≤ 4)
    (herror : ∀ R x, |f x - localApprox R x| ≤ B * Real.exp (-c * R))
    (hlocal : ∀ R x,
      |localApprox R x| ≤ A * Real.exp (-m * ((radius x : ℝ) - (slope * R + width)))) :
    ∃ C r : ℝ, 0 < r ∧ ∀ x, |f x| ≤ C * Real.exp (-r * (radius x : ℝ)) := by
  let r : ℝ := min (m / 2) (c / 8)
  refine ⟨A * Real.exp (m * width) + B * Real.exp c, r, lt_min (by positivity) (by positivity), ?_⟩
  intro x
  let R : ℕ := radius x / 8
  have hlo : (radius x : ℝ) ≤ 8 * (R : ℝ) + 8 := by
    exact_mod_cast (show radius x ≤ 8 * R + 8 by dsimp [R]; omega)
  have hhi : 8 * (R : ℝ) ≤ (radius x : ℝ) := by
    exact_mod_cast (show 8 * R ≤ radius x by dsimp [R]; omega)
  have hlocal_exp :
      Real.exp (-m * ((radius x : ℝ) - (slope * R + width))) ≤
        Real.exp (m * width) * Real.exp (-r * (radius x : ℝ)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h₁ := mul_le_mul_of_nonneg_left hhi hm.le
    have h₂ := mul_le_mul_of_nonneg_right (min_le_left (m / 2) (c / 8))
      (Nat.cast_nonneg (radius x) : 0 ≤ (radius x : ℝ))
    have h₃ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hslope (Nat.cast_nonneg R)) hm.le
    nlinarith
  have herror_exp :
      Real.exp (-c * R) ≤ Real.exp c * Real.exp (-r * (radius x : ℝ)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h₁ := mul_le_mul_of_nonneg_left hlo hc.le
    have h₂ := mul_le_mul_of_nonneg_right (min_le_right (m / 2) (c / 8))
      (Nat.cast_nonneg (radius x) : 0 ≤ (radius x : ℝ))
    change _ ≤ c + -min (m / 2) (c / 8) * _
    nlinarith
  calc
    |f x| ≤ |localApprox R x| + |f x - localApprox R x| := by
      rw [add_comm]
      simpa only [sub_add_cancel] using
        (abs_add_le (f x - localApprox R x) (localApprox R x))
    _ ≤ A * Real.exp (-m * ((radius x : ℝ) - (slope * R + width))) + B * Real.exp (-c * R) :=
      add_le_add (hlocal R x) (herror R x)
    _ ≤ A * (Real.exp (m * width) * Real.exp (-r * (radius x : ℝ))) +
        B * (Real.exp c * Real.exp (-r * (radius x : ℝ))) :=
      add_le_add (mul_le_mul_of_nonneg_left hlocal_exp hA) (mul_le_mul_of_nonneg_left herror_exp hB)
    _ = _ := by ring

theorem exp_bound_of_local_approximants (f : Site → ℝ) (localApprox : ℕ → Site → ℝ)
    {A B c m width : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hm : 0 < m)
    (herror : ∀ R x, |f x - localApprox R x| ≤ B * Real.exp (-c * R))
    (hlocal : ∀ R x,
      |localApprox R x| ≤ A * Real.exp (-m * ((radius x : ℝ) - (3 * R + width)))) :
    ∃ C r : ℝ, 0 < r ∧ ∀ x, |f x| ≤ C * Real.exp (-r * (radius x : ℝ)) :=
  exp_bound_of_local_approximants_linear f localApprox hA hB hc hm (by norm_num) herror hlocal

/-- A closed kernel obeying the Ward response cannot have exponentially
decaying entries. Rates and prefactors may depend on the pair of orientations. -/
theorem no_exponential_clustering_of_ward (β : ℝ) (K S : Kernel)
    (hclosed : ∀ J, d₂ (fun I => K I J) = 0)
    (hresponse : WardResponse β K S)
    (hS : ∀ I J, Summable (S I J))
    (hnormalize : ∑' x, S .xy .xy x = 0) :
    ¬ (∀ I J, ∃ C m : ℝ, 0 < m ∧
      ∀ x, |K I J x| ≤ C * Real.exp (-m * (radius x : ℝ))) := by
  intro hdecay
  apply not_summable_of_ward β K S hclosed hresponse hS hnormalize
  intro I J
  obtain ⟨C, m, hm, hbound⟩ := hdecay I J
  exact summable_of_exp_bound (K I J) hm hbound

end GaplessYangMills

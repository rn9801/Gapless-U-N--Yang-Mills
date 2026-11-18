module

public import GaplessYangMills.TracePowerOrder
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A finite trace comparison for even transfer cycles

Cauchy–Schwarz reflects each half of a trace cycle. A maximizing cycle with
a longest constant run then forces a constant cycle to attain the maximum.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem trace_mul_sq_le (P Q : Matrix ι ι ℝ) :
    (P * Q).trace ^ 2 ≤ (P * Pᴴ).trace * (Qᴴ * Q).trace := by
  have h (A B : Matrix ι ι ℝ) :
      (A * B).trace = ∑ u : ι × ι, A u.1 u.2 * B u.2 u.1 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [h P Q, h P Pᴴ, h Qᴴ Q]
  simp only [Matrix.conjTranspose_apply, star_trivial, ← sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun u : ι × ι => P u.1 u.2)
    (fun u => Q u.2 u.1)

noncomputable section

private def cycleTrace {J : Type*} (A : J → Matrix ι ι ℝ) (u : List J) : ℝ :=
  (u.map A).prod.trace

private theorem cycleTrace_rotate {J : Type*} (A : J → Matrix ι ι ℝ) (u v : List J) :
    cycleTrace A (u ++ v) = cycleTrace A (v ++ u) := by
  simpa only [cycleTrace, List.map_append, List.prod_append] using
    Matrix.trace_mul_comm (u.map A).prod (v.map A).prod

private theorem cycle_reverse {J : Type*} {A : J → Matrix ι ι ℝ}
    (hA : ∀ j, (A j).IsHermitian) (u : List J) :
    (u.reverse.map A).prod = (u.map A).prodᴴ := by
  induction u with
  | nil => simp
  | cons j u ih =>
    simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Matrix.conjTranspose_mul, ih, (hA j).eq]

private theorem cycleTrace_reverse_nonneg {J : Type*} {A : J → Matrix ι ι ℝ}
    (hA : ∀ j, (A j).IsHermitian) (u : List J) : 0 ≤ cycleTrace A (u.reverse ++ u) := by
  simp only [cycleTrace, List.map_append, List.prod_append, cycle_reverse hA]
  exact (Matrix.posSemidef_conjTranspose_mul_self (u.map A).prod).trace_nonneg

private theorem cycleTrace_sq_le {J : Type*} {A : J → Matrix ι ι ℝ}
    (hA : ∀ j, (A j).IsHermitian) (u v : List J) :
    cycleTrace A (u ++ v) ^ 2 ≤ cycleTrace A (u.reverse ++ u) * cycleTrace A (v.reverse ++ v) := by
  simp only [cycleTrace, List.map_append, List.prod_append, cycle_reverse hA]
  rw [Matrix.trace_mul_comm (u.map A).prodᴴ]
  exact trace_mul_sq_le (u.map A).prod (v.map A).prod

private def wordsOfLength (J : Type*) [Fintype J] [DecidableEq J] (n : ℕ) : Finset (List J) :=
  Nat.rec {[]} (fun _ words => Finset.univ.biUnion fun j : J => words.image (List.cons j)) n

private theorem wordsOfLength_succ (J : Type*) [Fintype J] [DecidableEq J] (n : ℕ) :
    wordsOfLength J (n + 1) = Finset.univ.biUnion fun j : J => (wordsOfLength J n).image (List.cons j) := rfl

private theorem mem_wordsOfLength {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (w : List J) : w ∈ wordsOfLength J n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [wordsOfLength]
  | succ n ih => cases w <;> simp [wordsOfLength_succ, Finset.mem_biUnion, Finset.mem_image, ih]

private theorem reflected_max {J : Type*} {A : J → Matrix ι ι ℝ}
    (hA : ∀ j, (A j).IsHermitian) {n : ℕ} {m : ℝ} (hm : 0 < m)
    (hmax : ∀ w : List J, w.length = 2 * n → cycleTrace A w ≤ m)
    (u v : List J) (hu : u.length = n) (hv : v.length = n)
    (h : cycleTrace A (u ++ v) = m) : cycleTrace A (u.reverse ++ u) = m := by
  have hU : cycleTrace A (u.reverse ++ u) ≤ m :=
    hmax _ (by simp [hu, two_mul])
  have hV : cycleTrace A (v.reverse ++ v) ≤ m :=
    hmax _ (by simp [hv, two_mul])
  have hCS := cycleTrace_sq_le hA u v
  rw [h, pow_two] at hCS
  have hh := hCS.trans (mul_le_mul_of_nonneg_left hV (cycleTrace_reverse_nonneg hA u))
  exact hU.antisymm ((mul_le_mul_iff_left₀ hm).mp hh)

/-- For every even cycle the trace is bounded by the trace of a constant
cycle drawn from the same finite family of positive steps. -/
theorem trace_even_word_le_constant {J : Type*} [Fintype J] [Nonempty J]
    (A : J → Matrix ι ι ℝ) (hA : ∀ j, (A j).PosSemidef) {n : ℕ}
    (hn : 0 < n) (w : List J) (hw : w.length = 2 * n) :
    ∃ j : J, (w.map A).prod.trace ≤ ((A j) ^ (2 * n)).trace := by
  classical
  let T := wordsOfLength J (2 * n)
  obtain ⟨best, hbest, hmax⟩ := T.exists_max_image (cycleTrace A)
    ⟨w, (mem_wordsOfLength _ _).mpr hw⟩
  let m := cycleTrace A best
  have hle (v : List J) (hv : v.length = 2 * n) : cycleTrace A v ≤ m :=
    hmax v ((mem_wordsOfLength _ _).mpr hv)
  by_cases hm : 0 < m
  swap
  · let j : J := Classical.choice ‹Nonempty J›
    exact ⟨j, (hle w hw).trans ((le_of_not_gt hm).trans ((hA j).pow _).trace_nonneg)⟩
  let Q (r : ℕ) :=
    ∃ (j : J) (v : List J), (List.replicate r j ++ v).length = 2 * n ∧
      cycleTrace A (List.replicate r j ++ v) = m
  have h1 : Q 1 := by
    have hl := (mem_wordsOfLength _ _).mp hbest
    cases best with
    | nil => simp at hl; omega
    | cons j v => exact ⟨j, v, hl, rfl⟩
  let r := Nat.findGreatest Q (2 * n)
  have hr₁ : 1 ≤ r := Nat.le_findGreatest (by omega) h1
  obtain ⟨j, v, hlen, hvalue⟩ := Nat.findGreatest_spec (by omega : 1 ≤ 2 * n) h1
  change (List.replicate r j ++ v).length = 2 * n at hlen
  change cycleTrace A (List.replicate r j ++ v) = m at hvalue
  have hvlen : r + v.length = 2 * n := by simpa only [List.length_append, List.length_replicate] using hlen
  have hform := fun j => (hA j).isHermitian
  have reflect (u v' : List J) (hu : u.length = n) (hv' : v'.length = n)
      (h : u ++ v' = List.replicate r j ++ v) : cycleTrace A (u.reverse ++ u) = m :=
    reflected_max hform hm hle u v' hu hv' (h ▸ hvalue)
  by_cases hr : n ≤ r
  · let u := List.replicate n j
    let v' := List.replicate (r - n) j ++ v
    have hs : u ++ v' = List.replicate r j ++ v := by
      simp only [u, v', ← List.append_assoc, ← List.replicate_add, Nat.add_sub_of_le hr]
    have hv' : v'.length = n := by
      simp only [v', List.length_append, List.length_replicate]
      omega
    have hr' := reflect u v' (List.length_replicate) hv' hs
    have he : ((A j) ^ (2 * n)).trace = m := by
      simpa only [u, List.reverse_replicate, ← List.replicate_add, cycleTrace,
        List.map_replicate, List.prod_replicate, two_mul] using hr'
    exact ⟨j, (hle w hw).trans_eq he.symm⟩
  · let a := v.take (n - r)
    let b := v.drop (n - r)
    let u := List.replicate r j ++ a
    have ha : a.length = n - r := by
      simp only [a, List.length_take]
      exact Nat.min_eq_left (by omega)
    have hu : u.length = n := by
      simp only [u, List.length_append, List.length_replicate, ha]
      omega
    have hb : b.length = n := by
      simp only [b, List.length_drop]
      omega
    have hsplit : u ++ b = List.replicate r j ++ v := by
      simp [u, a, b, List.append_assoc]
    have hnew : cycleTrace A (List.replicate (r + r) j ++ (a ++ a.reverse)) = m := by
      calc
        _ = cycleTrace A (a.reverse ++ (List.replicate (r + r) j ++ a)) := by
          rw [← List.append_assoc, cycleTrace_rotate]
        _ = cycleTrace A (u.reverse ++ u) := by
          simp only [u, List.reverse_append, List.reverse_replicate, List.replicate_add,
            List.append_assoc]
        _ = _ := reflect u b hu hb hsplit
    have hQ : Q (r + r) := ⟨j, a ++ a.reverse, by
      simp only [List.length_append, List.length_replicate, List.length_reverse, ha]
      omega, hnew⟩
    have hbound : r + r ≤ r := Nat.le_findGreatest (by omega) hQ
    omega

/-- This is the ordered-product inequality for a finite sample of an even
Wilson transfer cycle. -/
theorem trace_even_word_le_reference {J : Type*} [Fintype J] [Nonempty J]
    (A : J → Matrix ι ι ℝ) (B : Matrix ι ι ℝ) (hA : ∀ j, (A j).PosSemidef)
    (hAB : ∀ j, (B - A j).PosSemidef) {n : ℕ} (hn : 0 < n)
    (w : List J) (hw : w.length = 2 * n) :
    (w.map A).prod.trace ≤ (B ^ (2 * n)).trace := by
  obtain ⟨j, hj⟩ := trace_even_word_le_constant A hA hn w hw
  exact hj.trans (trace_pow_mono_of_posSemidef (hA j) (hAB j) _)

end

end GaplessYangMills

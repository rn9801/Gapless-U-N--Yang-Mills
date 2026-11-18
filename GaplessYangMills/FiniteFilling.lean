module

public import GaplessYangMills.Lattice
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.FinCases

/-!
# Filling finite integer currents

Section 3 fills the current by comparing the coordinate-ordered paths to the
two endpoints of each edge. Interchanging two adjacent steps sweeps one square.
The vertex paths cancel when the original current has zero boundary.
-/

@[expose] public section

namespace GaplessYangMills

abbrev OrientedEdge := Site × Axis
abbrev OrientedSquare := Site × Face
abbrev VertexChain := Site →₀ ℤ
abbrev EdgeChain := OrientedEdge →₀ ℤ
abbrev SquareChain := OrientedSquare →₀ ℤ

noncomputable section

def vertex (x : Site) : VertexChain := Finsupp.single x 1
def edge (x : Site) (i : Axis) : EdgeChain := Finsupp.single (x, i) 1

/-- Total absolute coefficient of a finitely supported integer chain. -/
def chainMass {E : Type*} (q : E →₀ ℤ) : ℕ := q.sum fun _ z => z.natAbs

@[simp] theorem chainMass_zero {E : Type*} : chainMass (0 : E →₀ ℤ) = 0 := by
  simp [chainMass]

@[simp] theorem chainMass_single {E : Type*} (e : E) (z : ℤ) :
    chainMass (Finsupp.single e z) = z.natAbs := by
  simp [chainMass, Finsupp.sum_single_index]

@[simp] theorem chainMass_neg {E : Type*} (q : E →₀ ℤ) :
    chainMass (-q) = chainMass q := by
  simp [chainMass, Finsupp.sum, Finsupp.support_neg]

theorem chainMass_add_le {E : Type*} (q r : E →₀ ℤ) :
    chainMass (q + r) ≤ chainMass q + chainMass r := by
  classical
  unfold chainMass
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_add _ (by simp),
    Finsupp.sum_of_support_subset q (Finset.subset_union_left) _ (by simp),
    Finsupp.sum_of_support_subset r (Finset.subset_union_right) _ (by simp),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun e _ => Int.natAbs_add_le (q e) (r e)

theorem chainMass_smul {E : Type*} (a : ℤ) (q : E →₀ ℤ) :
    chainMass (a • q) = a.natAbs * chainMass q := by
  classical
  unfold chainMass
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (by simp)]
  simp [Finsupp.sum, Int.natAbs_mul, Finset.mul_sum]

def boundary₁ : EdgeChain →ₗ[ℤ] VertexChain :=
  Finsupp.linearCombination ℤ fun (x, i) => vertex (x + step i) - vertex x

def boundary₂ : SquareChain →ₗ[ℤ] EdgeChain :=
  Finsupp.linearCombination ℤ fun (x, I) =>
    let (i, j) := I.axes
    edge x i + edge (x + step i) j - edge x j - edge (x + step j) i

@[simp]
theorem boundary₁_edge (x : Site) (i : Axis) :
    boundary₁ (edge x i) = vertex (x + step i) - vertex x := by
  simp [boundary₁, edge]

private theorem swapped_steps_bound (x : Site) (i j : Axis) :
    ∃ s : SquareChain,
      boundary₂ s = edge x i + edge (x + step i) j - edge x j - edge (x + step j) i ∧
        (∀ p ∈ s.support, p.1 = x) ∧ chainMass s ≤ 1 := by
  have hpos (I : Face) :
      ∃ s : SquareChain, boundary₂ s =
        edge x I.axes.1 + edge (x + step I.axes.1) I.axes.2 -
          edge x I.axes.2 - edge (x + step I.axes.2) I.axes.1 ∧
            (∀ p ∈ s.support, p.1 = x) ∧ chainMass s ≤ 1 := by
    refine ⟨Finsupp.single (x, I) 1, ?_, ?_, by simp⟩
    · cases I <;> simp [boundary₂, Face.axes]
    · intro p hp
      have he : p = (x, I) := by simpa using hp
      exact congrArg Prod.fst he
  have hneg (I : Face) :
      ∃ s : SquareChain, boundary₂ s =
        edge x I.axes.2 + edge (x + step I.axes.2) I.axes.1 -
          edge x I.axes.1 - edge (x + step I.axes.1) I.axes.2 ∧
            (∀ p ∈ s.support, p.1 = x) ∧ chainMass s ≤ 1 := by
    obtain ⟨s, hs, hbase, hmass⟩ := hpos I
    refine ⟨-s, ?_, ?_, by simpa using hmass⟩
    · rw [map_neg, hs]
      abel
    · simpa using hbase
  fin_cases i <;> fin_cases j
  all_goals first
    | exact hpos .xy
    | exact hpos .xz
    | exact hpos .xw
    | exact hpos .yz
    | exact hpos .yw
    | exact hpos .zw
    | exact hneg .xy
    | exact hneg .xz
    | exact hneg .xw
    | exact hneg .yz
    | exact hneg .yw
    | exact hneg .zw
    | exact ⟨0, by simp [add_sub_cancel_left], by simp, by simp⟩

/-- Follow a word in the positive lattice directions. -/
def pathEnd (x : Site) (l : List Axis) : Site :=
  l.foldl (fun y i => y + step i) x

def pathChain (x : Site) (l : List Axis) : EdgeChain :=
  l.foldr (fun i tail y => edge y i + tail (y + step i)) (fun _ => 0) x

@[simp]
theorem pathEnd_nil (x : Site) : pathEnd x [] = x := rfl

@[simp]
theorem pathEnd_cons (x : Site) (i : Axis) (l : List Axis) :
    pathEnd x (i :: l) = pathEnd (x + step i) l := rfl

@[simp]
theorem pathChain_nil (x : Site) : pathChain x [] = 0 := rfl

@[simp]
theorem pathChain_cons (x : Site) (i : Axis) (l : List Axis) :
    pathChain x (i :: l) = edge x i + pathChain (x + step i) l := rfl

private theorem pathEnd_count (x : Site) (l : List Axis) (i : Axis) :
    pathEnd x l i = x i + (l.count i : ℤ) := by
  induction l generalizing x with
  | nil => simp
  | cons j l ih =>
    by_cases h : j = i
    · subst j
      simp only [pathEnd_cons, ih, Pi.add_apply, step_same, List.count_cons_self,
        Nat.cast_add, Nat.cast_one]
      abel
    · rw [List.count_cons_of_ne h]
      simp [ih, step_other h]

private theorem pathChain_snoc (x : Site) (l : List Axis) (i : Axis) :
    pathChain x (l ++ [i]) = pathChain x l + edge (pathEnd x l) i := by
  induction l generalizing x with
  | nil => simp
  | cons j l ih => simp [ih, add_assoc]

/-- Each square's base vertex is in the coordinate box. -/
def SquareBasesIn (s : SquareChain) (o b : Site) : Prop :=
  ∀ p ∈ s.support, o ≤ p.1 ∧ p.1 ≤ b

private theorem squareBasesIn_add {s t : SquareChain} {o b : Site}
    (hs : SquareBasesIn s o b) (ht : SquareBasesIn t o b) : SquareBasesIn (s + t) o b := by
  classical
  intro p hp
  exact (Finset.mem_union.mp (Finsupp.support_add hp)).elim (hs p) (ht p)

private theorem le_pathEnd (x : Site) (l : List Axis) : x ≤ pathEnd x l := by
  intro i
  rw [pathEnd_count]
  exact le_add_of_nonneg_right (Int.natCast_nonneg _)

private theorem pathEnd_perm {l l' : List Axis} (h : l.Perm l') (x : Site) :
    pathEnd x l = pathEnd x l' := by
  funext i
  rw [pathEnd_count, pathEnd_count, h.count_eq i]

/-- Permuting a positive path word changes the chain by a square boundary
supported in any box containing the endpoints of the path. -/
theorem path_perm_boundary_in_box {l l' : List Axis} (h : l.Perm l') (x o b : Site)
    (ho : o ≤ x) (hb : pathEnd x l ≤ b) :
    ∃ s : SquareChain, boundary₂ s = pathChain x l - pathChain x l' ∧ SquareBasesIn s o b := by
  induction h generalizing x with
  | nil => exact ⟨0, by simp, by simp [SquareBasesIn]⟩
  | cons i _ ih =>
    have hstep : x ≤ x + step i := le_pathEnd x [i]
    obtain ⟨s, hs, hbox⟩ := ih (x + step i) (ho.trans hstep) hb
    refine ⟨s, ?_, hbox⟩
    rw [hs]
    simp
  | swap i j l =>
    obtain ⟨s, hs, hbase, _⟩ := swapped_steps_bound x j i
    refine ⟨s, ?_, ?_⟩
    · rw [hs]
      simp only [pathChain_cons, add_right_comm x (step j) (step i)]
      abel
    · intro p hp
      rw [hbase p hp]
      exact ⟨ho, (le_pathEnd x (j :: i :: l)).trans hb⟩
  | trans hl _ ih ih' =>
    obtain ⟨s, hs, hsbox⟩ := ih x ho hb
    obtain ⟨t, ht, htbox⟩ := ih' x ho ((pathEnd_perm hl x).symm.le.trans hb)
    refine ⟨s + t, ?_, squareBasesIn_add hsbox htbox⟩
    rw [map_add, hs, ht]
    abel

theorem path_perm_boundary {l l' : List Axis} (h : l.Perm l') (x : Site) :
    ∃ s : SquareChain, boundary₂ s = pathChain x l - pathChain x l' := by
  obtain ⟨s, hs, _⟩ := path_perm_boundary_in_box h x x (pathEnd x l) le_rfl le_rfl
  exact ⟨s, hs⟩

def coordinateWord (o x : Site) : List Axis :=
  List.replicate (x 0 - o 0).toNat 0 ++ List.replicate (x 1 - o 1).toNat 1 ++
    List.replicate (x 2 - o 2).toNat 2 ++ List.replicate (x 3 - o 3).toNat 3

private theorem coordinateWord_count (o x : Site) (i : Axis) :
    (coordinateWord o x).count i = (x i - o i).toNat := by
  fin_cases i <;> simp [coordinateWord, List.count_replicate]

private theorem pathEnd_coordinateWord (o x : Site) (hx : ∀ i, o i ≤ x i) :
    pathEnd o (coordinateWord o x) = x := by
  funext i
  rw [pathEnd_count, coordinateWord_count, Int.toNat_of_nonneg (sub_nonneg.mpr (hx i))]
  abel

private theorem pathEnd_snoc (x : Site) (l : List Axis) (i : Axis) :
    pathEnd x (l ++ [i]) = pathEnd x l + step i := by
  induction l generalizing x with
  | nil => simp
  | cons j l ih => simp [ih]

private theorem pathChain_append (x : Site) (u v : List Axis) :
    pathChain x (u ++ v) = pathChain x u + pathChain (pathEnd x u) v := by
  induction u generalizing x with
  | nil => simp
  | cons i u ih => simp [ih, add_assoc]

private theorem pathEnd_append (x : Site) (u v : List Axis) :
    pathEnd x (u ++ v) = pathEnd (pathEnd x u) v := by
  exact List.foldl_append (f := fun y i => y + step i) (b := x) (l := u) (l' := v)

private theorem sweep_appended_step (x o b : Site) (l : List Axis) (i : Axis)
    (ho : o ≤ x) (hb : pathEnd x (l ++ [i]) ≤ b) :
    ∃ s : SquareChain, boundary₂ s = pathChain x (l ++ [i]) - pathChain x (i :: l) ∧
      SquareBasesIn s o b ∧ chainMass s ≤ l.length := by
  induction l generalizing x with
  | nil => exact ⟨0, by simp, by simp [SquareBasesIn], by simp⟩
  | cons j l ih =>
    obtain ⟨s, hs, hsbase, hsmass⟩ :=
      ih (x + step j) (ho.trans (le_pathEnd x [j])) hb
    obtain ⟨t, ht, htbase, htmass⟩ := swapped_steps_bound x j i
    refine ⟨s + t, ?_, ?_, ?_⟩
    · rw [map_add, hs, ht]
      simp only [List.cons_append, pathChain_cons, add_right_comm x (step j) (step i)]
      abel
    · apply squareBasesIn_add hsbase
      intro p hp
      rw [htbase p hp]
      exact ⟨ho, (le_pathEnd x ((j :: l) ++ [i])).trans hb⟩
    · exact (chainMass_add_le s t).trans (Nat.add_le_add hsmass htmass)

/-- Sum of the coordinate widths of the box. -/
def boxWidth (o b : Site) : ℕ := ∑ i, (b i - o i).toNat

private theorem coordinateWord_length (o x : Site) :
    (coordinateWord o x).length = boxWidth o x := by
  simp [coordinateWord, boxWidth, Fin.sum_univ_succ]

private theorem connector_boundary (o b x : Site) (hx : o ≤ x) (i : Axis)
    (hb : x + step i ≤ b) :
    ∃ s : SquareChain, boundary₂ s = pathChain o (coordinateWord o x) + edge x i -
      pathChain o (coordinateWord o (x + step i)) ∧ SquareBasesIn s o b ∧
        chainMass s ≤ boxWidth o b := by
  let firstSteps := coordinateWord o (fun j => if j ≤ i then x j else o j)
  let laterSteps := coordinateWord o (fun j => if i < j then x j else o j)
  have hword : coordinateWord o x = firstSteps ++ laterSteps := by
    fin_cases i <;> simp [firstSteps, laterSteps, coordinateWord, List.append_assoc]
  have hnext : coordinateWord o (x + step i) = firstSteps ++ i :: laterSteps := by
    have hn (j : Axis) : (x j + 1 - o j).toNat = (x j - o j).toNat + 1 := by
      have hi : o j ≤ x j := hx j
      omega
    fin_cases i <;>
      simp [firstSteps, laterSteps, coordinateWord, List.append_assoc, step, hn, List.replicate_succ']
  have hlaterSteps : (pathEnd (pathEnd o firstSteps) (laterSteps ++ [i])) ≤ b := by
    rw [← pathEnd_append, ← List.append_assoc, ← hword, pathEnd_snoc,
      pathEnd_coordinateWord o x hx]
    exact hb
  obtain ⟨s, hs, hbox, hmass⟩ := sweep_appended_step (pathEnd o firstSteps) o b laterSteps i
    (le_pathEnd o firstSteps) hlaterSteps
  refine ⟨s, ?_, hbox, hmass.trans ?_⟩
  · have ha := pathChain_snoc o (coordinateWord o x) i
    rw [pathEnd_coordinateWord o x hx] at ha
    rw [← ha, hnext, hword, List.append_assoc, hs]
    simp only [pathChain_append o firstSteps]
    abel
  · rw [coordinateWord_length]
    apply Finset.sum_le_sum
    intro j _
    have hxb : x j ≤ b j := (le_pathEnd x [i] j).trans (hb j)
    have ho : o j ≤ b j := (hx j).trans hxb
    change ((if i < j then x j else o j) - o j).toNat ≤ (b j - o j).toNat
    split_ifs <;> omega

/-- The filling sweeps at most one square per step of each edge connector. -/
theorem exists_finite_filling_in_box_mass (q : EdgeChain) (hq : boundary₁ q = 0)
    (o b : Site) (hbox : ∀ e ∈ q.support, o ≤ e.1 ∧ e.1 + step e.2 ≤ b) :
    ∃ s : SquareChain, boundary₂ s = q ∧ SquareBasesIn s o b ∧
      chainMass s ≤ chainMass q * boxWidth o b := by
  classical
  let paths : VertexChain →ₗ[ℤ] EdgeChain :=
    Finsupp.linearCombination ℤ (fun x => pathChain o (coordinateWord o x))
  have hedges (e : OrientedEdge) (he : e ∈ q.support) :
      ∃ s : SquareChain, boundary₂ s =
        edge e.1 e.2 - paths (boundary₁ (edge e.1 e.2)) ∧ SquareBasesIn s o b ∧
          chainMass s ≤ boxWidth o b := by
    obtain ⟨s, hs, hbase, hmass⟩ := connector_boundary o b e.1 (hbox e he).1 e.2 (hbox e he).2
    refine ⟨s, ?_, hbase, hmass⟩
    simp only [hs, boundary₁_edge, map_sub, paths, vertex, Finsupp.linearCombination_single, one_smul]
    abel
  choose connector hconnector using hedges
  let cell (e : OrientedEdge) : SquareChain :=
    if he : e ∈ q.support then connector e he else 0
  have hrep : ∑ e ∈ q.support, q e • edge e.1 e.2 = q := by
    simpa [Finsupp.sum, edge, Finsupp.smul_single] using q.sum_single
  have hbase (T : Finset OrientedEdge) (hT : T ⊆ q.support) :
      SquareBasesIn (∑ e ∈ T, q e • cell e) o b := by
    induction T using Finset.induction_on with
    | empty => simp [SquareBasesIn]
    | insert e T he ih =>
      rw [Finset.sum_insert he]
      apply squareBasesIn_add _ (ih (fun f hf => hT (Finset.mem_insert_of_mem hf)))
      have heq := hT (Finset.mem_insert_self e T)
      intro p hp
      have hp' : p ∈ (cell e).support := Finsupp.support_smul hp
      have hebox := (hconnector e heq).2.1
      exact hebox p (by simpa only [cell, dite_eq_left heq] using hp')
  have hmass (T : Finset OrientedEdge) (hT : T ⊆ q.support) :
      chainMass (∑ e ∈ T, q e • cell e) ≤ ∑ e ∈ T, (q e).natAbs * boxWidth o b := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert e T he ih =>
      rw [Finset.sum_insert he, Finset.sum_insert he]
      refine (chainMass_add_le _ _).trans (Nat.add_le_add ?_ (ih fun f hf =>
        hT (Finset.mem_insert_of_mem hf)))
      rw [chainMass_smul]
      have heq := hT (Finset.mem_insert_self e T)
      exact Nat.mul_le_mul_left _ (by simpa only [cell, dite_eq_left heq] using (hconnector e heq).2.2)
  refine ⟨∑ e ∈ q.support, q e • cell e, ?_, hbase _ (fun _ he => he), ?_⟩
  swap
  · change chainMass _ ≤ (∑ e ∈ q.support, (q e).natAbs) * boxWidth o b
    rw [Finset.sum_mul]
    exact hmass _ (fun _ he => he)
  rw [map_sum]
  calc
    _ = ∑ e ∈ q.support, q e • (edge e.1 e.2 - paths (boundary₁ (edge e.1 e.2))) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [map_smul]
      simpa only [cell, dite_eq_left he] using congrArg (q e • ·) (hconnector e he).1
    _ = q - paths (boundary₁ q) := by
      simp_rw [smul_sub, ← map_smul paths, ← map_smul boundary₁]
      rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, hrep]
    _ = q := by simp [hq]

/-- A divergence-free current with all endpoints in a box admits a square
filling whose bases stay inside the box. -/
theorem exists_finite_filling_in_box (q : EdgeChain) (hq : boundary₁ q = 0)
    (o b : Site) (hbox : ∀ e ∈ q.support, o ≤ e.1 ∧ e.1 + step e.2 ≤ b) :
    ∃ s : SquareChain, boundary₂ s = q ∧ SquareBasesIn s o b := by
  obtain ⟨s, hs, hbase, _⟩ := exists_finite_filling_in_box_mass q hq o b hbox
  exact ⟨s, hs, hbase⟩

/-- A finitely supported, divergence-free integer current bounds a finitely
supported integer square chain. -/
theorem exists_finite_filling (q : EdgeChain) (hq : boundary₁ q = 0) :
    ∃ s : SquareChain, boundary₂ s = q := by
  classical
  by_cases hz : q = 0
  · exact ⟨0, by simp [hz]⟩
  have hn : q.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun hs => hz (Finsupp.support_eq_empty.mp hs))
  let o : Site := fun i => q.support.inf' hn (fun e => e.1 i)
  let b : Site := fun i => q.support.sup' hn (fun e => (e.1 + step e.2) i)
  have hbox (e : OrientedEdge) (he : e ∈ q.support) : o ≤ e.1 ∧ e.1 + step e.2 ≤ b :=
    ⟨fun _ => Finset.inf'_le _ he, fun i => Finset.le_sup' (fun f => (f.1 + step f.2) i) he⟩
  obtain ⟨s, hs, _⟩ := exists_finite_filling_in_box q hq o b hbox
  exact ⟨s, hs⟩

end

end GaplessYangMills

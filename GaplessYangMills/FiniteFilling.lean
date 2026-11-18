module

public import GaplessYangMills.Lattice
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
      boundary₂ s = edge x i + edge (x + step i) j - edge x j - edge (x + step j) i := by
  have hpos (I : Face) :
      ∃ s : SquareChain, boundary₂ s =
        edge x I.axes.1 + edge (x + step I.axes.1) I.axes.2 -
          edge x I.axes.2 - edge (x + step I.axes.2) I.axes.1 := by
    refine ⟨Finsupp.single (x, I) 1, ?_⟩
    cases I <;> simp [boundary₂, Face.axes]
  have hneg (I : Face) :
      ∃ s : SquareChain, boundary₂ s =
        edge x I.axes.2 + edge (x + step I.axes.2) I.axes.1 -
          edge x I.axes.1 - edge (x + step I.axes.1) I.axes.2 := by
    obtain ⟨s, hs⟩ := hpos I
    refine ⟨-s, ?_⟩
    rw [map_neg, hs]
    abel
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
    | exact ⟨0, by simp [add_sub_cancel_left]⟩

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

/-- Permuting a positive path word changes the chain by a square boundary. -/
theorem path_perm_boundary {l l' : List Axis} (h : l.Perm l') (x : Site) :
    ∃ s : SquareChain, boundary₂ s = pathChain x l - pathChain x l' := by
  induction h generalizing x with
  | nil => exact ⟨0, by simp⟩
  | cons i _ ih =>
    obtain ⟨s, hs⟩ := ih (x + step i)
    refine ⟨s, ?_⟩
    rw [hs]
    simp
  | swap i j l =>
    obtain ⟨s, hs⟩ := swapped_steps_bound x j i
    refine ⟨s, ?_⟩
    rw [hs]
    simp only [pathChain_cons, add_right_comm x (step j) (step i)]
    abel
  | trans _ _ ih ih' =>
    obtain ⟨s, hs⟩ := ih x
    obtain ⟨t, ht⟩ := ih' x
    refine ⟨s + t, ?_⟩
    rw [map_add, hs, ht]
    abel

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

private theorem connector_boundary (o x : Site) (hx : ∀ i, o i ≤ x i) (i : Axis) :
    ∃ s : SquareChain, boundary₂ s = pathChain o (coordinateWord o x) + edge x i -
      pathChain o (coordinateWord o (x + step i)) := by
  have hp : (coordinateWord o x ++ [i]).Perm (coordinateWord o (x + step i)) := by
    apply List.perm_iff_count.mpr
    intro j
    rw [List.count_append, coordinateWord_count, coordinateWord_count]
    have h := hx j
    by_cases hij : i = j
    · subst j
      simp only [List.count_cons_self, List.count_nil, zero_add, Pi.add_apply, step_same]
      omega
    · simp [hij, step_other hij]
  obtain ⟨s, hs⟩ := path_perm_boundary hp o
  rw [pathChain_snoc, pathEnd_coordinateWord o x hx] at hs
  exact ⟨s, hs⟩

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
  let paths : VertexChain →ₗ[ℤ] EdgeChain :=
    Finsupp.linearCombination ℤ (fun x => pathChain o (coordinateWord o x))
  have hedges (e : OrientedEdge) (he : e ∈ q.support) :
      ∃ s : SquareChain, boundary₂ s =
        edge e.1 e.2 - paths (boundary₁ (edge e.1 e.2)) := by
    have heo (i : Axis) : o i ≤ e.1 i := Finset.inf'_le _ he
    obtain ⟨s, hs⟩ := connector_boundary o e.1 heo e.2
    refine ⟨s, ?_⟩
    simp only [hs, boundary₁_edge, map_sub, paths, vertex, Finsupp.linearCombination_single, one_smul]
    abel
  choose connector hconnector using hedges
  let cell (e : OrientedEdge) : SquareChain :=
    if he : e ∈ q.support then connector e he else 0
  have hrep : ∑ e ∈ q.support, q e • edge e.1 e.2 = q := by
    simpa [Finsupp.sum, edge, Finsupp.smul_single] using q.sum_single
  refine ⟨∑ e ∈ q.support, q e • cell e, ?_⟩
  rw [map_sum]
  calc
    _ = ∑ e ∈ q.support, q e • (edge e.1 e.2 - paths (boundary₁ (edge e.1 e.2))) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [map_smul]
      simpa only [cell, dite_eq_left he] using congrArg (q e • ·) (hconnector e he)
    _ = q - paths (boundary₁ q) := by
      simp_rw [smul_sub, ← map_smul paths, ← map_smul boundary₁]
      rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, hrep]
    _ = q := by simp [hq]

end

end GaplessYangMills

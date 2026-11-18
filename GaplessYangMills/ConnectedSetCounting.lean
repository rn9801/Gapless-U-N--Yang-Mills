module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Data.Finset.Card

/-!
# Counting finite connected sets by closed walks

Starting at a prescribed root, a connected set of (n) vertices is the
support of a closed walk of length (2(n-1)). The first step of a walk
has at most as many choices as the degree bound of the graph.
-/

@[expose] public section

namespace GaplessYangMills

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [DecidableEq V]

theorem walk_crosses_finset {x y : V} (p : G.Walk x y) (S : Finset V)
    (hx : x ∈ S) (hy : y ∉ S) :
    ∃ a ∈ S, ∃ b ∈ p.support, b ∉ S ∧ G.Adj a b := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons u v w huv p ih =>
    by_cases hv : v ∈ S
    · obtain ⟨a, ha, b, hb, hbS, hab⟩ := ih hv hy
      exact ⟨a, ha, b, List.mem_cons_of_mem _ hb, hbS, hab⟩
    · exact ⟨u, hx, v, List.mem_cons_of_mem _ p.start_mem_support, hv, huv⟩

private theorem closedWalk_insert_support {x a b : V} (p : G.Walk x x)
    (ha : a ∈ p.support) (hab : G.Adj a b) :
    ∃ q : G.Walk x x, q.support.toFinset = insert b p.support.toFinset ∧
      q.length = p.length + 2 := by
  let left := p.takeUntil a ha
  let right := p.dropUntil a ha
  let excursion : G.Walk a a := .cons hab (.cons hab.symm .nil)
  let q := left.append (excursion.append right)
  have hsplit : left.append right = p := p.take_spec ha
  refine ⟨q, ?_, ?_⟩
  · ext z
    have hz : z ∈ p.support ↔ z ∈ left.support ∨ z ∈ right.support := by
      rw [← hsplit, Walk.mem_support_append_iff]
    have hleft : a ∈ left.support := left.end_mem_support
    simp only [q, List.mem_toFinset, Finset.mem_insert, Walk.mem_support_append_iff, hz,
      excursion, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false]
    by_cases hza : z = a
    · subst z
      simp [hleft]
    · simp [hza]
      tauto
  · have h := congrArg Walk.length hsplit
    simp only [q, Walk.length_append, excursion, Walk.length_cons, Walk.length_nil] at h ⊢
    omega

private theorem extend_closedWalk {x : V} (S : Finset V)
    (hS : ∀ y ∈ S, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ S)
    (k : ℕ) (p : G.Walk x x) (hp : p.support.toFinset ⊆ S)
    (hlen : p.length = 2 * (p.support.toFinset.card - 1))
    (hrest : S.card - p.support.toFinset.card ≤ k) :
    ∃ q : G.Walk x x, q.support.toFinset = S ∧ q.length = 2 * (S.card - 1) := by
  induction k generalizing p with
  | zero =>
    have hcard : S.card ≤ p.support.toFinset.card := by omega
    have he := Finset.eq_of_subset_of_card_le hp hcard
    exact ⟨p, he, he ▸ hlen⟩
  | succ k ih =>
    by_cases he : p.support.toFinset = S
    · exact ⟨p, he, he ▸ hlen⟩
    have hss : p.support.toFinset ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hp, he⟩
    obtain ⟨y, hy, hyp⟩ := Finset.exists_of_ssubset hss
    obtain ⟨r, hr⟩ := hS y hy
    have hx : x ∈ p.support.toFinset := List.mem_toFinset.mpr p.start_mem_support
    obtain ⟨a, ha, b, hb, hbp, hab⟩ := walk_crosses_finset G r p.support.toFinset hx hyp
    obtain ⟨q, hq, hqLen⟩ := closedWalk_insert_support G p (List.mem_toFinset.mp ha) hab
    have hcard : q.support.toFinset.card = p.support.toFinset.card + 1 := by
      rw [hq, Finset.card_insert_of_notMem hbp]
    have hnonempty : 0 < p.support.toFinset.card := Finset.card_pos.mpr ⟨x, hx⟩
    apply ih q
    · rw [hq]
      exact Finset.insert_subset (hr b hb) hp
    · rw [hqLen, hlen, hcard]
      omega
    · rw [hcard]
      omega

theorem exists_closedWalk_with_support {x : V} (S : Finset V) (hx : x ∈ S)
    (hS : ∀ y ∈ S, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ S) :
    ∃ q : G.Walk x x, q.support.toFinset = S ∧ q.length = 2 * (S.card - 1) := by
  apply extend_closedWalk G S hS S.card .nil
  · simpa [Walk.support_nil] using hx
  · simp [Walk.support_nil]
  · exact Nat.sub_le _ _

variable [LocallyFinite G]

theorem card_finsetWalkLength_le (D : ℕ) (hD : ∀ u, Fintype.card (G.neighborSet u) ≤ D)
    (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v).card ≤ D ^ n := by
  induction n generalizing u v with
  | zero => rcases eq_or_ne u v with rfl | h <;> simp [finsetWalkLength, *]
  | succ n ih =>
    classical
    rw [finsetWalkLength]
    refine Finset.card_biUnion_le.trans ?_
    simp only [Finset.card_map]
    calc
      _ ≤ ∑ _ : G.neighborSet u, D ^ n := Finset.sum_le_sum fun w _ => ih w v
      _ = Fintype.card (G.neighborSet u) * D ^ n := by simp
      _ ≤ D ^ (n + 1) := by rw [pow_succ']; exact Nat.mul_le_mul_right _ (hD u)

/-- A finite family containing every connected size-`n` set through `x`. -/
def connectedSetCover (x : V) (n : ℕ) : Finset (Finset V) :=
  ((G.finsetWalkLength (2 * (n - 1)) x x).image fun p => p.support.toFinset).filter
    fun S => S.card = n

theorem mem_connectedSetCover {x : V} (S : Finset V) (hx : x ∈ S)
    (hS : ∀ y ∈ S, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ S) :
    S ∈ connectedSetCover G x S.card := by
  obtain ⟨p, hp, hpLen⟩ := exists_closedWalk_with_support G S hx hS
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨p, mem_finsetWalkLength_iff.mpr hpLen, hp⟩, rfl⟩

theorem card_connectedSetCover_le (D : ℕ) (hD : ∀ u, Fintype.card (G.neighborSet u) ≤ D)
    (x : V) (n : ℕ) :
    (connectedSetCover G x n).card ≤ D ^ (2 * (n - 1)) :=
  Finset.card_filter_le _ _ |>.trans
    (Finset.card_image_le.trans (card_finsetWalkLength_le G D hD _ x x))

end GaplessYangMills

module

public import GaplessYangMills.Duality
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Separating current components

Divergence is evaluated at a vertex from the finitely many incident edges.
Restricting a current to a union of its support components preserves divergence.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

def incident (e : OrientedEdge) (x : Site) : Prop :=
  e.1 = x ∨ e.1 + step e.2 = x

def currentDivergence (q : OrientedEdge → ℤ) (x : Site) : ℤ :=
  ∑ i : Axis, (q (x - step i, i) - q (x, i))

theorem boundary₁_eq_currentDivergence (q : EdgeChain) (x : Site) :
    boundary₁ q x = currentDivergence q x := by
  have h0 := boundary₁_primalCurrent q (-x)
  simp [d₃, diff, primalCurrent] at h0
  rw [h0]
  simp only [currentDivergence, Fin.sum_univ_succ,
    sub_eq_add_neg, add_comm x]
  abel

/-- An edge set is saturated for a current when any two supported edges at
the same vertex belong to the set together. -/
def CurrentSaturated (q : OrientedEdge → ℤ) (C : Set OrientedEdge) : Prop :=
  ∀ ⦃x e f⦄, incident e x → incident f x → q e ≠ 0 → q f ≠ 0 → e ∈ C → f ∈ C

def restrictCurrent (q : OrientedEdge → ℤ) (C : Set OrientedEdge) : OrientedEdge → ℤ :=
  C.indicator q

theorem currentDivergence_restrict (q : OrientedEdge → ℤ) (C : Set OrientedEdge)
    (hsat : CurrentSaturated q C) (hq : ∀ x, currentDivergence q x = 0) (x : Site) :
    currentDivergence (restrictCurrent q C) x = 0 := by
  classical
  have hin (i : Axis) : incident (x - step i, i) x :=
    Or.inr (sub_add_cancel x (step i))
  have hout (i : Axis) : incident (x, i) x := Or.inl rfl
  by_cases hmeet : ∃ e ∈ C, incident e x ∧ q e ≠ 0
  · obtain ⟨e, he, hex, hn⟩ := hmeet
    have hall (f : OrientedEdge) (hfx : incident f x) : restrictCurrent q C f = q f := by
      by_cases hf : q f = 0
      · simp [restrictCurrent, Set.indicator_apply, hf]
      · exact Set.indicator_of_mem (hsat hex hfx hn hf he) _
    rw [← hq x]
    unfold currentDivergence
    exact Finset.sum_congr rfl fun i _ => by rw [hall _ (hin i), hall _ (hout i)]
  · have hall (f : OrientedEdge) (hfx : incident f x) : restrictCurrent q C f = 0 := by
      by_cases hf : f ∈ C
      · rw [restrictCurrent, Set.indicator_of_mem hf]
        by_contra hn
        exact hmeet ⟨f, hf, hfx, hn⟩
      · exact Set.indicator_of_notMem hf _
    simp [currentDivergence, hall _ (hin _), hall _ (hout _)]

/-- Each finite saturated portion of a divergence-free current has an integer
square filling, even when the original current has infinite support. -/
theorem exists_component_filling (q : OrientedEdge → ℤ) (C : Set OrientedEdge)
    (hsat : CurrentSaturated q C) (hq : ∀ x, currentDivergence q x = 0)
    (hfinite : (Function.support (restrictCurrent q C)).Finite) :
    ∃ s : SquareChain, (boundary₂ s : OrientedEdge → ℤ) = restrictCurrent q C := by
  let r := Finsupp.ofSupportFinite (restrictCurrent q C) hfinite
  have hr : (r : OrientedEdge → ℤ) = restrictCurrent q C := Finsupp.ofSupportFinite_coe
  have hd : boundary₁ r = 0 := by
    ext x
    rw [boundary₁_eq_currentDivergence, hr]
    exact currentDivergence_restrict q C hsat hq x
  obtain ⟨s, hs⟩ := exists_finite_filling r hd
  exact ⟨s, hs ▸ hr⟩

end

end GaplessYangMills

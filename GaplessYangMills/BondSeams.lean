module

public import GaplessYangMills.BondReflectionGeometry
public import GaplessYangMills.PeriodicGauge

/-!
# Crossing links and faces at a bond reflection

The two sets of crossing normal links form a matching. Gauging the head
of each such link by the original link value sets every crossing link
to identity. A crossing plaquette then compares a tangent link in the
positive half with its reflected partner.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

def bondSeamLinks (L : ℕ) [NeZero L] (τ : Axis) : Finset (TorusLink L) := by
  classical
  exact Finset.univ.filter (bondCutBoundary τ (normalLink τ))

theorem mem_bondSeamLinks {L : ℕ} [NeZero L] (τ : Axis) (p : TorusLink L) :
    p ∈ bondSeamLinks L τ ↔ bondCutBoundary τ (normalLink τ) p := by
  classical
  simp [bondSeamLinks]

theorem normalLink_true_iff (τ i : Axis) : normalLink τ i = true ↔ i = τ := by
  simp [normalLink]

theorem normalFace_true_iff (τ : Axis) (I : Face) :
    normalFace τ I = true ↔ I.axes.1 = τ ∨ I.axes.2 = τ := by
  simp [normalFace]

theorem bondSeamHead_time {L : ℕ} [NeZero L] (hL : 4 ≤ L) (τ : Axis) (x : TorusSite L)
    (hx : (τ, x) ∈ bondSeamLinks L τ) :
    ((x + torusStep L τ) τ).val = L / 2 ∨ ((x + torusStep L τ) τ).val = 0 := by
  have h := ((mem_bondSeamLinks τ (τ, x)).mp hx).2
  rw [torusStep_time_eq, ite_eq_left rfl, ZMod.val_add, ZMod.val_one'' (by omega : L ≠ 1)]
  rcases h with h | h
  · left
    rw [h, Nat.mod_eq_of_lt (by omega)]
  · right
    rw [h, Nat.mod_self]

def bondSeamGauge {L N : ℕ} [NeZero L] (τ : Axis) (a : PeriodicBlock N (bondSeamLinks L τ))
    (x : TorusSite L) : UnitaryMatrix N := by
  classical
  exact if h : (τ, x - torusStep L τ) ∈ bondSeamLinks L τ then a ⟨_, h⟩ else 1

theorem bondSeamGauge_fixes {L N : ℕ} [NeZero L] (hL : 4 ≤ L) (τ : Axis)
    (a : PeriodicBlock N (bondSeamLinks L τ)) (e : {p // p ∈ bondSeamLinks L τ}) :
    bondSeamGauge τ a e.val.2 * a e *
      (bondSeamGauge τ a (e.val.2 + torusStep L e.val.1))⁻¹ = 1 := by
  classical
  obtain ⟨⟨i, x⟩, hx⟩ := e
  have hc := (mem_bondSeamLinks τ (i, x)).mp hx
  have hi := (normalLink_true_iff τ i).mp hc.1
  subst i
  have hc' : (x τ).val + 1 = L / 2 ∨ (x τ).val + 1 = L := hc.2
  have ht : (τ, x - torusStep L τ) ∉ bondSeamLinks L τ := by
    intro hp
    have hh := bondSeamHead_time hL τ (x - torusStep L τ) hp
    rw [sub_add_cancel] at hh
    rcases hh with hm | h0 <;> rcases hc' with h | h <;> omega
  change bondSeamGauge τ a x * a ⟨(τ, x), hx⟩ * (bondSeamGauge τ a (x + torusStep L τ))⁻¹ = 1
  simp [bondSeamGauge, ht, hx]

theorem bondPositivePlaquette_links {L : ℕ} [NeZero L] (hL : 4 ≤ L) (τ : Axis)
    (p : Face × TorusSite L) (hp : bondCutInterior τ (normalFace τ) p) :
    ∀ e ∈ periodicBoundaryLinks p, bondCutInterior τ (normalLink τ) e := by
  obtain ⟨I, x⟩ := p
  have hlt : (x τ).val < L / 2 := hp.1
  have hbase (i : Axis) (hi : i = I.axes.1 ∨ i = I.axes.2) : bondCutInterior τ (normalLink τ) (i, x) := by
    refine ⟨hlt, fun h => hp.2 ⟨?_, h.2⟩⟩
    have he := (normalLink_true_iff τ i).mp h.1
    exact (normalFace_true_iff τ I).mpr (hi.elim (fun h => Or.inl (h.symm.trans he))
      (fun h => Or.inr (h.symm.trans he)))
  have hshift (i j : Axis) (hij : i ≠ j) (hi : i = I.axes.1 ∨ i = I.axes.2)
      (hj : j = I.axes.1 ∨ j = I.axes.2) :
      bondCutInterior τ (normalLink τ) (i, x + torusStep L j) := by
    by_cases hn : j = τ
    · have ht : normalFace τ I = true := (normalFace_true_iff τ I).mpr
        (hj.elim (fun h => Or.inl (h.symm.trans hn)) (fun h => Or.inr (h.symm.trans hn)))
      have hhalf : (x τ).val + 1 < L / 2 := by
        have he : (x τ).val + 1 ≠ L / 2 := fun h => hp.2 ⟨ht, Or.inl h⟩
        omega
      constructor
      · change ((x + torusStep L j) τ).val < L / 2
        rw [torusStep_time_eq, ite_eq_left hn, ZMod.val_add, ZMod.val_one'' (by omega : L ≠ 1),
          Nat.mod_eq_of_lt (by omega)]
        exact hhalf
      · intro hb
        exact hij (((normalLink_true_iff τ i).mp hb.1).trans hn.symm)
    · simpa only [bondCutInterior, bondCutBoundary, torusStep_time_eq, ite_eq_right hn] using hbase i hi
  have hne : I.axes.1 ≠ I.axes.2 := by cases I <;> decide
  intro e he
  simp only [periodicBoundaryLinks, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact hbase _ (Or.inl rfl)
  · exact hshift _ _ hne.symm (Or.inr rfl) (Or.inl rfl)
  · exact hshift _ _ hne (Or.inl rfl) (Or.inr rfl)
  · exact hbase _ (Or.inr rfl)

def bondTangentAxis (τ : Axis) (I : Face) : Axis :=
  if I.axes.1 = τ then I.axes.2 else I.axes.1

theorem bondTangentAxis_ne (τ : Axis) (I : Face) : bondTangentAxis τ I ≠ τ := by
  have hne : I.axes.1 ≠ I.axes.2 := by cases I <;> decide
  by_cases h : I.axes.1 = τ
  · rw [bondTangentAxis, ite_eq_left h, ← h]
    exact hne.symm
  · simpa only [bondTangentAxis, ite_eq_right h] using h

theorem bondSeamFace_normal_links {L : ℕ} [NeZero L] (τ : Axis) (p : Face × TorusSite L)
    (hp : bondCutBoundary τ (normalFace τ) p) :
    (τ, p.2) ∈ bondSeamLinks L τ ∧
      (τ, p.2 + torusStep L (bondTangentAxis τ p.1)) ∈ bondSeamLinks L τ := by
  have h := hp.2
  constructor
  · exact (mem_bondSeamLinks τ _).mpr ⟨(normalLink_true_iff τ τ).mpr rfl, h⟩
  · apply (mem_bondSeamLinks τ _).mpr
    refine ⟨(normalLink_true_iff τ τ).mpr rfl, ?_⟩
    simpa only [torusStep_time_eq, ite_eq_right (bondTangentAxis_ne τ p.1)] using h

theorem bondSeamFace_tangents_reflect {L : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L)
    (τ : Axis) (p : Face × TorusSite L) (hp : bondCutBoundary τ (normalFace τ) p) :
    bondReflectCell τ (normalLink τ) (bondTangentAxis τ p.1, p.2) =
      (bondTangentAxis τ p.1, p.2 + torusStep L τ) := by
  have h := bondReflectCell_boundary hL he τ (normalFace τ) p hp
  have hs : reflectSiteOn τ (-2 : ZMod L) p.2 = p.2 := by
    have hh := congrArg Prod.snd h
    simpa [bondReflectCell, hp.1] using hh
  have ht : reflectSiteOn τ (-1 : ZMod L) p.2 = p.2 + torusStep L τ := by
    rw [← reflectSiteOn_lower_add_torusStep τ (-1 : ZMod L) p.2,
      show ((-1 : ZMod L) - 1) = -2 by ring, hs]
  have hn := bondTangentAxis_ne τ p.1
  simp [bondReflectCell, normalLink, hn, ht]

/-- The seam tangent lying in the positive half of the lattice. -/
def bondSeamPositiveLink {L : ℕ} [NeZero L] (hL : 4 ≤ L) (τ : Axis) (p : Face × TorusSite L)
    (hp : bondCutBoundary τ (normalFace τ) p) :
    {e : TorusLink L // bondCutInterior τ (normalLink τ) e} := by
  let x := if (p.2 τ).val < L / 2 then p.2 else p.2 + torusStep L τ
  have hn := bondTangentAxis_ne τ p.1
  refine ⟨(bondTangentAxis τ p.1, x), ?_, fun h => hn ((normalLink_true_iff τ _).mp h.1)⟩
  change (x τ).val < L / 2
  by_cases ht : (p.2 τ).val < L / 2
  · simpa only [x, ite_eq_left ht] using ht
  · have hlast : (p.2 τ).val + 1 = L := hp.2.elim (fun h => False.elim (ht (by omega))) id
    dsimp only [x]
    rw [ite_eq_right ht, torusStep_time_eq, ite_eq_left rfl, ZMod.val_add,
      ZMod.val_one'' (by omega : L ≠ 1), hlast, Nat.mod_self]
    omega

end

end GaplessYangMills

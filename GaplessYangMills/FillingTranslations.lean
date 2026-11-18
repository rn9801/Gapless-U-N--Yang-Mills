module

public import GaplessYangMills.FiniteFilling
public import Mathlib.Algebra.Order.Group.OrderIso

/-!
# Translation-covariant finite fillings

The filling is chosen after translating the lower corner to the origin.
The normalized current is the same for all translates of the original
current, so translating the chosen squares back is covariant.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

def cellTranslation (a : Site) (I : Type*) : (Site × I) ≃ (Site × I) :=
  (Equiv.addRight a).prodCongr (Equiv.refl I)

def translateCells (a : Site) (I : Type*) : ((Site × I) →₀ ℤ) ≃+ ((Site × I) →₀ ℤ) :=
  Finsupp.domCongr (cellTranslation a I)

theorem translateCells_apply {I : Type*} (a : Site) (q : (Site × I) →₀ ℤ) (p : Site × I) :
    translateCells a I q p = q (p.1 - a, p.2) := rfl

@[simp] theorem translateCells_zero_shift {I : Type*} (q : (Site × I) →₀ ℤ) :
    translateCells 0 I q = q := by ext p; simp [translateCells_apply]

theorem translateCells_add_shift {I : Type*} (a b : Site) (q : (Site × I) →₀ ℤ) :
    translateCells b I (translateCells a I q) = translateCells (a + b) I q := by
  ext p
  simp [translateCells_apply, sub_sub, add_comm a b]

theorem support_translateCells {I : Type*} (a : Site) (q : (Site × I) →₀ ℤ) :
    (translateCells a I q).support = q.support.map (cellTranslation a I).toEmbedding := rfl

theorem chainMass_translateCells {I : Type*} (a : Site) (q : (Site × I) →₀ ℤ) :
    chainMass (translateCells a I q) = chainMass q := by
  simp [chainMass, Finsupp.sum, support_translateCells, Finset.sum_map, cellTranslation,
    translateCells_apply]

theorem boundary₁_translateCells (a : Site) (q : EdgeChain) :
    boundary₁ (translateCells a Axis q) = Finsupp.domCongr (Equiv.addRight a) (boundary₁ q) := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | single p z =>
    obtain ⟨x, i⟩ := p
    simp [translateCells, cellTranslation, boundary₁, vertex, Finsupp.linearCombination_single,
      add_right_comm x a (step i)]
    rw [← Finsupp.domCongr_apply]
    simp only [map_zsmul, map_sub]
    simp

theorem boundary₂_translateCells (a : Site) (s : SquareChain) :
    boundary₂ (translateCells a Face s) = translateCells a Axis (boundary₂ s) := by
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add s t hs ht => simp [map_add, hs, ht]
  | single p z =>
    obtain ⟨x, I⟩ := p
    cases I <;> simp [translateCells, cellTranslation, boundary₂, edge, Face.axes,
      Finsupp.linearCombination_single, add_right_comm x a]
    all_goals
      rw [← Finsupp.domCongr_apply]
      simp only [map_zsmul, map_sub, map_add]
      simp

theorem SquareBasesIn.translateCells {s : SquareChain} {o b : Site}
    (hs : SquareBasesIn s o b) (a : Site) :
    SquareBasesIn (translateCells a Face s) (o + a) (b + a) := by
  intro p hp
  rw [support_translateCells] at hp
  obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hp
  refine ⟨fun i => ?_, fun i => ?_⟩
  · change o i + a i ≤ r.1 i + a i
    exact add_le_add_left ((hs r hr).1 i) (a i)
  · change r.1 i + a i ≤ b i + a i
    exact add_le_add_left ((hs r hr).2 i) (a i)

def edgeChainLower (q : EdgeChain) : Site :=
  if h : q.support.Nonempty then fun i => q.support.inf' h (fun e => e.1 i) else 0

def edgeChainUpper (q : EdgeChain) : Site :=
  if h : q.support.Nonempty then fun i => q.support.sup' h (fun e => (e.1 + step e.2) i) else 0

theorem edgeChain_box (q : EdgeChain) (e : OrientedEdge) (he : e ∈ q.support) :
    edgeChainLower q ≤ e.1 ∧ e.1 + step e.2 ≤ edgeChainUpper q := by
  have h : q.support.Nonempty := ⟨e, he⟩
  simp only [edgeChainLower, edgeChainUpper, dite_eq_left h]
  exact ⟨fun i => Finset.inf'_le (fun e => e.1 i) he,
    fun i => Finset.le_sup' (fun e => (e.1 + step e.2) i) he⟩

theorem edgeChainLower_translateCells (q : EdgeChain) (h : q.support.Nonempty) (a : Site) :
    edgeChainLower (translateCells a Axis q) = edgeChainLower q + a := by
  have ht : (translateCells a Axis q).support.Nonempty := by
    rw [support_translateCells]
    exact h.map
  funext i
  simp only [edgeChainLower, dite_eq_left h, dite_eq_left ht, Pi.add_apply]
  change (q.support.map (cellTranslation a Axis).toEmbedding).inf' h.map (fun e => e.1 i) = _
  rw [Finset.inf'_map]
  exact (map_finset_inf' (OrderIso.addRight (a i)) h (fun e => e.1 i)).symm

theorem edgeChainUpper_translateCells (q : EdgeChain) (h : q.support.Nonempty) (a : Site) :
    edgeChainUpper (translateCells a Axis q) = edgeChainUpper q + a := by
  have ht : (translateCells a Axis q).support.Nonempty := by
    rw [support_translateCells]
    exact h.map
  funext i
  simp only [edgeChainUpper, dite_eq_left h, dite_eq_left ht, Pi.add_apply]
  change (q.support.map (cellTranslation a Axis).toEmbedding).sup' h.map
    (fun e => (e.1 + step e.2) i) = _
  rw [Finset.sup'_map]
  have he : (fun e : OrientedEdge => (e.1 + step e.2) i) ∘ (cellTranslation a Axis).toEmbedding =
      (OrderIso.addRight (a i)) ∘ (fun e : OrientedEdge => (e.1 + step e.2) i) := by
    funext e
    change ((e.1 + a) + step e.2) i = (e.1 + step e.2) i + a i
    rw [add_right_comm e.1 a]
    rfl
  rw [he]
  exact (map_finset_sup' (OrderIso.addRight (a i)) h (fun e => (e.1 + step e.2) i)).symm

/-- Choose a bounded filling of a closed chain in its coordinate box. -/
def boxedChainFilling (q : EdgeChain) : SquareChain :=
  if h : boundary₁ q = 0 then
    Classical.choose (exists_finite_filling_in_box_mass q h (edgeChainLower q) (edgeChainUpper q)
      (edgeChain_box q))
  else 0

theorem boxedChainFilling_spec (q : EdgeChain) (h : boundary₁ q = 0) :
    boundary₂ (boxedChainFilling q) = q ∧
      SquareBasesIn (boxedChainFilling q) (edgeChainLower q) (edgeChainUpper q) ∧
      chainMass (boxedChainFilling q) ≤ chainMass q * boxWidth (edgeChainLower q) (edgeChainUpper q) := by
  rw [boxedChainFilling, dite_eq_left h]
  exact Classical.choose_spec (exists_finite_filling_in_box_mass q h _ _ (edgeChain_box q))

/-- Fill the translated current in coordinates measured from its lower corner. -/
def translatedChainFilling (q : EdgeChain) : SquareChain :=
  if q = 0 then 0 else
    let o := edgeChainLower q
    translateCells o Face (boxedChainFilling (translateCells (-o) Axis q))

theorem translatedChainFilling_translateCells (q : EdgeChain) (a : Site) :
    translatedChainFilling (translateCells a Axis q) =
      translateCells a Face (translatedChainFilling q) := by
  by_cases hz : q = 0
  · simp [translatedChainFilling, hz]
  have ht : translateCells a Axis q ≠ 0 := fun h => hz ((translateCells a Axis).injective (by simpa using h))
  have hs : q.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    fun h => hz (Finsupp.support_eq_empty.mp h)
  have ho := edgeChainLower_translateCells q hs a
  have harg : translateCells (-(edgeChainLower q + a)) Axis (translateCells a Axis q) =
      translateCells (-(edgeChainLower q)) Axis q := by
    rw [translateCells_add_shift]
    congr 1
    abel
  simp only [translatedChainFilling, ite_eq_right hz, ite_eq_right ht, ho, harg, translateCells_add_shift]

theorem translatedChainFilling_spec (q : EdgeChain) (hq : boundary₁ q = 0) :
    boundary₂ (translatedChainFilling q) = q ∧
      SquareBasesIn (translatedChainFilling q) (edgeChainLower q) (edgeChainUpper q) ∧
      chainMass (translatedChainFilling q) ≤
        chainMass q * boxWidth (edgeChainLower q) (edgeChainUpper q) := by
  by_cases hz : q = 0
  · simp [hz, translatedChainFilling, SquareBasesIn]
  let o := edgeChainLower q
  let r := translateCells (-o) Axis q
  have hs : q.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr
    fun h => hz (Finsupp.support_eq_empty.mp h)
  have hr : boundary₁ r = 0 := by
    change boundary₁ (translateCells (-o) Axis q) = 0
    rw [boundary₁_translateCells, hq, map_zero]
  obtain ⟨hbd, hbox, hmass⟩ := boxedChainFilling_spec r hr
  simp only [translatedChainFilling, ite_eq_right hz]
  constructor
  · rw [boundary₂_translateCells, hbd]
    change translateCells o Axis (translateCells (-o) Axis q) = _
    rw [translateCells_add_shift, neg_add_cancel, translateCells_zero_shift]
  · have hLo : edgeChainLower r + o = edgeChainLower q := by
      change edgeChainLower (translateCells (-o) Axis q) + o = _
      rw [edgeChainLower_translateCells q hs, add_assoc, neg_add_cancel, add_zero]
    have hHi : edgeChainUpper r + o = edgeChainUpper q := by
      change edgeChainUpper (translateCells (-o) Axis q) + o = _
      rw [edgeChainUpper_translateCells q hs, add_assoc, neg_add_cancel, add_zero]
    refine ⟨by simpa only [hLo, hHi] using hbox.translateCells o, ?_⟩
    have hwidth : boxWidth (edgeChainLower r) (edgeChainUpper r) =
        boxWidth (edgeChainLower q) (edgeChainUpper q) := by
      rw [← hLo, ← hHi]
      simp [boxWidth, Pi.add_apply]
    rw [chainMass_translateCells, ← hwidth, ← chainMass_translateCells (-o) q]
    exact hmass

end

end GaplessYangMills

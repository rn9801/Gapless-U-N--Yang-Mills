module

public import GaplessYangMills.WilsonReflections

/-!
# Site reflection on the periodic lattice

On an even torus the shared planes are at times zero and half the period.
A tangential cell in either plane is fixed. Every other cell belongs to
one strict half and has a unique reflected partner in the other half.
-/

@[expose] public section

namespace GaplessYangMills

def siteCutBoundary {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L) : Prop :=
  normal p.1 = false ∧ ((p.2 τ).val = 0 ∨ (p.2 τ).val = L / 2)

def siteCutInterior {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L) : Prop :=
  (p.2 τ).val < L / 2 ∧ ¬ siteCutBoundary τ normal p

def siteCutPositive {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L) : Prop :=
  siteCutBoundary τ normal p ∨ siteCutInterior τ normal p

theorem siteCutPositive_iff {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L)
    (hL : 0 < L / 2) :
    siteCutPositive τ normal p ↔
      (p.2 τ).val < L / 2 ∨ (normal p.1 = false ∧ (p.2 τ).val = L / 2) := by
  constructor
  · rintro (⟨hn, hz | hm⟩ | ⟨hi, _⟩)
    · exact Or.inl (hz ▸ hL)
    · exact Or.inr ⟨hn, hm⟩
    · exact Or.inl hi
  · rintro (hlt | ⟨hn, hm⟩)
    · by_cases hb : siteCutBoundary τ normal p
      · exact Or.inl hb
      · exact Or.inr ⟨hlt, hb⟩
    · exact Or.inl ⟨hn, Or.inr hm⟩

def siteReflectCell {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L) :
    J × TorusSite L :=
  (p.1, reflectSiteOn τ (if normal p.1 then -1 else 0) p.2)

theorem siteReflectCell_involutive {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) :
    Function.Involutive (siteReflectCell (L := L) τ normal) := fun p =>
  Prod.ext (show p.1 = p.1 from rfl) (reflectSiteOn_involutive τ _ p.2)

private theorem val_neg_one_zmod {L : ℕ} [NeZero L] : (-1 : ZMod L).val = L - 1 := by
  cases L with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ L => exact ZMod.val_neg_one L

theorem siteReflectCell_boundary {L : ℕ} [NeZero L] (hL : 2 * (L / 2) = L)
    {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L)
    (h : siteCutBoundary τ normal p) : siteReflectCell τ normal p = p := by
  obtain ⟨hn, hb⟩ := h
  refine Prod.ext ?_ ?_
  · rfl
  · have htime : (if normal p.1 then (-1 : ZMod L) else 0) = 0 := by simp [hn]
    change reflectSiteOn τ (if normal p.1 then (-1 : ZMod L) else 0) p.2 = p.2
    rw [htime]
    funext i
    by_cases hi : i = τ
    · subst i
      simp [reflectSiteOn]
      rcases hb with hz | hh
      · rw [(ZMod.val_eq_zero _).mp hz, neg_zero]
      · have hne : p.2 τ ≠ 0 := by
          intro hzero
          rw [hzero, ZMod.val_zero] at hh
          have := NeZero.ne L
          omega
        let : NeZero (p.2 τ) := ⟨hne⟩
        apply ZMod.val_injective
        rw [ZMod.val_neg_of_ne_zero, hh]
        omega
    · simp [reflectSiteOn, hi]

theorem siteReflectCell_boundary_iff {L : ℕ} [NeZero L] (hL : 2 * (L / 2) = L)
    {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L) :
    siteCutBoundary τ normal (siteReflectCell τ normal p) ↔ siteCutBoundary τ normal p := by
  constructor
  · intro h
    have he := siteReflectCell_boundary hL τ normal _ h
    rw [siteReflectCell_involutive τ normal p] at he
    exact he ▸ h
  · intro h
    simpa only [siteReflectCell_boundary hL τ normal p h] using h

theorem siteReflectCell_interior_iff {L : ℕ} [NeZero L] (hL : 2 * (L / 2) = L)
    {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L)
    (hb : ¬ siteCutBoundary τ normal p) :
    siteCutInterior τ normal (siteReflectCell τ normal p) ↔ ¬ siteCutInterior τ normal p := by
  have hbr : ¬ siteCutBoundary τ normal (siteReflectCell τ normal p) :=
    (siteReflectCell_boundary_iff hL τ normal p).not.mpr hb
  simp only [siteCutInterior, hb, hbr, not_false_eq_true, and_true]
  have hlt := ZMod.val_lt (p.2 τ)
  cases hn : normal p.1
  · have hh : (p.2 τ).val ≠ 0 ∧ (p.2 τ).val ≠ L / 2 := by
      exact not_or.mp (fun h => hb ⟨hn, h⟩)
    let : NeZero (p.2 τ) := ⟨(ZMod.val_eq_zero _).not.mp hh.1⟩
    have he : ((siteReflectCell τ normal p).2 τ).val = L - (p.2 τ).val := by
      simpa [siteReflectCell, hn, reflectSiteOn] using ZMod.val_neg_of_ne_zero (p.2 τ)
    omega
  · have he : ((siteReflectCell τ normal p).2 τ).val = L - 1 - (p.2 τ).val := by
      have ha : (p.2 τ).val ≤ (-1 : ZMod L).val := by rw [val_neg_one_zmod]; omega
      simpa [siteReflectCell, hn, reflectSiteOn, val_neg_one_zmod] using ZMod.val_sub ha
    omega

/-- Each strict-positive cell labels its two-element reflection orbit. -/
noncomputable def siteCutCellEquiv {L : ℕ} [NeZero L] (hL : 2 * (L / 2) = L)
    {J : Type*} (τ : Axis) (normal : J → Bool) :
    ({p // siteCutBoundary (L := L) τ normal p} ⊕
      ({p // siteCutInterior (L := L) τ normal p} ⊕ {p // siteCutInterior (L := L) τ normal p})) ≃
        J × TorusSite L := by
  classical
  let r := siteReflectCell (L := L) τ normal
  let B := siteCutBoundary (L := L) τ normal
  let P := siteCutInterior (L := L) τ normal
  refine
    { toFun := fun
        | .inl p => p.val
        | .inr (.inl p) => p.val
        | .inr (.inr p) => r p.val
      invFun := fun p => if hb : B p then .inl ⟨p, hb⟩ else
        if hp : P p then .inr (.inl ⟨p, hp⟩) else
          .inr (.inr ⟨r p, (siteReflectCell_interior_iff hL τ normal p hb).mpr hp⟩)
      left_inv := ?_
      right_inv := ?_ }
  · rintro (p | p | p)
    · have hb : B p.val := p.property
      simp only [dite_eq_left hb]
    · have hb : ¬ B p.val := p.property.2
      have hp : P p.val := p.property
      simp only [dite_eq_right hb, dite_eq_left hp]
    · have hb : ¬ B (r p.val) :=
        (siteReflectCell_boundary_iff hL τ normal p.val).not.mpr p.property.2
      have hp : ¬ P (r p.val) := fun h =>
        (siteReflectCell_interior_iff hL τ normal p.val p.property.2).mp h p.property
      simp only [dite_eq_right hb, dite_eq_right hp]
      exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext (siteReflectCell_involutive τ normal p.val))
  · intro p
    by_cases hb : B p
    · simp only [dite_eq_left hb]
    · by_cases hp : P p
      · simp only [dite_eq_right hb, dite_eq_left hp]
      · simp only [dite_eq_right hb, dite_eq_right hp]
        exact siteReflectCell_involutive τ normal p

def normalLink (τ : Axis) (i : Axis) : Bool := decide (i = τ)

def normalFace (τ : Axis) (I : Face) : Bool := decide (I.axes.1 = τ ∨ I.axes.2 = τ)

theorem reflectLinkIndex_site {L : ℕ} (τ : Axis) (e : TorusLink L) :
    reflectLinkIndex τ (0 : ZMod L) e = siteReflectCell τ (normalLink τ) e := by
  by_cases h : e.1 = τ <;> simp [normalLink, reflectLinkIndex, siteReflectCell, h]

theorem reflectFaceIndex_site {L : ℕ} (τ : Axis) (p : Face × TorusSite L) :
    (p.1, reflectedFaceBase τ (0 : ZMod L) p.1 p.2) = siteReflectCell τ (normalFace τ) p := by
  by_cases h : p.1.axes.1 = τ ∨ p.1.axes.2 = τ <;>
    simp [normalFace, reflectedFaceBase, siteReflectCell, h]

end GaplessYangMills

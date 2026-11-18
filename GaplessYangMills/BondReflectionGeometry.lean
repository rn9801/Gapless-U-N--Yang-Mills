module

public import GaplessYangMills.SiteReflectionGeometry

/-!
# Bond reflection on the periodic lattice

Reflection through time `-1/2` fixes the two layers of crossing normal
links as unoriented links. All remaining cells come in reflected pairs.
-/

@[expose] public section

namespace GaplessYangMills

def bondCutBoundary {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L) : Prop :=
  normal p.1 = true ∧ ((p.2 τ).val + 1 = L / 2 ∨ (p.2 τ).val + 1 = L)

def bondCutInterior {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L) : Prop :=
  (p.2 τ).val < L / 2 ∧ ¬ bondCutBoundary τ normal p

def bondReflectCell {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L) :
    J × TorusSite L :=
  (p.1, reflectSiteOn τ (if normal p.1 then -2 else -1) p.2)

theorem bondReflectCell_involutive {L : ℕ} {J : Type*} (τ : Axis) (normal : J → Bool) :
    Function.Involutive (bondReflectCell (L := L) τ normal) := fun p =>
  Prod.ext (show p.1 = p.1 from rfl) (reflectSiteOn_involutive τ _ p.2)

private theorem val_neg_two_zmod {L : ℕ} [NeZero L] (hL : 4 ≤ L) :
    (-2 : ZMod L).val = L - 2 := by
  have h : (1 : ZMod L).val ≤ (-1 : ZMod L).val := by
    rw [ZMod.val_one'' (by omega : L ≠ 1), val_neg_one_zmod]
    omega
  rw [show (-2 : ZMod L) = (-1 : ZMod L) - 1 by ring, ZMod.val_sub h,
    val_neg_one_zmod, ZMod.val_one'' (by omega : L ≠ 1)]
  omega

theorem bondReflectCell_boundary {L : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L)
    {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L)
    (h : bondCutBoundary τ normal p) : bondReflectCell τ normal p = p := by
  obtain ⟨hn, hb⟩ := h
  refine Prod.ext ?_ ?_
  · rfl
  · change reflectSiteOn τ (if normal p.1 then (-2 : ZMod L) else -1) p.2 = p.2
    simp only [hn, ite_true]
    funext i
    by_cases hi : i = τ
    · subst i
      simp [reflectSiteOn]
      rcases hb with hm | hlast
      · have hv : (p.2 τ).val ≤ (-2 : ZMod L).val := by rw [val_neg_two_zmod hL]; omega
        apply ZMod.val_injective
        rw [ZMod.val_sub hv, val_neg_two_zmod hL]
        omega
      · have hv : p.2 τ = (-1 : ZMod L) := by
          apply ZMod.val_injective
          rw [val_neg_one_zmod]
          omega
        rw [hv]
        ring
    · simp [reflectSiteOn, hi]

theorem bondReflectCell_boundary_iff {L : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L)
    {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L) :
    bondCutBoundary τ normal (bondReflectCell τ normal p) ↔ bondCutBoundary τ normal p := by
  constructor
  · intro h
    have hb := bondReflectCell_boundary hL he τ normal _ h
    rw [bondReflectCell_involutive τ normal p] at hb
    exact hb ▸ h
  · intro h
    simpa only [bondReflectCell_boundary hL he τ normal p h] using h

theorem bondReflectCell_interior_iff {L : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L)
    {J : Type*} (τ : Axis) (normal : J → Bool) (p : J × TorusSite L)
    (hb : ¬ bondCutBoundary τ normal p) :
    bondCutInterior τ normal (bondReflectCell τ normal p) ↔ ¬ bondCutInterior τ normal p := by
  have hbr := (bondReflectCell_boundary_iff hL he τ normal p).not.mpr hb
  simp only [bondCutInterior, hb, hbr, not_false_eq_true, and_true]
  have hlt := ZMod.val_lt (p.2 τ)
  cases hn : normal p.1
  · have hv : (p.2 τ).val ≤ (-1 : ZMod L).val := by rw [val_neg_one_zmod]; omega
    have hc : ((bondReflectCell τ normal p).2 τ).val = L - 1 - (p.2 τ).val := by
      simpa [bondReflectCell, hn, reflectSiteOn, val_neg_one_zmod] using ZMod.val_sub hv
    omega
  · have hh : (p.2 τ).val + 1 ≠ L / 2 ∧ (p.2 τ).val + 1 ≠ L :=
      not_or.mp (fun h => hb ⟨hn, h⟩)
    have hv : (p.2 τ).val ≤ (-2 : ZMod L).val := by rw [val_neg_two_zmod hL]; omega
    have hc : ((bondReflectCell τ normal p).2 τ).val = L - 2 - (p.2 τ).val := by
      simpa [bondReflectCell, hn, reflectSiteOn, val_neg_two_zmod hL] using ZMod.val_sub hv
    omega

noncomputable def bondCutCellEquiv {L : ℕ} [NeZero L] (hL : 4 ≤ L) (he : 2 * (L / 2) = L)
    {J : Type*} (τ : Axis) (normal : J → Bool) :
    ({p // bondCutBoundary (L := L) τ normal p} ⊕
      ({p // bondCutInterior (L := L) τ normal p} ⊕ {p // bondCutInterior (L := L) τ normal p})) ≃
        J × TorusSite L :=
  reflectionOrbitEquiv _ (bondReflectCell_involutive τ normal) _ _ (fun _ h => h.2)
    (bondReflectCell_boundary_iff hL he τ normal) (bondReflectCell_interior_iff hL he τ normal)

theorem reflectLinkIndex_bond {L : ℕ} (τ : Axis) (e : TorusLink L) :
    reflectLinkIndex τ (-1 : ZMod L) e = bondReflectCell τ (normalLink τ) e := by
  have h : ((-1 : ZMod L) - 1) = -2 := by ring
  by_cases hi : e.1 = τ <;> simp [normalLink, reflectLinkIndex, bondReflectCell, hi, h]

theorem reflectFaceIndex_bond {L : ℕ} (τ : Axis) (p : Face × TorusSite L) :
    (p.1, reflectedFaceBase τ (-1 : ZMod L) p.1 p.2) = bondReflectCell τ (normalFace τ) p := by
  have h : ((-1 : ZMod L) - 1) = -2 := by ring
  by_cases hi : p.1.axes.1 = τ ∨ p.1.axes.2 = τ <;>
    simp [normalFace, reflectedFaceBase, bondReflectCell, hi, h]

end GaplessYangMills

module

public import GaplessYangMills.FiniteFilling
public import GaplessYangMills.Flux

/-!
# Integer cubical duality

Reflecting the indexing lattice turns primal forward differences into the
incoming-minus-outgoing convention for dual boundaries.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

def primalCurrent (q : EdgeChain) : ThreeForm ℤ
  | .yzw, x => q (-x, 0)
  | .xzw, x => -q (-x, 1)
  | .xyw, x => q (-x, 2)
  | .xyz, x => -q (-x, 3)

def primalFilling (s : SquareChain) : TwoForm ℤ
  | .zw, x => -s (-x, .xy)
  | .yw, x => s (-x, .xz)
  | .yz, x => -s (-x, .xw)
  | .xw, x => -s (-x, .yz)
  | .xz, x => s (-x, .yw)
  | .xy, x => -s (-x, .zw)

private theorem site_eq_add_iff (a b v : Site) : b + v = a ↔ a + -v = b := by
  rw [← sub_eq_add_neg, sub_eq_iff_eq_add, eq_comm]

theorem boundary₁_primalCurrent (q : EdgeChain) (x : Site) :
    boundary₁ q (-x) = d₃ (primalCurrent q) x := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [primalCurrent, d₃, diff]
  | add q r hq hr =>
    simp only [map_add, Finsupp.add_apply, hq, hr]
    simp [primalCurrent, d₃, diff, Finsupp.add_apply, Pi.sub_apply, Pi.add_apply]
    abel
  | single e a =>
    obtain ⟨y, i⟩ := e
    fin_cases i <;>
      simp [boundary₁, vertex, Finsupp.linearCombination_single, primalCurrent, d₃, diff,
        Finsupp.single_apply, Prod.mk.injEq, eq_comm (a := y), site_eq_add_iff (b := y)] <;> simp only [add_comm (-x)] <;> split_ifs <;> ring

set_option maxHeartbeats 800000 in
theorem boundary₂_primalFilling (s : SquareChain) :
    primalCurrent (boundary₂ s) = d₂ (primalFilling s) := by
  classical
  induction s using Finsupp.induction_linear with
  | zero =>
    funext c x
    cases c <;> simp [primalCurrent, primalFilling, d₂, diff]
  | add s t hs ht =>
    funext c x
    have ha (u v : EdgeChain) : primalCurrent (u + v) = primalCurrent u + primalCurrent v := by
      funext c x
      cases c <;> simp [primalCurrent] <;> abel
    have hb : primalFilling (s + t) = primalFilling s + primalFilling t := by
      funext c x
      cases c <;> simp [primalFilling] <;> abel
    rw [map_add, ha, hs, ht, hb, d₂_add]
  | single e a =>
    obtain ⟨y, I⟩ := e
    funext c x
    cases I <;> cases c <;>
      simp [boundary₂, edge, Finsupp.linearCombination_single, Face.axes, primalCurrent,
        primalFilling, d₂, diff, Finsupp.single_apply, Prod.mk.injEq,
        eq_comm (a := y), site_eq_add_iff (b := y)] <;> simp only [add_comm (-x)] <;> split_ifs <;> ring

/-- A closed integer three-form supported on finitely many cubes is exact. -/
theorem exists_cochain_filling (q : ThreeForm ℤ) (hq : d₃ q = 0)
    (hfinite : ∀ c, (Function.support (q c)).Finite) :
    ∃ s : SquareChain, d₂ (primalFilling s) = q := by
  let current : OrientedEdge → ℤ := fun (x, i) =>
    if i = 0 then q .yzw (-x)
    else if i = 1 then -q .xzw (-x)
    else if i = 2 then q .xyw (-x)
    else -q .xyz (-x)
  have hs : (Function.support current).Finite := by
    apply (((hfinite .yzw).image (fun x : Site => (-x, (0 : Axis)))).union
      (((hfinite .xzw).image (fun x : Site => (-x, (1 : Axis)))).union
      (((hfinite .xyw).image (fun x : Site => (-x, (2 : Axis)))).union
       ((hfinite .xyz).image (fun x : Site => (-x, (3 : Axis))))))).subset
    rintro ⟨x, i⟩ hi
    fin_cases i
    · exact Or.inl ⟨-x, by simpa [current] using hi, by simp⟩
    · exact Or.inr (Or.inl ⟨-x, by simpa [current] using hi, by simp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨-x, by simpa [current] using hi, by simp⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨-x, by simpa [current] using hi, by simp⟩))
  let Q := Finsupp.ofSupportFinite current hs
  have hQ : primalCurrent Q = q := by
    funext c x
    cases c <;> simp [primalCurrent, Q, current, Finsupp.ofSupportFinite_coe]
  have hz : boundary₁ Q = 0 := by
    ext x
    simpa [hQ, hq] using boundary₁_primalCurrent Q (-x)
  obtain ⟨s, hs⟩ := exists_finite_filling Q hz
  exact ⟨s, (boundary₂_primalFilling s).symm.trans (hs ▸ hQ)⟩


theorem primalFilling_finite (s : SquareChain) (I : Face) :
    (Function.support (primalFilling s I)).Finite := by
  have hs (J : Face) : (Function.support fun x : Site => s (-x, J)).Finite := by
    have hinj : Function.Injective (fun x : Site => (-x, J)) := by
      intro x y h
      exact neg_injective (congrArg Prod.fst h)
    apply (s.support.finite_toSet.preimage hinj.injOn).subset
    intro x hx
    exact Finsupp.mem_support_iff.mpr hx
  cases I
  · simpa [primalFilling, Function.support] using hs .zw
  · exact hs .yw
  · simpa [primalFilling, Function.support] using hs .yz
  · simpa [primalFilling, Function.support] using hs .xw
  · exact hs .xz
  · simpa [primalFilling, Function.support] using hs .xy

/-- A determinant lift with a finite defect can be repaired by a finite integer
two-form. -/
theorem exists_finite_flux_repair (a : TwoForm ℝ)
    (h : ∀ c x, Circle.exp (d₂ a c x) = 1)
    (hfinite : ∀ c, (Function.support (defect a c)).Finite) :
    ∃ Y : TwoForm ℤ, (∀ I, (Function.support (Y I)).Finite) ∧
      d₂ Y = defect a ∧ d₂ (repairFlux (fun _ => Y) a) = 0 := by
  obtain ⟨s, hs⟩ := exists_cochain_filling (defect a) (defect_closed a h) hfinite
  exact ⟨primalFilling s, primalFilling_finite s, hs, repairFlux_closed _ a h hs⟩

end

end GaplessYangMills

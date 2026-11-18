module

public import GaplessYangMills.Lattice
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Bad-face witnesses for marked dual edges

A marked dual edge is indexed by its primal cube. The joint bad-face estimate
implies equation (1) by a union bound over witness assignments.
-/

public section

namespace GaplessYangMills

open MeasureTheory
open scoped BigOperators ENNReal

instance faceFintype : Fintype Face where
  elems := {.xy, .xz, .xw, .yz, .yw, .zw}
  complete I := by cases I <;> simp

abbrev Plaquette := Face × Site
abbrev DualEdge := Cube × Site

@[expose] def cubeFaceList : DualEdge → List Plaquette
  | (.xyz, x) => [(.yz, x), (.yz, x + step 0), (.xz, x), (.xz, x + step 1),
      (.xy, x), (.xy, x + step 2)]
  | (.xyw, x) => [(.yw, x), (.yw, x + step 0), (.xw, x), (.xw, x + step 1),
      (.xy, x), (.xy, x + step 3)]
  | (.xzw, x) => [(.zw, x), (.zw, x + step 0), (.xw, x), (.xw, x + step 2),
      (.xz, x), (.xz, x + step 3)]
  | (.yzw, x) => [(.zw, x), (.zw, x + step 1), (.yw, x), (.yw, x + step 2),
      (.yz, x), (.yz, x + step 3)]

private def faceCubeList : Plaquette → List DualEdge
  | (.xy, x) => [(.xyz, x), (.xyz, x - step 2), (.xyw, x), (.xyw, x - step 3)]
  | (.xz, x) => [(.xyz, x), (.xyz, x - step 1), (.xzw, x), (.xzw, x - step 3)]
  | (.xw, x) => [(.xyw, x), (.xyw, x - step 1), (.xzw, x), (.xzw, x - step 2)]
  | (.yz, x) => [(.xyz, x), (.xyz, x - step 0), (.yzw, x), (.yzw, x - step 3)]
  | (.yw, x) => [(.xyw, x), (.xyw, x - step 0), (.yzw, x), (.yzw, x - step 2)]
  | (.zw, x) => [(.xzw, x), (.xzw, x - step 0), (.yzw, x), (.yzw, x - step 1)]

/-- The six primal faces of the cube corresponding to a dual edge. -/
noncomputable def cubeFaces (e : DualEdge) : Finset Plaquette := by
  classical
  exact (cubeFaceList e).toFinset

theorem mem_cubeFaces_list {p : Plaquette} (e : DualEdge) :
    p ∈ cubeFaces e ↔ p ∈ cubeFaceList e := by
  classical
  simp [cubeFaces]

/-- The four cubes incident to a primal face. -/
noncomputable def faceCubes (p : Plaquette) : Finset DualEdge := by
  classical
  exact (faceCubeList p).toFinset

theorem mem_cubeFaces_iff {p : Plaquette} {e : DualEdge} :
    p ∈ cubeFaces e ↔ e ∈ faceCubes p := by
  obtain ⟨I, p⟩ := p
  obtain ⟨c, x⟩ := e
  cases I <;> cases c <;>
    simp [cubeFaces, faceCubes, cubeFaceList, faceCubeList, eq_comm (a := p), eq_sub_iff_add_eq]

private theorem cubeFaces_card_le (e : DualEdge) : (cubeFaces e).card ≤ 6 := by
  obtain ⟨c, x⟩ := e
  exact (List.toFinset_card_le _).trans (by cases c <;> simp [cubeFaceList])

private theorem faceCubes_card_le (p : Plaquette) : (faceCubes p).card ≤ 4 := by
  obtain ⟨I, x⟩ := p
  exact (List.toFinset_card_le _).trans (by cases I <;> simp [faceCubeList])

@[expose] def allBad {P Ω : Type*} (bad : P → Set Ω) (S : Finset P) : Set Ω :=
  {ω | ∀ p ∈ S, ω ∈ bad p}

@[expose] def allMarked {Ω : Type*} (bad : Plaquette → Set Ω) (S : Finset DualEdge) : Set Ω :=
  {ω | ∀ e ∈ S, ∃ p ∈ cubeFaces e, ω ∈ bad p}

/-- A joint bound with exponent `a` per bad face gives the joint marked-edge
bound with at most six choices per edge and at most four uses of each face. -/
theorem measure_allMarked_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (bad : Plaquette → Set Ω) (a : ℝ) (ha : 0 ≤ a)
    (hbad : ∀ P, μ (allBad bad P) ≤ ENNReal.ofReal (Real.exp (-a * P.card)))
    (S : Finset DualEdge) :
    μ (allMarked bad S) ≤ ENNReal.ofReal ((6 * Real.exp (-(a / 4))) ^ S.card) := by
  classical
  let A := Fintype.piFinset (fun e : S => cubeFaces e.val)
  let images (f : S → Plaquette) := S.attach.image f
  have hcover : allMarked bad S ⊆ ⋃ f ∈ A, allBad bad (images f) := by
    intro ω hω
    have hw (e : S) : ∃ p ∈ cubeFaces e.val, ω ∈ bad p := hω e.val e.property
    choose f hf hf' using hw
    apply Set.mem_iUnion.mpr
    refine ⟨f, Set.mem_iUnion.mpr ⟨Fintype.mem_piFinset.mpr hf, ?_⟩⟩
    intro p hp
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hp
    exact hf' e
  have hcard : A.card ≤ 6 ^ S.card := by
    rw [Fintype.card_piFinset]
    calc
      ∏ e : S, (cubeFaces e.val).card ≤ ∏ _e : S, (6 : ℕ) :=
        Finset.prod_le_prod fun e _ => cubeFaces_card_le e.val
      _ = _ := by simp
  have hterm (f : S → Plaquette) (hf : f ∈ A) :
      μ (allBad bad (images f)) ≤ ENNReal.ofReal (Real.exp (-(a / 4) * S.card)) := by
    apply (hbad (images f)).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hc : S.card ≤ 4 * (images f).card := by
      rw [← Finset.card_attach (s := S)]
      apply Finset.card_le_mul_card_image _ 4
      intro p _
      refine (Finset.card_le_card_of_injOn (fun e : S => e.val) ?_ ?_).trans (faceCubes_card_le p)
      · intro e he
        have he' := (Finset.mem_filter.mp he).2
        exact mem_cubeFaces_iff.mp (he' ▸ Fintype.mem_piFinset.mp hf e)
      · exact Subtype.val_injective.injOn
    have hc' : (S.card : ℝ) ≤ 4 * ((images f).card : ℝ) := by exact_mod_cast hc
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hc')]
  calc
    μ (allMarked bad S) ≤ μ (⋃ f ∈ A, allBad bad (images f)) := measure_mono hcover
    _ ≤ ∑ f ∈ A, μ (allBad bad (images f)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _f ∈ A, ENNReal.ofReal (Real.exp (-(a / 4) * S.card)) := Finset.sum_le_sum hterm
    _ ≤ ((6 : ℝ≥0∞) ^ S.card) * ENNReal.ofReal (Real.exp (-(a / 4) * S.card)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_left (by exact_mod_cast hcard) _
    _ = _ := by
      have he : Real.exp (-(a / 4) * (S.card : ℝ)) =
          Real.exp (-(a / 4)) ^ S.card := by rw [← Real.exp_nat_mul, mul_comm]
      rw [he]
      rw [mul_pow, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (Real.exp_nonneg _)]
      simp

end GaplessYangMills

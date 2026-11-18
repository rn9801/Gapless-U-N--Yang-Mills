module

public import GaplessYangMills.LocalWilsonGeometry
public import GaplessYangMills.Ward

/-!
# Evaluating the Ward response on one link

A unit test at one positive link has exterior derivative supported on
the two faces of each adjacent orientation. The resulting convolution
is the right derivative in displacement coordinates.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

def unitLinkTest (i : Axis) : OneForm ℝ :=
  fun j y => if j = i ∧ y = 0 then 1 else 0

theorem unitLinkTest_support (i : Axis) : ∀ e ∉ ({(i, 0)} : Finset InfiniteLink), unitLinkTest i e.1 e.2 = 0 := by
  rintro ⟨j, y⟩ h
  have hn : ¬(j = i ∧ y = 0) := fun hn => h (Finset.mem_singleton.mpr (Prod.ext hn.1 hn.2))
  exact ite_eq_right hn

private def testFaceSites (i : Axis) (I : Face) : Finset Site :=
  if i = I.axes.1 then {0, -step I.axes.2}
  else if i = I.axes.2 then {0, -step I.axes.1}
  else ∅

private theorem mem_affectedPlaquettes_unitLink (i : Axis) (I : Face) (x : Site) :
    (I, x) ∈ affectedPlaquettes {(i, 0)} ↔ x ∈ testFaceSites i I := by
  have hne : I.axes.1 ≠ I.axes.2 := by cases I <;> decide
  have h₀ (j : Axis) : (0 : Site) = x + step j ↔ x = -step j := by
    constructor
    · intro h
      exact eq_neg_of_add_eq_zero_left h.symm
    · intro h
      rw [h, neg_add_cancel]
  rw [mem_affectedPlaquettes_iff]
  simp only [Finset.mem_singleton, exists_eq_left, boundaryLinks, Finset.mem_insert, Prod.mk.injEq, h₀]
  by_cases h1 : i = I.axes.1
  · simp [testFaceSites, h1, hne, eq_comm (a := (0 : Site))]
  · by_cases h2 : i = I.axes.2
    · simp [testFaceSites, h2, Ne.symm hne, eq_comm (a := (0 : Site)), or_comm]
    · simp [testFaceSites, h1, h2]

private theorem sum_affectedPlaquettes_unitLink (i : Axis) (f : Plaquette → ℝ) :
    (∑ p ∈ affectedPlaquettes {(i, 0)}, f p) =
      ∑ I : Face, ∑ y ∈ testFaceSites i I, f (I, y) := by
  let C (I : Face) := (testFaceSites i I).image (Prod.mk I)
  have h : affectedPlaquettes {(i, 0)} = Finset.univ.biUnion C := by
    ext p
    rcases p with ⟨I, y⟩
    constructor
    · intro hp
      exact Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ _, Finset.mem_image_of_mem _
        ((mem_affectedPlaquettes_unitLink i I y).mp hp)⟩
    · intro hp
      obtain ⟨J, _, hJ⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hJ
      have he : J = I ∧ z = y := Prod.mk.inj heq
      obtain ⟨rfl, rfl⟩ := he
      exact (mem_affectedPlaquettes_unitLink i J z).mpr hz
  have hd : (↑(Finset.univ : Finset Face) : Set Face).PairwiseDisjoint C := by
    intro I _ J _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hq
    exact hne ((Prod.mk.inj hb).1.symm)
  rw [h, Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro I _
  exact Finset.sum_image (fun _ _ _ _ he => (Prod.mk.inj he).2)

private theorem step_ne_zero (i : Axis) : step i ≠ 0 := by
  intro h
  have h' := congrFun h i
  simp only [step_same, Pi.zero_apply] at h'
  exact Int.one_ne_zero h'

set_option maxHeartbeats 500000 in
theorem rightDerivative_eq_unitLink_test (K : Kernel) (I : Face) (i : Axis) (x : Site) :
    rightDerivative K I i x =
      ∑ p ∈ affectedPlaquettes {(i, 0)}, d₁ (unitLinkTest i) p.1 p.2 * K I p.1 (x - p.2) := by
  rw [sum_affectedPlaquettes_unitLink]
  have hU : (Finset.univ : Finset Face) = {.xy, .xz, .xw, .yz, .yw, .zw} := rfl
  rw [hU]
  fin_cases i <;>
    simp [rightDerivative, testFaceSites, unitLinkTest, Face.axes, d₁, diff, step_ne_zero, sub_neg_eq_add] <;> ring

theorem unitLink_test_identityKernel (I : Face) (i : Axis) (x : Site) :
    (∑ p ∈ affectedPlaquettes {(i, 0)}, d₁ (unitLinkTest i) p.1 p.2 * identityKernel I p.1 (x - p.2)) =
      d₁ (unitLinkTest i) I x := by
  rw [Finset.sum_eq_single (I, x)]
  · simp [identityKernel]
  · intro p _ hp
    have hn : ¬(I = p.1 ∧ x - p.2 = 0) := fun hh =>
      hp ((Prod.ext hh.1 (sub_eq_zero.mp hh.2)).symm)
    simp [identityKernel, hn]
  · intro h
    rw [d₁_eq_zero_of_notMem_affectedPlaquettes (unitLinkTest i) (unitLinkTest_support i) h, zero_mul]

end

end GaplessYangMills

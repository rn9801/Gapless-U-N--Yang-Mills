module

public import GaplessYangMills.CutResponse
public import GaplessYangMills.Decay
public import GaplessYangMills.Ward

/-!
# Response to changing one cut

Changes of the defect current inside one marked component can only
change repaired fillings in the coordinate box of that component.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory SimpleGraph
open scoped ENat Topology

noncomputable section

private theorem edgeBoxContains_mono {S T : Finset OrientedEdge} (h : S ⊆ T) {x : Site}
    (hx : edgeBoxContains S x) : edgeBoxContains T x := by
  have hs : edgeVertices S ⊆ edgeVertices T :=
    Finset.union_subset_union (Finset.image_mono _ h) (Finset.image_mono _ h)
  intro i
  obtain ⟨⟨a, ha, hax⟩, b, hb, hxb⟩ := hx i
  exact ⟨⟨a, hs ha, hax⟩, b, hs hb, hxb⟩

theorem finite_edgeBoxContains (S : Finset OrientedEdge) :
    {x : Site | edgeBoxContains S (-x)}.Finite := by
  let R := (edgeVertices S).sup fun u => Finset.univ.sup fun i : Axis => (u i).natAbs
  let A := Fintype.piFinset fun _ : Axis => Finset.Icc (-(R : ℤ)) R
  have hb (u : Site) (hu : u ∈ edgeVertices S) (i : Axis) : (u i).natAbs ≤ R :=
    (Finset.le_sup (f := fun j : Axis => (u j).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun v : Site => Finset.univ.sup fun j : Axis => (v j).natAbs) hu)
  refine A.finite_toSet.subset fun x hx => Fintype.mem_piFinset.mpr fun i => ?_
  obtain ⟨⟨a, ha, hax⟩, b, hb', hxb⟩ := hx i
  have h₁ := hb a ha i
  have h₂ := hb b hb' i
  simp only [Pi.neg_apply] at hax hxb
  apply Finset.mem_Icc.mpr
  omega

private theorem markedComponent_closed_under_adj {M : Set OrientedEdge} {e f a : OrientedEdge}
    (he : e ∈ markedComponent dualEdgeGraph M a) (hf : f ∈ M) (h : dualEdgeGraph.Adj e f) :
    f ∈ markedComponent dualEdgeGraph M a := by
  obtain ⟨p, hp⟩ := he
  refine ⟨p.append h.toWalk, fun g hg => ?_⟩
  rcases (Walk.mem_support_append_iff _ _).mp hg with h₁ | h₂
  · exact hp g h₁
  · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at h₂
    rcases h₂ with rfl | rfl
    · exact hp _ p.end_mem_support
    · exact hf

private theorem inspection_disjoint_of_not_subset {M : Set OrientedEdge} {a : OrientedEdge}
    (hC : (markedComponent dualEdgeGraph M a).Finite)
    (S : Finset OrientedEdge) (hS : (↑S : Set OrientedEdge) ⊆ M)
    (hconn : ∃ e ∈ S, ∀ f ∈ S, ∃ w : dualEdgeGraph.Walk e f, ∀ g ∈ w.support, g ∈ S)
    (houtside : ¬S ⊆ hC.toFinset) :
    ∀ e ∈ componentInspectionEdges S, e ∉ markedComponent dualEdgeGraph M a := by
  have hdisj (e : OrientedEdge) (he : e ∈ S) : e ∉ markedComponent dualEdgeGraph M a := by
    intro hE
    obtain ⟨r, _, hR⟩ := hconn
    have hc (f : OrientedEdge) (hf : f ∈ S) : f ∈ markedComponent dualEdgeGraph M r := by
      obtain ⟨w, hw⟩ := hR f hf
      exact ⟨w, fun g hg => hS (hw g hg)⟩
    have heq : markedComponent dualEdgeGraph M r = markedComponent dualEdgeGraph M a :=
      (component_eq_of_mem _ (hc e he)).trans (component_eq_of_mem _ hE).symm
    exact houtside (fun g hg => hC.mem_toFinset.mpr (heq ▸ hc g hg))
  intro e he
  rcases Finset.mem_union.mp he with hs | hs
  · exact hdisj e hs
  · obtain ⟨f, hf, he'⟩ := Finset.mem_biUnion.mp hs
    intro hE
    exact hdisj f hf (markedComponent_closed_under_adj hE (hS hf) ((mem_edgeNeighborFinset f e).mp he').symm)

private theorem certifiedFillValue_eq_outside_component {q r : ThreeForm ℤ}
    (hq : d₃ q = 0) (hr : d₃ r = 0)
    {M : Set OrientedEdge} (hqM : Function.support (dualCurrent q) ⊆ M)
    (hrM : Function.support (dualCurrent r) ⊆ M) {a : OrientedEdge}
    (hC : (markedComponent dualEdgeGraph M a).Finite)
    (heq : ∀ e ∉ markedComponent dualEdgeGraph M a, dualCurrent q e = dualCurrent r e)
    (S : Finset OrientedEdge) (I : Face) (x : Site)
    (hx : ¬ S ⊆ hC.toFinset ∨ ¬edgeBoxContains hC.toFinset (-x)) :
    certifiedFillValue (dualCurrent q) S I x = certifiedFillValue (dualCurrent r) S I x := by
  have hc (v : ThreeForm ℤ) (hv : d₃ v = 0) (hvM : Function.support (dualCurrent v) ⊆ M)
      (h : certifiedFillValue (dualCurrent v) S I x ≠ 0) :
      ∀ e ∈ componentInspectionEdges S, e ∉ markedComponent dualEdgeGraph M a := by
    have hdiv (y : Site) : currentDivergence (dualCurrent v) y = 0 := by
      rw [currentDivergence_dualCurrent, hv, Pi.zero_apply]
    obtain ⟨hm, hbox, hconn⟩ := certifiedFillValue_ne_zero_box _ hdiv S I x h
    have hnot : ¬S ⊆ hC.toFinset := hx.elim id (fun ho hs => ho (edgeBoxContains_mono hs hbox))
    exact inspection_disjoint_of_not_subset hC S (hm.trans hvM) hconn hnot
  by_cases hq₀ : certifiedFillValue (dualCurrent q) S I x = 0
  · by_cases hr₀ : certifiedFillValue (dualCurrent r) S I x = 0
    · rw [hq₀, hr₀]
    · exact certifiedFillValue_congr_on _ _ S (fun e he => heq e (hc r hr hrM hr₀ e he)) I x
  · exact certifiedFillValue_congr_on _ _ S (fun e he => heq e (hc q hq hqM hq₀ e he)) I x

theorem fillDefect_eq_outside_markedComponent_box (q r : ThreeForm ℤ)
    (hq : d₃ q = 0) (hr : d₃ r = 0)
    (M : Set OrientedEdge) (hqM : Function.support (dualCurrent q) ⊆ M)
    (hrM : Function.support (dualCurrent r) ⊆ M) (a : OrientedEdge)
    (hC : (markedComponent dualEdgeGraph M a).Finite)
    (heq : ∀ e ∉ markedComponent dualEdgeGraph M a, dualCurrent q e = dualCurrent r e)
    (I : Face) (x : Site) (hx : ¬edgeBoxContains hC.toFinset (-x)) :
    fillDefect q I x = fillDefect r I x := by
  rw [fillDefect_eq_finsum_certified, fillDefect_eq_finsum_certified]
  exact finsum_congr fun S => certifiedFillValue_eq_outside_component hq hr hqM hrM hC heq S I x (Or.inr hx)

private theorem abs_fillDefectApprox_change_le (q r : ThreeForm ℤ)
    (hq : d₃ q = 0) (hr : d₃ r = 0)
    {M : Set OrientedEdge} (hqM : Function.support (dualCurrent q) ⊆ M)
    (hrM : Function.support (dualCurrent r) ⊆ M) {a : OrientedEdge}
    (hC : (markedComponent dualEdgeGraph M a).Finite)
    (heq : ∀ e ∉ markedComponent dualEdgeGraph M a, dualCurrent q e = dualCurrent r e)
    (B : ℕ) (hqB : ∀ e, (dualCurrent q e).natAbs ≤ B) (hrB : ∀ e, (dualCurrent r e).natAbs ≤ B)
    (R : ℕ) (I : Face) (x : Site) :
    |(fillDefectApprox q R I x : ℝ) - (fillDefectApprox r R I x : ℝ)| ≤
      (2 : ℝ) ^ hC.toFinset.card * (40 * (B : ℝ) * ((hC.toFinset.card : ℝ) + 1) ^ 2) := by
  classical
  let C := hC.toFinset
  let A := boundedBoxCover (-x) R
  let D := A.filter (· ⊆ C)
  let f (S : Finset OrientedEdge) := (certifiedFillValue (dualCurrent q) S I x : ℝ) -
    (certifiedFillValue (dualCurrent r) S I x : ℝ)
  have hsum : (fillDefectApprox q R I x : ℝ) - (fillDefectApprox r R I x : ℝ) = ∑ S ∈ D, f S := by
    unfold fillDefectApprox
    push_cast
    rw [← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hn
    have hnot : ¬S ⊆ C := fun hs => hn (Finset.mem_filter.mpr ⟨hS, hs⟩)
    exact sub_eq_zero.mpr (congrArg (fun z : ℤ => (z : ℝ))
      (certifiedFillValue_eq_outside_component hq hr hqM hrM hC heq S I x (Or.inl hnot)))
  let L := 20 * (B : ℝ) * ((C.card : ℝ) + 1) ^ 2
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbound (v : ThreeForm ℤ) (hv : d₃ v = 0) (hvB : ∀ e, (dualCurrent v e).natAbs ≤ B)
      (S : Finset OrientedEdge) (hS : S ⊆ C) :
      |(certifiedFillValue (dualCurrent v) S I x : ℝ)| ≤ L := by
    have hdiv (y : Site) : currentDivergence (dualCurrent v) y = 0 := by
      rw [currentDivergence_dualCurrent, hv, Pi.zero_apply]
    have h₁ := natAbs_certifiedFillValue_le (dualCurrent v) S I x hdiv B hvB
    have h₂ : (S.card : ℝ) ≤ C.card := by exact_mod_cast Finset.card_le_card hS
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    calc
      _ ≤ 20 * (B : ℝ) * ((S.card : ℝ) + 1) ^ 2 := by exact_mod_cast h₁
      _ ≤ _ := by dsimp only [L]; gcongr
  have hcard : (D.card : ℝ) ≤ (2 : ℝ) ^ C.card := by
    have h : D ⊆ C.powerset := fun S hS => Finset.mem_powerset.mpr (Finset.mem_filter.mp hS).2
    exact_mod_cast (Finset.card_le_card h).trans_eq (Finset.card_powerset C)
  rw [hsum]
  calc
    _ ≤ ∑ S ∈ D, |f S| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ D, 2 * L := by
      apply Finset.sum_le_sum
      intro S hS
      have hs := (Finset.mem_filter.mp hS).2
      unfold f
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, two_mul]
      exact add_le_add (hbound q hq hqB S hs) (hbound r hr hrB S hs)
    _ = (D.card : ℝ) * (2 * L) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ C.card * (2 * L) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by dsimp only [L, C]; ring

def incidentDualEdges (p : Plaquette) : Finset OrientedEdge :=
  (faceCubes p).map edgeCubeEquiv.symm.toEmbedding

theorem mem_incidentDualEdges_iff (p : Plaquette) (e : OrientedEdge) :
    e ∈ incidentDualEdges p ↔ p ∈ cubeFaces (edgeCubeEquiv e) :=
  (Finset.mem_map_equiv (f := edgeCubeEquiv.symm)).trans mem_cubeFaces_iff.symm

private theorem incidentDualEdges_square (p : Plaquette) :
    ∃ a b : Axis, a ≠ b ∧
      incidentDualEdges p =
        {(-p.2, a), (-p.2, b), (-p.2 + step a, b), (-p.2 + step b, a)} := by
  obtain ⟨I, x⟩ := p
  cases I
  · refine ⟨2, 3, by decide, ?_⟩
    simp [incidentDualEdges, faceCubes, faceCubeList, edgeCubeEquiv, sub_eq_add_neg,
      add_comm, Finset.insert_comm]
  · refine ⟨1, 3, by decide, ?_⟩
    simp [incidentDualEdges, faceCubes, faceCubeList, edgeCubeEquiv, sub_eq_add_neg,
      add_comm, Finset.insert_comm]
  · refine ⟨1, 2, by decide, ?_⟩
    simp [incidentDualEdges, faceCubes, faceCubeList, edgeCubeEquiv, sub_eq_add_neg,
      add_comm, Finset.insert_comm]
  · refine ⟨0, 3, by decide, ?_⟩
    simp [incidentDualEdges, faceCubes, faceCubeList, edgeCubeEquiv, sub_eq_add_neg,
      add_comm, Finset.insert_comm]
  · refine ⟨0, 2, by decide, ?_⟩
    simp [incidentDualEdges, faceCubes, faceCubeList, edgeCubeEquiv, sub_eq_add_neg,
      add_comm, Finset.insert_comm]
  · refine ⟨0, 1, by decide, ?_⟩
    simp [incidentDualEdges, faceCubes, faceCubeList, edgeCubeEquiv, sub_eq_add_neg,
      add_comm, Finset.insert_comm]

private theorem incidentDualEdges_in_component {M : Set OrientedEdge} (p : Plaquette)
    (hM : (↑(incidentDualEdges p) : Set OrientedEdge) ⊆ M) :
    ∃ a : OrientedEdge, a.1 = -p.2 ∧ a ∈ markedComponent dualEdgeGraph M a ∧
      (↑(incidentDualEdges p) : Set OrientedEdge) ⊆ markedComponent dualEdgeGraph M a := by
  obtain ⟨a, b, hab, hs⟩ := incidentDualEdges_square p
  let e : OrientedEdge := (-p.2, a)
  let f : OrientedEdge := (-p.2, b)
  let g : OrientedEdge := (-p.2 + step a, b)
  let h : OrientedEdge := (-p.2 + step b, a)
  have hs' : incidentDualEdges p = {e, f, g, h} := hs
  have hM' : ∀ q : OrientedEdge, q = e ∨ q = f ∨ q = g ∨ q = h → q ∈ M := by
    intro q hq
    apply hM
    simpa only [hs', Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using hq
  have he : e ∈ markedComponent dualEdgeGraph M e := ⟨.nil, by simpa using hM' e (Or.inl rfl)⟩
  have hef : dualEdgeGraph.Adj e f :=
    ⟨fun hEq => hab (congrArg Prod.snd hEq), -p.2, Or.inl rfl, Or.inl rfl⟩
  have heg : dualEdgeGraph.Adj e g :=
    ⟨fun hEq => hab (congrArg Prod.snd hEq), -p.2 + step a, Or.inr rfl, Or.inl rfl⟩
  have hfh : dualEdgeGraph.Adj f h :=
    ⟨fun hEq => hab (congrArg Prod.snd hEq).symm, -p.2 + step b, Or.inr rfl, Or.inl rfl⟩
  have hf := markedComponent_closed_under_adj he (hM' f (Or.inr (Or.inl rfl))) hef
  have hg := markedComponent_closed_under_adj he (hM' g (Or.inr (Or.inr (Or.inl rfl)))) heg
  have hh := markedComponent_closed_under_adj hf (hM' h (Or.inr (Or.inr (Or.inr rfl)))) hfh
  refine ⟨e, rfl, he, ?_⟩
  intro q hq
  simp only [hs', Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact he
  · exact hf
  · exact hg
  · exact hh

private theorem d₂_congr_cubeFaces (F G : TwoForm ℝ) (c : Cube) (x : Site)
    (h : ∀ p ∈ cubeFaces (c, x), F p.1 p.2 = G p.1 p.2) :
    d₂ F c x = d₂ G c x := by
  have hf (p : Plaquette) (hp : p ∈ cubeFaceList (c, x)) : F p.1 p.2 = G p.1 p.2 :=
    h p ((mem_cubeFaces_list (c, x)).mpr hp)
  have hh : ∀ p ∈ cubeFaceList (c, x), F p.1 p.2 = G p.1 p.2 := hf
  cases c <;>
    simp only [cubeFaceList, List.forall_mem_cons] at hh <;>
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hh <;>
    simp only [d₂, diff, Pi.add_apply, Pi.sub_apply, h₁, h₂, h₃, h₄, h₅, h₆]

private theorem liftFlux_eq_of_single_cut_good {N : ℕ} (U : InfiniteConfig N) (p : Plaquette)
    (hgood : U ∉ badPlaquette p) (η ζ : TwoForm ℝ)
    (hη : ∀ I x, |η I x| ≤ Real.pi / 16) (hζ : ∀ I x, |ζ I x| ≤ Real.pi / 16)
    (hagree : ∀ q : Plaquette, q ≠ p → η q.1 q.2 = ζ q.1 q.2) :
    liftFlux η (plaquetteEigenangles (fun i y => U (i, y))) =
      liftFlux ζ (plaquetteEigenangles (fun i y => U (i, y))) := by
  funext I x
  rw [liftFlux_eq_eigenAngleLift, liftFlux_eq_eigenAngleLift]
  by_cases h : (I, x) = p
  · have hP : ¬badUnitary (plaquetteHolonomy (fun i y => U (i, y)) I x) := by
      change U ∉ badPlaquette (I, x)
      rwa [h]
    rw [eigenAngleLift_of_good _ _ (hη I x) hP, eigenAngleLift_of_good _ _ (hζ I x) hP]
  · rw [hagree (I, x) h]

private theorem dualCurrent_eq_off_incidentDualEdges {N : ℕ} (U : InfiniteConfig N) (p : Plaquette)
    (η ζ : TwoForm ℝ) (hagree : ∀ q : Plaquette, q ≠ p → η q.1 q.2 = ζ q.1 q.2)
    (e : OrientedEdge) (he : e ∉ incidentDualEdges p) :
    dualCurrent (defect (liftFlux η (plaquetteEigenangles (fun j y => U (j, y))))) e =
      dualCurrent (defect (liftFlux ζ (plaquetteEigenangles (fun j y => U (j, y))))) e := by
  let V : OneForm (UnitaryMatrix N) := fun j y => U (j, y)
  let L (ν : TwoForm ℝ) := liftFlux ν (plaquetteEigenangles V)
  have hL (q : Plaquette) (hq : q ≠ p) : L η q.1 q.2 = L ζ q.1 q.2 := by
    simp only [L, liftFlux_eq_eigenAngleLift, hagree q hq]
  change dualCurrent (defect (L η)) e = dualCurrent (defect (L ζ)) e
  have hcube : p ∉ cubeFaces (edgeCubeEquiv e) := fun hp =>
    he ((mem_incidentDualEdges_iff p e).mpr hp)
  obtain ⟨y, i⟩ := e
  fin_cases i <;> simp [edgeCubeEquiv] at hcube <;>
    simp [dualCurrent, defect, d₂_congr_cubeFaces _ _ _ _ (fun q hmem => hL q (by
      intro heq
      exact hcube (heq ▸ hmem)))]

private theorem repairedCutFlux_eq_outside_singleCut_box {N : ℕ} (U : InfiniteConfig N)
    (p : Plaquette) (η ζ : TwoForm ℝ)
    (hη : ∀ I x, |η I x| ≤ Real.pi / 16) (hζ : ∀ I x, |ζ I x| ≤ Real.pi / 16)
    (hagree : ∀ q : Plaquette, q ≠ p → η q.1 q.2 = ζ q.1 q.2)
    (a : OrientedEdge) (ha : a.1 = -p.2) :
    let M := {e | U ∈ markedDualLink badPlaquette e}
    let C := markedComponent dualEdgeGraph M a
    (haC : a ∈ C) → (hInc : (↑(incidentDualEdges p) : Set OrientedEdge) ⊆ C) → (hC : C.Finite) →
    ∀ I x, ¬edgeBoxContains hC.toFinset (-x) →
      repairedCutFlux (fun j y => U (j, y)) η I x = repairedCutFlux (fun j y => U (j, y)) ζ I x := by
  dsimp only
  intro haC hInc hC I x hx
  let V : OneForm (UnitaryMatrix N) := fun j y => U (j, y)
  let L (ν : TwoForm ℝ) := liftFlux ν (plaquetteEigenangles V)
  have hL (q : Plaquette) (hq : q ≠ p) : L η q.1 q.2 = L ζ q.1 q.2 := by
    simp only [L, liftFlux_eq_eigenAngleLift, hagree q hq]
  have hq (e : OrientedEdge)
      (he : e ∉ markedComponent dualEdgeGraph {e | U ∈ markedDualLink badPlaquette e} a) :
      dualCurrent (defect (L η)) e = dualCurrent (defect (L ζ)) e := by
    exact dualCurrent_eq_off_incidentDualEdges U p η ζ hagree e (fun h => he (hInc h))
  have hfill := fillDefect_eq_outside_markedComponent_box (defect (L η)) (defect (L ζ))
    (plaquetteDefect_closed V η) (plaquetteDefect_closed V ζ)
    _ (cutDefect_supported_in_marks U η hη) (cutDefect_supported_in_marks U ζ hζ) a hC hq I x hx
  have hbase : (I, x) ≠ p := by
    intro heq
    have hpx : x = p.2 := congrArg Prod.snd heq
    have hv : a.1 ∈ edgeVertices hC.toFinset :=
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hC.mem_toFinset.mpr haC))
    exact hx (fun i => ⟨⟨a.1, hv, by rw [ha, hpx]⟩, a.1, hv, by rw [ha, hpx]⟩)
  change L η I x - 2 * Real.pi * (fillDefect (defect (L η)) I x : ℝ) =
    L ζ I x - 2 * Real.pi * (fillDefect (defect (L ζ)) I x : ℝ)
  rw [hL (I, x) hbase, hfill]

/-- For a fixed input face, the change in the repaired flux has finite support
uniformly over all pairs of allowed cuts that differ only at that face. -/
theorem singleCut_fluxDifference_finite_periodicLimit_ae {N : ℕ} (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂μ.toMeasure, ∀ p : Plaquette, ∃ S : Finset Site, ∀ η ζ : TwoForm ℝ,
      (∀ I x, |η I x| ≤ Real.pi / 16) → (∀ I x, |ζ I x| ≤ Real.pi / 16) →
      (∀ q : Plaquette, q ≠ p → η q.1 q.2 = ζ q.1 q.2) →
      ∀ I x, x ∉ S →
        repairedCutFlux (fun j y => U (j, y)) η I x = repairedCutFlux (fun j y => U (j, y)) ζ I x := by
  filter_upwards [markedComponents_finite_periodicLimit hN hβ μ l hl hμ] with U hU
  intro p
  by_cases hp : U ∈ badPlaquette p
  · let M := {e | U ∈ markedDualLink badPlaquette e}
    have hmarked : (↑(incidentDualEdges p) : Set OrientedEdge) ⊆ M := by
      intro e he
      exact ⟨p, (mem_incidentDualEdges_iff p e).mp he, hp⟩
    obtain ⟨a, ha, haC, hInc⟩ := incidentDualEdges_in_component p hmarked
    let hC := hU a
    let hBox := finite_edgeBoxContains hC.toFinset
    refine ⟨hBox.toFinset, fun η ζ hη hζ hagree I x hx => ?_⟩
    exact repairedCutFlux_eq_outside_singleCut_box U p η ζ hη hζ hagree a ha haC hInc hC I x
      (fun h => hx (hBox.mem_toFinset.mpr h))
  · refine ⟨∅, fun η ζ hη hζ hagree I x _ => ?_⟩
    rw [repairedCutFlux, repairedCutFlux, liftFlux_eq_of_single_cut_good U p hp η ζ hη hζ hagree]

/-- The signed change from replacing a single cut has zero total flux
in each output orientation, configuration by configuration. -/
theorem tsum_singleCut_fluxDifference_eq_zero_periodicLimit_ae {N : ℕ} (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂μ.toMeasure, ∀ p : Plaquette, ∀ η ζ : TwoForm ℝ,
      (∀ I x, |η I x| ≤ Real.pi / 16) → (∀ I x, |ζ I x| ≤ Real.pi / 16) →
      (∀ q : Plaquette, q ≠ p → η q.1 q.2 = ζ q.1 q.2) →
      ∀ I, (∑' x, (repairedCutFlux (fun j y => U (j, y)) η I x -
        repairedCutFlux (fun j y => U (j, y)) ζ I x)) = 0 := by
  filter_upwards [singleCut_fluxDifference_finite_periodicLimit_ae hN hβ μ l hl hμ,
    repairedCutFlux_closed_periodicLimit_ae hN hβ μ l hl hμ] with U hfinite hclosed
  intro p η ζ hη hζ hagree I
  obtain ⟨S, hS⟩ := hfinite p
  let B := repairedCutFlux (fun j y => U (j, y)) η - repairedCutFlux (fun j y => U (j, y)) ζ
  have hBs (J : Face) : Summable (B J) :=
    summable_of_ne_finset_zero (s := S) fun x hx => sub_eq_zero.mpr (hS η ζ hη hζ hagree J x hx)
  have hBc : d₂ B = 0 := by
    change d₂ (repairedCutFlux (fun j y => U (j, y)) η -
      repairedCutFlux (fun j y => U (j, y)) ζ) = 0
    rw [d₂_sub, (hclosed η hη).2, (hclosed ζ hζ).2, sub_zero]
  exact tsum_closed_twoForm_eq_zero B hBs hBc I

private theorem edgeBox_radius_of_component {M : Set OrientedEdge} {a : OrientedEdge}
    (hC : (markedComponent dualEdgeGraph M a).Finite) (ha : a ∈ markedComponent dualEdgeGraph M a)
    {x : Site} (hx : edgeBoxContains hC.toFinset (-x)) :
    radius (x + a.1) ≤ 2 * hC.toFinset.card + 1 := by
  let C := hC.toFinset
  have hc (e : OrientedEdge) (he : e ∈ C) :
      ∃ p : dualEdgeGraph.Walk a e, ∀ f ∈ p.support, f ∈ C := by
    obtain ⟨p, hp⟩ := hC.mem_toFinset.mp he
    refine ⟨p, fun f hf => hC.mem_toFinset.mpr ⟨p.takeUntil f hf, fun g hg => ?_⟩⟩
    exact hp g (p.support_takeUntil_subset_support hf hg)
  obtain ⟨p, hp, hlen⟩ := exists_closedWalk_with_support dualEdgeGraph C (hC.mem_toFinset.mpr ha) hc
  have hb (e : OrientedEdge) (he : e ∈ C) (i : Axis) :
      a.1 i ≤ e.1 i + 2 * (C.card : ℤ) ∧ e.1 i ≤ a.1 i + 2 * (C.card : ℤ) := by
    have hw : e ∈ p.support := List.mem_toFinset.mp (hp.symm ▸ he)
    have h := walk_coordinate_bounds p hw i
    omega
  have hv (y : Site) (hy : y ∈ edgeVertices C) (i : Axis) :
      a.1 i ≤ y i + (2 * (C.card : ℤ) + 1) ∧ y i ≤ a.1 i + (2 * (C.card : ℤ) + 1) := by
    rcases Finset.mem_union.mp hy with hl | hr
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
      have h := hb e he i
      omega
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hr
      have h := hb e he i
      simp only [Pi.add_apply, step]
      split <;> omega
  apply Finset.sup_le
  intro i _
  obtain ⟨⟨u, hu, hul⟩, v, hv', hvl⟩ := hx i
  have hlo := (hv u hu i).1
  have hhi := (hv v hv' i).2
  simp only [Pi.neg_apply] at hul hvl
  change ((x + a.1) i).natAbs ≤ 2 * C.card + 1
  simp only [Pi.add_apply]
  omega

def singleCutAmplitudeBound (N n : ℕ) : ℝ :=
  (2 * (N : ℝ) * (17 * Real.pi / 16) + 2 * Real.pi * (40 * (4 * (N : ℝ)))) *
    ((2 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2)

theorem singleCutAmplitudeBound_nonneg (N n : ℕ) : 0 ≤ singleCutAmplitudeBound N n := by
  unfold singleCutAmplitudeBound
  positivity

/-- A cut change is bounded by a function of one marked-component size and
is supported within the corresponding radius of the input plaquette. -/
theorem singleCut_fluxDifference_amplitude_periodicLimit_ae {N : ℕ} (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂μ.toMeasure, ∀ p : Plaquette, ∃ n : ℕ,
      (n = 0 ∨ ∃ i : Axis, (n : ℕ∞) ≤
        (markedComponent dualEdgeGraph {e | U ∈ markedDualLink badPlaquette e} (-p.2, i)).encard) ∧
      ∀ η ζ : TwoForm ℝ, (∀ I x, |η I x| ≤ Real.pi / 16) → (∀ I x, |ζ I x| ≤ Real.pi / 16) →
        (∀ q : Plaquette, q ≠ p → η q.1 q.2 = ζ q.1 q.2) →
        ∀ I x, |repairedCutFlux (fun j y => U (j, y)) η I x -
          repairedCutFlux (fun j y => U (j, y)) ζ I x| ≤
            if radius (x - p.2) ≤ 2 * n + 1 then singleCutAmplitudeBound N n else 0 := by
  filter_upwards [markedComponents_finite_periodicLimit hN hβ μ l hl hμ,
    repairedCutFluxApprox_eventually_eq_periodicLimit hN hβ μ l hl hμ] with U hU hApprox
  intro p
  by_cases hp : U ∈ badPlaquette p
  · let M := {e | U ∈ markedDualLink badPlaquette e}
    have hmarked : (↑(incidentDualEdges p) : Set OrientedEdge) ⊆ M :=
      fun e he => ⟨p, (mem_incidentDualEdges_iff p e).mp he, hp⟩
    obtain ⟨a, ha, haC, hInc⟩ := incidentDualEdges_in_component p hmarked
    let hC := hU a
    let n := hC.toFinset.card
    have ha' : a = (-p.2, a.2) := Prod.ext ha rfl
    have hsize : (n : ℕ∞) ≤ (markedComponent dualEdgeGraph M (-p.2, a.2)).encard := by
      rw [← ha']
      exact hC.encard_eq_coe_toFinset_card.ge
    refine ⟨n, Or.inr ⟨a.2, hsize⟩, fun η ζ hη hζ hagree I x => ?_⟩
    by_cases hx : radius (x - p.2) ≤ 2 * n + 1
    · rw [ite_eq_left hx]
      let V : OneForm (UnitaryMatrix N) := fun i y => U (i, y)
      let A (b : TwoForm ℝ) := liftFlux b (plaquetteEigenangles V)
      let q (b : TwoForm ℝ) := defect (A b)
      have hq : ∀ e ∉ markedComponent dualEdgeGraph M a, dualCurrent (q η) e = dualCurrent (q ζ) e :=
        fun e he => dualCurrent_eq_off_incidentDualEdges U p η ζ hagree e (fun h => he (hInc h))
      obtain ⟨R, hR⟩ := hApprox I x
      have hY := abs_fillDefectApprox_change_le (q η) (q ζ) (plaquetteDefect_closed V η)
        (plaquetteDefect_closed V ζ) (cutDefect_supported_in_marks U η hη) (cutDefect_supported_in_marks U ζ hζ)
        hC hq (4 * N) (natAbs_cutDefect_le V η hη) (natAbs_cutDefect_le V ζ hζ) R I x
      have hA : |A η I x - A ζ I x| ≤ 2 * (N : ℝ) * (17 * Real.pi / 16) := by
        rw [sub_eq_add_neg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, two_mul, add_mul]
        exact add_le_add (abs_liftFlux_le η _ I x (hη I x)) (abs_liftFlux_le ζ _ I x (hζ I x))
      rw [← hR R le_rfl η hη, ← hR R le_rfl ζ hζ]
      change |(A η I x - 2 * Real.pi * (fillDefectApprox (q η) R I x : ℝ)) -
        (A ζ I x - 2 * Real.pi * (fillDefectApprox (q ζ) R I x : ℝ))| ≤ _
      let D := (fillDefectApprox (q η) R I x : ℝ) - (fillDefectApprox (q ζ) R I x : ℝ)
      let P := (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ 2
      have hP : 1 ≤ P := by
        dsimp only [P]
        refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ ?_)
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have he : (A η I x - 2 * Real.pi * (fillDefectApprox (q η) R I x : ℝ)) -
          (A ζ I x - 2 * Real.pi * (fillDefectApprox (q ζ) R I x : ℝ)) =
          (A η I x - A ζ I x) + -((2 * Real.pi) * D) := by dsimp only [D]; ring
      rw [he]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_mul, abs_of_nonneg Real.two_pi_pos.le]
      have hD : |D| ≤ (40 * (4 * (N : ℝ))) * P := by
        convert hY using 1
        push_cast
        dsimp only [P, n]
        ring
      have hRaw : 2 * (N : ℝ) * (17 * Real.pi / 16) ≤ (2 * (N : ℝ) * (17 * Real.pi / 16)) * P :=
        le_mul_of_one_le_right (by positivity) hP
      unfold singleCutAmplitudeBound
      change _ ≤ (2 * (N : ℝ) * (17 * Real.pi / 16) + 2 * Real.pi * (40 * (4 * (N : ℝ)))) * P
      rw [add_mul]
      exact add_le_add (hA.trans hRaw)
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hD Real.two_pi_pos.le)
    · rw [ite_eq_right hx]
      have hBox : ¬edgeBoxContains hC.toFinset (-x) := fun h =>
        hx (by simpa only [ha, ← sub_eq_add_neg] using edgeBox_radius_of_component hC haC h)
      rw [repairedCutFlux_eq_outside_singleCut_box U p η ζ hη hζ hagree a ha haC hInc hC I x hBox, sub_self, abs_zero]
  · refine ⟨0, Or.inl rfl, fun η ζ hη hζ hagree I x => ?_⟩
    rw [repairedCutFlux, repairedCutFlux, liftFlux_eq_of_single_cut_good U p hp η ζ hη hζ hagree, sub_self, abs_zero]
    split
    · exact singleCutAmplitudeBound_nonneg _ _
    · exact le_rfl

end

end GaplessYangMills

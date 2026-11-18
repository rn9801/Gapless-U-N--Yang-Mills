module

public import GaplessYangMills.CutResponse
public import GaplessYangMills.Ward

/-!
# Response to changing one cut

Changes of the defect current inside one marked component can only
change repaired fillings in the coordinate box of that component.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory SimpleGraph
open scoped Topology

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

private theorem inspection_disjoint_of_box {M : Set OrientedEdge} {a : OrientedEdge}
    (hC : (markedComponent dualEdgeGraph M a).Finite)
    (S : Finset OrientedEdge) (x : Site) (hS : (↑S : Set OrientedEdge) ⊆ M)
    (hbox : edgeBoxContains S x)
    (hconn : ∃ e ∈ S, ∀ f ∈ S, ∃ w : dualEdgeGraph.Walk e f, ∀ g ∈ w.support, g ∈ S)
    (houtside : ¬edgeBoxContains hC.toFinset x) :
    ∀ e ∈ componentInspectionEdges S, e ∉ markedComponent dualEdgeGraph M a := by
  have hdisj (e : OrientedEdge) (he : e ∈ S) : e ∉ markedComponent dualEdgeGraph M a := by
    intro hE
    obtain ⟨r, _, hR⟩ := hconn
    have hc (f : OrientedEdge) (hf : f ∈ S) : f ∈ markedComponent dualEdgeGraph M r := by
      obtain ⟨w, hw⟩ := hR f hf
      exact ⟨w, fun g hg => hS (hw g hg)⟩
    have heq : markedComponent dualEdgeGraph M r = markedComponent dualEdgeGraph M a :=
      (component_eq_of_mem _ (hc e he)).trans (component_eq_of_mem _ hE).symm
    exact houtside (edgeBoxContains_mono (fun g hg => hC.mem_toFinset.mpr (heq ▸ hc g hg)) hbox)
  intro e he
  rcases Finset.mem_union.mp he with hs | hs
  · exact hdisj e hs
  · obtain ⟨f, hf, he'⟩ := Finset.mem_biUnion.mp hs
    intro hE
    exact hdisj f hf (markedComponent_closed_under_adj hE (hS hf) ((mem_edgeNeighborFinset f e).mp he').symm)

theorem fillDefect_eq_outside_markedComponent_box (q r : ThreeForm ℤ)
    (hq : d₃ q = 0) (hr : d₃ r = 0)
    (M : Set OrientedEdge) (hqM : Function.support (dualCurrent q) ⊆ M)
    (hrM : Function.support (dualCurrent r) ⊆ M) (a : OrientedEdge)
    (hC : (markedComponent dualEdgeGraph M a).Finite)
    (heq : ∀ e ∉ markedComponent dualEdgeGraph M a, dualCurrent q e = dualCurrent r e)
    (I : Face) (x : Site) (hx : ¬edgeBoxContains hC.toFinset (-x)) :
    fillDefect q I x = fillDefect r I x := by
  rw [fillDefect_eq_finsum_certified, fillDefect_eq_finsum_certified]
  apply finsum_congr
  intro S
  have hc (v : ThreeForm ℤ) (hv : d₃ v = 0) (hvM : Function.support (dualCurrent v) ⊆ M)
      (h : certifiedFillValue (dualCurrent v) S I x ≠ 0) :
      ∀ e ∈ componentInspectionEdges S, e ∉ markedComponent dualEdgeGraph M a := by
    have hdiv (y : Site) : currentDivergence (dualCurrent v) y = 0 := by
      rw [currentDivergence_dualCurrent, hv, Pi.zero_apply]
    obtain ⟨hm, hbox, hconn⟩ := certifiedFillValue_ne_zero_box _ hdiv S I x h
    exact inspection_disjoint_of_box hC S (-x) (hm.trans hvM) hbox hconn hx
  by_cases hq₀ : certifiedFillValue (dualCurrent q) S I x = 0
  · by_cases hr₀ : certifiedFillValue (dualCurrent r) S I x = 0
    · rw [hq₀, hr₀]
    · exact certifiedFillValue_congr_on _ _ S (fun e he => heq e (hc r hr hrM hr₀ e he)) I x
  · exact certifiedFillValue_congr_on _ _ S (fun e he => heq e (hc q hq hqM hq₀ e he)) I x

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
    have hcube : p ∉ cubeFaces (edgeCubeEquiv e) := fun hp =>
      he (hInc ((mem_incidentDualEdges_iff p e).mpr hp))
    obtain ⟨y, i⟩ := e
    fin_cases i <;> simp [edgeCubeEquiv] at hcube <;>
      simp [dualCurrent, defect, d₂_congr_cubeFaces _ _ _ _ (fun q hmem => hL q (by
        intro heq
        exact hcube (heq ▸ hmem)))]
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

end

end GaplessYangMills

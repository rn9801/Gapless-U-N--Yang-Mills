module

public import GaplessYangMills.MeasurableRepair

/-!
# Finite approximants to the repaired cut flux

For each square, enumerate the finite connected sets of bounded size whose
boxes could contribute there. The same finite certificate used for
measurability determines the contribution of each set.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory SimpleGraph
open scoped Topology

noncomputable section

theorem finiteEdgeChain_support_subset (q : OrientedEdge → ℤ) (S : Finset OrientedEdge) :
    (finiteEdgeChain S fun e => q e.val).support ⊆ S := by
  intro e he
  by_contra hn
  have h := Finsupp.mem_support_iff.mp he
  rw [congrFun (finiteEdgeChain_coe q S) e, restrictCurrent, Set.indicator_of_notMem hn] at h
  exact h rfl

theorem finiteEdgeChain_boundary₁_eq_zero (q : OrientedEdge → ℤ)
    (hdiv : ∀ x, currentDivergence q x = 0) {S : Finset OrientedEdge}
    (hS : certifiesCurrentComponent q S) :
    boundary₁ (finiteEdgeChain S (fun e => q e.val)) = 0 := by
  obtain ⟨C, he⟩ := hS
  ext x
  rw [boundary₁_eq_currentDivergence, finiteEdgeChain_coe, he]
  exact currentDivergence_restrict q C.val (component_saturated C) hdiv x

private theorem boxContains_of_chainBox (r : EdgeChain) (hr : r.support.Nonempty)
    {S : Finset OrientedEdge} (hS : r.support ⊆ S) (x : Site)
    (hlo : edgeChainLower r ≤ x) (hhi : x ≤ edgeChainUpper r) :
    edgeBoxContains S x := by
  intro i
  obtain ⟨e, he, hmin⟩ := Finset.exists_mem_eq_inf' hr (fun e => e.1 i)
  obtain ⟨f, hf, hmax⟩ := Finset.exists_mem_eq_sup' hr (fun e => (e.1 + step e.2) i)
  have hl : e.1 i ≤ x i := by
    rw [← hmin]
    simpa only [edgeChainLower, dite_eq_left hr] using hlo i
  have hu : x i ≤ (f.1 + step f.2) i := by
    rw [← hmax]
    simpa only [edgeChainUpper, dite_eq_left hr] using hhi i
  exact ⟨⟨e.1, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hS he)), hl⟩,
    ⟨f.1 + step f.2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hS hf)), hu⟩⟩

theorem certifiedFillValue_ne_zero_box (q : OrientedEdge → ℤ)
    (hdiv : ∀ x, currentDivergence q x = 0) (S : Finset OrientedEdge) (I : Face) (x : Site)
    (h : certifiedFillValue q S I x ≠ 0) :
    S ∈ markedConnectedBoxes (Function.support q) (-x) := by
  classical
  have hS : certifiesCurrentComponent q S := by
    by_contra hn
    exact h (ite_eq_right hn)
  let r := finiteEdgeChain S (fun e => q e.val)
  let s := translatedChainFilling r
  have hn : primalFilling s I x ≠ 0 := by
    simpa only [certifiedFillValue, ite_eq_left hS, r, s] using h
  have hs : ∃ J : Face, s (-x, J) ≠ 0 := by
    by_contra! hz
    exact hn (by cases I <;> simp [primalFilling, hz])
  obtain ⟨J, hJ⟩ := hs
  have hr : r.support.Nonempty := by
    by_contra! hz
    have hr₀ : r = 0 := Finsupp.support_eq_empty.mp hz
    exact hJ (by simp [s, translatedChainFilling, hr₀])
  have hbd := finiteEdgeChain_boundary₁_eq_zero q hdiv hS
  have hbox := (translatedChainFilling_spec r hbd).2.1 (-x, J) (Finsupp.mem_support_iff.mpr hJ)
  obtain ⟨hmark, _, hconn⟩ := (certifiesCurrentComponent_iff q S).mp hS
  exact ⟨fun e he => hmark e he,
    boxContains_of_chainBox r hr (finiteEdgeChain_support_subset q S) (-x) hbox.1 hbox.2, hconn⟩

/-- The candidate components of size at most `R` for one output vertex. -/
def boundedBoxCover (x : Site) (R : ℕ) : Finset (Finset OrientedEdge) :=
  (Finset.range (R + 1)).biUnion fun n => connectedBoxCover x n

def componentInspectionEdges (S : Finset OrientedEdge) : Finset OrientedEdge :=
  S ∪ S.biUnion edgeNeighborFinset

theorem certifiedFillValue_congr_on (q r : OrientedEdge → ℤ) (S : Finset OrientedEdge)
    (h : ∀ e ∈ componentInspectionEdges S, q e = r e) (I : Face) (x : Site) :
    certifiedFillValue q S I x = certifiedFillValue r S I x := by
  have he (e : OrientedEdge) (he : e ∈ S) : q e = r e :=
    h e (Finset.mem_union_left _ he)
  have hf (e : OrientedEdge) (he : e ∈ S) (f : OrientedEdge) (hf : f ∈ edgeNeighborFinset e) :
      q f = r f :=
    h f (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, hf⟩))
  have hcert : certifiesCurrentComponent q S ↔ certifiesCurrentComponent r S := by
    simp only [certifiesCurrentComponent_iff]
    constructor
    · rintro ⟨hS, hN, hc⟩
      exact ⟨fun e heS => he e heS ▸ hS e heS,
        fun e heS f hfS hnot => hf e heS f hfS ▸ hN e heS f hfS hnot, hc⟩
    · rintro ⟨hS, hN, hc⟩
      exact ⟨fun e heS => (he e heS).symm ▸ hS e heS,
        fun e heS f hfS hnot => (hf e heS f hfS).symm ▸ hN e heS f hfS hnot, hc⟩
  have hchain : finiteEdgeChain S (fun e => q e.val) = finiteEdgeChain S (fun e => r e.val) :=
    congrArg (finiteEdgeChain S) (funext fun e => he e.val e.property)
  classical
  by_cases hc : certifiesCurrentComponent q S
  · simp only [certifiedFillValue, ite_eq_left hc, ite_eq_left (hcert.mp hc), hchain]
  · simp only [certifiedFillValue, ite_eq_right hc, ite_eq_right (mt hcert.mpr hc)]

theorem componentInspectionEdges_subset {x : Site} {R : ℕ} {S : Finset OrientedEdge}
    (hS : S ∈ boundedBoxCover x R) :
    componentInspectionEdges S ⊆ edgesNearVertex x (4 * R + 2) := by
  obtain ⟨n, hn, hS'⟩ := Finset.mem_biUnion.mp hS
  have hnR := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  obtain ⟨e, he, hcov⟩ := Finset.mem_biUnion.mp hS'
  obtain ⟨w, hw, hwS⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hcov).1
  have hlen := mem_finsetWalkLength_iff.mp hw
  have hE := (mem_edgesNearVertex_iff _ _ _).mp he
  have hbase (f : OrientedEdge) (hf : f ∈ S) (i : Axis) :
      x i - (4 * (R : ℤ) + 1) ≤ f.1 i ∧ f.1 i ≤ x i + (4 * (R : ℤ) + 1) := by
    have hfw : f ∈ w.support := List.mem_toFinset.mp (hwS.symm ▸ hf)
    have hb := walk_coordinate_bounds w hfw i
    have hx := hE i
    push_cast at hx
    omega
  intro f hf
  apply (mem_edgesNearVertex_iff _ _ _).mpr
  intro i
  rcases Finset.mem_union.mp hf with h | h
  · have hb := hbase f h i
    push_cast
    omega
  · obtain ⟨g, hg, hg'⟩ := Finset.mem_biUnion.mp h
    have hb := hbase g hg i
    have ha := adjacent_coordinate_bounds ((mem_edgeNeighborFinset g f).mp hg') i
    push_cast
    omega

def fillDefectApprox (q : ThreeForm ℤ) (R : ℕ) (I : Face) (x : Site) : ℤ :=
  ∑ S ∈ boundedBoxCover (-x) R, certifiedFillValue (dualCurrent q) S I x

/-- Each truncated filling reads only the defect current in the indicated
finite box, including the edges needed to check its component boundaries. -/
theorem fillDefectApprox_congr_on (q r : ThreeForm ℤ) (R : ℕ) (I : Face) (x : Site)
    (h : ∀ e ∈ edgesNearVertex (-x) (4 * R + 2), dualCurrent q e = dualCurrent r e) :
    fillDefectApprox q R I x = fillDefectApprox r R I x :=
  Finset.sum_congr rfl fun S hS => certifiedFillValue_congr_on _ _ S
    (fun e he => h e (componentInspectionEdges_subset hS he)) I x

def repairedCutFluxApprox {N : ℕ} (R : ℕ) (U : OneForm (UnitaryMatrix N)) (η : TwoForm ℝ) :
    TwoForm ℝ :=
  repairFlux (fun q => fillDefectApprox q R) (liftFlux η (plaquetteEigenangles U))

private theorem fillDefectApprox_eq_of_card_bound (q : ThreeForm ℤ) (hq : d₃ q = 0)
    (M : Set OrientedEdge) (hM : Function.support (dualCurrent q) ⊆ M)
    (I : Face) (x : Site) (R : ℕ) (hR : ∀ S ∈ markedConnectedBoxes M (-x), S.card ≤ R) :
    fillDefectApprox q R I x = fillDefect q I x := by
  have hdiv (y : Site) : currentDivergence (dualCurrent q) y = 0 := by
    rw [currentDivergence_dualCurrent, hq, Pi.zero_apply]
  rw [fillDefect_eq_finsum_certified]
  symm
  apply finsum_eq_sum_of_support_subset
  intro S hS
  obtain ⟨hm, hb, hc⟩ := certifiedFillValue_ne_zero_box (dualCurrent q) hdiv S I x hS
  have hsize := hR S ⟨hm.trans hM, hb, hc⟩
  exact Finset.mem_biUnion.mpr
    ⟨S.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hsize), mem_connectedBoxCover S (-x) hb hc⟩

theorem cutDefect_supported_in_marks {N : ℕ} (U : InfiniteConfig N) (η : TwoForm ℝ)
    (hη : ∀ I x, |η I x| ≤ Real.pi / 16) :
    Function.support (dualCurrent (defect (liftFlux η (plaquetteEigenangles (fun i x => U (i, x)))))) ⊆
      {e | U ∈ markedDualLink badPlaquette e} := by
  intro e he
  exact has_bad_face_of_nonzero_defect U η (edgeCubeEquiv e) (fun p _ => hη p.1 p.2)
    ((support_dualCurrent _ e).mp he)

/-- At each face in almost every Wilson configuration, the size truncation
is eventually exact, with a threshold independent of the allowed cuts. -/
theorem repairedCutFluxApprox_eventually_eq_periodicLimit {N : ℕ} (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂(μ : Measure (InfiniteConfig N)), ∀ I x, ∃ K : ℕ, ∀ R ≥ K,
      ∀ η : TwoForm ℝ, (∀ J y, |η J y| ≤ Real.pi / 16) →
      repairedCutFluxApprox R (fun i y => U (i, y)) η I x =
        repairedCutFlux (fun i y => U (i, y)) η I x := by
  filter_upwards [markedConnectedBoxes_finite_periodicLimit hN hβ μ l hl hμ] with U hboxes
  intro I x
  let M := {e | U ∈ markedDualLink badPlaquette e}
  let C := hboxes (-x)
  let K := C.toFinset.sup Finset.card
  refine ⟨K, fun R hR η hη => ?_⟩
  let A : OneForm (UnitaryMatrix N) := fun i y => U (i, y)
  let a := liftFlux η (plaquetteEigenangles A)
  let q := defect a
  have hclosed : d₃ q = 0 :=
    defect_closed a (unitary_liftFlux_exp_closed A η _ (prod_exp_plaquetteEigenangles A))
  have hf : fillDefectApprox q R I x = fillDefect q I x :=
    fillDefectApprox_eq_of_card_bound q hclosed M (cutDefect_supported_in_marks U η hη)
      I x R (fun S hS => (Finset.le_sup (f := Finset.card) (C.mem_toFinset.mpr hS)).trans hR)
  change a I x - 2 * Real.pi * (fillDefectApprox q R I x : ℝ) =
    a I x - 2 * Real.pi * (fillDefect q I x : ℝ)
  rw [hf]

end

end GaplessYangMills

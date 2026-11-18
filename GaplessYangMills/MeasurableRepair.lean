module

public import GaplessYangMills.ComponentFlux
public import GaplessYangMills.CutFluxMeasurability

/-!
# Finite certificates for component fillings

A proposed finite support is a current component exactly when it is
connected, all its coefficients are nonzero, and its neighboring edges
outside the support have zero coefficient. This uses finitely many
coordinates and gives measurable contributions to the repaired flux.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory SimpleGraph

noncomputable section

def certifiesCurrentComponent (q : OrientedEdge → ℤ) (S : Finset OrientedEdge) : Prop :=
  ∃ C : CurrentComponent q, (↑S : Set OrientedEdge) = C.val

private theorem walk_stays_in_componentSet {q : OrientedEdge → ℤ} {S : Finset OrientedEdge}
    (hboundary : ∀ e ∈ S, ∀ f ∈ edgeNeighborFinset e, f ∉ S → q f = 0)
    {x y : OrientedEdge} (w : dualEdgeGraph.Walk x y) (hx : x ∈ S)
    (hw : ∀ z ∈ w.support, z ∈ Function.support q) : y ∈ S := by
  induction w with
  | nil => exact hx
  | @cons u v y h w ih =>
    apply ih _ (fun z hz => hw z (List.mem_cons_of_mem _ hz))
    by_contra hv
    have hn := hboundary u hx v ((mem_edgeNeighborFinset u v).mpr h) hv
    exact hw v (List.mem_cons_of_mem _ w.start_mem_support) hn

theorem certifiesCurrentComponent_iff (q : OrientedEdge → ℤ) (S : Finset OrientedEdge) :
    certifiesCurrentComponent q S ↔
      (∀ e ∈ S, q e ≠ 0) ∧
      (∀ e ∈ S, ∀ f ∈ edgeNeighborFinset e, f ∉ S → q f = 0) ∧
      ∃ x ∈ S, ∀ y ∈ S, ∃ w : dualEdgeGraph.Walk x y, ∀ z ∈ w.support, z ∈ S := by
  constructor
  · rintro ⟨C, hC⟩
    have he (e : OrientedEdge) : e ∈ S ↔ e ∈ C.val :=
      Set.ext_iff.mp hC e
    have hn (e : OrientedEdge) (h : e ∈ S) : q e ≠ 0 := component_support C ((he e).mp h)
    refine ⟨hn, ?_, ?_⟩
    · intro e heS f hf hnot
      obtain ⟨_, x, hxe, hxf⟩ := (mem_edgeNeighborFinset e f).mp hf
      by_contra hq
      exact hnot ((he f).mpr (component_saturated C hxe hxf (hn e heS) hq ((he e).mp heS)))
    · obtain ⟨x, hx, hconn⟩ := component_connected C
      refine ⟨x, (he x).mpr hx, fun y hy => ?_⟩
      obtain ⟨w, hw⟩ := hconn y ((he y).mp hy)
      exact ⟨w, fun z hz => (he z).mpr (hw z hz)⟩
  · rintro ⟨hnonzero, hboundary, x, hx, hconn⟩
    have he : (↑S : Set OrientedEdge) = markedComponent dualEdgeGraph (Function.support q) x := by
      ext y
      constructor
      · intro hy
        obtain ⟨w, hw⟩ := hconn y hy
        exact ⟨w, fun z hz => hnonzero z (hw z hz)⟩
      · rintro ⟨w, hw⟩
        exact walk_stays_in_componentSet hboundary w hx hw
    exact ⟨⟨S, x, hnonzero x hx, he⟩, rfl⟩

def finiteEdgeChain (S : Finset OrientedEdge) (v : S → ℤ) : EdgeChain :=
  ∑ e : S, Finsupp.single e.val (v e)

theorem finiteEdgeChain_coe (q : OrientedEdge → ℤ) (S : Finset OrientedEdge) :
    (finiteEdgeChain S (fun e => q e.val) : OrientedEdge → ℤ) = restrictCurrent q (↑S) := by
  classical
  funext e
  unfold finiteEdgeChain
  rw [Finset.sum_apply']
  by_cases he : e ∈ S
  · let eS : S := ⟨e, he⟩
    rw [Finset.sum_eq_single eS]
    · simp [eS, restrictCurrent, Set.indicator_of_mem he]
    · intro j _ hne
      have h' : j.val ≠ e := fun h => hne (Subtype.ext h)
      simp [h']
    · simp
  · rw [Finset.sum_eq_zero]
    · exact (Set.indicator_of_notMem he _).symm
    · intro j _
      have h' : j.val ≠ e := fun h => he (h ▸ j.property)
      simp [h']

private theorem support_restrictCurrent_component {q : OrientedEdge → ℤ} (C : CurrentComponent q) :
    Function.support (restrictCurrent q C.val) = C.val := by
  ext e
  by_cases he : e ∈ C.val
  · simpa only [Function.mem_support, restrictCurrent, Set.indicator_of_mem he, he, iff_true] using
      component_support C he
  · simp only [Function.mem_support, restrictCurrent, Set.indicator_of_notMem he, he, ne_self_iff_false]

def certifiedFillValue (q : OrientedEdge → ℤ) (S : Finset OrientedEdge)
    (I : Face) (x : Site) : ℤ := by
  classical
  exact if certifiesCurrentComponent q S then
    primalFilling (translatedChainFilling (finiteEdgeChain S (fun e => q e.val))) I x
  else 0

private theorem certifiedFillValue_eq {q : OrientedEdge → ℤ} (S : Finset OrientedEdge)
    (C : CurrentComponent q) (hc : (↑S : Set OrientedEdge) = C.val) (I : Face) (x : Site) :
    certifiedFillValue q S I x = primalFilling (signedComponentFilling q C) I x := by
  classical
  have hf : (Function.support (restrictCurrent q C.val)).Finite := by
    rw [support_restrictCurrent_component, ← hc]
    exact S.finite_toSet
  have he : finiteEdgeChain S (fun e => q e.val) =
      Finsupp.ofSupportFinite (restrictCurrent q C.val) hf := by
    apply DFunLike.coe_injective
    rw [finiteEdgeChain_coe, hc, Finsupp.ofSupportFinite_coe]
  have hcert : certifiesCurrentComponent q S := ⟨C, hc⟩
  simp only [certifiedFillValue, ite_eq_left hcert, signedComponentFilling, dite_eq_left hf, he]

theorem fillDefect_eq_finsum_certified (q : ThreeForm ℤ) (I : Face) (x : Site) :
    fillDefect q I x = ∑ᶠ S : Finset OrientedEdge, certifiedFillValue (dualCurrent q) S I x := by
  classical
  let r := dualCurrent q
  let A : Set (CurrentComponent r) := {C | C.val.Finite}
  let B : Set (Finset OrientedEdge) := {S | certifiesCurrentComponent r S}
  let e (C : CurrentComponent r) : Finset OrientedEdge := if h : C.val.Finite then h.toFinset else ∅
  have he (C : CurrentComponent r) (h : C ∈ A) : (↑(e C) : Set OrientedEdge) = C.val := by
    change C.val.Finite at h
    simp [e, dite_eq_left h]
  have hbij : A.BijOn e B := by
    refine ⟨fun C hc => ⟨C, he C hc⟩, ?_, ?_⟩
    · intro C hc D hd hCD
      have hsets := congrArg (fun S : Finset OrientedEdge => (↑S : Set OrientedEdge)) hCD
      exact Subtype.ext ((he C hc).symm.trans (hsets.trans (he D hd)))
    · rintro S ⟨C, hC⟩
      have hfinite : C ∈ A := by
        change C.val.Finite
        rw [← hC]
        exact S.finite_toSet
      exact ⟨C, hfinite, Finset.coe_injective ((he C hfinite).trans hC.symm)⟩
  let f (C : CurrentComponent r) := primalFilling (signedComponentFilling r C) I x
  let g (S : Finset OrientedEdge) := certifiedFillValue r S I x
  have hf : (∑ᶠ C, f C) = ∑ᶠ C ∈ A, f C := by
    rw [finsum_mem_def]
    apply finsum_congr
    intro C
    by_cases h : C ∈ A
    · exact (Set.indicator_of_mem h _).symm
    · have hh : ¬(Function.support (restrictCurrent r C.val)).Finite := by
        rwa [support_restrictCurrent_component]
      cases I <;> simp [Set.indicator_of_notMem h, f, signedComponentFilling, dite_eq_right hh, primalFilling]
  have hg : (∑ᶠ S ∈ B, g S) = ∑ᶠ S, g S := by
    rw [finsum_mem_def]
    apply finsum_congr
    intro S
    by_cases h : S ∈ B
    · exact Set.indicator_of_mem h _
    · have hc : ¬certifiesCurrentComponent r S := h
      simp [Set.indicator_of_notMem h, g, certifiedFillValue, ite_eq_right hc]
  change (∑ᶠ C, f C) = ∑ᶠ S, g S
  rw [hf, ← hg]
  exact finsum_mem_eq_of_bijOn e hbij fun C hc => (certifiedFillValue_eq (e C) C (he C hc) I x).symm

private theorem measurableSet_forall_countable {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {p : ι → Ω → Prop} (hp : ∀ i, MeasurableSet {ω | p i ω}) :
    MeasurableSet {ω | ∀ i, p i ω} := by
  have he : {ω | ∀ i, p i ω} = ⋂ i, {ω | p i ω} := by ext ω; simp
  rw [he]
  exact MeasurableSet.iInter hp

private theorem measurableSet_certifiesCurrentComponent {Ω : Type*} [MeasurableSpace Ω]
    (q : Ω → OrientedEdge → ℤ) (hq : ∀ e, Measurable (fun ω => q ω e))
    (S : Finset OrientedEdge) : MeasurableSet {ω | certifiesCurrentComponent (q ω) S} := by
  classical
  let K : Prop := ∃ e ∈ S, ∀ f ∈ S, ∃ p : dualEdgeGraph.Walk e f, ∀ g ∈ p.support, g ∈ S
  let A : Set Ω := {ω | ∀ e : S, q ω e.val ≠ 0}
  let B : Set Ω := {ω | ∀ e : S, ∀ f : {f // f ∈ edgeNeighborFinset e.val ∧ f ∉ S},
    q ω f.val = 0}
  have hz (e : OrientedEdge) : MeasurableSet {ω | q ω e = 0} := hq e (measurableSet_singleton 0)
  have hA : MeasurableSet A := measurableSet_forall_countable fun e =>
    (hz e.val).compl
  have hB : MeasurableSet B := measurableSet_forall_countable fun _ =>
    measurableSet_forall_countable fun f => hz f.val
  have hK : MeasurableSet ({_ω : Ω | K} : Set Ω) := by by_cases h : K <;> simp [h]
  have he : {ω | certifiesCurrentComponent (q ω) S} = (A ∩ B) ∩ {_ω : Ω | K} := by
    ext ω
    simp only [certifiesCurrentComponent_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, A, B, K,
      Subtype.forall, and_imp]
    tauto
  rw [he]
  exact (hA.inter hB).inter hK

theorem measurable_certifiedFillValue {Ω : Type*} [MeasurableSpace Ω]
    (q : Ω → OrientedEdge → ℤ) (hq : ∀ e, Measurable (fun ω => q ω e))
    (S : Finset OrientedEdge) (I : Face) (x : Site) :
    Measurable (fun ω => certifiedFillValue (q ω) S I x) := by
  classical
  let v (ω : Ω) (e : S) := q ω e.val
  let f (u : S → ℤ) := primalFilling (translatedChainFilling (finiteEdgeChain S u)) I x
  have hv : Measurable v := measurable_pi_iff.mpr fun e => hq e.val
  have hf : Measurable f := measurable_of_countable _
  unfold certifiedFillValue
  exact Measurable.ite (measurableSet_certifiesCurrentComponent q hq S)
    (hf.comp hv) measurable_const

private theorem measurable_finsum_int {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (f : ι → Ω → ℤ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => ∑ᶠ i, f i ω) := by
  classical
  let K (S : Finset ι) : Set Ω := {ω | ∀ i : {i // i ∉ S}, f i.val ω = 0}
  have hK (S : Finset ι) : MeasurableSet (K S) :=
    measurableSet_forall_countable fun i => hf i.val (measurableSet_singleton 0)
  have hKS (ω : Ω) (S : Finset ι) :
      ω ∈ K S ↔ Function.support (fun i => f i ω) ⊆ (↑S : Set ι) := by
    constructor
    · intro h i hi
      by_contra hn
      exact hi (h ⟨i, hn⟩)
    · intro h i
      by_contra hi
      exact i.property (h hi)
  let F : Set Ω := ⋃ S : Finset ι, K S
  have hF : MeasurableSet F := MeasurableSet.iUnion hK
  have hFS (ω : Ω) : ω ∈ F ↔ (Function.support (fun i => f i ω)).Finite := by
    constructor
    · intro h
      obtain ⟨S, hS⟩ := Set.mem_iUnion.mp h
      exact S.finite_toSet.subset ((hKS ω S).mp hS)
    · intro h
      exact Set.mem_iUnion.mpr ⟨h.toFinset, (hKS ω h.toFinset).mpr
        fun i hi => h.mem_toFinset.mpr hi⟩
  have hzero (ω : Ω) (hω : ω ∉ F) : (∑ᶠ i, f i ω) = 0 :=
    finsum_of_infinite_support (f := fun i => f i ω) (mt (hFS ω).mpr hω)
  apply measurable_to_countable'
  intro z
  let U : Set Ω := ⋃ S : Finset ι, K S ∩ (fun ω => ∑ i ∈ S, f i ω) ⁻¹' {z}
  let E : Set Ω := if z = 0 then Fᶜ else ∅
  have hU : MeasurableSet U := MeasurableSet.iUnion fun S => (hK S).inter
    ((Finset.measurable_sum S fun i _ => hf i) (measurableSet_singleton z))
  have hE : MeasurableSet E := by by_cases h : z = 0 <;> simp [E, h, hF.compl]
  have he : (fun ω => ∑ᶠ i, f i ω) ⁻¹' ({z} : Set ℤ) = U ∪ E := by
    ext ω
    change (∑ᶠ i, f i ω) = z ↔ ω ∈ U ∨ ω ∈ E
    constructor
    · intro h
      by_cases hw : ω ∈ F
      · obtain ⟨S, hS⟩ := Set.mem_iUnion.mp hw
        left
        exact Set.mem_iUnion.mpr ⟨S, hS,
          (finsum_eq_sum_of_support_subset _ ((hKS ω S).mp hS)).symm.trans h⟩
      · have hz : z = 0 := h.symm.trans (hzero ω hw)
        right
        change ω ∈ (if z = 0 then Fᶜ else ∅)
        rw [ite_eq_left hz]
        exact hw
    · rintro (h | h)
      · obtain ⟨S, hS, hz⟩ := Set.mem_iUnion.mp h
        exact (finsum_eq_sum_of_support_subset _ ((hKS ω S).mp hS)).trans hz
      · by_cases hz : z = 0
        · rw [hz]
          change ω ∈ (if z = 0 then Fᶜ else ∅) at h
          rw [ite_eq_left hz] at h
          exact hzero ω h
        · change ω ∈ (if z = 0 then Fᶜ else ∅) at h
          simp only [ite_eq_right hz, Set.notMem_empty] at h
  rw [he]
  exact hU.union hE

theorem measurable_dualCurrent_coordinate {Ω : Type*} [MeasurableSpace Ω]
    (q : Ω → ThreeForm ℤ) (hq : ∀ c x, Measurable (fun ω => q ω c x)) (e : OrientedEdge) :
    Measurable (fun ω => dualCurrent (q ω) e) := by
  obtain ⟨y, i⟩ := e
  fin_cases i
  · simpa [dualCurrent] using hq .yzw (-y)
  · simpa [dualCurrent] using hq .xzw (-y)
  · simpa [dualCurrent] using hq .xyw (-y)
  · simpa [dualCurrent] using hq .xyz (-y)

theorem measurable_fillDefect_coordinate {Ω : Type*} [MeasurableSpace Ω]
    (q : Ω → ThreeForm ℤ) (hq : ∀ c x, Measurable (fun ω => q ω c x)) (I : Face) (x : Site) :
    Measurable (fun ω => fillDefect (q ω) I x) := by
  simp_rw [fillDefect_eq_finsum_certified]
  exact measurable_finsum_int _ (fun S =>
    measurable_certifiedFillValue _ (measurable_dualCurrent_coordinate q hq) S I x)

theorem measurable_repairedCutFlux_coordinate {N : ℕ} (I : Face) (x : Site) :
    Measurable (fun p : InfiniteConfig N × TwoForm ℝ =>
      repairedCutFlux (fun i y => p.1 (i, y)) p.2 I x) := by
  let a (p : InfiniteConfig N × TwoForm ℝ) :=
    liftFlux p.2 (plaquetteEigenangles (fun i y => p.1 (i, y)))
  have hy : Measurable (fun p : InfiniteConfig N × TwoForm ℝ => fillDefect (defect (a p)) I x) :=
    measurable_fillDefect_coordinate (fun p => defect (a p)) measurable_cutDefect_coordinate I x
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := measurable_of_countable _
  change Measurable (fun p => a p I x - (2 * Real.pi) * (fillDefect (defect (a p)) I x : ℝ))
  exact (measurable_cutFlux_coordinate I x).sub (measurable_const.mul (hcast.comp hy))

end

end GaplessYangMills

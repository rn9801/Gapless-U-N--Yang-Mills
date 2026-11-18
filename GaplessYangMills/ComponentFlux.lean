module

public import GaplessYangMills.Gluing
public import GaplessYangMills.GoodCubes
public import GaplessYangMills.FillingTranslations
public import GaplessYangMills.MarkedBoxes

/-!
# Locally finite repairs of the cut flux

The support of each signed-current component lies in one marked component.
Fill the signed component inside its own box. The almost-sure bound on marked
boxes makes the sums of these fillings locally finite for every allowed cut.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory Filter SimpleGraph
open scoped Topology

noncomputable section

private theorem component_eq_of_mem {V : Type*} (G : SimpleGraph V) {M : Set V} {x y : V}
    (hy : y ∈ markedComponent G M x) : markedComponent G M x = markedComponent G M y := by
  obtain ⟨p, hp⟩ := hy
  ext z
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨p.reverse.append q, fun v hv => ?_⟩
    rcases (Walk.mem_support_append_iff _ _).mp hv with h | h
    · exact hp v (by simpa only [Walk.support_reverse, List.mem_reverse] using h)
    · exact hq v h
  · rintro ⟨q, hq⟩
    exact ⟨p.append q, fun v hv =>
      ((Walk.mem_support_append_iff _ _).mp hv).elim (hp v) (hq v)⟩

/-- A component is indexed by its support set, so different possible roots
of the same component give just one index. -/
def CurrentComponent (q : OrientedEdge → ℤ) :=
  {C : Set OrientedEdge // ∃ e, q e ≠ 0 ∧
    C = markedComponent dualEdgeGraph (Function.support q) e}

theorem component_support {q : OrientedEdge → ℤ} (C : CurrentComponent q) :
    C.val ⊆ Function.support q := by
  obtain ⟨e, _, hC⟩ := C.property
  intro f hf
  rw [hC] at hf
  obtain ⟨p, hp⟩ := hf
  exact hp f p.end_mem_support

theorem component_connected {q : OrientedEdge → ℤ} (C : CurrentComponent q) :
    ∃ e ∈ C.val, ∀ f ∈ C.val, ∃ p : dualEdgeGraph.Walk e f, ∀ g ∈ p.support, g ∈ C.val := by
  obtain ⟨e, he, hC⟩ := C.property
  refine ⟨e, ?_, fun f hf => ?_⟩
  · rw [hC]
    exact ⟨.nil, by simpa using he⟩
  · rw [hC] at hf
    obtain ⟨p, hp⟩ := hf
    refine ⟨p, fun g hg => ?_⟩
    rw [hC]
    exact ⟨p.takeUntil g hg, fun v hv => hp v (p.support_takeUntil_subset_support hg hv)⟩

theorem component_saturated {q : OrientedEdge → ℤ} (C : CurrentComponent q) :
    CurrentSaturated q C.val := by
  obtain ⟨a, _, hC⟩ := C.property
  intro x e f he hf he₀ hf₀ h
  by_cases hne : e = f
  · rwa [← hne]
  rw [hC] at h ⊢
  obtain ⟨p, hp⟩ := h
  let hAdj : dualEdgeGraph.Adj e f := ⟨hne, x, he, hf⟩
  refine ⟨p.append hAdj.toWalk, fun g hg => ?_⟩
  rcases (Walk.mem_support_append_iff _ _).mp hg with hh | hh
  · exact hp g hh
  · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hh
    exact hh.elim (fun h => h ▸ he₀) (fun h => h ▸ hf₀)

/-- The signed current in the dual indexing of a primal three-cochain. -/
def dualCurrent (q : ThreeForm ℤ) (e : OrientedEdge) : ℤ :=
  if e.2 = 0 then q .yzw (-e.1) else if e.2 = 1 then -q .xzw (-e.1) else
    if e.2 = 2 then q .xyw (-e.1) else -q .xyz (-e.1)

theorem currentDivergence_dualCurrent (q : ThreeForm ℤ) (x : Site) :
    currentDivergence (dualCurrent q) x = d₃ q (-x) := by
  simp [currentDivergence, dualCurrent, Fin.sum_univ_succ, d₃, diff, neg_sub, add_comm]
  abel

theorem support_dualCurrent (q : ThreeForm ℤ) (e : OrientedEdge) :
    dualCurrent q e ≠ 0 ↔ q (edgeCubeEquiv e).1 (edgeCubeEquiv e).2 ≠ 0 := by
  obtain ⟨x, i⟩ := e
  fin_cases i <;> simp [dualCurrent, edgeCubeEquiv]

/-- The filling of a finite component depends only on its signed current. -/
def signedComponentFilling (q : OrientedEdge → ℤ) (C : CurrentComponent q) : SquareChain := by
  classical
  exact if h : (Function.support (restrictCurrent q C.val)).Finite then
    translatedChainFilling (Finsupp.ofSupportFinite (restrictCurrent q C.val) h)
  else 0

/-- Each chosen filling has the component as its boundary. Only finitely
many of the fillings contribute squares at a fixed base. -/
theorem signedComponentFillings_spec (q : OrientedEdge → ℤ)
    (hq : ∀ x, currentDivergence q x = 0) (M : Set OrientedEdge) (hM : Function.support q ⊆ M)
    (hfinite : ∀ e, (markedComponent dualEdgeGraph M e).Finite)
    (hboxes : ∀ x, (markedConnectedBoxes M x).Finite) :
    (∀ C : CurrentComponent q,
      (boundary₂ (signedComponentFilling q C) : OrientedEdge → ℤ) = restrictCurrent q C.val) ∧
      ∀ x : Site, {C | ∃ I : Face, signedComponentFilling q C (x, I) ≠ 0}.Finite := by
  classical
  have hC (C : CurrentComponent q) : C.val.Finite := by
    obtain ⟨e, _, h⟩ := C.property
    rw [h]
    exact (hfinite e).subset (fun f ⟨p, hp⟩ => ⟨p, fun g hg => hM (hp g hg)⟩)
  let S (C : CurrentComponent q) := (hC C).toFinset
  have hS (C : CurrentComponent q) (e : OrientedEdge) : e ∈ S C ↔ e ∈ C.val :=
    Set.Finite.mem_toFinset _
  have hfill (C : CurrentComponent q) :
      (boundary₂ (signedComponentFilling q C) : OrientedEdge → ℤ) = restrictCurrent q C.val ∧
        ∀ p ∈ (signedComponentFilling q C).support, edgeBoxContains (S C) p.1 := by
    have hsupp : (Function.support (restrictCurrent q C.val)).Finite :=
      (hC C).subset fun e he => by
        by_contra hn
        exact he (Set.indicator_of_notMem hn _)
    let r := Finsupp.ofSupportFinite (restrictCurrent q C.val) hsupp
    have hr : (r : OrientedEdge → ℤ) = restrictCurrent q C.val := Finsupp.ofSupportFinite_coe
    have hsupport (e : OrientedEdge) (he : e ∈ r.support) : e ∈ S C := by
      rw [hS]
      exact (show e ∈ Function.support (restrictCurrent q C.val) from
        hr ▸ Finsupp.mem_support_iff.mp he) |> fun h => by
          by_contra hn
          exact h (Set.indicator_of_notMem hn _)
    obtain ⟨e, he, _⟩ := component_connected C
    have hn : r.support.Nonempty := by
      refine ⟨e, Finsupp.mem_support_iff.mpr ?_⟩
      rw [congrFun hr e, restrictCurrent, Set.indicator_of_mem he]
      exact component_support C he
    have hdiv : boundary₁ r = 0 := by
      ext x
      rw [boundary₁_eq_currentDivergence, hr]
      exact currentDivergence_restrict q C.val (component_saturated C) hq x
    rw [signedComponentFilling, dite_eq_left hsupp]
    change (boundary₂ (translatedChainFilling r) : OrientedEdge → ℤ) = _ ∧ _
    obtain ⟨hsr, hbox, _⟩ := translatedChainFilling_spec r hdiv
    refine ⟨(congrArg (fun Q : EdgeChain => (Q : OrientedEdge → ℤ)) hsr).trans hr, fun p hp i => ?_⟩
    have hlo : r.support.inf' hn (fun e => e.1 i) ≤ p.1 i := by
      simpa only [edgeChainLower, dite_eq_left hn] using (hbox p hp).1 i
    have hhi : p.1 i ≤ r.support.sup' hn (fun e => (e.1 + step e.2) i) := by
      simpa only [edgeChainUpper, dite_eq_left hn] using (hbox p hp).2 i
    obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf' hn (fun f => f.1 i)
    obtain ⟨z, hz, hmax⟩ := Finset.exists_mem_eq_sup' hn (fun f => (f.1 + step f.2) i)
    exact ⟨⟨a.1, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (hsupport a ha)), hmin ▸ hlo⟩,
      ⟨z.1 + step z.2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (hsupport z hz)),
        hmax ▸ hhi⟩⟩
  refine ⟨fun C => (hfill C).1, fun x => ?_⟩
  have hinj : Function.Injective S := by
    intro C D he
    apply Subtype.ext
    ext e
    rw [← hS C e, ← hS D e, he]
  refine ((hboxes x).preimage hinj.injOn).subset ?_
  intro C h
  obtain ⟨I, hi⟩ := h
  obtain ⟨e, he, hconn⟩ := component_connected C
  refine ⟨fun f hf => hM (component_support C ((hS C f).mp hf)),
    (hfill C).2 (x, I) (Finsupp.mem_support_iff.mpr hi), e, (hS C e).mpr he, ?_⟩
  intro f hf
  obtain ⟨p, hp⟩ := hconn f ((hS C f).mp hf)
  exact ⟨p, fun g hg => (hS C g).mpr (hp g hg)⟩

theorem exists_locallyFinite_componentFillings (q : OrientedEdge → ℤ)
    (hq : ∀ x, currentDivergence q x = 0) (M : Set OrientedEdge) (hM : Function.support q ⊆ M)
    (hfinite : ∀ e, (markedComponent dualEdgeGraph M e).Finite)
    (hboxes : ∀ x, (markedConnectedBoxes M x).Finite) :
    ∃ Y : CurrentComponent q → SquareChain,
      (∀ C, (boundary₂ (Y C) : OrientedEdge → ℤ) = restrictCurrent q C.val) ∧
      ∀ x : Site, {C | ∃ I : Face, Y C (x, I) ≠ 0}.Finite :=
  ⟨signedComponentFilling q, signedComponentFillings_spec q hq M hM hfinite hboxes⟩

def fillDefect (q : ThreeForm ℤ) : TwoForm ℤ :=
  sumFillings (fun C : CurrentComponent (dualCurrent q) => primalFilling (signedComponentFilling _ C))

/-- A closed integer defect supported in the marked graph is the exterior
derivative of the sum of the chosen component fillings. -/
theorem d₂_fillDefect_of_markedBoxes (q : ThreeForm ℤ) (hq : d₃ q = 0)
    (M : Set OrientedEdge) (hM : Function.support (dualCurrent q) ⊆ M)
    (hfinite : ∀ e, (markedComponent dualEdgeGraph M e).Finite)
    (hboxes : ∀ x, (markedConnectedBoxes M x).Finite) :
    d₂ (fillDefect q) = q := by
  classical
  let r := dualCurrent q
  have hd (x : Site) : currentDivergence r x = 0 := by
    change currentDivergence (dualCurrent q) x = _
    rw [currentDivergence_dualCurrent, hq, Pi.zero_apply]
  obtain ⟨hY, hb⟩ := signedComponentFillings_spec r hd M hM hfinite hboxes
  let Yp (C : CurrentComponent r) := primalFilling (signedComponentFilling r C)
  have hlocal (I : Face) (x : Site) :
      (Function.support fun C => Yp C I x).Finite := by
    refine (hb (-x)).subset fun C hc => ?_
    cases I
    · exact ⟨.zw, by simpa [Yp, primalFilling, Function.mem_support] using hc⟩
    · exact ⟨.yw, by simpa [Yp, primalFilling, Function.mem_support] using hc⟩
    · exact ⟨.yz, by simpa [Yp, primalFilling, Function.mem_support] using hc⟩
    · exact ⟨.xw, by simpa [Yp, primalFilling, Function.mem_support] using hc⟩
    · exact ⟨.xz, by simpa [Yp, primalFilling, Function.mem_support] using hc⟩
    · exact ⟨.xy, by simpa [Yp, primalFilling, Function.mem_support] using hc⟩
  have hterm (C : CurrentComponent r) (c : Cube) (x : Site) :
      d₂ (Yp C) c x = if edgeCubeEquiv.symm (c, x) ∈ C.val then q c x else 0 := by
    change d₂ (primalFilling (signedComponentFilling r C)) c x = _
    rw [← boundary₂_primalFilling]
    cases c <;>
      simp [primalCurrent, edgeCubeEquiv, hY, restrictCurrent,
        Set.indicator_apply, r, dualCurrent] <;> split <;> simp_all
  change d₂ (sumFillings Yp) = q
  funext c x
  rw [d₂_sumFillings Yp hlocal]
  simp_rw [hterm]
  let e := edgeCubeEquiv.symm (c, x)
  by_cases hq₀ : q c x = 0
  · simp [hq₀]
  · have h₀ : r e ≠ 0 := (support_dualCurrent q e).mpr (by simpa only [e, Equiv.apply_symm_apply] using hq₀)
    let C₀ : CurrentComponent r := ⟨markedComponent dualEdgeGraph (Function.support r) e, e, h₀, rfl⟩
    have he₀ : e ∈ C₀.val := ⟨.nil, by simpa using h₀⟩
    rw [finsum_eq_single _ C₀]
    · exact ite_eq_left he₀
    · intro C hne
      apply ite_eq_right
      intro he
      obtain ⟨f, _, hC⟩ := C.property
      change e ∈ C.val at he
      rw [hC] at he
      exact hne (Subtype.ext (hC.trans (component_eq_of_mem dualEdgeGraph he)))

theorem exists_fluxFilling_of_markedBoxes (q : ThreeForm ℤ) (hq : d₃ q = 0)
    (M : Set OrientedEdge) (hM : Function.support (dualCurrent q) ⊆ M)
    (hfinite : ∀ e, (markedComponent dualEdgeGraph M e).Finite)
    (hboxes : ∀ x, (markedConnectedBoxes M x).Finite) :
    ∃ Y : TwoForm ℤ, d₂ Y = q :=
  ⟨fillDefect q, d₂_fillDefect_of_markedBoxes q hq M hM hfinite hboxes⟩

def repairedCutFlux {N : ℕ} (U : OneForm (UnitaryMatrix N)) (η : TwoForm ℝ) : TwoForm ℝ :=
  repairFlux fillDefect (liftFlux η (plaquetteEigenangles U))

theorem repairedCutFlux_central_links {N : ℕ} (hN : 0 < N) (U : OneForm (UnitaryMatrix N))
    (α : OneForm ℝ) (η : TwoForm ℝ) :
    repairedCutFlux (fun i x => centralPhase N (Circle.exp (α i x / N)) * U i x) η =
      repairedCutFlux U (shiftCuts η (d₁ α) N) + d₁ α :=
  repairFlux_central_links hN U α η fillDefect

/-- Almost every Wilson configuration admits locally finite repairs for
all cuts in the specified interval. -/
theorem repairedCutFlux_closed_periodicLimit_ae {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂(μ : Measure (InfiniteConfig N)), ∀ η : TwoForm ℝ, (∀ I x, |η I x| ≤ Real.pi / 16) →
      let a := liftFlux η (plaquetteEigenangles (fun i x => U (i, x)))
      d₂ (fillDefect (defect a)) = defect a ∧ d₂ (repairedCutFlux (fun i x => U (i, x)) η) = 0 := by
  filter_upwards [markedComponents_finite_periodicLimit hN hβ μ l hl hμ,
    markedConnectedBoxes_finite_periodicLimit hN hβ μ l hl hμ] with U hfinite hboxes
  intro η hη
  let A : OneForm (UnitaryMatrix N) := fun i x => U (i, x)
  let a := liftFlux η (plaquetteEigenangles A)
  have hcube : ∀ c x, Circle.exp (d₂ a c x) = 1 :=
    unitary_liftFlux_exp_closed A η _ (prod_exp_plaquetteEigenangles A)
  have hclosed : d₃ (defect a) = 0 := defect_closed a hcube
  have hs : Function.support (dualCurrent (defect a)) ⊆ {e | U ∈ markedDualLink badPlaquette e} := by
    intro e he
    apply has_bad_face_of_nonzero_defect U η (edgeCubeEquiv e) (fun p _ => hη p.1 p.2)
    exact (support_dualCurrent (defect a) e).mp he
  have hY := d₂_fillDefect_of_markedBoxes (defect a) hclosed _ hs hfinite hboxes
  exact ⟨hY, repairFlux_closed fillDefect a hcube hY⟩

theorem exists_fluxFilling_periodicLimit_ae {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂(μ : Measure (InfiniteConfig N)), ∀ η : TwoForm ℝ, (∀ I x, |η I x| ≤ Real.pi / 16) →
      let a := liftFlux η (plaquetteEigenangles (fun i x => U (i, x)))
      ∃ Y : TwoForm ℤ, d₂ Y = defect a ∧ d₂ (repairFlux (fun _ => Y) a) = 0 := by
  filter_upwards [repairedCutFlux_closed_periodicLimit_ae hN hβ μ l hl hμ] with U hU
  intro η hη
  obtain ⟨hfill, hc⟩ := hU η hη
  exact ⟨_, hfill, hc⟩

end

end GaplessYangMills

module

public import GaplessYangMills.CutLaw
public import GaplessYangMills.WilsonTranslations
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Gauge invariance and translations of the cut flux

The eigenangle lift depends on the conjugacy class of a holonomy. The
repair depends only on the signed current and commutes with translation.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory SimpleGraph

noncomputable section

def gaugeConfig {N : ℕ} (g : Site → UnitaryMatrix N) (U : InfiniteConfig N) : InfiniteConfig N :=
  fun (i, x) => g x * U (i, x) * (g (x + step i))⁻¹

theorem plaquetteHolonomy_gaugeConfig {N : ℕ} (g : Site → UnitaryMatrix N) (U : InfiniteConfig N)
    (I : Face) (x : Site) :
    plaquetteHolonomy (fun j y => gaugeConfig g U (j, y)) I x =
      g x * plaquetteHolonomy (fun j y => U (j, y)) I x * (g x)⁻¹ := by
  simp only [plaquetteHolonomy, gaugeConfig]
  rw [add_right_comm x (step I.axes.1) (step I.axes.2)]
  group

private theorem eigenAngleLift_conj {N : ℕ} (g U : UnitaryMatrix N) (η : ℝ) :
    eigenAngleLift (g * U * g⁻¹) η = eigenAngleLift U η := by
  have hinv : (g⁻¹).val * g.val = 1 :=
    congrArg (fun v : UnitaryMatrix N => v.val) (inv_mul_cancel g)
  have h : (g * U * g⁻¹).val.charpoly = U.val.charpoly := by
    change (g.val * U.val * (g⁻¹).val).charpoly = _
    rw [Matrix.charpoly_mul_comm, ← mul_assoc, hinv, one_mul]
  simp only [eigenAngleLift, h]

private theorem liftFlux_gaugeConfig {N : ℕ} (g : Site → UnitaryMatrix N) (U : InfiniteConfig N)
    (η : TwoForm ℝ) :
    liftFlux η (plaquetteEigenangles (fun j y => gaugeConfig g U (j, y))) =
      liftFlux η (plaquetteEigenangles (fun j y => U (j, y))) := by
  funext I x
  simp only [liftFlux_eq_eigenAngleLift, plaquetteHolonomy_gaugeConfig, eigenAngleLift_conj]

theorem repairedCutFlux_gaugeConfig {N : ℕ} (g : Site → UnitaryMatrix N) (U : InfiniteConfig N)
    (η : TwoForm ℝ) :
    repairedCutFlux (fun j y => gaugeConfig g U (j, y)) η =
      repairedCutFlux (fun j y => U (j, y)) η := by
  rw [repairedCutFlux, repairedCutFlux, liftFlux_gaugeConfig]

theorem averagedFlux_gaugeConfig {N : ℕ} (ν : Measure (TwoForm ℝ))
    (g : Site → UnitaryMatrix N) (U : InfiniteConfig N) :
    averagedFlux ν (gaugeConfig g U) = averagedFlux ν U := by
  funext I x
  simp only [averagedFlux, repairedCutFlux_gaugeConfig]

theorem averagedFluxApprox_gaugeConfig {N : ℕ} (ν : Measure (TwoForm ℝ)) (R : ℕ)
    (g : Site → UnitaryMatrix N) (U : InfiniteConfig N) :
    averagedFluxApprox ν R (gaugeConfig g U) = averagedFluxApprox ν R U := by
  funext I x
  simp only [averagedFluxApprox, repairedCutFluxApprox, liftFlux_gaugeConfig]

private theorem incident_translate (a : Site) (e : OrientedEdge) (x : Site) :
    incident (cellTranslation a Axis e) (x + a) ↔ incident e x := by
  change (e.1 + a = x + a ∨ (e.1 + a) + step e.2 = x + a) ↔
    e.1 = x ∨ e.1 + step e.2 = x
  simp only [add_right_comm e.1 a, add_left_inj]

private def edgeTranslationIso (a : Site) : dualEdgeGraph ≃g dualEdgeGraph where
  toEquiv := cellTranslation a Axis
  map_rel_iff' := by
    intro e f
    constructor
    · rintro ⟨hne, x, he, hf⟩
      have hx : x - a + a = x := sub_add_cancel x a
      rw [← hx] at he hf
      exact ⟨fun h => hne (congrArg (cellTranslation a Axis) h), x - a,
        (incident_translate a e _).mp he, (incident_translate a f _).mp hf⟩
    · rintro ⟨hne, x, he, hf⟩
      exact ⟨fun h => hne ((cellTranslation a Axis).injective h), x + a,
        (incident_translate a e x).mpr he, (incident_translate a f x).mpr hf⟩

private theorem markedComponent_image_iso {E : Type*} {G : SimpleGraph E} (φ : G ≃g G)
    (M : Set E) (e : E) :
    markedComponent G (φ.toEquiv '' M) (φ e) = φ.toEquiv '' markedComponent G M e := by
  ext y
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨φ.symm y, ⟨(p.map φ.symm.toHom).copy (φ.symm_apply_apply e) rfl, ?_⟩, φ.apply_symm_apply y⟩
    intro z hz
    rw [Walk.support_copy, Walk.support_map] at hz
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
    obtain ⟨v, hv, he⟩ := hp u hu
    have h : φ v = u := he
    rw [← h]
    change φ.symm (φ v) ∈ M
    rwa [φ.symm_apply_apply]
  · rintro ⟨y, ⟨p, hp⟩, rfl⟩
    refine ⟨p.map φ.toHom, fun z hz => ?_⟩
    rw [Walk.support_map] at hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    exact ⟨v, hp v hv, rfl⟩

private theorem support_comp_symm (q : OrientedEdge → ℤ) (e : OrientedEdge ≃ OrientedEdge) :
    Function.support (q ∘ e.symm) = e '' Function.support q := by
  ext u
  constructor
  · intro hu
    exact ⟨e.symm u, hu, e.apply_symm_apply u⟩
  · rintro ⟨v, hv, rfl⟩
    simpa only [Function.mem_support, Function.comp_apply, Equiv.symm_apply_apply] using hv

private theorem certifiesCurrentComponent_map (φ : dualEdgeGraph ≃g dualEdgeGraph)
    (q : OrientedEdge → ℤ) (S : Finset OrientedEdge) (h : certifiesCurrentComponent q S) :
    certifiesCurrentComponent (q ∘ φ.toEquiv.symm) (φ.toEquiv.finsetCongr S) := by
  obtain ⟨⟨C, e, he, hC⟩, hS⟩ := h
  let e' := φ.toEquiv
  have hc : e' '' C = markedComponent dualEdgeGraph (Function.support (q ∘ e'.symm)) (e' e) := by
    rw [hC, support_comp_symm]
    exact (markedComponent_image_iso φ (Function.support q) e).symm
  have hn : (q ∘ e'.symm) (e' e) ≠ 0 := by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using he
  refine ⟨⟨e' '' C, e' e, hn, hc⟩, ?_⟩
  change (↑(S.map e'.toEmbedding) : Set OrientedEdge) = e' '' C
  rw [Finset.coe_map, Equiv.coe_toEmbedding, hS]

private theorem certifiesCurrentComponent_translate_iff (a : Site)
    (q : OrientedEdge → ℤ) (S : Finset OrientedEdge) :
    certifiesCurrentComponent (q ∘ (cellTranslation a Axis).symm)
      ((cellTranslation a Axis).finsetCongr S) ↔ certifiesCurrentComponent q S := by
  let φ := edgeTranslationIso a
  let e := cellTranslation a Axis
  constructor
  · intro h
    have h' := certifiesCurrentComponent_map φ.symm (q ∘ e.symm) (e.finsetCongr S) h
    change certifiesCurrentComponent ((q ∘ e.symm) ∘ e) (e.finsetCongr.symm (e.finsetCongr S)) at h'
    have he : (q ∘ e.symm) ∘ e = q := by funext f; simp
    rwa [Equiv.symm_apply_apply, he] at h'
  · exact certifiesCurrentComponent_map φ q S

private theorem finiteEdgeChain_translate (a : Site) (q : OrientedEdge → ℤ) (S : Finset OrientedEdge) :
    finiteEdgeChain ((cellTranslation a Axis).finsetCongr S) (fun e => q ((cellTranslation a Axis).symm e.val)) =
      translateCells a Axis (finiteEdgeChain S (fun e => q e.val)) := by
  ext e
  let E := cellTranslation a Axis
  change finiteEdgeChain (E.finsetCongr S) (fun f => (q ∘ E.symm) f.val) e = _
  rw [congrFun (finiteEdgeChain_coe (q ∘ E.symm) (E.finsetCongr S)) e, translateCells_apply,
    congrFun (finiteEdgeChain_coe q S) (e.1 - a, e.2)]
  have hmem : e ∈ E.finsetCongr S ↔ E.symm e ∈ S := Finset.mem_map_equiv
  have hes : E.symm e = (e.1 - a, e.2) := rfl
  simp only [restrictCurrent, Set.indicator_apply, Finset.mem_coe, hmem, Function.comp_apply, hes]

private theorem primalFilling_translateCells (a : Site) (s : SquareChain) (I : Face) (x : Site) :
    primalFilling (translateCells a Face s) I x = primalFilling s I (x + a) := by
  have h : -x - a = -(x + a) := by abel
  cases I <;> simp only [primalFilling, translateCells_apply, h]

private theorem certifiedFillValue_translate (a : Site) (q : OrientedEdge → ℤ)
    (S : Finset OrientedEdge) (I : Face) (x : Site) :
    certifiedFillValue (q ∘ (cellTranslation a Axis).symm) ((cellTranslation a Axis).finsetCongr S) I x =
      certifiedFillValue q S I (x + a) := by
  classical
  simp only [certifiedFillValue, certifiesCurrentComponent_translate_iff, Function.comp_apply,
    finiteEdgeChain_translate, translatedChainFilling_translateCells, primalFilling_translateCells]

private theorem dualCurrent_translate (a : Site) (q : ThreeForm ℤ) :
    dualCurrent (fun c x => q c (x + a)) = dualCurrent q ∘ (cellTranslation a Axis).symm := by
  funext e
  have h : -(e.1 - a) = -e.1 + a := by abel
  change dualCurrent (fun c x => q c (x + a)) e = dualCurrent q (e.1 - a, e.2)
  simp only [dualCurrent, h]

theorem fillDefect_translate (a : Site) (q : ThreeForm ℤ) (I : Face) (x : Site) :
    fillDefect (fun c y => q c (y + a)) I x = fillDefect q I (x + a) := by
  rw [fillDefect_eq_finsum_certified, fillDefect_eq_finsum_certified, dualCurrent_translate]
  let e := (cellTranslation a Axis).finsetCongr
  rw [← finsum_comp_equiv e]
  exact finsum_congr fun S => certifiedFillValue_translate a (dualCurrent q) S I x

private theorem liftFlux_translate {N : ℕ} (a : Site) (U : InfiniteConfig N) (η : TwoForm ℝ) :
    liftFlux (fun I x => η I (x + a)) (plaquetteEigenangles (fun j y => translateConfig a U (j, y))) =
      fun I x => liftFlux η (plaquetteEigenangles (fun j y => U (j, y))) I (x + a) := by
  have hh (I : Face) (x : Site) :
      plaquetteHolonomy (fun j y => translateConfig a U (j, y)) I x =
        plaquetteHolonomy (fun j y => U (j, y)) I (x + a) := by
    cases I <;> simp only [plaquetteHolonomy, translateConfig, Face.axes, add_right_comm x]
  funext I x
  simp only [liftFlux_eq_eigenAngleLift, hh]

private theorem defect_translate (a : Site) (F : TwoForm ℝ) :
    defect (fun I x => F I (x + a)) = fun c x => defect F c (x + a) := by
  funext c x
  cases c <;> simp only [defect, d₂, diff, Pi.add_apply, Pi.sub_apply, add_right_comm x]

theorem repairedCutFlux_translate {N : ℕ} (a : Site) (U : InfiniteConfig N) (η : TwoForm ℝ)
    (I : Face) (x : Site) :
    repairedCutFlux (fun j y => translateConfig a U (j, y)) (fun J y => η J (y + a)) I x =
      repairedCutFlux (fun j y => U (j, y)) η I (x + a) := by
  simp only [repairedCutFlux, liftFlux_translate, repairFlux, Pi.sub_apply, defect_translate, fillDefect_translate]

def translateCutField (a : Site) : TwoForm ℝ ≃ᵐ TwoForm ℝ where
  toFun η I x := η I (x + a)
  invFun η I x := η I (x - a)
  left_inv η := by funext I x; simp
  right_inv η := by funext I x; simp
  measurable_toFun := measurable_pi_iff.mpr fun I => measurable_pi_iff.mpr fun x =>
    (measurable_pi_apply (x + a)).comp (measurable_pi_apply I)
  measurable_invFun := measurable_pi_iff.mpr fun I => measurable_pi_iff.mpr fun x =>
    (measurable_pi_apply (x - a)).comp (measurable_pi_apply I)

theorem translateCutField_preserving (a : Site) :
    MeasurePreserving (translateCutField a) iidCutLaw iidCutLaw := by
  let e : Plaquette ≃ Plaquette := (Equiv.refl Face).prodCongr (Equiv.addRight (-a))
  let shift := MeasurableEquiv.piCongrLeft (fun _ : Plaquette => ℝ) e
  have he : (translateCutField a : TwoForm ℝ → TwoForm ℝ) ∘ cutFieldEquiv =
      (cutFieldEquiv : (Plaquette → ℝ) → TwoForm ℝ) ∘ shift := by
    funext η I x
    change η (I, x + a) = shift η (I, x)
    have hidx : e (I, x + a) = (I, x) := by
      change (I, x + a + -a) = (I, x)
      simp
    rw [← hidx]
    exact (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℝ) e η (I, x + a)).symm
  refine ⟨(translateCutField a).measurable, ?_⟩
  rw [iidCutLaw, Measure.map_map (translateCutField a).measurable cutFieldEquiv.measurable, he,
    ← Measure.map_map cutFieldEquiv.measurable shift.measurable,
    Measure.infinitePi_map_piCongrLeft (fun _ : Plaquette => cutDisplacementLaw) e]

theorem iidAveragedFlux_translate {N : ℕ} (a : Site) (U : InfiniteConfig N) (I : Face) (x : Site) :
    averagedFlux iidCutLaw (translateConfig a U) I x = averagedFlux iidCutLaw U I (x + a) := by
  unfold averagedFlux
  rw [← (translateCutField_preserving a).integral_comp']
  exact integral_congr_ae (ae_of_all _ fun η => repairedCutFlux_translate a U η I x)

end

end GaplessYangMills

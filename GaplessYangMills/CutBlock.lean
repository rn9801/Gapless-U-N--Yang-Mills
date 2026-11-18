module

public import GaplessYangMills.CutLaw
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Finite blocks of the independent cuts

The cut field splits into a finite block with a smooth product density
with respect to Lebesgue measure, and an independent exterior field.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped ENNReal

noncomputable section

abbrev CutBlock (S : Finset Plaquette) := {p // p ∈ S} → ℝ
abbrev CutExterior (S : Finset Plaquette) := {p // p ∉ S} → ℝ

def cutBlockLaw (S : Finset Plaquette) : Measure (CutBlock S) :=
  Measure.pi fun _ => cutDisplacementLaw

def cutExteriorLaw (S : Finset Plaquette) : Measure (CutExterior S) :=
  Measure.infinitePi fun _ => cutDisplacementLaw

instance cutBlockLaw_probability (S : Finset Plaquette) : IsProbabilityMeasure (cutBlockLaw S) := by
  unfold cutBlockLaw
  infer_instance

instance cutExteriorLaw_probability (S : Finset Plaquette) : IsProbabilityMeasure (cutExteriorLaw S) := by
  unfold cutExteriorLaw
  infer_instance

def splitCutField (S : Finset Plaquette) : TwoForm ℝ ≃ᵐ CutBlock S × CutExterior S :=
  cutFieldEquiv.symm.trans (MeasurableEquiv.piEquivPiSubtypeProd (fun _ => ℝ) (· ∈ S))

theorem splitCutField_symm_apply (S : Finset Plaquette) (y : CutBlock S) (z : CutExterior S)
    (p : Plaquette) :
    (splitCutField S).symm (y, z) p.1 p.2 = if h : p ∈ S then y ⟨p, h⟩ else z ⟨p, h⟩ := rfl

theorem splitCutField_symm_preserving (S : Finset Plaquette) :
    MeasurePreserving (splitCutField S).symm ((cutBlockLaw S).prod (cutExteriorLaw S)) iidCutLaw := by
  let e := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Plaquette => ℝ) (· ∈ S)).symm
  have hE : ((cutBlockLaw S).prod (cutExteriorLaw S)).map e =
      Measure.infinitePi fun _ : Plaquette => cutDisplacementLaw := by
    apply Measure.eq_infinitePi (fun _ => cutDisplacementLaw)
    intro A s hs
    let B := A.preimage (Subtype.val : {p // p ∈ S} → Plaquette) Subtype.val_injective.injOn
    let C := A.preimage (Subtype.val : {p // p ∉ S} → Plaquette) Subtype.val_injective.injOn
    have he : e ⁻¹' Set.pi (↑A : Set Plaquette) s =
        (Set.pi ↑B fun p => s p.val) ×ˢ (Set.pi ↑C fun p => s p.val) := by
      ext ⟨y, z⟩
      constructor
      · intro h
        refine ⟨fun p hp => ?_, fun p hp => ?_⟩
        · have h₀ := h p.val (Finset.mem_preimage.mp hp)
          change (if h : p.val ∈ S then y ⟨p.val, h⟩ else z ⟨p.val, h⟩) ∈ s p.val at h₀
          simpa only [dite_eq_left p.property] using h₀
        · have h₀ := h p.val (Finset.mem_preimage.mp hp)
          change (if h : p.val ∈ S then y ⟨p.val, h⟩ else z ⟨p.val, h⟩) ∈ s p.val at h₀
          simpa only [dite_eq_right p.property] using h₀
      · rintro ⟨hy, hz⟩ p hp
        change (if h : p ∈ S then y ⟨p, h⟩ else z ⟨p, h⟩) ∈ s p
        by_cases h : p ∈ S
        · rw [dite_eq_left h]
          exact hy ⟨p, h⟩ (Finset.mem_preimage.mpr hp)
        · rw [dite_eq_right h]
          exact hz ⟨p, h⟩ (Finset.mem_preimage.mpr hp)
    have hB : B.map ⟨Subtype.val, Subtype.val_injective⟩ = A.filter (· ∈ S) := by
      ext p
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_preimage, Finset.mem_filter, B]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨hq, q.property⟩
      · rintro ⟨hp, hm⟩
        exact ⟨⟨p, hm⟩, hp, rfl⟩
    have hC : C.map ⟨Subtype.val, Subtype.val_injective⟩ = A.filter (· ∉ S) := by
      ext p
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_preimage, Finset.mem_filter, C]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨hq, q.property⟩
      · rintro ⟨hp, hm⟩
        exact ⟨⟨p, hm⟩, hp, rfl⟩
    rw [e.map_apply, he, Measure.prod_prod, cutBlockLaw,
      ← Measure.infinitePi_eq_pi, cutExteriorLaw,
      Measure.infinitePi_pi _ (fun p _ => hs p.val), Measure.infinitePi_pi _ (fun p _ => hs p.val)]
    calc
      _ = (∏ p ∈ B.map ⟨Subtype.val, Subtype.val_injective⟩, cutDisplacementLaw (s p)) *
          ∏ p ∈ C.map ⟨Subtype.val, Subtype.val_injective⟩, cutDisplacementLaw (s p) := by
        rw [Finset.prod_map, Finset.prod_map]
        rfl
      _ = _ := by rw [hB, hC, Finset.prod_filter_mul_prod_filter_not]
  refine ⟨(splitCutField S).symm.measurable, ?_⟩
  change Measure.map (cutFieldEquiv ∘ e) _ = iidCutLaw
  rw [← Measure.map_map cutFieldEquiv.measurable e.measurable, hE]
  rfl

def cutBlockDensity (S : Finset Plaquette) (y : CutBlock S) : ℝ :=
  ∏ p : {p // p ∈ S}, cutDensity (y p)

theorem cutBlockDensity_nonneg (S : Finset Plaquette) (y : CutBlock S) : 0 ≤ cutBlockDensity S y :=
  Finset.prod_nonneg fun p _ => cutDensity_nonneg (y p)

theorem continuous_cutBlockDensity (S : Finset Plaquette) : Continuous (cutBlockDensity S) :=
  continuous_finsetProd _ fun p _ => (cutDensity_contDiff 0).continuous.comp (continuous_apply p)

theorem cutBlockLaw_eq_withDensity (S : Finset Plaquette) :
    cutBlockLaw S = volume.withDensity (fun y => ENNReal.ofReal (cutBlockDensity S y)) := by
  unfold cutBlockLaw
  apply Measure.pi_eq
  intro s hs
  let f (p : {p // p ∈ S}) := (s p).indicator cutDensity
  have hf₀ (p : {p // p ∈ S}) (u : ℝ) : 0 ≤ f p u :=
    Set.indicator_nonneg (fun u _ => cutDensity_nonneg u) _
  have hf (p : {p // p ∈ S}) : Integrable (f p) volume :=
    (cutBump.integrable_normed : Integrable cutDensity volume).indicator (hs p)
  have hprod : Integrable (fun y : CutBlock S => ∏ p, f p (y p)) volume := Integrable.fintype_prod hf
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hI (y : CutBlock S) : (Set.univ.pi s).indicator (fun z => ENNReal.ofReal (cutBlockDensity S z)) y =
      ENNReal.ofReal (∏ p, f p (y p)) := by
    by_cases hy : y ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hy]
      simp only [cutBlockDensity]
      congr 1
      exact Finset.prod_congr rfl fun p _ => (Set.indicator_of_mem (hy p (Set.mem_univ p)) _).symm
    · obtain ⟨p, hp⟩ : ∃ p, y p ∉ s p := by simpa only [Set.mem_univ_pi, not_forall] using hy
      rw [Set.indicator_of_notMem hy, Finset.prod_eq_zero (Finset.mem_univ p)
        (Set.indicator_of_notMem hp _), ENNReal.ofReal_zero]
  simp_rw [hI]
  rw [← ofReal_integral_eq_lintegral_ofReal hprod (ae_of_all _ fun y => Finset.prod_nonneg fun p _ => hf₀ p (y p)),
    integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun p _ => integral_nonneg (hf₀ p))]
  apply Finset.prod_congr rfl
  intro p _
  rw [ofReal_integral_eq_lintegral_ofReal (hf p) (ae_of_all _ (hf₀ p)), cutDisplacementLaw,
    withDensity_apply _ (hs p), ← lintegral_indicator (hs p)]
  apply lintegral_congr
  intro u
  by_cases hu : u ∈ s p <;> simp [f, hu, Set.indicator_of_mem, Set.indicator_of_notMem]

def shiftCutBlock (S : Finset Plaquette) (v : CutBlock S) (η : TwoForm ℝ) : TwoForm ℝ :=
  (splitCutField S).symm ((splitCutField S η).1 - v, (splitCutField S η).2)

theorem shiftCutBlock_symm_apply (S : Finset Plaquette) (v : CutBlock S)
    (y : CutBlock S) (z : CutExterior S) :
    shiftCutBlock S v ((splitCutField S).symm (y, z)) = (splitCutField S).symm (y - v, z) := by
  simp only [shiftCutBlock, MeasurableEquiv.apply_symm_apply]

theorem cutExteriorLaw_ae_abs_le (S : Finset Plaquette) :
    ∀ᵐ z ∂cutExteriorLaw S, ∀ p, |z p| ≤ Real.pi / 32 := by
  apply ae_all_iff.mpr
  intro p
  have hm := measurePreserving_eval_infinitePi (fun _ : {p // p ∉ S} => cutDisplacementLaw) p
  have h : ∀ᵐ u ∂(cutExteriorLaw S).map (fun z => z p), |u| ≤ Real.pi / 32 := by
    rw [show (cutExteriorLaw S).map (fun z => z p) = cutDisplacementLaw from hm.map_eq]
    exact cutDisplacementLaw_ae_abs_le
  exact ae_of_ae_map hm.measurable.aemeasurable h

/-- Changing the integration variables for a finite cut shift leaves
the exterior law fixed and translates the block density. -/
theorem integral_iidCutLaw_shiftCutBlock (S : Finset Plaquette) (v : CutBlock S)
    (f : TwoForm ℝ → ℝ) :
    (∫ η, f (shiftCutBlock S v η) ∂iidCutLaw) =
      ∫ p : CutBlock S × CutExterior S, cutBlockDensity S (p.1 + v) * f ((splitCutField S).symm p)
        ∂(volume.prod (cutExteriorLaw S)) := by
  rw [← (splitCutField_symm_preserving S).integral_comp']
  have hD : Measurable (fun y : CutBlock S => ENNReal.ofReal (cutBlockDensity S y)) :=
    (continuous_cutBlockDensity S).measurable.ennreal_ofReal
  rw [cutBlockLaw_eq_withDensity, prod_withDensity_left hD]
  have hD' : Measurable (fun p : CutBlock S × CutExterior S => ENNReal.ofReal (cutBlockDensity S p.1)) :=
    hD.comp measurable_fst
  rw [integral_withDensity_eq_integral_toReal_smul hD' (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  let e := (MeasurableEquiv.addRight v).prodCongr (MeasurableEquiv.refl (CutExterior S))
  have he : MeasurePreserving e (volume.prod (cutExteriorLaw S)) (volume.prod (cutExteriorLaw S)) :=
    (measurePreserving_add_right (volume : Measure (CutBlock S)) v).prod (MeasurePreserving.id _)
  rw [← he.integral_comp']
  apply integral_congr_ae
  refine ae_of_all _ fun ⟨y, z⟩ => ?_
  change (ENNReal.ofReal (cutBlockDensity S (y + v))).toReal *
    f (shiftCutBlock S v ((splitCutField S).symm (y + v, z))) = _
  rw [ENNReal.toReal_ofReal (cutBlockDensity_nonneg S _), shiftCutBlock_symm_apply, add_sub_cancel_right]

end

end GaplessYangMills

module

public import GaplessYangMills.FiniteWilson
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Conditional resampling in finite Wilson volume

At fixed exterior links, the inside links have the Wilson density with respect
to their product Haar measure, divided by its partition function.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped ENNReal

noncomputable section

abbrev PeriodicBlock {L : ℕ} (N : ℕ) (Λ : Finset (TorusLink L)) :=
  {e // e ∈ Λ} → UnitaryMatrix N

abbrev PeriodicExterior {L : ℕ} (N : ℕ) (Λ : Finset (TorusLink L)) :=
  {e // e ∉ Λ} → UnitaryMatrix N

def splitPeriodicLinks {L N : ℕ} (Λ : Finset (TorusLink L)) :
    TorusConfig L N ≃ᵐ PeriodicBlock N Λ × PeriodicExterior N Λ := by
  classical
  exact MeasurableEquiv.piEquivPiSubtypeProd (fun _ => UnitaryMatrix N) (· ∈ Λ)

def blockHaar {L N : ℕ} [NeZero L] (Λ : Finset (TorusLink L)) : Measure (PeriodicBlock N Λ) :=
  Measure.pi fun _ => unitaryHaar N

def exteriorHaar {L N : ℕ} [NeZero L] (Λ : Finset (TorusLink L)) :
    Measure (PeriodicExterior N Λ) :=
  Measure.pi fun _ => unitaryHaar N

instance blockHaar_probability {L N : ℕ} [NeZero L] (Λ : Finset (TorusLink L)) :
    IsProbabilityMeasure (blockHaar (N := N) Λ) := by
  unfold blockHaar
  infer_instance

instance exteriorHaar_probability {L N : ℕ} [NeZero L] (Λ : Finset (TorusLink L)) :
    IsProbabilityMeasure (exteriorHaar (N := N) Λ) := by
  unfold exteriorHaar
  infer_instance

theorem splitPeriodicLinks_preserving {L N : ℕ} [NeZero L]
    (Λ : Finset (TorusLink L)) :
    MeasurePreserving (splitPeriodicLinks (N := N) Λ) (periodicHaar L N)
      ((blockHaar Λ).prod (exteriorHaar Λ)) := by
  classical
  have hfin : Finset.Subtype.fintype Λ = Subtype.fintype (· ∈ Λ) := Subsingleton.elim _ _
  simp only [splitPeriodicLinks, periodicHaar, blockHaar, exteriorHaar]
  rw [hfin]
  exact measurePreserving_piEquivPiSubtypeProd (fun _ => unitaryHaar N) (· ∈ Λ)

def periodicBlockWeight {L N : ℕ} [NeZero L] (Λ : Finset (TorusLink L)) (β : ℝ)
    (z : PeriodicBlock N Λ × PeriodicExterior N Λ) : ℝ≥0∞ :=
  periodicWeight β ((splitPeriodicLinks Λ).symm z)

theorem periodicBlockWeight_measurable {L N : ℕ} [NeZero L]
    (Λ : Finset (TorusLink L)) (β : ℝ) :
    Measurable (periodicBlockWeight (N := N) Λ β) :=
  (periodicWeight_measurable β).comp (splitPeriodicLinks Λ).symm.measurable

def periodicBlockPartition {L N : ℕ} [NeZero L] (Λ : Finset (TorusLink L)) (β : ℝ)
    (x : PeriodicExterior N Λ) : ℝ≥0∞ :=
  ∫⁻ y, periodicBlockWeight Λ β (y, x) ∂blockHaar Λ

theorem periodicBlockPartition_ne_zero {L N : ℕ} [NeZero L]
    (Λ : Finset (TorusLink L)) (β : ℝ) (x : PeriodicExterior N Λ) :
    periodicBlockPartition Λ β x ≠ 0 := by
  unfold periodicBlockPartition
  have h : Measurable (fun y => periodicBlockWeight Λ β (y, x)) :=
    (periodicBlockWeight_measurable (N := N) Λ β).comp (measurable_id.prodMk measurable_const)
  apply ne_of_gt
  refine (lintegral_pos_iff_support h).mpr ?_
  simp [Function.support, periodicBlockWeight, periodicWeight, Real.exp_pos]

theorem periodicBlockPartition_ne_top {L N : ℕ} [NeZero L]
    (Λ : Finset (TorusLink L)) (β : ℝ) (x : PeriodicExterior N Λ) :
    periodicBlockPartition Λ β x ≠ ⊤ := by
  have hc : Continuous (fun U : TorusConfig L N => Real.exp (periodicLogWeight β U)) :=
    Real.continuous_exp.comp (continuous_periodicLogWeight β)
  obtain ⟨C, hC⟩ := (isCompact_univ.image hc).bddAbove
  have h (y : PeriodicBlock N Λ) : periodicBlockWeight Λ β (y, x) ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (hC ⟨_, Set.mem_univ _, rfl⟩)
  exact ((lintegral_mono h).trans_lt (by simp)).ne

/-- Resample the indicated links with the exterior fixed. -/
def periodicBlockExpectation {L N : ℕ} [NeZero L] (Λ : Finset (TorusLink L)) (β : ℝ)
    (f : TorusConfig L N → ℝ≥0∞) (x : PeriodicExterior N Λ) : ℝ≥0∞ :=
  (periodicBlockPartition Λ β x)⁻¹ *
    ∫⁻ y, periodicBlockWeight Λ β (y, x) * f ((splitPeriodicLinks Λ).symm (y, x)) ∂blockHaar Λ

theorem periodicBlockExpectation_measurable {L N : ℕ} [NeZero L]
    (Λ : Finset (TorusLink L)) (β : ℝ) {f : TorusConfig L N → ℝ≥0∞} (hf : Measurable f) :
    Measurable (periodicBlockExpectation Λ β f) := by
  have hw := periodicBlockWeight_measurable (N := N) Λ β
  have h := hw.mul (hf.comp (splitPeriodicLinks Λ).symm.measurable)
  exact (hw.lintegral_prod_left').inv.mul h.lintegral_prod_left'

private theorem lintegral_periodicWilson_split {L N : ℕ} [NeZero L]
    (Λ : Finset (TorusLink L)) (β : ℝ) {f : TorusConfig L N → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ U, f U ∂periodicWilson L N β) =
      (periodicPartition L N β)⁻¹ *
        ∫⁻ z, periodicBlockWeight Λ β z * f ((splitPeriodicLinks Λ).symm z)
          ∂(blockHaar Λ).prod (exteriorHaar Λ) := by
  rw [periodicWilson, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (periodicWeight_measurable β) hf]
  have h := ((splitPeriodicLinks_preserving (N := N) Λ).symm (splitPeriodicLinks Λ)).lintegral_comp
    ((periodicWeight_measurable β).mul hf)
  exact congrArg ((periodicPartition L N β)⁻¹ * ·) h.symm

/-- The normalized block law preserves Wilson expectations against every
measurable test function of the exterior links. -/
theorem lintegral_periodicWilson_resample {L N : ℕ} [NeZero L]
    (Λ : Finset (TorusLink L)) (β : ℝ) {f : TorusConfig L N → ℝ≥0∞}
    (hf : Measurable f) {g : PeriodicExterior N Λ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ U, f U * g (splitPeriodicLinks Λ U).2 ∂periodicWilson L N β) =
      ∫⁻ U, periodicBlockExpectation Λ β f (splitPeriodicLinks Λ U).2 *
        g (splitPeriodicLinks Λ U).2 ∂periodicWilson L N β := by
  let e := splitPeriodicLinks (N := N) Λ
  have he : Measurable (fun U => (e U).2) := measurable_snd.comp e.measurable
  have hp := periodicBlockExpectation_measurable Λ β hf
  have hl : Measurable (fun U => f U * g (e U).2) := hf.mul (hg.comp he)
  have hr : Measurable (fun U => periodicBlockExpectation Λ β f (e U).2 * g (e U).2) :=
    (hp.comp he).mul (hg.comp he)
  change (∫⁻ U, f U * g (e U).2 ∂periodicWilson L N β) =
    ∫⁻ U, periodicBlockExpectation Λ β f (e U).2 * g (e U).2 ∂periodicWilson L N β
  rw [lintegral_periodicWilson_split Λ β hl, lintegral_periodicWilson_split Λ β hr]
  have hsplit (z : PeriodicBlock N Λ × PeriodicExterior N Λ) :
      e ((splitPeriodicLinks Λ).symm z) = z := e.apply_symm_apply z
  simp only [hsplit]
  congr 1
  let W := periodicBlockWeight (N := N) Λ β
  let F : PeriodicBlock N Λ × PeriodicExterior N Λ → ℝ≥0∞ := fun z => f (e.symm z)
  have hw : Measurable W := periodicBlockWeight_measurable Λ β
  have hF : Measurable F := hf.comp e.symm.measurable
  have hleft : Measurable (fun z => W z * (F z * g z.2)) :=
    hw.mul (hF.mul (hg.comp measurable_snd))
  have hright : Measurable (fun z => W z * (periodicBlockExpectation Λ β f z.2 * g z.2)) :=
    hw.mul ((hp.comp measurable_snd).mul (hg.comp measurable_snd))
  change (∫⁻ z, W z * (F z * g z.2) ∂(blockHaar Λ).prod (exteriorHaar Λ)) =
    ∫⁻ z, W z * (periodicBlockExpectation Λ β f z.2 * g z.2) ∂(blockHaar Λ).prod (exteriorHaar Λ)
  rw [lintegral_prod_symm' _ hleft, lintegral_prod_symm' _ hright]
  refine lintegral_congr fun x => ?_
  have hs : Measurable (fun y : PeriodicBlock N Λ => (y, x)) :=
    measurable_id.prodMk measurable_const
  have hW : Measurable (fun y => W (y, x)) := hw.comp hs
  have hWF : Measurable (fun y => W (y, x) * F (y, x)) := (hw.mul hF).comp hs
  have hWP : Measurable (fun y => W (y, x) * periodicBlockExpectation Λ β f x) :=
    hW.mul measurable_const
  change (∫⁻ y, W (y, x) * (F (y, x) * g x) ∂blockHaar Λ) =
    ∫⁻ y, W (y, x) * (periodicBlockExpectation Λ β f x * g x) ∂blockHaar Λ
  simp only [← mul_assoc (W _)]
  rw [lintegral_mul_const (g x) hWF, lintegral_mul_const (g x) hWP,
    lintegral_mul_const (periodicBlockExpectation Λ β f x) hW]
  change _ = periodicBlockPartition Λ β x * periodicBlockExpectation Λ β f x * g x
  rw [periodicBlockExpectation, ← mul_assoc,
    ENNReal.mul_inv_cancel (periodicBlockPartition_ne_zero Λ β x)
      (periodicBlockPartition_ne_top Λ β x), one_mul]

/-- The four positive links used by a periodic plaquette. -/
def periodicBoundaryLinks {L : ℕ} [NeZero L] (p : Face × TorusSite L) :
    Finset (TorusLink L) :=
  {(p.1.axes.1, p.2), (p.1.axes.2, p.2 + torusStep L p.1.axes.1),
    (p.1.axes.1, p.2 + torusStep L p.1.axes.2), (p.1.axes.2, p.2)}

theorem periodicHolonomy_congr {L N : ℕ} [NeZero L] {U V : TorusConfig L N}
    (p : Face × TorusSite L) (h : ∀ e ∈ periodicBoundaryLinks p, U e = V e) :
    periodicHolonomy U p.1 p.2 = periodicHolonomy V p.1 p.2 := by
  have h₁ := h (p.1.axes.1, p.2) (by simp [periodicBoundaryLinks])
  have h₂ := h (p.1.axes.2, p.2 + torusStep L p.1.axes.1) (by simp [periodicBoundaryLinks])
  have h₃ := h (p.1.axes.1, p.2 + torusStep L p.1.axes.2) (by simp [periodicBoundaryLinks])
  have h₄ := h (p.1.axes.2, p.2) (by simp [periodicBoundaryLinks])
  obtain ⟨I, x⟩ := p
  cases I <;> simp only [periodicHolonomy, Face.axes] at * <;> rw [h₁, h₂, h₃, h₄]

def periodicAffectedPlaquettes {L : ℕ} [NeZero L] (Λ : Finset (TorusLink L)) :
    Finset (Face × TorusSite L) :=
  Finset.univ.filter fun p => ¬ Disjoint (periodicBoundaryLinks p) Λ

private theorem joinPeriodic_eq_exterior {L N : ℕ} {Λ : Finset (TorusLink L)}
    (y : PeriodicBlock N Λ) (x : PeriodicExterior N Λ) {e : TorusLink L} (he : e ∉ Λ) :
    (splitPeriodicLinks Λ).symm (y, x) e = x ⟨e, he⟩ := by
  have h := (splitPeriodicLinks (N := N) Λ).apply_symm_apply (y, x)
  exact congrArg (fun z : PeriodicBlock N Λ × PeriodicExterior N Λ => z.2 ⟨e, he⟩) h

private theorem periodicHolonomy_eq_of_exterior {L N : ℕ} [NeZero L]
    {Λ : Finset (TorusLink L)} (p : Face × TorusSite L)
    (hp : p ∉ periodicAffectedPlaquettes Λ) (x : PeriodicExterior N Λ)
    (y y' : PeriodicBlock N Λ) :
    periodicHolonomy ((splitPeriodicLinks Λ).symm (y, x)) p.1 p.2 =
      periodicHolonomy ((splitPeriodicLinks Λ).symm (y', x)) p.1 p.2 := by
  have hd : Disjoint (periodicBoundaryLinks p) Λ := by
    by_contra hn
    exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
  apply periodicHolonomy_congr p
  intro e he
  rw [joinPeriodic_eq_exterior y x (Finset.disjoint_left.mp hd he),
    joinPeriodic_eq_exterior y' x (Finset.disjoint_left.mp hd he)]

/-- Only the plaquettes touching the resampled block appear in this weight. -/
def periodicLocalWeight {L N : ℕ} [NeZero L] (Λ : Finset (TorusLink L)) (β : ℝ)
    (z : PeriodicBlock N Λ × PeriodicExterior N Λ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((N : ℝ) * β *
    ∑ p ∈ periodicAffectedPlaquettes Λ,
      (periodicHolonomy ((splitPeriodicLinks Λ).symm z) p.1 p.2).val.trace.re))

private theorem periodicBlockWeight_factor {L N : ℕ} [NeZero L]
    (Λ : Finset (TorusLink L)) (β : ℝ) (x : PeriodicExterior N Λ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ y : PeriodicBlock N Λ,
      periodicBlockWeight Λ β (y, x) = c * periodicLocalWeight Λ β (y, x) := by
  let S := periodicAffectedPlaquettes Λ
  let Y (y : PeriodicBlock N Λ) : TorusConfig L N := (splitPeriodicLinks Λ).symm (y, x)
  let H (y : PeriodicBlock N Λ) (p : Face × TorusSite L) : ℝ :=
    (periodicHolonomy (Y y) p.1 p.2).val.trace.re
  let y₀ : PeriodicBlock N Λ := fun _ => 1
  let out := (N : ℝ) * β * ∑ p ∈ Finset.univ \ S, H y₀ p
  refine ⟨ENNReal.ofReal (Real.exp out), by simp [Real.exp_pos], ENNReal.ofReal_ne_top, ?_⟩
  intro y
  have hrest : ∑ p ∈ Finset.univ \ S, H y p = ∑ p ∈ Finset.univ \ S, H y₀ p := by
    apply Finset.sum_congr rfl
    intro p hp
    exact congrArg (fun U : UnitaryMatrix N => U.val.trace.re)
      (periodicHolonomy_eq_of_exterior p (Finset.mem_sdiff.mp hp).2 x y y₀)
  have hall : periodicLogWeight β (Y y) = out + (N : ℝ) * β * ∑ p ∈ S, H y p := by
    change (N : ℝ) * β * (∑ p, H y p) = _
    rw [← Finset.sum_sdiff (f := H y) (Finset.subset_univ S), mul_add, hrest]
  change ENNReal.ofReal (Real.exp (periodicLogWeight β (Y y))) =
    ENNReal.ofReal (Real.exp out) * ENNReal.ofReal (Real.exp ((N : ℝ) * β * ∑ p ∈ S, H y p))
  rw [hall, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- The exterior-only weight cancels from the conditional resampling law. -/
theorem periodicBlockExpectation_eq_local {L N : ℕ} [NeZero L]
    (Λ : Finset (TorusLink L)) (β : ℝ) (f : TorusConfig L N → ℝ≥0∞)
    (x : PeriodicExterior N Λ) :
    periodicBlockExpectation Λ β f x =
      (∫⁻ y, periodicLocalWeight Λ β (y, x) ∂blockHaar Λ)⁻¹ *
        ∫⁻ y, periodicLocalWeight Λ β (y, x) * f ((splitPeriodicLinks Λ).symm (y, x)) ∂blockHaar Λ := by
  obtain ⟨c, hc₀, hctop, hfac⟩ := periodicBlockWeight_factor Λ β x
  simp only [periodicBlockExpectation, periodicBlockPartition, hfac, mul_assoc c]
  rw [lintegral_const_mul' _ _ hctop, lintegral_const_mul' _ _ hctop,
    ENNReal.mul_inv (Or.inl hc₀) (Or.inl hctop)]
  calc
    _ = (c⁻¹ * c) *
      ((∫⁻ y, periodicLocalWeight Λ β (y, x) ∂blockHaar Λ)⁻¹ *
        ∫⁻ y, periodicLocalWeight Λ β (y, x) * f ((splitPeriodicLinks Λ).symm (y, x)) ∂blockHaar Λ) := by
      ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hc₀ hctop, one_mul]

end

end GaplessYangMills

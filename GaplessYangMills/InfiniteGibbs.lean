module

public import GaplessYangMills.BadEvents
public import GaplessYangMills.LocalWilsonGeometry
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Conditional Wilson resampling on the infinite lattice

The resampling kernel replaces the links of a finite block with their
locally normalized Wilson density and keeps the exterior fixed.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal Topology

noncomputable section

abbrev InfiniteBlock (N : ℕ) (Λ : Finset InfiniteLink) :=
  {e // e ∈ Λ} → UnitaryMatrix N

def infiniteBlockHaar {N : ℕ} (Λ : Finset InfiniteLink) : Measure (InfiniteBlock N Λ) :=
  Measure.pi fun _ => unitaryHaar N

instance infiniteBlockHaar_probability {N : ℕ} (Λ : Finset InfiniteLink) :
    IsProbabilityMeasure (infiniteBlockHaar (N := N) Λ) := by
  unfold infiniteBlockHaar
  infer_instance

def replaceLinks {N : ℕ} (Λ : Finset InfiniteLink) (U : InfiniteConfig N) (y : InfiniteBlock N Λ) :
    InfiniteConfig N :=
  fun e => if he : e ∈ Λ then y ⟨e, he⟩ else U e

theorem continuous_replaceLinks {N : ℕ} (Λ : Finset InfiniteLink) :
    Continuous (fun z : InfiniteConfig N × InfiniteBlock N Λ => replaceLinks Λ z.1 z.2) := by
  apply continuous_pi
  intro e
  by_cases he : e ∈ Λ
  · simpa only [replaceLinks, dite_eq_left he, Function.comp_def] using
      (continuous_apply (⟨e, he⟩ : {e // e ∈ Λ})).comp continuous_snd
  · simpa only [replaceLinks, dite_eq_right he, Function.comp_def] using
      (continuous_apply e).comp continuous_fst

def localWilsonWeight {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (U : InfiniteConfig N) : ℝ :=
  Real.exp ((N : ℝ) * β *
    ∑ p ∈ affectedPlaquettes Λ, (plaquetteHolonomy (fun i x => U (i, x)) p.1 p.2).val.trace.re)

theorem continuous_localWilsonWeight {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) :
    Continuous (localWilsonWeight (N := N) Λ β) := by
  unfold localWilsonWeight
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun p _ => ?_))
  exact Complex.continuous_re.comp (Continuous.matrix_trace
    (continuous_subtype_val.comp (continuous_plaquetteHolonomy p)))

def infiniteBlockPartition {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (U : InfiniteConfig N) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (localWilsonWeight Λ β (replaceLinks Λ U y)) ∂infiniteBlockHaar Λ

private theorem continuous_localWilsonWeight_replace {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) :
    Continuous (fun z : InfiniteConfig N × InfiniteBlock N Λ =>
      localWilsonWeight Λ β (replaceLinks Λ z.1 z.2)) :=
  (continuous_localWilsonWeight Λ β).comp (continuous_replaceLinks Λ)

theorem infiniteBlockPartition_pos {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (U : InfiniteConfig N) :
    0 < infiniteBlockPartition Λ β U := by
  have h : Measurable (fun y => ENNReal.ofReal (localWilsonWeight Λ β (replaceLinks Λ U y))) :=
    ((continuous_localWilsonWeight_replace Λ β).comp
      (continuous_const.prodMk continuous_id : Continuous (fun y : InfiniteBlock N Λ => (U, y)))).measurable.ennreal_ofReal
  rw [infiniteBlockPartition, lintegral_pos_iff_support h]
  simp [Function.support, localWilsonWeight, Real.exp_pos]

private theorem integrable_continuous_block {N : ℕ} (Λ : Finset InfiniteLink)
    {f : InfiniteBlock N Λ → ℝ} (hf : Continuous f) : Integrable f (infiniteBlockHaar Λ) := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hf.norm).bddAbove
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable C
    (ae_of_all _ fun y => hC ⟨y, Set.mem_univ _, rfl⟩)

theorem infiniteBlockPartition_lt_top {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (U : InfiniteConfig N) :
    infiniteBlockPartition Λ β U < ⊤ := by
  let w (y : InfiniteBlock N Λ) := localWilsonWeight Λ β (replaceLinks Λ U y)
  have hpair : Continuous (fun y : InfiniteBlock N Λ => (U, y)) :=
    continuous_const.prodMk continuous_id
  have hreplace : Continuous (replaceLinks Λ U) := (continuous_replaceLinks (N := N) Λ).comp hpair
  have h : Continuous w := (continuous_localWilsonWeight (N := N) Λ β).comp hreplace
  have hw₀ (y : InfiniteBlock N Λ) : 0 ≤ w y := Real.exp_nonneg _
  have he : ENNReal.ofReal (∫ y, w y ∂infiniteBlockHaar Λ) = infiniteBlockPartition Λ β U :=
    ofReal_integral_eq_lintegral_ofReal (integrable_continuous_block Λ h) (ae_of_all _ hw₀)
  rw [← he]
  exact ENNReal.ofReal_lt_top

theorem measurable_infiniteBlockPartition {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) :
    Measurable (infiniteBlockPartition (N := N) Λ β) :=
  (continuous_localWilsonWeight_replace Λ β).measurable.ennreal_ofReal.lintegral_prod_right'

def infiniteGibbsKernel {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (U : InfiniteConfig N) :
    Measure (InfiniteConfig N) :=
  (infiniteBlockPartition Λ β U)⁻¹ •
    ((infiniteBlockHaar Λ).withDensity (fun y =>
      ENNReal.ofReal (localWilsonWeight Λ β (replaceLinks Λ U y)))).map (replaceLinks Λ U)

private theorem measurable_replaceLinks_fixed {N : ℕ} (Λ : Finset InfiniteLink) (U : InfiniteConfig N) :
    Measurable (replaceLinks Λ U) :=
  ((continuous_replaceLinks Λ).comp (continuous_const.prodMk continuous_id)).measurable

instance infiniteGibbsKernel_probability {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (U : InfiniteConfig N) :
    IsProbabilityMeasure (infiniteGibbsKernel Λ β U) := by
  constructor
  rw [infiniteGibbsKernel, smul_apply, Measure.map_apply (measurable_replaceLinks_fixed Λ U)
    MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul, ← infiniteBlockPartition]
  exact ENNReal.inv_mul_cancel (infiniteBlockPartition_pos Λ β U).ne'
    (infiniteBlockPartition_lt_top Λ β U).ne

theorem lintegral_infiniteGibbsKernel {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (U : InfiniteConfig N)
    {f : InfiniteConfig N → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ V, f V ∂infiniteGibbsKernel Λ β U) = (infiniteBlockPartition Λ β U)⁻¹ *
      ∫⁻ y, ENNReal.ofReal (localWilsonWeight Λ β (replaceLinks Λ U y)) *
        f (replaceLinks Λ U y) ∂infiniteBlockHaar Λ := by
  rw [infiniteGibbsKernel, lintegral_smul_measure, lintegral_map hf (measurable_replaceLinks_fixed Λ U)]
  have hw : Measurable (fun y => ENNReal.ofReal (localWilsonWeight Λ β (replaceLinks Λ U y))) :=
    (continuous_localWilsonWeight Λ β).measurable.ennreal_ofReal.comp (measurable_replaceLinks_fixed Λ U)
  exact congrArg ((infiniteBlockPartition Λ β U)⁻¹ * ·)
    (lintegral_withDensity_eq_lintegral_mul _ hw (hf.comp (measurable_replaceLinks_fixed Λ U)))

theorem measurable_infiniteGibbsKernel {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) :
    Measurable (infiniteGibbsKernel (N := N) Λ β) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have h (U : InfiniteConfig N) :
      infiniteGibbsKernel Λ β U s =
        (infiniteBlockPartition Λ β U)⁻¹ * ∫⁻ y,
          ENNReal.ofReal (localWilsonWeight Λ β (replaceLinks Λ U y)) *
            s.indicator (fun _ => 1) (replaceLinks Λ U y) ∂infiniteBlockHaar Λ := by
    rw [← lintegral_infiniteGibbsKernel Λ β U (measurable_const.indicator hs),
      lintegral_indicator hs, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, one_mul]
  simp_rw [h]
  apply (measurable_infiniteBlockPartition Λ β).inv.mul
  exact ((continuous_localWilsonWeight_replace Λ β).measurable.ennreal_ofReal.mul
    ((measurable_const.indicator hs).comp (continuous_replaceLinks Λ).measurable)).lintegral_prod_right'

private theorem continuous_integral_block {N : ℕ} (Λ : Finset InfiniteLink)
    {f : InfiniteConfig N × InfiniteBlock N Λ → ℝ} (h : Continuous f) :
    Continuous (fun U => ∫ y, f (U, y) ∂infiniteBlockHaar Λ) := by
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous (f := fun U y => f (U, y))
      (μ := infiniteBlockHaar Λ) h isCompact_univ)

theorem exists_continuous_infiniteGibbs_average {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ)
    (f : InfiniteConfig N →ᵇ ℝ≥0) :
    ∃ g : InfiniteConfig N →ᵇ ℝ≥0, ∀ U,
      (g U : ℝ≥0∞) = (∫⁻ V, (f V : ℝ≥0∞) ∂infiniteGibbsKernel Λ β U) := by
  let w (z : InfiniteConfig N × InfiniteBlock N Λ) :=
    localWilsonWeight Λ β (replaceLinks Λ z.1 z.2)
  let v (z : InfiniteConfig N × InfiniteBlock N Λ) :=
    w z * (f (replaceLinks Λ z.1 z.2) : ℝ)
  have hw : Continuous w := continuous_localWilsonWeight_replace Λ β
  have hv : Continuous v := hw.mul (NNReal.continuous_coe.comp (f.continuous.comp (continuous_replaceLinks Λ)))
  let D (U : InfiniteConfig N) := ∫ y, w (U, y) ∂infiniteBlockHaar Λ
  let G (U : InfiniteConfig N) := ∫ y, v (U, y) ∂infiniteBlockHaar Λ
  have hw₀ (z : InfiniteConfig N × InfiniteBlock N Λ) : 0 ≤ w z := Real.exp_nonneg _
  have hv₀ (z : InfiniteConfig N × InfiniteBlock N Λ) : 0 ≤ v z := mul_nonneg (hw₀ z) (NNReal.coe_nonneg _)
  have hD (U : InfiniteConfig N) : ENNReal.ofReal (D U) = infiniteBlockPartition Λ β U :=
    ofReal_integral_eq_lintegral_ofReal
      (integrable_continuous_block Λ (hw.comp (continuous_const.prodMk continuous_id)))
      (ae_of_all _ fun y => hw₀ (U, y))
  have hDpos (U : InfiniteConfig N) : 0 < D U :=
    (ENNReal.ofReal_pos.mp ((hD U).symm ▸ infiniteBlockPartition_pos Λ β U))
  have hG (U : InfiniteConfig N) : ENNReal.ofReal (G U) =
      (∫⁻ y, ENNReal.ofReal (w (U, y)) * (f (replaceLinks Λ U y) : ℝ≥0∞) ∂infiniteBlockHaar Λ) := by
    have hi : Integrable (fun y => v (U, y)) (infiniteBlockHaar Λ) :=
      integrable_continuous_block Λ (hv.comp (continuous_const.prodMk continuous_id))
    change ENNReal.ofReal (∫ y, v (U, y) ∂infiniteBlockHaar Λ) = _
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => hv₀ (U, y))]
    refine lintegral_congr fun y => ?_
    rw [show v (U, y) = w (U, y) * (f (replaceLinks Λ U y) : ℝ) from rfl,
      ENNReal.ofReal_mul (hw₀ _), ENNReal.ofReal_coe_nnreal]
  have hc : Continuous (fun U => (G U / D U).toNNReal) :=
    continuous_real_toNNReal.comp ((continuous_integral_block Λ hv).div
      (continuous_integral_block Λ hw) (fun U => (hDpos U).ne'))
  refine ⟨BoundedContinuousFunction.mkOfCompact ⟨_, hc⟩, fun U => ?_⟩
  change ENNReal.ofReal (G U / D U) = _
  rw [lintegral_infiniteGibbsKernel Λ β U f.continuous.measurable.coe_nnreal_ennreal,
    ENNReal.ofReal_div_of_pos (hDpos U), hD, hG, div_eq_mul_inv, mul_comm]

/-- The links needed to resample a block and evaluate an observable on (S). -/
def resamplingSupport (Λ S : Finset InfiniteLink) : Finset InfiniteLink :=
  (Λ ∪ S) ∪ (affectedPlaquettes Λ).biUnion boundaryLinks

private def blockReductionEquiv {L : ℕ} (Λ : Finset InfiniteLink)
    (h : Set.InjOn (torusCellReduction L) (↑Λ : Set InfiniteLink)) :
    {e // e ∈ Λ} ≃ {e // e ∈ Λ.image (torusCellReduction L)} :=
  Equiv.ofBijective (fun e => ⟨torusCellReduction L e.val, Finset.mem_image_of_mem _ e.property⟩) <| by
    constructor
    · intro e f hef
      exact Subtype.ext (h e.property f.property (congrArg Subtype.val hef))
    · rintro ⟨e, he⟩
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      exact ⟨⟨p, hp⟩, rfl⟩

set_option maxHeartbeats 600000 in
theorem lintegral_periodicWilson_resample_infinite {L N : ℕ} [NeZero L]
    (Λ S : Finset InfiniteLink) (β : ℝ) (f : InfiniteConfig N → ℝ≥0∞) (hf : Measurable f)
    (hs : ∀ U V : InfiniteConfig N, (∀ e ∈ S, U e = V e) → f U = f V)
    (hL : 2 * cellSetRadius (resamplingSupport Λ S) < L)
    (hplaquettes : 2 * cellSetRadius (affectedPlaquettes Λ) < L) :
    (∫⁻ U, f (extendPeriodic U) ∂periodicWilson L N β) =
      ∫⁻ U, ∫⁻ V, f V ∂infiniteGibbsKernel Λ β (extendPeriodic U) ∂periodicWilson L N β := by
  let Λ' := Λ.image (torusCellReduction L)
  let P := splitPeriodicLinks (N := N) Λ'
  have hinj := torusCellReduction_injOn (resamplingSupport Λ S) hL
  have hΛ {e : InfiniteLink} (he : e ∈ Λ) : e ∈ resamplingSupport Λ S :=
    Finset.mem_union_left _ (Finset.mem_union_left _ he)
  let e := blockReductionEquiv Λ (hinj.mono fun _ he => hΛ he)
  let E := MeasurableEquiv.piCongrLeft (fun _ : {a // a ∈ Λ'} => UnitaryMatrix N) e
  have hE : MeasurePreserving E (infiniteBlockHaar Λ) (blockHaar (N := N) Λ') := by
    unfold infiniteBlockHaar blockHaar
    exact measurePreserving_piCongrLeft (fun _ => unitaryHaar N) e
  let R (U : TorusConfig L N) (y : InfiniteBlock N Λ) :=
    P.symm (E y, (P U).2)
  have hR (U : TorusConfig L N) (y : InfiniteBlock N Λ) (a : InfiniteLink)
      (ha : a ∈ resamplingSupport Λ S) :
      extendPeriodic (R U y) a = replaceLinks Λ (extendPeriodic U) y a := by
    have hsplit := P.apply_symm_apply (E y, (P U).2)
    by_cases ha₀ : a ∈ Λ
    · rw [replaceLinks, dite_eq_left ha₀]
      have hval := congrArg (fun z : PeriodicBlock N Λ' × PeriodicExterior N Λ' => z.1 (e ⟨a, ha₀⟩)) hsplit
      change R U y (torusCellReduction L a) = E y (e ⟨a, ha₀⟩) at hval
      change R U y (torusCellReduction L a) = y ⟨a, ha₀⟩
      exact hval.trans (MeasurableEquiv.piCongrLeft_apply_apply e
        (β := fun _ => UnitaryMatrix N) y ⟨a, ha₀⟩)
    · rw [replaceLinks, dite_eq_right ha₀]
      have ha' : torusCellReduction L a ∉ Λ' := by
        intro h
        obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp h
        exact ha₀ (hinj (hΛ hb) ha hb' ▸ hb)
      have hval := congrArg (fun z : PeriodicBlock N Λ' × PeriodicExterior N Λ' =>
        z.2 ⟨torusCellReduction L a, ha'⟩) hsplit
      change R U y (torusCellReduction L a) = U (torusCellReduction L a) at hval
      exact hval
  have hWeight (U : TorusConfig L N) (y : InfiniteBlock N Λ) :
      periodicLocalWeight Λ' β (E y, (P U).2) =
        ENNReal.ofReal (localWilsonWeight Λ β (replaceLinks Λ (extendPeriodic U) y)) := by
    rw [periodicLocalWeight, localWilsonWeight, periodicAffectedPlaquettes_image Λ,
      Finset.sum_image (torusCellReduction_injOn (affectedPlaquettes Λ) hplaquettes)]
    apply congrArg (fun z : ℝ => ENNReal.ofReal (Real.exp ((N : ℝ) * β * z)))
    apply Finset.sum_congr rfl
    intro p hp
    change (periodicHolonomy (R U y) (torusCellReduction L p).1 (torusCellReduction L p).2).val.trace.re = _
    rw [← periodicHolonomy_extendPeriodic]
    exact congrArg (fun V : UnitaryMatrix N => V.val.trace.re)
      (plaquetteHolonomy_congr_boundary p (fun a ha => hR U y a
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, hp, ha⟩))))
  let F (U : TorusConfig L N) := f (extendPeriodic U)
  have hF : Measurable F := hf.comp (continuous_extendPeriodic L N).measurable
  have h := lintegral_periodicWilson_resample Λ' β hF
    (g := fun _ => 1) measurable_const
  simp only [mul_one] at h
  refine h.trans (lintegral_congr fun U => ?_)
  rw [periodicBlockExpectation_eq_local, lintegral_infiniteGibbsKernel Λ β _ hf]
  rw [← hE.lintegral_comp_emb E.measurableEmbedding (fun z => periodicLocalWeight Λ' β (z, (P U).2)),
    ← hE.lintegral_comp_emb E.measurableEmbedding (fun z =>
      periodicLocalWeight Λ' β (z, (P U).2) * F (P.symm (z, (P U).2)))]
  simp only [hWeight, infiniteBlockPartition, F]
  congr 1
  apply lintegral_congr
  intro y
  change _ * f (extendPeriodic (R U y)) = _
  rw [hs _ _ (fun a ha => hR U y a (Finset.mem_union_left _ (Finset.mem_union_right _ ha)))]

private theorem lintegral_periodicLimit_resample_cylinder {N : ℕ} (Λ S : Finset InfiniteLink)
    (β : ℝ) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (f : InfiniteConfig N →ᵇ ℝ≥0)
    (hs : ∀ U V : InfiniteConfig N, (∀ e ∈ S, U e = V e) → f U = f V) :
    (∫⁻ U, (f U : ℝ≥0∞) ∂μ.toMeasure) =
      ∫⁻ U, ∫⁻ V, (f V : ℝ≥0∞) ∂infiniteGibbsKernel Λ β U ∂μ.toMeasure := by
  obtain ⟨g, hg⟩ := exists_continuous_infiniteGibbs_average Λ β f
  let m := max (cellSetRadius (resamplingSupport Λ S)) (cellSetRadius (affectedPlaquettes Λ))
  have h : (fun n => ∫⁻ U, (f U : ℝ≥0∞) ∂(extendedWilson (evenLength (l n)) N β).toMeasure) =ᶠ[atTop]
      fun n => ∫⁻ U, (g U : ℝ≥0∞) ∂(extendedWilson (evenLength (l n)) N β).toMeasure := by
    filter_upwards [eventually_ge_atTop m] with n hn
    let L := evenLength (l n)
    have hN : n ≤ l n := hl.id_le n
    have hL : 2 * cellSetRadius (resamplingSupport Λ S) < L := by
      have := le_max_left (cellSetRadius (resamplingSupport Λ S)) (cellSetRadius (affectedPlaquettes Λ))
      dsimp [m] at hn
      dsimp [L, evenLength]
      omega
    have hP : 2 * cellSetRadius (affectedPlaquettes Λ) < L := by
      have := le_max_right (cellSetRadius (resamplingSupport Λ S)) (cellSetRadius (affectedPlaquettes Λ))
      dsimp [m] at hn
      dsimp [L, evenLength]
      omega
    have hφ : Measurable (fun U => (f U : ℝ≥0∞)) := f.continuous.measurable.coe_nnreal_ennreal
    have hψ : Measurable (fun U => (g U : ℝ≥0∞)) := g.continuous.measurable.coe_nnreal_ennreal
    have hExt := (continuous_extendPeriodic L N).measurable
    change (∫⁻ U, (f U : ℝ≥0∞) ∂Measure.map extendPeriodic (periodicWilson L N β)) =
      ∫⁻ U, (g U : ℝ≥0∞) ∂Measure.map extendPeriodic (periodicWilson L N β)
    rw [lintegral_map hφ hExt, lintegral_map hψ hExt]
    simp_rw [hg]
    exact lintegral_periodicWilson_resample_infinite Λ S β _ hφ
      (fun U V hUV => congrArg (fun t : ℝ≥0 => (t : ℝ≥0∞)) (hs U V hUV)) hL hP
  have hf_lim := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hμ f
  have hg_lim := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hμ g
  simpa only [hg] using tendsto_nhds_unique (hf_lim.congr' h) hg_lim

/-- The infinite-volume periodic limit is fixed by every finite Gibbs resampling. -/
theorem periodicLimit_bind_infiniteGibbsKernel {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    μ.toMeasure = μ.toMeasure.bind (infiniteGibbsKernel Λ β) := by
  let P (S : Finset InfiniteLink) := μ.toMeasure.map (S.restrict : InfiniteConfig N → InfiniteBlock N S)
  have hp : IsProjectiveLimit μ.toMeasure P := fun _ => rfl
  have hK := (measurable_infiniteGibbsKernel (N := N) Λ β).aemeasurable (μ := μ.toMeasure)
  have hpb : IsProjectiveLimit (μ.toMeasure.bind (infiniteGibbsKernel Λ β)) P := by
    intro S
    symm
    apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
    intro f
    let r : InfiniteConfig N → InfiniteBlock N S := S.restrict
    have hr : Continuous r := continuous_pi fun e => continuous_apply e.val
    let F : InfiniteConfig N →ᵇ ℝ≥0 := BoundedContinuousFunction.mkOfCompact ⟨f ∘ r, f.continuous.comp hr⟩
    have hF : ∀ U V : InfiniteConfig N, (∀ e ∈ S, U e = V e) → F U = F V := by
      intro U V h
      exact congrArg f (funext fun e => h e.val e.property)
    have hf : Measurable (fun y => (f y : ℝ≥0∞)) := f.continuous.measurable.coe_nnreal_ennreal
    have hφ : Measurable (fun U => (f (r U) : ℝ≥0∞)) := hf.comp hr.measurable
    change (∫⁻ y, (f y : ℝ≥0∞) ∂μ.toMeasure.map r) =
      ∫⁻ y, (f y : ℝ≥0∞) ∂(μ.toMeasure.bind (infiniteGibbsKernel Λ β)).map r
    rw [lintegral_map hf hr.measurable, lintegral_map hf hr.measurable, Measure.lintegral_bind hK hφ.aemeasurable]
    exact lintegral_periodicLimit_resample_cylinder Λ S β μ l hl hμ F hF
  exact hp.unique hpb

/-- The finite-region conditional Gibbs identity in every periodic weak limit. -/
theorem lintegral_periodicLimit_conditionalGibbs {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    {f g : InfiniteConfig N → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hg_exterior : ∀ U y, g (replaceLinks Λ U y) = g U) :
    (∫⁻ U, f U * g U ∂μ.toMeasure) =
      ∫⁻ U, (∫⁻ V, f V ∂infiniteGibbsKernel Λ β U) * g U ∂μ.toMeasure := by
  calc
    _ = ∫⁻ U, f U * g U ∂μ.toMeasure.bind (infiniteGibbsKernel Λ β) :=
      congrArg (lintegral · (fun U => f U * g U)) (periodicLimit_bind_infiniteGibbsKernel Λ β μ l hl hμ)
    _ = ∫⁻ U, ∫⁻ V, f V * g V ∂infiniteGibbsKernel Λ β U ∂μ.toMeasure :=
      Measure.lintegral_bind (measurable_infiniteGibbsKernel Λ β).aemeasurable (hf.mul hg).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro U
      have hfg : Measurable (fun V => f V * g V) := hf.mul hg
      rw [lintegral_infiniteGibbsKernel Λ β U hfg, lintegral_infiniteGibbsKernel Λ β U hf]
      have hr := measurable_replaceLinks_fixed Λ U
      have hw : Measurable (fun y => ENNReal.ofReal (localWilsonWeight Λ β (replaceLinks Λ U y))) :=
        (continuous_localWilsonWeight Λ β).measurable.ennreal_ofReal.comp hr
      have hWF : Measurable (fun y => ENNReal.ofReal (localWilsonWeight Λ β (replaceLinks Λ U y)) *
          f (replaceLinks Λ U y)) := hw.mul (hf.comp hr)
      simp_rw [hg_exterior, ← mul_assoc]
      rw [lintegral_mul_const _ hWF, mul_assoc]

end

end GaplessYangMills

module

public import GaplessYangMills.CutBlock
public import GaplessYangMills.InfiniteAction

/-!
# Differentiating the smooth cut average

Only the cuts on plaquettes meeting the varied links move. The
derivative is a finite sum of derivatives of the smooth product density.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

def shiftedCutDensity (S : Finset Plaquette) (c : CutBlock S) (t : ℝ) (y : CutBlock S) : ℝ :=
  cutBlockDensity S (y + t • c)

def shiftedCutDensityDerivative (S : Finset Plaquette) (c : CutBlock S) (t : ℝ) (y : CutBlock S) : ℝ :=
  ∑ p : {p // p ∈ S}, (∏ r ∈ Finset.univ.erase p, cutDensity (y r + t * c r)) *
    (deriv cutDensity (y p + t * c p) * c p)

private theorem differentiable_cutDensity : Differentiable ℝ cutDensity :=
  (cutDensity_contDiff 1).differentiable (by norm_num)

private theorem continuous_cutDensity_deriv : Continuous (deriv cutDensity) :=
  (cutDensity_contDiff 1).continuous_deriv (by norm_num)

theorem continuous_shiftedCutDensity (S : Finset Plaquette) (c : CutBlock S) :
    Continuous (fun p : ℝ × CutBlock S => shiftedCutDensity S c p.1 p.2) :=
  (continuous_cutBlockDensity S).comp (continuous_snd.add (continuous_fst.smul continuous_const))

theorem continuous_shiftedCutDensityDerivative (S : Finset Plaquette) (c : CutBlock S) :
    Continuous (fun p : ℝ × CutBlock S => shiftedCutDensityDerivative S c p.1 p.2) := by
  have ha (r : {p // p ∈ S}) : Continuous (fun p : ℝ × CutBlock S => p.2 r + p.1 * c r) :=
    ((continuous_apply r).comp continuous_snd).add (continuous_fst.mul continuous_const)
  unfold shiftedCutDensityDerivative
  exact continuous_finsetSum _ fun p _ => (continuous_finsetProd _ fun r _ =>
    (cutDensity_contDiff 0).continuous.comp (ha r)).mul
    ((continuous_cutDensity_deriv.comp (ha p)).mul continuous_const)

theorem hasDerivAt_shiftedCutDensity (S : Finset Plaquette) (c : CutBlock S) (t : ℝ)
    (y : CutBlock S) :
    HasDerivAt (fun s => shiftedCutDensity S c s y) (shiftedCutDensityDerivative S c t y) t := by
  have hd (p : {p // p ∈ S}) :
      HasDerivAt (fun s => cutDensity (y p + s * c p))
        (deriv cutDensity (y p + t * c p) * c p) t := by
    have hi : HasDerivAt (fun s => y p + s * c p) (c p) t := by
      simpa only [one_mul] using ((hasDerivAt_id' t).mul_const (c p)).const_add (y p)
    exact ((differentiable_cutDensity (y p + t * c p)).hasDerivAt).comp t hi
  simpa only [shiftedCutDensity, shiftedCutDensityDerivative, cutBlockDensity, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] using HasDerivAt.fun_finsetProd (u := Finset.univ) (fun p _ => hd p)

private theorem deriv_cutDensity_eq_zero {x : ℝ} (hx : Real.pi / 32 < |x|) :
    deriv cutDensity x = 0 := by
  have h : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x] cutDensity := by
    have hh := continuous_abs.continuousAt.eventually (lt_mem_nhds hx)
    exact hh.mono fun u hu => (cutDensity_eq_zero_of_abs_ge hu.le).symm
  exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h.symm).deriv

def cutBlockBox (S : Finset Plaquette) : Set (CutBlock S) :=
  Metric.closedBall 0 (Real.pi / 16)

theorem mem_cutBlockBox_iff (S : Finset Plaquette) (y : CutBlock S) :
    y ∈ cutBlockBox S ↔ ∀ p, |y p| ≤ Real.pi / 16 := by
  rw [cutBlockBox, Metric.mem_closedBall, dist_eq_norm, sub_zero,
    pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ Real.pi / 16)]
  simp only [Real.norm_eq_abs]

theorem isCompact_cutBlockBox (S : Finset Plaquette) : IsCompact (cutBlockBox S) :=
  isCompact_closedBall _ _

theorem exists_shiftedCutDensity_support (S : Finset Plaquette) (c : CutBlock S) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ t ∈ Metric.ball (0 : ℝ) ε, ‖t • c‖ < Real.pi / 32) ∧
      ∀ t ∈ Metric.ball (0 : ℝ) ε,
      ∀ y ∉ cutBlockBox S, shiftedCutDensity S c t y = 0 ∧ shiftedCutDensityDerivative S c t y = 0 := by
  have hc : Continuous (fun t : ℝ => ‖t • c‖) := (continuous_id.smul continuous_const).norm
  have h₀ : ‖(0 : ℝ) • c‖ < Real.pi / 32 := by simp; positivity
  have hn : {t : ℝ | ‖t • c‖ < Real.pi / 32} ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.eventually (gt_mem_nhds h₀)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε, hε, fun _ ht => hsub ht, fun t ht y hy => ?_⟩
  have hsize : ‖t • c‖ < Real.pi / 32 := hsub ht
  rw [mem_cutBlockBox_iff] at hy
  push Not at hy
  obtain ⟨p, hp⟩ := hy
  have hc' : |t * c p| ≤ ‖t • c‖ := by
    simpa only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] using norm_le_pi_norm (t • c) p
  have ht' : Real.pi / 32 < |y p + t * c p| := by
    have ha : |y p| ≤ |y p + t * c p| + |t * c p| := by
      calc
        _ = |(y p + t * c p) + -(t * c p)| := by rw [add_neg_cancel_right]
        _ ≤ _ := by simpa only [abs_neg] using abs_add_le (y p + t * c p) (-(t * c p))
    linarith
  have hz := cutDensity_eq_zero_of_abs_ge ht'.le
  have hd := deriv_cutDensity_eq_zero ht'
  refine ⟨?_, ?_⟩
  · exact Finset.prod_eq_zero (Finset.mem_univ p) hz
  · apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r = p
    · subst r
      rw [hd, zero_mul, mul_zero]
    · rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hr, Finset.mem_univ p⟩) hz, zero_mul]

theorem exists_integrable_cutFluxBound_periodicLimit {N : ℕ} (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (I : Face) (x : Site) :
    ∃ B : InfiniteConfig N → ℝ, Measurable B ∧ Integrable B μ.toMeasure ∧ (∀ U, 0 ≤ B U) ∧
      ∀ᵐ U ∂μ.toMeasure, ∀ η : TwoForm ℝ, (∀ J y, |η J y| ≤ Real.pi / 16) →
        |repairedCutFlux (fun j y => U (j, y)) η I x| ≤ B U := by
  obtain ⟨M, hM⟩ := repairedCutFluxApprox_bounded N 0 I x
  obtain ⟨C, _, t, _, _, hC⟩ := eLpNorm_cutFluxErrorBound_periodicLimit_le hN hβ μ l hl hμ
  have hE : MemLp (cutFluxErrorBound 0 x) 2 μ.toMeasure :=
    (hC x 0).trans_lt ENNReal.ofReal_lt_top
  have hE' : Integrable (cutFluxErrorBound 0 x) μ.toMeasure := hE.integrable (by norm_num)
  refine ⟨fun U => |M| + cutFluxErrorBound 0 x U, measurable_const.add (measurable_cutFluxErrorBound hN 0 x),
    (integrable_const |M|).add hE', fun U => add_nonneg (abs_nonneg _) (cutFluxErrorBound_nonneg 0 x U), ?_⟩
  filter_upwards [abs_repairedCutFlux_sub_approx_le_periodicLimit_ae hN hβ μ l hl hμ] with U hu
  intro η hη
  let A := repairedCutFluxApprox 0 (fun j y => U (j, y)) η I x
  let F := repairedCutFlux (fun j y => U (j, y)) η I x
  calc
    |F| = |A + (F - A)| := by rw [add_comm, sub_add_cancel]
    _ ≤ |A| + |F - A| := abs_add_le _ _
    _ ≤ _ := add_le_add ((hM U η hη).trans (le_abs_self M)) (hu I x 0 η hη)

/-- Lebesgue measure on the allowed block of cuts, with the other cuts
distributed according to their original law. -/
def cutBlockReference (S : Finset Plaquette) : Measure (CutBlock S × CutExterior S) :=
  (volume.restrict (cutBlockBox S)).prod (cutExteriorLaw S)

instance cutBlockReference_finite (S : Finset Plaquette) : IsFiniteMeasure (cutBlockReference S) := by
  let : IsFiniteMeasure (volume.restrict (cutBlockBox S)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact (isCompact_cutBlockBox S).measure_lt_top⟩
  unfold cutBlockReference
  infer_instance

theorem joinedCutBlockReference_allowed (S : Finset Plaquette) :
    ∀ᵐ p ∂cutBlockReference S, ∀ I x, |(splitCutField S).symm p I x| ≤ Real.pi / 16 := by
  let m := volume.restrict (cutBlockBox S)
  have hY : ∀ᵐ p ∂cutBlockReference S, p.1 ∈ cutBlockBox S :=
    (Measure.quasiMeasurePreserving_fst (μ := m) (ν := cutExteriorLaw S)).ae
      (ae_restrict_mem (isCompact_cutBlockBox S).isClosed.measurableSet)
  have hZ : ∀ᵐ p ∂cutBlockReference S, ∀ q, |p.2 q| ≤ Real.pi / 32 :=
    (Measure.quasiMeasurePreserving_snd (μ := m) (ν := cutExteriorLaw S)).ae (cutExteriorLaw_ae_abs_le S)
  filter_upwards [hY, hZ] with p hy hz
  intro I x
  change |(splitCutField S).symm (p.1, p.2) I x| ≤ Real.pi / 16
  rw [splitCutField_symm_apply S p.1 p.2 (I, x)]
  by_cases h : (I, x) ∈ S
  · rw [dite_eq_left h]
    exact (mem_cutBlockBox_iff S p.1).mp hy _
  · rw [dite_eq_right h]
    exact (hz _).trans (by linarith [Real.pi_pos])

private theorem integral_shiftCutBlock_reference (S : Finset Plaquette) (c : CutBlock S) (t : ℝ)
    (h : ∀ y ∉ cutBlockBox S, shiftedCutDensity S c t y = 0) (f : TwoForm ℝ → ℝ) :
    (∫ η, f (shiftCutBlock S (t • c) η) ∂iidCutLaw) =
      ∫ p, shiftedCutDensity S c t p.1 * f ((splitCutField S).symm p) ∂cutBlockReference S := by
  rw [integral_iidCutLaw_shiftCutBlock, cutBlockReference, Measure.restrict_prod_eq_prod_univ,
    ← integral_indicator ((isCompact_cutBlockBox S).isClosed.measurableSet.prod MeasurableSet.univ)]
  apply integral_congr_ae
  refine ae_of_all _ fun p => ?_
  by_cases hp : p.1 ∈ cutBlockBox S
  · rw [Set.indicator_of_mem (show p ∈ cutBlockBox S ×ˢ Set.univ from ⟨hp, Set.mem_univ _⟩)]
    rfl
  · rw [Set.indicator_of_notMem (show p ∉ cutBlockBox S ×ˢ Set.univ from fun h' => hp h'.1)]
    change shiftedCutDensity S c t p.1 * _ = 0
    rw [h _ hp, zero_mul]

/-- A finite cut shift can be differentiated through both probability
integrals when the observable is dominated uniformly on the allowed cuts. -/
theorem hasDerivAt_integral_shiftCutBlock {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : Finset Plaquette) (c : CutBlock S)
    (f : Ω × TwoForm ℝ → ℝ) (hf : Measurable f) (B : Ω → ℝ) (hB : Integrable B μ)
    (hbound : ∀ᵐ u ∂μ, ∀ η : TwoForm ℝ, (∀ I x, |η I x| ≤ Real.pi / 16) → |f (u, η)| ≤ B u) :
    HasDerivAt (fun t : ℝ => ∫ u, ∫ η, f (u, shiftCutBlock S (t • c) η) ∂iidCutLaw ∂μ)
      (∫ p : Ω × (CutBlock S × CutExterior S),
        shiftedCutDensityDerivative S c 0 p.2.1 * f (p.1, (splitCutField S).symm p.2)
          ∂μ.prod (cutBlockReference S)) 0 := by
  obtain ⟨ε, hε, _, hsupport⟩ := exists_shiftedCutDensity_support S c
  let ν := μ.prod (cutBlockReference S)
  let g (p : Ω × (CutBlock S × CutExterior S)) := f (p.1, (splitCutField S).symm p.2)
  let F (t : ℝ) (p : Ω × (CutBlock S × CutExterior S)) := shiftedCutDensity S c t p.2.1 * g p
  let D (t : ℝ) (p : Ω × (CutBlock S × CutExterior S)) := shiftedCutDensityDerivative S c t p.2.1 * g p
  have hg : Measurable g := hf.comp (measurable_fst.prodMk ((splitCutField S).symm.measurable.comp measurable_snd))
  have hpBound : ∀ᵐ p ∂ν, |g p| ≤ B p.1 := by
    have h₁ : ∀ᵐ p ∂ν, ∀ η : TwoForm ℝ, (∀ I x, |η I x| ≤ Real.pi / 16) → |f (p.1, η)| ≤ B p.1 :=
      Measure.quasiMeasurePreserving_fst.ae hbound
    have h₂ : ∀ᵐ p ∂ν, ∀ I x, |(splitCutField S).symm p.2 I x| ≤ Real.pi / 16 :=
      Measure.quasiMeasurePreserving_snd.ae (joinedCutBlockReference_allowed S)
    filter_upwards [h₁, h₂] with p h₁p h₂p
    exact h₁p _ h₂p
  have hpBox : ∀ᵐ p : Ω × (CutBlock S × CutExterior S) ∂ν, p.2.1 ∈ cutBlockBox S :=
    Measure.quasiMeasurePreserving_snd.ae ((Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict (cutBlockBox S)) (ν := cutExteriorLaw S)).ae
        (ae_restrict_mem (isCompact_cutBlockBox S).isClosed.measurableSet))
  have hc : Continuous (fun q : ℝ × CutBlock S =>
      ‖shiftedCutDensity S c q.1 q.2‖ + ‖shiftedCutDensityDerivative S c q.1 q.2‖) :=
    (continuous_shiftedCutDensity S c).norm.add (continuous_shiftedCutDensityDerivative S c).norm
  obtain ⟨C, hC⟩ := ((isCompact_closedBall 0 ε).prod (isCompact_cutBlockBox S)).bddAbove_image hc.continuousOn
  have hC' (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) ε) (y : CutBlock S) (hy : y ∈ cutBlockBox S) :
      ‖shiftedCutDensity S c t y‖ ≤ C ∧ ‖shiftedCutDensityDerivative S c t y‖ ≤ C := by
    have h := hC ⟨(t, y), ⟨Metric.ball_subset_closedBall ht, hy⟩, rfl⟩
    exact ⟨(le_add_of_nonneg_right (norm_nonneg _)).trans h, (le_add_of_nonneg_left (norm_nonneg _)).trans h⟩
  have hInt : Integrable (fun p : Ω × (CutBlock S × CutExterior S) => C * B p.1) ν :=
    (hB.comp_fst (cutBlockReference S)).const_mul C
  have hFm (t : ℝ) : AEStronglyMeasurable (F t) ν := by
    have hm : Measurable (fun p : Ω × (CutBlock S × CutExterior S) => (t, p.2.1)) :=
      measurable_const.prodMk (measurable_fst.comp measurable_snd)
    exact (((continuous_shiftedCutDensity S c).measurable.comp hm).mul hg).aestronglyMeasurable
  have hDm (t : ℝ) : AEStronglyMeasurable (D t) ν := by
    have hm : Measurable (fun p : Ω × (CutBlock S × CutExterior S) => (t, p.2.1)) :=
      measurable_const.prodMk (measurable_fst.comp measurable_snd)
    exact (((continuous_shiftedCutDensityDerivative S c).measurable.comp hm).mul hg).aestronglyMeasurable
  have hBd : ∀ᵐ p ∂ν, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖F t p‖ ≤ C * B p.1 ∧ ‖D t p‖ ≤ C * B p.1 := by
    filter_upwards [hpBound, hpBox] with p hp hbox
    intro t ht
    have hgp : ‖g p‖ ≤ B p.1 := by simpa only [Real.norm_eq_abs] using hp
    obtain ⟨hw, hd⟩ := hC' t ht _ hbox
    constructor
    · change ‖shiftedCutDensity S c t p.2.1 * g p‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul hw hgp (norm_nonneg _) ((norm_nonneg _).trans hw)
    · change ‖shiftedCutDensityDerivative S c t p.2.1 * g p‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul hd hgp (norm_nonneg _) ((norm_nonneg _).trans hd)
  have hFint (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) ε) : Integrable (F t) ν :=
    hInt.mono' (hFm t) (hBd.mono fun p hp => (hp t ht).1)
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := D)
    (bound := fun p => C * B p.1) (Metric.ball_mem_nhds _ hε) (Eventually.of_forall hFm)
    (hFint 0 (Metric.mem_ball_self hε)) (hDm 0)
    (hBd.mono fun p hp t ht => (hp t ht).2) hInt
    (ae_of_all _ fun p t _ => (hasDerivAt_shiftedCutDensity S c t p.2.1).mul_const (g p))).2
  have hEq : (fun t => ∫ u, ∫ η, f (u, shiftCutBlock S (t • c) η) ∂iidCutLaw ∂μ) =ᶠ[𝓝 0]
      (fun t => ∫ p, F t p ∂ν) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    rw [integral_prod _ (hFint t ht)]
    exact integral_congr_ae (ae_of_all _ fun u =>
      integral_shiftCutBlock_reference S c t (fun y hy => (hsupport t ht y hy).1) (fun η => f (u, η)))
  exact h.congr_of_eventuallyEq hEq

theorem measurable_shiftCutBlock (S : Finset Plaquette) (v : CutBlock S) :
    Measurable (shiftCutBlock S v) := by
  have h := (splitCutField S).measurable
  exact (splitCutField S).symm.measurable.comp
    (((measurable_fst.comp h).sub measurable_const).prodMk (measurable_snd.comp h))

theorem shiftCutBlock_allowed (S : Finset Plaquette) (v : CutBlock S)
    (hV : ‖v‖ ≤ Real.pi / 32) :
    ∀ᵐ η ∂iidCutLaw, ∀ I x, |shiftCutBlock S v η I x| ≤ Real.pi / 16 := by
  filter_upwards [iidCutLaw_ae_abs_le] with η hη
  intro I x
  rw [shiftCutBlock, splitCutField_symm_apply S _ _ (I, x)]
  by_cases hp : (I, x) ∈ S
  · rw [dite_eq_left hp]
    change |η I x - v ⟨(I, x), hp⟩| ≤ _
    have hn : |v ⟨(I, x), hp⟩| ≤ Real.pi / 32 := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm v _).trans hV
    have h : |η I x - v ⟨(I, x), hp⟩| ≤ |η I x| + |v ⟨(I, x), hp⟩| := by
      rw [sub_eq_add_neg, ← abs_neg (v ⟨(I, x), hp⟩)]
      exact abs_add_le _ _
    linarith [hη I x]
  · rw [dite_eq_right hp]
    exact (hη I x).trans (by linarith [Real.pi_pos])

def linkCutDirection (N : ℕ) (Λ : Finset InfiniteLink) (α : OneForm ℝ) :
    CutBlock (affectedPlaquettes Λ) :=
  fun p => d₁ α p.val.1 p.val.2 / N

private theorem d₁_const_mul (t : ℝ) (α : OneForm ℝ) :
    d₁ (fun i y => t * α i y) = fun I x => t * d₁ α I x := by
  funext I x
  cases I <;> simp only [d₁, diff, Pi.sub_apply] <;> ring

private theorem shiftCuts_eq_shiftCutBlock (N : ℕ) (Λ : Finset InfiniteLink) (α : OneForm ℝ)
    (hα : ∀ e ∉ Λ, α e.1 e.2 = 0) (t : ℝ) (η : TwoForm ℝ) :
    shiftCuts η (d₁ (fun i y => t * α i y)) N =
      shiftCutBlock (affectedPlaquettes Λ) (t • linkCutDirection N Λ α) η := by
  funext I x
  rw [shiftCutBlock, splitCutField_symm_apply _ _ _ (I, x), d₁_const_mul]
  by_cases hp : (I, x) ∈ affectedPlaquettes Λ
  · rw [dite_eq_left hp]
    change η I x - (t * d₁ α I x) / N = η I x - t * (d₁ α I x / N)
    rw [mul_div_assoc]
  · rw [dite_eq_right hp]
    change η I x - (t * d₁ α I x) / N = η I x
    rw [d₁_eq_zero_of_notMem_affectedPlaquettes α hα hp, mul_zero, zero_div, sub_zero]

theorem repairedCutFlux_centralLinkVariation {N : ℕ} (hN : 0 < N) (Λ : Finset InfiniteLink)
    (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0) (t : ℝ) (U : InfiniteConfig N)
    (η : TwoForm ℝ) (I : Face) (x : Site) :
    repairedCutFlux (fun i y => centralLinkVariation α t U (i, y)) η I x =
      repairedCutFlux (fun i y => U (i, y))
        (shiftCutBlock (affectedPlaquettes Λ) (t • linkCutDirection N Λ α) η) I x + t * d₁ α I x := by
  have h := repairedCutFlux_central_links hN (fun i y => U (i, y)) (fun i y => t * α i y) η
  rw [shiftCuts_eq_shiftCutBlock N Λ α hα t η, d₁_const_mul] at h
  simpa only [centralLinkVariation, mul_div_assoc, Pi.add_apply] using (congrFun (congrFun h I) x)

def cutVariationResponse {N : ℕ} (Λ : Finset InfiniteLink) (α : OneForm ℝ)
    (μ : Measure (InfiniteConfig N)) (I : Face) (x : Site) : ℝ :=
  ∫ p : InfiniteConfig N × (CutBlock (affectedPlaquettes Λ) × CutExterior (affectedPlaquettes Λ)),
    shiftedCutDensityDerivative (affectedPlaquettes Λ) (linkCutDirection N Λ α) 0 p.2.1 *
      repairedCutFlux (fun j y => p.1 (j, y)) ((splitCutField (affectedPlaquettes Λ)).symm p.2) I x
      ∂μ.prod (cutBlockReference (affectedPlaquettes Λ))

/-- The cut-side derivative of the Wilson flux expectation under a finite central link rotation. -/
theorem hasDerivAt_averagedFlux_centralLinkVariation {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (Λ : Finset InfiniteLink) (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (I : Face) (x : Site) :
    HasDerivAt (fun t => ∫ U, averagedFlux iidCutLaw (centralLinkVariation α t U) I x ∂μ.toMeasure)
      (d₁ α I x + cutVariationResponse Λ α μ.toMeasure I x) 0 := by
  let S := affectedPlaquettes Λ
  let c := linkCutDirection N Λ α
  let f (p : InfiniteConfig N × TwoForm ℝ) := repairedCutFlux (fun j y => p.1 (j, y)) p.2 I x
  let G (t : ℝ) (U : InfiniteConfig N) := ∫ η, f (U, shiftCutBlock S (t • c) η) ∂iidCutLaw
  have hf : Measurable f := measurable_repairedCutFlux_coordinate I x
  obtain ⟨B, _, hB, _, hF⟩ := exists_integrable_cutFluxBound_periodicLimit hN hβ μ l hl hμ I x
  obtain ⟨ε, hε, hsize, _⟩ := exists_shiftedCutDensity_support S c
  have hD : HasDerivAt (fun t => ∫ U, G t U ∂μ.toMeasure)
      (cutVariationResponse Λ α μ.toMeasure I x) 0 :=
    hasDerivAt_integral_shiftCutBlock μ.toMeasure S c f hf B hB hF
  have h := ((hasDerivAt_id' (0 : ℝ)).mul_const (d₁ α I x)).add hD
  have heq : (fun t => ∫ U, averagedFlux iidCutLaw (centralLinkVariation α t U) I x ∂μ.toMeasure) =ᶠ[𝓝 0]
      (fun t => t * d₁ α I x + ∫ U, G t U ∂μ.toMeasure) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    have hη := shiftCutBlock_allowed S (t • c) (hsize t ht).le
    have hshift := measurable_shiftCutBlock S (t • c)
    have hGm : Measurable (G t) :=
      (hf.comp (measurable_fst.prodMk (hshift.comp measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable
    have hgood : ∀ᵐ U ∂μ.toMeasure,
        (averagedFlux iidCutLaw (centralLinkVariation α t U) I x = t * d₁ α I x + G t U) ∧
          |G t U| ≤ B U := by
      filter_upwards [hF] with U hU
      have hm : Measurable (fun η => f (U, shiftCutBlock S (t • c) η)) :=
        hf.comp (measurable_const.prodMk hshift)
      have hb : ∀ᵐ η ∂iidCutLaw, |f (U, shiftCutBlock S (t • c) η)| ≤ B U :=
        hη.mono fun η h => hU _ h
      have hi := Integrable.of_bound hm.aestronglyMeasurable (B U)
        (hb.mono fun η h => by simpa only [Real.norm_eq_abs] using h)
      constructor
      · unfold averagedFlux
        simp_rw [repairedCutFlux_centralLinkVariation hN Λ α hα t U _ I x]
        change (∫ η, f (U, shiftCutBlock S (t • c) η) + t * d₁ α I x ∂iidCutLaw) = _
        rw [integral_add hi (integrable_const _)]
        simp only [G, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, add_comm]
      · apply abs_integral_le_integral_abs.trans
        simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using
          integral_mono_ae hi.abs (integrable_const (B U)) hb
    have hg : Integrable (G t) μ.toMeasure := hB.mono' hGm.aestronglyMeasurable
      (hgood.mono fun U hU => by simpa only [Real.norm_eq_abs] using hU.2)
    rw [integral_congr_ae (hgood.mono fun _ h => h.1), integral_add (integrable_const _) hg]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  exact (by simpa only [one_mul, Pi.add_def] using h : HasDerivAt
    (fun t => t * d₁ α I x + ∫ U, G t U ∂μ.toMeasure)
    (d₁ α I x + cutVariationResponse Λ α μ.toMeasure I x) 0).congr_of_eventuallyEq heq

/-- Equating the two derivatives gives the weak-coupling Ward response on every finite link test. -/
theorem ward_centralVariation_periodicLimit {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (Λ : Finset InfiniteLink) (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (I : Face) (x : Site) :
    (∫ U, wilsonVariationScore Λ β α U * averagedFlux iidCutLaw U I x ∂μ.toMeasure) =
      d₁ α I x + cutVariationResponse Λ α μ.toMeasure I x := by
  have hf := measurable_averagedFlux (N := N) iidCutLaw I x
  have hi := ((iidAveragedFlux_exponential_approximation_periodicLimit hN hβ μ l hl hμ).2 I x).1
  exact (hasDerivAt_periodicLimit_centralLinkVariation hN Λ β α hα μ l hl hμ _ hf
    (hi.integrable (by norm_num))).unique
    (hasDerivAt_averagedFlux_centralLinkVariation hN hβ Λ α hα μ l hl hμ I x)

end

end GaplessYangMills

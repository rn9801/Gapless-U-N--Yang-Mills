module

public import GaplessYangMills.CutResponseKernel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Absolute summability of the cut response

The integrated response is dominated by a summable moment of one marked
component. This permits summing the closed single-cut difference before
integrating it.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped ENat ENNReal Topology

noncomputable section

private def siteRadiusBox (y : Site) (R : ℕ) : Finset Site :=
  Fintype.piFinset fun i : Axis => Finset.Icc (y i - (R : ℤ)) (y i + R)

private theorem mem_siteRadiusBox_iff (x y : Site) (R : ℕ) :
    x ∈ siteRadiusBox y R ↔ radius (x - y) ≤ R := by
  rw [siteRadiusBox, Fintype.mem_piFinset]
  constructor
  · intro h
    apply Finset.sup_le
    intro i _
    have hi := Finset.mem_Icc.mp (h i)
    simp only [Pi.sub_apply]
    omega
  · intro h i
    have hi := (natAbs_le_radius (x - y) i).trans h
    simp only [Pi.sub_apply] at hi
    exact Finset.mem_Icc.mpr (by omega)

private theorem siteRadiusBox_card (y : Site) (R : ℕ) :
    (siteRadiusBox y R).card = (2 * R + 1) ^ 4 := by
  have h (i : Axis) : (Finset.Icc (y i - (R : ℤ)) (y i + R)).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    omega
  simp [siteRadiusBox, Fintype.card_piFinset, h]

private def singleCutSizeEvent {N : ℕ} (p : Plaquette) (n : ℕ) : Set (InfiniteConfig N) :=
  {U | n = 0 ∨ ∃ i : Axis, (n : ℕ∞) ≤
    (markedComponent dualEdgeGraph {e | U ∈ markedDualLink badPlaquette e} (-p.2, i)).encard}

private def componentSizeRate (N : ℕ) (β : ℝ) : ℝ :=
  (14 : ℝ) ^ 2 * (6 * Real.exp (-(badPenalty * (N : ℝ) * β / 96)))

private theorem componentSizeRate_nonneg (N : ℕ) (β : ℝ) : 0 ≤ componentSizeRate N β := by
  unfold componentSizeRate
  positivity

private theorem twice_componentSizeRate_lt_one {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β) :
    2 * componentSizeRate N β < 1 := by
  let q := 6 * Real.exp (-(badPenalty * (N : ℝ) * β / 96))
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hp : (Real.exp (-(badPenalty * (N : ℝ) * β / 192))) ^ 2 =
      Real.exp (-(badPenalty * (N : ℝ) * β / 96)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hρ : defectTailRate N β ^ 2 = (14 : ℝ) ^ 4 * q := by
    simp only [defectTailRate, q, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), hp]
    ring
  change 2 * ((14 : ℝ) ^ 2 * q) < 1
  calc
    _ = (2 * (14 : ℝ) ^ 2) * q := (mul_assoc _ _ _).symm
    _ ≤ (14 : ℝ) ^ 4 * q := mul_le_mul_of_nonneg_right (by norm_num) hq
    _ = defectTailRate N β ^ 2 := hρ.symm
    _ < 1 := by
      have h₀ : 0 ≤ defectTailRate N β := by unfold defectTailRate; positivity
      simpa only [one_pow] using
        (sq_lt_sq₀ h₀ zero_le_one).mpr (defectTailRate_lt_one hN hβ)

private theorem measure_singleCutSizeEvent_le {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 40 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (p : Plaquette) (n : ℕ) :
    μ.toMeasure (singleCutSizeEvent p n) ≤ ENNReal.ofReal (4 * componentSizeRate N β ^ n) := by
  cases n with
  | zero =>
    rw [show singleCutSizeEvent (N := N) p 0 = Set.univ by ext; simp [singleCutSizeEvent]]
    norm_num
  | succ n =>
    let E (i : Axis) : Set (InfiniteConfig N) :=
      {U | (↑(n + 1) : ℕ∞) ≤
        (markedComponent dualEdgeGraph {e | U ∈ markedDualLink badPlaquette e} (-p.2, i)).encard}
    have hE : singleCutSizeEvent (N := N) p (n + 1) = ⋃ i, E i := by
      ext U
      simp [singleCutSizeEvent, E]
    rw [hE]
    calc
      _ ≤ ∑' i, μ.toMeasure (E i) := measure_iUnion_le E
      _ = ∑ i, μ.toMeasure (E i) := tsum_fintype _
      _ ≤ ∑ _i : Axis, ENNReal.ofReal (componentSizeRate N β ^ (n + 1)) :=
        Finset.sum_le_sum fun i _ => measure_periodicLimit_markedComponent_size_le hN hβ μ l hl hμ (-p.2, i) n
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        simp

private def singleCutMassEnvelope {N : ℕ} (μ : Measure (InfiniteConfig N)) (p : Plaquette)
    (U : InfiniteConfig N) : ℝ≥0∞ :=
  ∑' n : ℕ, (toMeasurable μ (singleCutSizeEvent p n)).indicator
    (fun _ => ENNReal.ofReal ((siteRadiusBox p.2 (2 * n + 1)).card * singleCutAmplitudeBound N n)) U

private theorem measurable_singleCutMassEnvelope {N : ℕ} (μ : Measure (InfiniteConfig N)) (p : Plaquette) :
    Measurable (singleCutMassEnvelope μ p) :=
  Measurable.tsum fun _ => measurable_const.indicator (measurableSet_toMeasurable _ _)

private theorem lintegral_singleCutMassEnvelope_lt_top {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (p : Plaquette) :
    (∫⁻ U, singleCutMassEnvelope μ.toMeasure p U ∂μ.toMeasure) < ⊤ := by
  let r := componentSizeRate N β
  let A := 2 * (N : ℝ) * (17 * Real.pi / 16) + 2 * Real.pi * (40 * (4 * (N : ℝ)))
  let b (n : ℕ) := (siteRadiusBox p.2 (2 * n + 1)).card * singleCutAmplitudeBound N n
  have hb (n : ℕ) : 0 ≤ b n := mul_nonneg (Nat.cast_nonneg _) (singleCutAmplitudeBound_nonneg N n)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hr : 0 ≤ r := componentSizeRate_nonneg N β
  have hseries : Summable (fun n : ℕ => (1024 * A) * (((n : ℝ) + 1) ^ 6 * (2 * r) ^ n)) :=
    (summable_sixth_geometric (by positivity) (twice_componentSizeRate_lt_one hN hβ)).mul_left _
  unfold singleCutMassEnvelope
  rw [lintegral_tsum fun _ => (measurable_const.indicator (measurableSet_toMeasurable _ _)).aemeasurable]
  refine lt_of_le_of_lt (tsum_le_tsum fun n => ?_) hseries.tsum_ofReal_lt_top
  change (∫⁻ U, (toMeasurable μ.toMeasure (singleCutSizeEvent p n)).indicator
    (fun _ => ENNReal.ofReal (b n)) U ∂μ.toMeasure) ≤ _
  rw [lintegral_indicator (measurableSet_toMeasurable _ _), lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, measure_toMeasurable]
  refine (mul_le_mul_of_nonneg_left (measure_singleCutSizeEvent_le hN (by linarith) μ l hl hμ p n)
    (by positivity)).trans ?_
  rw [← ENNReal.ofReal_mul (hb n)]
  apply ENNReal.ofReal_le_ofReal
  have hcard : ((siteRadiusBox p.2 (2 * n + 1)).card : ℝ) ≤ 256 * ((n : ℝ) + 1) ^ 4 := by
    rw [siteRadiusBox_card]
    push_cast
    calc
      _ ≤ (4 * ((n : ℝ) + 1)) ^ 4 := by
        apply pow_le_pow_left₀ (by positivity)
        linarith
      _ = _ := by ring
  calc
    _ ≤ (256 * ((n : ℝ) + 1) ^ 4 * singleCutAmplitudeBound N n) * (4 * r ^ n) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (singleCutAmplitudeBound_nonneg N n)) (by positivity)
    _ = _ := by
      simp only [singleCutAmplitudeBound, A, mul_pow]
      ring

private theorem singleCut_eNormMass_le_periodicLimit_ae {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (p : Plaquette) :
    ∀ᵐ U ∂μ.toMeasure, ∀ η ζ : TwoForm ℝ,
      (∀ I x, |η I x| ≤ Real.pi / 16) → (∀ I x, |ζ I x| ≤ Real.pi / 16) →
      (∀ q : Plaquette, q ≠ p → η q.1 q.2 = ζ q.1 q.2) →
      ∀ I, (∑' x, ‖repairedCutFlux (fun j y => U (j, y)) η I x -
        repairedCutFlux (fun j y => U (j, y)) ζ I x‖ₑ) ≤ singleCutMassEnvelope μ.toMeasure p U := by
  filter_upwards [singleCut_fluxDifference_amplitude_periodicLimit_ae hN hβ μ l hl hμ] with U hU
  obtain ⟨n, hn, hbound⟩ := hU p
  intro η ζ hη hζ hagree I
  let A := siteRadiusBox p.2 (2 * n + 1)
  let f (x : Site) := repairedCutFlux (fun j y => U (j, y)) η I x -
    repairedCutFlux (fun j y => U (j, y)) ζ I x
  let b := ENNReal.ofReal (singleCutAmplitudeBound N n)
  have hb (x : Site) : ‖f x‖ₑ ≤ (↑A : Set Site).indicator (fun _ => b) x := by
    rw [Real.eNorm_eq_ofReal_abs]
    apply (ENNReal.ofReal_le_ofReal (hbound η ζ hη hζ hagree I x)).trans
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem (show x ∈ (↑A : Set Site) from hx),
        ite_eq_left ((mem_siteRadiusBox_iff _ _ _).mp hx)]
    · rw [Set.indicator_of_notMem (show x ∉ (↑A : Set Site) from hx),
        ite_eq_right (mt (mem_siteRadiusBox_iff _ _ _).mpr hx), ENNReal.ofReal_zero]
  have hE : U ∈ toMeasurable μ.toMeasure (singleCutSizeEvent p n) :=
    subset_toMeasurable μ.toMeasure _ hn
  calc
    _ ≤ ∑' x, (↑A : Set Site).indicator (fun _ => b) x := tsum_le_tsum hb
    _ = ∑ _x ∈ A, b := by
      rw [tsum_eq_sum (s := A) (fun x hx =>
        Set.indicator_of_notMem (show x ∉ (↑A : Set Site) from hx) _)]
      exact Finset.sum_congr rfl (fun x hx => Set.indicator_of_mem (show x ∈ (↑A : Set Site) from hx) _)
    _ = ENNReal.ofReal ((A.card : ℝ) * singleCutAmplitudeBound N n) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp [b]
    _ ≤ _ := by
      have h := le_tsum (fun k : ℕ => (toMeasurable μ.toMeasure (singleCutSizeEvent p k)).indicator
        (fun _ => ENNReal.ofReal ((siteRadiusBox p.2 (2 * k + 1)).card * singleCutAmplitudeBound N k)) U) n
      simpa only [singleCutMassEnvelope, A, Set.indicator_of_mem hE] using h

/-- Every column of the cut response is absolutely summable and has
zero total mass in each output orientation, as in equation (6). -/
theorem singleCutResponse_hasSum_zero_periodicLimit {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (p : Plaquette) (I : Face) :
    HasSum (singleCutResponse μ.toMeasure p I) 0 := by
  let S : Finset Plaquette := {p}
  let w := shiftedCutDensityDerivative S (fun _ => 1) 0
  let ν := μ.toMeasure.prod (cutBlockReference S)
  let η (z : InfiniteConfig N × (CutBlock S × CutExterior S)) := (splitCutField S).symm z.2
  let g (x : Site) (z : InfiniteConfig N × (CutBlock S × CutExterior S)) :=
    w z.2.1 * (repairedCutFlux (fun j y => z.1 (j, y)) (η z) I x -
      repairedCutFlux (fun j y => z.1 (j, y)) (resetCut p (η z)) I x)
  have hη : Measurable η := (splitCutField S).symm.measurable.comp measurable_snd
  have hw : Continuous w := continuous_shiftedCutDensityDerivative_fixed S (fun _ => 1) 0
  have hg (x : Site) : Measurable (g x) := by
    let X := InfiniteConfig N × (CutBlock S × CutExterior S)
    let f (q : InfiniteConfig N × TwoForm ℝ) :=
      repairedCutFlux (fun j y => q.1 (j, y)) q.2 I x
    let L (z : X) := (z.1, η z)
    let R (z : X) := (z.1, resetCut p (η z))
    have hf : Measurable f := measurable_repairedCutFlux_coordinate I x
    have hL : Measurable L := measurable_fst.prodMk hη
    have hR : Measurable R :=
      measurable_fst.prodMk ((measurable_resetCut p).comp hη)
    have hW : Measurable (fun z : X => w z.2.1) :=
      hw.measurable.comp (measurable_fst.comp measurable_snd)
    have hh : Measurable (fun z : X => w z.2.1 * ((f ∘ L) z - (f ∘ R) z)) :=
      hW.mul ((hf.comp hL).sub (hf.comp hR))
    exact hh
  have hallow : ∀ᵐ z ∂ν, ∀ J y, |η z J y| ≤ Real.pi / 16 :=
    Measure.quasiMeasurePreserving_snd.ae (joinedCutBlockReference_allowed S)
  have hbox : ∀ᵐ z : InfiniteConfig N × (CutBlock S × CutExterior S) ∂ν, z.2.1 ∈ cutBlockBox S :=
    Measure.quasiMeasurePreserving_snd.ae
      ((Measure.quasiMeasurePreserving_fst (μ := volume.restrict (cutBlockBox S)) (ν := cutExteriorLaw S)).ae
        (ae_restrict_mem (isCompact_cutBlockBox S).isClosed.measurableSet))
  have hagree (z : InfiniteConfig N × (CutBlock S × CutExterior S)) (q : Plaquette) (hq : q ≠ p) :
      η z q.1 q.2 = resetCut p (η z) q.1 q.2 := by
    obtain ⟨J, y⟩ := q
    simp only [resetCut, ite_eq_right hq]
  obtain ⟨C, hC⟩ := ((isCompact_cutBlockBox S).image hw.norm).bddAbove
  have hpoint : ∀ᵐ z ∂ν, (∑' x, ‖g x z‖ₑ) ≤
      ENNReal.ofReal C * singleCutMassEnvelope μ.toMeasure p z.1 := by
    have hb := (Measure.quasiMeasurePreserving_fst (μ := μ.toMeasure) (ν := cutBlockReference S)).ae
        (singleCut_eNormMass_le_periodicLimit_ae hN hβ μ l hl hμ p)
    filter_upwards [hb, hallow, hbox] with z hU hz hzb
    have hW : ‖w z.2.1‖ₑ ≤ ENNReal.ofReal C := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC ⟨z.2.1, hzb, rfl⟩)
    have hd := hU (η z) (resetCut p (η z)) hz (resetCut_allowed p _ hz) (hagree z) I
    calc
      _ ≤ ∑' x, ENNReal.ofReal C * ‖repairedCutFlux (fun j y => z.1 (j, y)) (η z) I x -
          repairedCutFlux (fun j y => z.1 (j, y)) (resetCut p (η z)) I x‖ₑ := by
        apply tsum_le_tsum
        intro x
        change ‖w z.2.1 * (repairedCutFlux (fun j y => z.1 (j, y)) (η z) I x -
          repairedCutFlux (fun j y => z.1 (j, y)) (resetCut p (η z)) I x)‖ₑ ≤ _
        rw [eNorm_mul]
        exact mul_le_mul_of_nonneg_right hW (by positivity)
      _ ≤ _ := by
        rw [ENNReal.tsum_mul_left]
        exact mul_le_mul_of_nonneg_left hd (by positivity)
  have hFin : (∑' x, ∫⁻ z, ‖g x z‖ₑ ∂ν) ≠ ⊤ := by
    rw [← lintegral_tsum (fun x => (hg x).aemeasurable.eNorm)]
    apply ne_top_of_le_ne_top _ (lintegral_mono_ae hpoint)
    have hm := measurable_singleCutMassEnvelope μ.toMeasure p
    let f := singleCutMassEnvelope μ.toMeasure p ∘
      (Prod.fst : InfiniteConfig N × (CutBlock S × CutExterior S) → InfiniteConfig N)
    have hf : Measurable f := hm.comp measurable_fst
    change (∫⁻ z, ENNReal.ofReal C * f z ∂ν) ≠ ⊤
    rw [lintegral_const_mul _ hf]
    change ENNReal.ofReal C * (∫⁻ z, f z ∂μ.toMeasure.prod (cutBlockReference S)) ≠ ⊤
    rw [lintegral_prod _]
    · change ENNReal.ofReal C * (∫⁻ U, ∫⁻ _y, singleCutMassEnvelope μ.toMeasure p U
        ∂cutBlockReference S ∂μ.toMeasure) ≠ ⊤
      simp only [lintegral_const]
      rw [lintegral_mul_const _ hm]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (lintegral_singleCutMassEnvelope_lt_top hN hβ μ l hl hμ p).ne (measure_ne_top _ _))
    · exact hf.aemeasurable
  have hi (x : Site) : Integrable (g x) ν := by
    refine ⟨(hg x).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    exact (le_tsum (fun y => ∫⁻ z, ‖g y z‖ₑ ∂ν) x).trans_lt hFin.lt_top
  let d (x : Site) : NNReal := ⟨∫ z, ‖g x z‖ ∂ν, integral_nonneg fun z => norm_nonneg _⟩
  have hnorm (x : Site) : (d x : ℝ≥0∞) = ∫⁻ z, ‖g x z‖ₑ ∂ν := by
    simpa only [show (d x : ℝ) = ∫ z, ‖g x z‖ ∂ν from rfl, ← ENNReal.ofReal_coe_nnreal]
      using ofReal_integral_norm_eq_lintegral_eNorm (hi x)
  have hSum : Summable (fun x => ∫ z, ‖g x z‖ ∂ν) := by
    change Summable (fun x => (d x : ℝ))
    apply NNReal.summable_coe.mpr
    apply ENNReal.tsum_coe_ne_top_iff_summable.mp
    simpa only [hnorm] using hFin
  have h := hasSum_integral_of_summable_integral_norm hi hSum
  have hzero : ∀ᵐ z ∂ν, (∑' x, g x z) = 0 := by
    have hc := (Measure.quasiMeasurePreserving_fst (μ := μ.toMeasure) (ν := cutBlockReference S)).ae
      (tsum_singleCut_fluxDifference_eq_zero_periodicLimit_ae hN hβ μ l hl hμ)
    filter_upwards [hc, hallow] with z hz hy
    simp only [g, tsum_mul_left, hz p (η z) (resetCut p (η z)) hy (resetCut_allowed p _ hy) (hagree z) I, mul_zero]
  have heq : (∫ z, ∑' x, g x z ∂ν) = 0 :=
    (integral_congr_ae hzero).trans (integral_zero _ _)
  rw [heq] at h
  convert h using 1
  funext x
  exact singleCutResponse_eq_resetDifference hN hβ μ l hl hμ p I x

theorem wilsonCutResponseKernel_hasSum_zero {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (I J : Face) :
    HasSum (wilsonCutResponseKernel μ.toMeasure I J) 0 := by
  change HasSum (fun x => singleCutResponse μ.toMeasure (J, 0) I x / (N : ℝ)) 0
  simpa only [div_eq_mul_inv, zero_mul] using
    (singleCutResponse_hasSum_zero_periodicLimit hN hβ μ l hl hμ (J, 0) I).mul_right ((N : ℝ)⁻¹)

/-- The actual unprojected Wilson covariance cannot be absolutely summable. -/
theorem wilsonFluxCurrentCovariance_not_summable {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ¬ ∀ I J, Summable (wilsonFluxCurrentCovariance μ.toMeasure I J) :=
  not_summable_of_ward β _ _
    (wilsonFluxCurrentCovariance_closed hN hβ μ l hl hμ)
    (wilsonFluxCurrentCovariance_wardResponse hN hβ μ l hl hμ)
    (fun I J => (wilsonCutResponseKernel_hasSum_zero hN hβ μ l hl hμ I J).summable)
    (wilsonCutResponseKernel_hasSum_zero hN hβ μ l hl hμ .xy .xy).tsum_eq

end

end GaplessYangMills

module

public import GaplessYangMills.CutSensitivity
public import GaplessYangMills.WardTest
public import GaplessYangMills.WilsonCovariance

/-!
# The coefficients of the cut response

The response to a finite cut displacement is the sum of its single-cut
responses. The same single-coordinate derivative can be computed in any
finite block containing that coordinate.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped Topology

noncomputable section

def singleCutDirection (S : Finset Plaquette) (p : {q // q ∈ S}) : CutBlock S :=
  fun q => if q = p then 1 else 0

private theorem shiftedCutDensityDerivative_single_zero (S : Finset Plaquette)
    (p : {q // q ∈ S}) (y : CutBlock S) :
    shiftedCutDensityDerivative S (singleCutDirection S p) 0 y =
      (∏ r ∈ Finset.univ.erase p, cutDensity (y r)) * deriv cutDensity (y p) := by
  simp only [shiftedCutDensityDerivative, zero_mul, add_zero]
  rw [Finset.sum_eq_single p]
  · simp [singleCutDirection]
  · intro q _ hq
    simp [singleCutDirection, hq]
  · simp

private theorem shiftedCutDensityDerivative_zero_expand (S : Finset Plaquette)
    (c : CutBlock S) (y : CutBlock S) :
    shiftedCutDensityDerivative S c 0 y =
      ∑ p : {q // q ∈ S}, c p * shiftedCutDensityDerivative S (singleCutDirection S p) 0 y := by
  simp only [shiftedCutDensityDerivative_single_zero]
  simp only [shiftedCutDensityDerivative, zero_mul, add_zero]
  exact Finset.sum_congr rfl (fun p _ => by ring)

private theorem shiftCutBlock_coordinate (S : Finset Plaquette) (v : CutBlock S) (η : TwoForm ℝ)
    (p : Plaquette) :
    shiftCutBlock S v η p.1 p.2 = if h : p ∈ S then η p.1 p.2 - v ⟨p, h⟩ else η p.1 p.2 := by
  rw [shiftCutBlock, splitCutField_symm_apply S _ _ p]
  rfl

private theorem shiftCutBlock_single (S : Finset Plaquette) (p : {q // q ∈ S}) (t : ℝ) (η : TwoForm ℝ) :
    shiftCutBlock S (t • singleCutDirection S p) η =
      shiftCutBlock ({p.val} : Finset Plaquette) (t • (fun _ => 1 : CutBlock {p.val})) η := by
  funext I x
  let q : Plaquette := (I, x)
  change shiftCutBlock S (t • singleCutDirection S p) η q.1 q.2 = _
  rw [shiftCutBlock_coordinate S _ _ q, shiftCutBlock_coordinate {p.val} _ _ q]
  by_cases h : q = p.val
  · have hS : q ∈ S := h ▸ p.property
    have hp : q ∈ ({p.val} : Finset Plaquette) := Finset.mem_singleton.mpr h
    have he : (⟨q, hS⟩ : {q // q ∈ S}) = p := Subtype.ext h
    simp only [dite_eq_left hS, dite_eq_left hp, Pi.smul_apply, smul_eq_mul, he, singleCutDirection,
      ite_true, mul_one]
  · have hp : q ∉ ({p.val} : Finset Plaquette) := fun hp => h (Finset.mem_singleton.mp hp)
    rw [dite_eq_right hp]
    by_cases hS : q ∈ S
    · have he : (⟨q, hS⟩ : {q // q ∈ S}) ≠ p := fun he => h (congrArg Subtype.val he)
      simp only [dite_eq_left hS, Pi.smul_apply, smul_eq_mul, singleCutDirection, ite_eq_right he, mul_zero, sub_zero]
    · rw [dite_eq_right hS]

def integratedCutDerivative {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Finset Plaquette) (c : CutBlock S) (f : Ω × TwoForm ℝ → ℝ) : ℝ :=
  ∫ p : Ω × (CutBlock S × CutExterior S),
    shiftedCutDensityDerivative S c 0 p.2.1 * f (p.1, (splitCutField S).symm p.2)
      ∂μ.prod (cutBlockReference S)

private theorem integrable_on_cutBlockReference {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : Finset Plaquette)
    (f : Ω × TwoForm ℝ → ℝ) (hf : Measurable f) (B : Ω → ℝ) (hB : Integrable B μ)
    (hbound : ∀ᵐ u ∂μ, ∀ η : TwoForm ℝ, (∀ I x, |η I x| ≤ Real.pi / 16) → |f (u, η)| ≤ B u)
    {w : CutBlock S → ℝ} (hw : Continuous w) :
    Integrable (fun p : Ω × (CutBlock S × CutExterior S) => w p.2.1 * f (p.1, (splitCutField S).symm p.2))
      (μ.prod (cutBlockReference S)) := by
  let ν := μ.prod (cutBlockReference S)
  let m := volume.restrict (cutBlockBox S)
  have h₁ : ∀ᵐ p ∂ν, ∀ η : TwoForm ℝ, (∀ I x, |η I x| ≤ Real.pi / 16) → |f (p.1, η)| ≤ B p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hbound
  have h₂ : ∀ᵐ p ∂ν, ∀ I x, |(splitCutField S).symm p.2 I x| ≤ Real.pi / 16 :=
    Measure.quasiMeasurePreserving_snd.ae (joinedCutBlockReference_allowed S)
  have hbox : ∀ᵐ p : Ω × (CutBlock S × CutExterior S) ∂ν, p.2.1 ∈ cutBlockBox S :=
    Measure.quasiMeasurePreserving_snd.ae
      ((Measure.quasiMeasurePreserving_fst (μ := m) (ν := cutExteriorLaw S)).ae
        (ae_restrict_mem (isCompact_cutBlockBox S).isClosed.measurableSet))
  obtain ⟨C, hC⟩ := ((isCompact_cutBlockBox S).image hw.norm).bddAbove
  have hInt : Integrable (fun p : Ω × (CutBlock S × CutExterior S) => C * B p.1) ν :=
    (hB.comp_fst (cutBlockReference S)).const_mul C
  have hF : Measurable (fun p : Ω × (CutBlock S × CutExterior S) =>
      f (p.1, (splitCutField S).symm p.2)) :=
    hf.comp (measurable_fst.prodMk ((splitCutField S).symm.measurable.comp measurable_snd))
  refine hInt.mono' ((hw.measurable.comp (measurable_fst.comp measurable_snd)).mul hF).aestronglyMeasurable ?_
  filter_upwards [h₁, h₂, hbox] with p hp hη hy
  have hW : ‖w p.2.1‖ ≤ C := hC ⟨p.2.1, hy, rfl⟩
  rw [norm_mul]
  exact mul_le_mul hW (by simpa only [Real.norm_eq_abs] using hp _ hη) (norm_nonneg _)
    ((norm_nonneg _).trans hW)

private theorem integratedCutDerivative_single {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S : Finset Plaquette) (p : {q // q ∈ S})
    (f : Ω × TwoForm ℝ → ℝ) (hf : Measurable f) (B : Ω → ℝ) (hB : Integrable B μ)
    (hbound : ∀ᵐ u ∂μ, ∀ η : TwoForm ℝ, (∀ I x, |η I x| ≤ Real.pi / 16) → |f (u, η)| ≤ B u) :
    integratedCutDerivative μ S (singleCutDirection S p) f =
      integratedCutDerivative μ {p.val} (fun _ => 1) f := by
  have h₁ := hasDerivAt_integral_shiftCutBlock μ S (singleCutDirection S p) f hf B hB hbound
  have h₂ := hasDerivAt_integral_shiftCutBlock μ ({p.val} : Finset Plaquette)
    (fun _ => 1) f hf B hB hbound
  simp_rw [shiftCutBlock_single S p] at h₁
  exact h₁.unique h₂

def singleCutResponse {N : ℕ} (μ : Measure (InfiniteConfig N)) (p : Plaquette) (I : Face) (x : Site) : ℝ :=
  integratedCutDerivative μ {p} (fun _ => 1) (fun q =>
    repairedCutFlux (fun j y => q.1 (j, y)) q.2 I x)

theorem continuous_shiftedCutDensityDerivative_fixed (S : Finset Plaquette)
    (c : CutBlock S) (t : ℝ) :
    Continuous (shiftedCutDensityDerivative S c t) := by
  have hp : Continuous (fun y : CutBlock S => (t, y)) := continuous_const.prodMk continuous_id
  have h := (continuous_shiftedCutDensityDerivative S c).comp hp
  simpa only [Function.comp_def] using h

/-- Expanding the finite product derivative gives the response coefficient
of each varied plaquette, with the rank factor of the cut displacement. -/
theorem cutVariationResponse_eq_sum_single {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (Λ : Finset InfiniteLink) (α : OneForm ℝ)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (I : Face) (x : Site) :
    cutVariationResponse Λ α μ.toMeasure I x =
      ∑ p ∈ affectedPlaquettes Λ, (d₁ α p.1 p.2 / (N : ℝ)) * singleCutResponse μ.toMeasure p I x := by
  let S := affectedPlaquettes Λ
  let c := linkCutDirection N Λ α
  let f (q : InfiniteConfig N × TwoForm ℝ) := repairedCutFlux (fun j y => q.1 (j, y)) q.2 I x
  have hf : Measurable f := measurable_repairedCutFlux_coordinate I x
  obtain ⟨B, _, hB, _, hbound⟩ := exists_integrable_cutFluxBound_periodicLimit hN hβ μ l hl hμ I x
  let ν := μ.toMeasure.prod (cutBlockReference S)
  have hInt (p : {q // q ∈ S}) : Integrable (fun q : InfiniteConfig N × (CutBlock S × CutExterior S) =>
      shiftedCutDensityDerivative S (singleCutDirection S p) 0 q.2.1 * f (q.1, (splitCutField S).symm q.2)) ν :=
    integrable_on_cutBlockReference μ.toMeasure S f hf B hB hbound
      (continuous_shiftedCutDensityDerivative_fixed S (singleCutDirection S p) 0)
  change (∫ q, shiftedCutDensityDerivative S c 0 q.2.1 * f (q.1, (splitCutField S).symm q.2) ∂ν) = _
  simp_rw [shiftedCutDensityDerivative_zero_expand S c, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun p _ => (hInt p).const_mul (c p))]
  simp_rw [integral_const_mul]
  change (∑ p : {q // q ∈ S}, c p * integratedCutDerivative μ.toMeasure S (singleCutDirection S p) f) = _
  simp_rw [integratedCutDerivative_single μ.toMeasure S _ f hf B hB hbound]
  let G (p : Plaquette) := d₁ α p.1 p.2 / (N : ℝ) * singleCutResponse μ.toMeasure p I x
  change (∑ p : {q // q ∈ S}, G p.val) = ∑ p ∈ S, G p
  exact Finset.sum_attach S G

private theorem translateCutField_shift_single (a : Site) (p : Plaquette) (t : ℝ) (η : TwoForm ℝ) :
    translateCutField a (shiftCutBlock {(p.1, p.2 + a)} (t • (fun _ => 1)) η) =
      shiftCutBlock {p} (t • (fun _ => 1)) (translateCutField a η) := by
  funext I x
  change shiftCutBlock ({(p.1, p.2 + a)} : Finset Plaquette) (t • (fun _ => 1)) η I (x + a) =
    shiftCutBlock ({p} : Finset Plaquette) (t • (fun _ => 1)) (translateCutField a η) I x
  rw [shiftCutBlock_coordinate _ _ _ (I, x + a), shiftCutBlock_coordinate _ _ _ (I, x)]
  by_cases h : (I, x) = p
  · have ht : (I, x + a) = (p.1, p.2 + a) :=
      congrArg (fun q : Plaquette => (q.1, q.2 + a)) h
    simp only [dite_eq_left (Finset.mem_singleton.mpr h), dite_eq_left (Finset.mem_singleton.mpr ht),
      Pi.smul_apply, smul_eq_mul, mul_one]
    rfl
  · have ht : (I, x + a) ≠ (p.1, p.2 + a) := by
      intro he
      have hi : I = p.1 := congrArg (fun q : Plaquette => q.1) he
      have hx : x + a = p.2 + a := congrArg (fun q : Plaquette => q.2) he
      exact h (Prod.ext hi (add_right_cancel hx))
    simp only [dite_eq_right (mt Finset.mem_singleton.mp h), dite_eq_right (mt Finset.mem_singleton.mp ht)]
    rfl

theorem singleCutResponse_translate {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (a : Site) (p : Plaquette) (I : Face) (x : Site) :
    singleCutResponse μ.toMeasure (p.1, p.2 + a) I (x + a) = singleCutResponse μ.toMeasure p I x := by
  let p' : Plaquette := (p.1, p.2 + a)
  let f (q : InfiniteConfig N × TwoForm ℝ) := repairedCutFlux (fun j y => q.1 (j, y)) q.2 I x
  let f' (q : InfiniteConfig N × TwoForm ℝ) := repairedCutFlux (fun j y => q.1 (j, y)) q.2 I (x + a)
  have hf : Measurable f := measurable_repairedCutFlux_coordinate I x
  have hf' : Measurable f' := measurable_repairedCutFlux_coordinate I (x + a)
  obtain ⟨B, _, hB, _, hbound⟩ := exists_integrable_cutFluxBound_periodicLimit hN hβ μ l hl hμ I x
  obtain ⟨B', _, hB', _, hbound'⟩ := exists_integrable_cutFluxBound_periodicLimit hN hβ μ l hl hμ I (x + a)
  have h := hasDerivAt_integral_shiftCutBlock μ.toMeasure {p} (fun _ => 1) f hf B hB hbound
  have h' := hasDerivAt_integral_shiftCutBlock μ.toMeasure {p'} (fun _ => 1) f' hf' B' hB' hbound'
  have heq : (fun t : ℝ => ∫ U, ∫ η, f' (U, shiftCutBlock {p'} (t • (fun _ => 1)) η) ∂iidCutLaw ∂μ.toMeasure) =
      (fun t : ℝ => ∫ U, ∫ η, f (U, shiftCutBlock {p} (t • (fun _ => 1)) η) ∂iidCutLaw ∂μ.toMeasure) := by
    funext t
    let s := shiftCutBlock {p} (t • (fun _ => 1))
    let G (U : InfiniteConfig N) := ∫ η, f (U, s η) ∂iidCutLaw
    have hs : Measurable s := measurable_shiftCutBlock _ _
    have hG : Measurable G :=
      (hf.comp (measurable_fst.prodMk (hs.comp measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable
    calc
      _ = ∫ U, ∫ η, f (translateConfig a U, s (translateCutField a η)) ∂iidCutLaw ∂μ.toMeasure := by
        apply integral_congr_ae
        refine ae_of_all _ fun U => integral_congr_ae (ae_of_all _ fun η => ?_)
        change f' (U, shiftCutBlock {p'} (t • (fun _ => 1)) η) =
          f (translateConfig a U, s (translateCutField a η))
        rw [show s (translateCutField a η) =
          translateCutField a (shiftCutBlock {p'} (t • (fun _ => 1)) η) from
            (translateCutField_shift_single a p t η).symm]
        exact (repairedCutFlux_translate a U (shiftCutBlock {p'} (t • (fun _ => 1)) η) I x).symm
      _ = ∫ U, G (translateConfig a U) ∂μ.toMeasure :=
        integral_congr_ae (ae_of_all _ fun U =>
          (translateCutField_preserving a).integral_comp' (fun η => f (translateConfig a U, s η)))
      _ = _ := integral_translateConfig β μ hμ a G hG
  rw [heq] at h'
  exact h'.unique h

def resetCut (p : Plaquette) (η : TwoForm ℝ) : TwoForm ℝ :=
  fun I x => if (I, x) = p then 0 else η I x

theorem measurable_resetCut (p : Plaquette) : Measurable (resetCut p) := by
  apply measurable_pi_iff.mpr
  intro I
  apply measurable_pi_iff.mpr
  intro x
  by_cases hp : (I, x) = p
  · simp only [resetCut, ite_eq_left hp]
    exact measurable_const
  · simp only [resetCut, ite_eq_right hp]
    exact (measurable_pi_apply x).comp (measurable_pi_apply I)

private theorem resetCut_shift_single (p : Plaquette) (t : ℝ) (η : TwoForm ℝ) :
    resetCut p (shiftCutBlock {p} (t • (fun _ => 1)) η) = resetCut p η := by
  funext I x
  by_cases h : (I, x) = p
  · simp only [resetCut, ite_eq_left h]
  · simp only [resetCut, ite_eq_right h]
    rw [shiftCutBlock_coordinate {p} _ _ (I, x), dite_eq_right (mt Finset.mem_singleton.mp h)]

theorem resetCut_allowed (p : Plaquette) (η : TwoForm ℝ) (hη : ∀ I x, |η I x| ≤ Real.pi / 16) :
    ∀ I x, |resetCut p η I x| ≤ Real.pi / 16 := by
  intro I x
  by_cases h : (I, x) = p
  · simp only [resetCut, ite_eq_left h, abs_zero]
    positivity
  · simpa only [resetCut, ite_eq_right h] using hη I x

theorem singleCutResponse_eq_resetDifference {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (p : Plaquette) (I : Face) (x : Site) :
    singleCutResponse μ.toMeasure p I x =
      integratedCutDerivative μ.toMeasure {p} (fun _ => 1) (fun q =>
        repairedCutFlux (fun j y => q.1 (j, y)) q.2 I x -
          repairedCutFlux (fun j y => q.1 (j, y)) (resetCut p q.2) I x) := by
  let S : Finset Plaquette := {p}
  let c : CutBlock S := fun _ => 1
  let f (q : InfiniteConfig N × TwoForm ℝ) := repairedCutFlux (fun j y => q.1 (j, y)) q.2 I x
  let f₀ (q : InfiniteConfig N × TwoForm ℝ) := f (q.1, resetCut p q.2)
  have hf : Measurable f := measurable_repairedCutFlux_coordinate I x
  have hf₀ : Measurable f₀ := hf.comp (measurable_fst.prodMk ((measurable_resetCut p).comp measurable_snd))
  obtain ⟨B, _, hB, _, hbound⟩ := exists_integrable_cutFluxBound_periodicLimit hN hβ μ l hl hμ I x
  have hb₀ : ∀ᵐ U ∂μ.toMeasure, ∀ η : TwoForm ℝ, (∀ J y, |η J y| ≤ Real.pi / 16) → |f₀ (U, η)| ≤ B U :=
    hbound.mono fun _ h η hη => h _ (resetCut_allowed p η hη)
  have h₀ := hasDerivAt_integral_shiftCutBlock μ.toMeasure S c f₀ hf₀ B hB hb₀
  have hEq : (fun t : ℝ => ∫ U, ∫ η, f₀ (U, shiftCutBlock S (t • c) η) ∂iidCutLaw ∂μ.toMeasure) =
      fun _ : ℝ => ∫ U, ∫ η, f₀ (U, η) ∂iidCutLaw ∂μ.toMeasure := by
    funext t
    simp only [f₀, S, c, resetCut_shift_single]
  rw [hEq] at h₀
  have hz : integratedCutDerivative μ.toMeasure S c f₀ = 0 := h₀.unique (hasDerivAt_const _ _)
  let w (y : CutBlock S) := shiftedCutDensityDerivative S c 0 y
  have hw : Continuous w := continuous_shiftedCutDensityDerivative_fixed S c 0
  let ν := μ.toMeasure.prod (cutBlockReference S)
  have hi := integrable_on_cutBlockReference μ.toMeasure S f hf B hB hbound hw
  have hi₀ := integrable_on_cutBlockReference μ.toMeasure S f₀ hf₀ B hB hb₀ hw
  change integratedCutDerivative μ.toMeasure S c f =
    integratedCutDerivative μ.toMeasure S c (fun q => f q - f₀ q)
  rw [← sub_zero (integratedCutDerivative μ.toMeasure S c f), ← hz]
  unfold integratedCutDerivative
  rw [← integral_sub hi hi₀]
  exact integral_congr_ae (ae_of_all _ fun q => by dsimp only [w]; rw [mul_sub])

def wilsonCutResponseKernel {N : ℕ} (μ : Measure (InfiniteConfig N)) : Kernel :=
  fun I J x => singleCutResponse μ (J, 0) I x / N

/-- Equation (7) for the actual Wilson state and the cut-response kernel. -/
theorem wilsonFluxCurrentCovariance_wardResponse {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    WardResponse β (wilsonFluxCurrentCovariance μ.toMeasure) (wilsonCutResponseKernel μ.toMeasure) := by
  intro I
  funext i x
  let S := affectedPlaquettes ({(i, 0)} : Finset InfiniteLink)
  let α := unitLinkTest i
  let K := wilsonFluxCurrentCovariance μ.toMeasure
  let C := wilsonCutResponseKernel μ.toMeasure
  have h := wilsonFluxCurrentCovariance_ward_test hN hβ {(i, 0)} α (unitLinkTest_support i) μ l hl hμ I x
  have hR : cutVariationResponse {(i, 0)} α μ.toMeasure I x =
      ∑ p ∈ S, d₁ α p.1 p.2 * C I p.1 (x - p.2) := by
    rw [cutVariationResponse_eq_sum_single hN hβ _ α μ l hl hμ I x]
    apply Finset.sum_congr rfl
    intro p _
    have hT : singleCutResponse μ.toMeasure p I x = singleCutResponse μ.toMeasure (p.1, 0) I (x - p.2) := by
      have ht := singleCutResponse_translate hN hβ μ l hl hμ p.2 (p.1, 0) I (x - p.2)
      simpa only [zero_add, sub_add_cancel, Prod.eta] using ht
    rw [hT]
    change (d₁ α p.1 p.2 / (N : ℝ)) * _ = d₁ α p.1 p.2 * (_ / (N : ℝ))
    ring
  rw [hR] at h
  change rightDerivative (fun I J y => β * K I J y - (identityKernel I J y + C I J y)) I i x = 0
  rw [rightDerivative_eq_unitLink_test]
  calc
    _ = β * (∑ p ∈ S, d₁ α p.1 p.2 * K I p.1 (x - p.2)) -
        (d₁ α I x + ∑ p ∈ S, d₁ α p.1 p.2 * C I p.1 (x - p.2)) := by
      rw [Finset.mul_sum, ← unitLink_test_identityKernel I i x, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      change d₁ α p.1 p.2 * (β * K I p.1 (x - p.2) - (identityKernel I p.1 (x - p.2) + C I p.1 (x - p.2))) =
          β * (d₁ α p.1 p.2 * K I p.1 (x - p.2)) -
            (d₁ α p.1 p.2 * identityKernel I p.1 (x - p.2) + d₁ α p.1 p.2 * C I p.1 (x - p.2))
      ring
    _ = 0 := sub_eq_zero.mpr h

end

end GaplessYangMills

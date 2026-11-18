module

public import GaplessYangMills.CutResponse
public import GaplessYangMills.FluxSymmetries
public import GaplessYangMills.Ward

/-!
# The Wilson flux-current covariance

Translation invariance puts the covariance in displacement coordinates.
Closedness and the finite-test response then hold for this actual Wilson
covariance.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

theorem integral_translateConfig {N : ℕ} (β : ℝ) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (a : Site) (f : InfiniteConfig N → ℝ) (hf : Measurable f) :
    (∫ U, f (translateConfig a U) ∂μ.toMeasure) = ∫ U, f U ∂μ.toMeasure := by
  have hmap : μ.toMeasure.map (translateConfig a) = μ.toMeasure :=
    congrArg ProbabilityMeasure.toMeasure (periodicWilson_limit_translate β μ hμ a)
  rw [← integral_map (continuous_translateConfig a).measurable.aemeasurable
    hf.stronglyMeasurable.aestronglyMeasurable, hmap]

private theorem plaquetteCurrent_translateConfig {N : ℕ} (a : Site) (U : InfiniteConfig N)
    (I : Face) (x : Site) : plaquetteCurrent (translateConfig a U) (I, x) = plaquetteCurrent U (I, x + a) := by
  cases I <;> simp only [plaquetteCurrent, plaquetteHolonomy, Face.axes, translateConfig, add_right_comm x]

def centeredPlaquetteCurrent {N : ℕ} (m : Measure (InfiniteConfig N)) (U : InfiniteConfig N) (p : Plaquette) : ℝ :=
  plaquetteCurrent U p - ∫ V, plaquetteCurrent V p ∂m

private theorem continuous_centeredPlaquetteCurrent {N : ℕ} (m : Measure (InfiniteConfig N)) (p : Plaquette) :
    Continuous (fun U => centeredPlaquetteCurrent m U p) :=
  (continuous_plaquetteCurrent p).sub continuous_const

private theorem centeredPlaquetteCurrent_translateConfig {N : ℕ} (β : ℝ) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (a : Site) (U : InfiniteConfig N) (I : Face) (x : Site) :
    centeredPlaquetteCurrent μ.toMeasure (translateConfig a U) (I, x) =
      centeredPlaquetteCurrent μ.toMeasure U (I, x + a) := by
  have h := integral_translateConfig β μ hμ a _ (continuous_plaquetteCurrent (I, x)).measurable
  simp_rw [plaquetteCurrent_translateConfig] at h
  simp only [centeredPlaquetteCurrent, plaquetteCurrent_translateConfig, h]

def wilsonFluxCurrentCovariance {N : ℕ} (m : Measure (InfiniteConfig N)) (I J : Face) (x : Site) : ℝ :=
  ∫ U, averagedFlux iidCutLaw U I x * centeredPlaquetteCurrent m U (J, 0) ∂m

private theorem integral_flux_mul_current_eq_covariance {N : ℕ} (β : ℝ) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (I : Face) (x : Site) (p : Plaquette) :
    (∫ U, averagedFlux iidCutLaw U I x * centeredPlaquetteCurrent μ.toMeasure U p ∂μ.toMeasure) =
      wilsonFluxCurrentCovariance μ.toMeasure I p.1 (x - p.2) := by
  obtain ⟨J, y⟩ := p
  let f (U : InfiniteConfig N) :=
    averagedFlux iidCutLaw U I (x - y) * centeredPlaquetteCurrent μ.toMeasure U (J, 0)
  have hf : Measurable f := (measurable_averagedFlux iidCutLaw I (x - y)).mul
    (continuous_centeredPlaquetteCurrent μ.toMeasure (J, 0)).measurable
  rw [wilsonFluxCurrentCovariance, ← integral_translateConfig β μ hμ y f hf]
  apply integral_congr_ae
  exact ae_of_all _ fun U => by
    simp only [f, iidAveragedFlux_translate, centeredPlaquetteCurrent_translateConfig β μ hμ,
      sub_add_cancel, zero_add]

private theorem integrable_flux_mul_centeredCurrent {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (I : Face) (x : Site) (p : Plaquette) :
    Integrable (fun U => averagedFlux iidCutLaw U I x * centeredPlaquetteCurrent μ.toMeasure U p) μ.toMeasure := by
  have hF := ((iidAveragedFlux_exponential_approximation_periodicLimit hN hβ μ l hl hμ).2 I x).1
  have hj := continuous_centeredPlaquetteCurrent μ.toMeasure p
  obtain ⟨C, hC⟩ := (isCompact_univ.image hj.norm).bddAbove
  exact (hF.integrable (by norm_num)).mul_bdd hj.measurable.aestronglyMeasurable
    (ae_of_all _ fun U => hC ⟨U, Set.mem_univ _, rfl⟩)

theorem wilsonFluxCurrentCovariance_closed {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (J : Face) :
    d₂ (fun I => wilsonFluxCurrentCovariance μ.toMeasure I J) = 0 := by
  funext c x
  unfold wilsonFluxCurrentCovariance
  rw [d₂_integral μ.toMeasure _ (fun I y =>
    integrable_flux_mul_centeredCurrent hN hβ μ l hl hμ I y (J, 0))]
  have hC : ∀ᵐ U ∂μ.toMeasure, d₂ (averagedFlux iidCutLaw U) = 0 :=
    averagedFlux_closed_periodicLimit_ae iidCutLaw iidCutLaw_allowed hN hβ μ l hl hμ
  have hz : (fun U => d₂ (fun I y => averagedFlux iidCutLaw U I y *
      centeredPlaquetteCurrent μ.toMeasure U (J, 0)) c x) =ᵐ[μ.toMeasure] (fun _ => 0) :=
    hC.mono fun U hU => by
      have h (c : Cube) :
        d₂ (fun I y => averagedFlux iidCutLaw U I y * centeredPlaquetteCurrent μ.toMeasure U (J, 0)) c x =
          d₂ (averagedFlux iidCutLaw U) c x * centeredPlaquetteCurrent μ.toMeasure U (J, 0) := by
        cases c <;> simp only [d₂, diff, Pi.add_apply, Pi.sub_apply] <;> ring
      change d₂ (fun I y => averagedFlux iidCutLaw U I y *
        centeredPlaquetteCurrent μ.toMeasure U (J, 0)) c x = 0
      rw [h c, hU]
      simp only [Pi.zero_apply, zero_mul]
  rw [integral_congr_ae hz, Pi.zero_apply, Pi.zero_apply]
  exact integral_zero _ _

theorem integral_wilsonVariationScore_eq_zero {N : ℕ} (hN : 0 < N)
    (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    (∫ U, wilsonVariationScore Λ β α U ∂μ.toMeasure) = 0 := by
  have h := hasDerivAt_periodicLimit_centralLinkVariation hN Λ β α hα μ l hl hμ
    (fun _ => 1) measurable_const (integrable_const 1)
  simp only [mul_one, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at h
  exact h.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))

/-- The finite-test response in displacement coordinates for the centered Wilson covariance. -/
theorem wilsonFluxCurrentCovariance_ward_test {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (Λ : Finset InfiniteLink) (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (I : Face) (x : Site) :
    β * (∑ p ∈ affectedPlaquettes Λ, d₁ α p.1 p.2 * wilsonFluxCurrentCovariance μ.toMeasure I p.1 (x - p.2)) =
      d₁ α I x + cutVariationResponse Λ α μ.toMeasure I x := by
  let S := affectedPlaquettes Λ
  let F (U : InfiniteConfig N) := averagedFlux iidCutLaw U I x
  let d (p : Plaquette) := β * d₁ α p.1 p.2
  let m := μ.toMeasure
  have hMean : ∑ p ∈ S, d p * (∫ U, plaquetteCurrent U p ∂m) = 0 := by
    have hj (p : Plaquette) : Integrable (fun U => plaquetteCurrent U p) m := by
      have hc := continuous_plaquetteCurrent (N := N) p
      obtain ⟨C, hC⟩ := (isCompact_univ.image hc.norm).bddAbove
      exact Integrable.of_bound hc.measurable.aestronglyMeasurable C (ae_of_all _ fun U => hC ⟨U, Set.mem_univ _, rfl⟩)
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun p _ => (hj p).const_mul (d p))]
    exact integral_wilsonVariationScore_eq_zero hN Λ β α hα μ l hl hμ
  have hscore (U : InfiniteConfig N) :
      (∑ p ∈ S, d p * centeredPlaquetteCurrent m U p) = wilsonVariationScore Λ β α U := by
    simp only [centeredPlaquetteCurrent, mul_sub, Finset.sum_sub_distrib, hMean, sub_zero]
    rfl
  calc
    _ = ∑ p ∈ S, d p * (∫ U, F U * centeredPlaquetteCurrent m U p ∂m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_flux_mul_current_eq_covariance β μ hμ I x p]
      simp only [d, mul_assoc]
    _ = ∫ U, wilsonVariationScore Λ β α U * F U ∂m := by
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ (fun p _ =>
        (integrable_flux_mul_centeredCurrent hN hβ μ l hl hμ I x p).const_mul (d p))]
      apply integral_congr_ae
      refine ae_of_all _ fun U => ?_
      calc
        _ = ∑ p ∈ S, (d p * centeredPlaquetteCurrent m U p) * F U :=
          Finset.sum_congr rfl (fun p _ => by dsimp only [F, m]; ring)
        _ = _ := by rw [← Finset.sum_mul, hscore]
    _ = _ := ward_centralVariation_periodicLimit hN hβ Λ α hα μ l hl hμ I x

end

end GaplessYangMills

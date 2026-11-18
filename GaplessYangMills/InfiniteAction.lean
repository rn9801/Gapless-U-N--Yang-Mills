module

public import GaplessYangMills.Action
public import GaplessYangMills.InfiniteGibbs
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Central link variations of the infinite Wilson state

Changing finitely many links changes the Wilson density only on their
incident plaquettes. Haar invariance in the conditional block gives the
exact likelihood ratio in any periodic weak limit.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

def centralLinkVariation {N : ℕ} (α : OneForm ℝ) (t : ℝ) (U : InfiniteConfig N) :
    InfiniteConfig N :=
  fun e => centralPhase N (Circle.exp (t * (α e.1 e.2 / N))) * U e

theorem centralLinkVariation_zero {N : ℕ} (α : OneForm ℝ) (U : InfiniteConfig N) :
    centralLinkVariation α 0 U = U := by
  funext e
  simp [centralLinkVariation]

theorem centralLinkVariation_add {N : ℕ} (α : OneForm ℝ) (s t : ℝ) (U : InfiniteConfig N) :
    centralLinkVariation α s (centralLinkVariation α t U) = centralLinkVariation α (s + t) U := by
  funext e
  simp only [centralLinkVariation, add_mul, Circle.exp_add, map_mul, mul_assoc]

private theorem continuous_centralLinkVariation {N : ℕ} (α : OneForm ℝ) :
    Continuous (fun p : ℝ × InfiniteConfig N => centralLinkVariation α p.1 p.2) := by
  have hc : Continuous (centralPhase N) := by
    have h : Continuous (fun z : Circle => (z : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
      continuous_subtype_val.smul continuous_const
    exact h.subtype_mk _
  apply continuous_pi
  intro e
  exact (hc.comp (Circle.exp.continuous.comp (continuous_fst.mul continuous_const))).mul
    ((continuous_apply e).comp continuous_snd)

def centralLikelihood {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ)
    (t : ℝ) (U : InfiniteConfig N) : ℝ :=
  localWilsonWeight Λ β (centralLinkVariation α (-t) U) / localWilsonWeight Λ β U

theorem centralLikelihood_pos {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ)
    (t : ℝ) (U : InfiniteConfig N) : 0 < centralLikelihood Λ β α t U :=
  div_pos (Real.exp_pos _) (Real.exp_pos _)

theorem continuous_centralLikelihood {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ) :
    Continuous (fun p : ℝ × InfiniteConfig N => centralLikelihood Λ β α p.1 p.2) := by
  have hc := continuous_localWilsonWeight (N := N) Λ β
  exact (hc.comp ((continuous_centralLinkVariation α).comp (continuous_fst.neg.prodMk continuous_snd))).div
    (hc.comp continuous_snd) (fun _ => (Real.exp_pos _).ne')

private theorem measurable_centralLinkVariation {N : ℕ} (α : OneForm ℝ) (t : ℝ) :
    Measurable (centralLinkVariation (N := N) α t) :=
  ((continuous_centralLinkVariation α).comp
    (continuous_const.prodMk continuous_id : Continuous (fun U : InfiniteConfig N => (t, U)))).measurable

private theorem measurable_centralLikelihood_weight {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ)
    (α : OneForm ℝ) (t : ℝ) :
    Measurable (fun U : InfiniteConfig N => ENNReal.ofReal (centralLikelihood Λ β α t U)) :=
  ((continuous_centralLikelihood Λ β α).comp
    (continuous_const.prodMk continuous_id : Continuous (fun U : InfiniteConfig N => (t, U)))).measurable.ennreal_ofReal

private def blockPhase (N : ℕ) (Λ : Finset InfiniteLink) (α : OneForm ℝ) (t : ℝ) :
    InfiniteBlock N Λ :=
  fun e => centralPhase N (Circle.exp (t * (α e.val.1 e.val.2 / N)))

private theorem blockPhase_neg (N : ℕ) (Λ : Finset InfiniteLink) (α : OneForm ℝ) (t : ℝ) :
    blockPhase N Λ α (-t) = (blockPhase N Λ α t)⁻¹ := by
  funext e
  simp [blockPhase, neg_mul, Circle.exp_neg]

private theorem centralLinkVariation_replaceLinks {N : ℕ} (Λ : Finset InfiniteLink)
    (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0) (t : ℝ) (U : InfiniteConfig N)
    (y : InfiniteBlock N Λ) :
    centralLinkVariation α t (replaceLinks Λ U y) = replaceLinks Λ U (blockPhase N Λ α t * y) := by
  funext e
  by_cases he : e ∈ Λ
  · simp only [centralLinkVariation, replaceLinks, dite_eq_left he, Pi.mul_apply, blockPhase]
  · simp [centralLinkVariation, replaceLinks, he, hα e he]

private theorem blockPhase_preserving {N : ℕ} (Λ : Finset InfiniteLink) (α : OneForm ℝ) (t : ℝ) :
    MeasurePreserving (fun y => blockPhase N Λ α t * y) (infiniteBlockHaar Λ) (infiniteBlockHaar Λ) := by
  unfold infiniteBlockHaar
  exact measurePreserving_pi _ _ (fun e => measurePreserving_mul_left (unitaryHaar N) (blockPhase N Λ α t e))

private theorem lintegral_infiniteGibbsKernel_centralVariation {N : ℕ}
    (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0)
    (t : ℝ) (U : InfiniteConfig N) (f : InfiniteConfig N → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ V, f (centralLinkVariation α t V) ∂infiniteGibbsKernel Λ β U) =
      ∫⁻ V, ENNReal.ofReal (centralLikelihood Λ β α t V) * f V ∂infiniteGibbsKernel Λ β U := by
  let A := blockPhase N Λ α t
  let R (y : InfiniteBlock N Λ) := replaceLinks Λ U y
  let W (y : InfiniteBlock N Λ) := ENNReal.ofReal (localWilsonWeight Λ β (R y))
  have hV := measurable_centralLinkVariation (N := N) α t
  have hℓ := measurable_centralLikelihood_weight (N := N) Λ β α t
  have h₁ : Measurable (fun V => f (centralLinkVariation α t V)) := hf.comp hV
  have h₂ : Measurable (fun V => ENNReal.ofReal (centralLikelihood Λ β α t V) * f V) := hℓ.mul hf
  rw [lintegral_infiniteGibbsKernel Λ β U h₁, lintegral_infiniteGibbsKernel Λ β U h₂]
  apply congrArg ((infiniteBlockPartition Λ β U)⁻¹ * ·)
  simp_rw [centralLinkVariation_replaceLinks Λ α hα t]
  let H (y : InfiniteBlock N Λ) := W (A⁻¹ * y) * f (R y)
  calc
    _ = ∫⁻ y, H (A * y) ∂infiniteBlockHaar Λ := by
      apply lintegral_congr
      intro y
      simp only [H, inv_mul_cancel_left]
      rfl
    _ = ∫⁻ y, H y ∂infiniteBlockHaar Λ :=
      (blockPhase_preserving Λ α t).lintegral_comp_emb (MeasurableEquiv.mulLeft A).measurableEmbedding H
    _ = _ := by
      apply lintegral_congr
      intro y
      have hW0 : W y ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
      have hWt : W y ≠ ⊤ := ENNReal.ofReal_ne_top
      have hL : ENNReal.ofReal (centralLikelihood Λ β α t (R y)) = W (A⁻¹ * y) / W y := by
        have hp : 0 < localWilsonWeight Λ β (R y) := Real.exp_pos _
        rw [centralLikelihood, ENNReal.ofReal_div_of_pos hp]
        simp only [R, centralLinkVariation_replaceLinks Λ α hα (-t), blockPhase_neg]
        rfl
      change W (A⁻¹ * y) * f (R y) = W y * (ENNReal.ofReal (centralLikelihood Λ β α t (R y)) * f (R y))
      rw [hL]
      calc
        _ = 1 * (W (A⁻¹ * y) * f (R y)) := (one_mul _).symm
        _ = (W y * (W y)⁻¹) * (W (A⁻¹ * y) * f (R y)) := by rw [ENNReal.mul_inv_cancel hW0 hWt]
        _ = _ := by rw [div_eq_mul_inv]; ac_rfl

/-- The exact infinite-volume change of variables for compactly supported real link variations. -/
theorem map_periodicLimit_centralLinkVariation {N : ℕ}
    (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0)
    (t : ℝ) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    μ.toMeasure.map (centralLinkVariation α t) =
      μ.toMeasure.withDensity (fun U => ENNReal.ofReal (centralLikelihood Λ β α t U)) := by
  have hV := measurable_centralLinkVariation (N := N) α t
  have hℓ := measurable_centralLikelihood_weight (N := N) Λ β α t
  apply Measure.ext_of_lintegral _
  intro f hf
  rw [lintegral_map hf hV, lintegral_withDensity_eq_lintegral_mul _ hℓ hf]
  simp only [Pi.mul_apply]
  have hK : ∀ g : InfiniteConfig N → ℝ≥0∞, Measurable g →
      (∫⁻ U, g U ∂μ.toMeasure) = ∫⁻ U, ∫⁻ V, g V ∂infiniteGibbsKernel Λ β U ∂μ.toMeasure := by
    intro g hg
    simpa only [mul_one] using lintegral_periodicLimit_conditionalGibbs Λ β μ l hl hμ hg
      (g := fun _ => 1) measurable_const (fun _ _ => rfl)
  rw [hK (fun U => f (centralLinkVariation α t U)) (hf.comp hV),
    hK (fun U => ENNReal.ofReal (centralLikelihood Λ β α t U) * f U) (hℓ.mul hf)]
  exact lintegral_congr fun U => lintegral_infiniteGibbsKernel_centralVariation Λ β α hα t U f hf

def plaquetteCurrent {N : ℕ} (U : InfiniteConfig N) (p : Face × Site) : ℝ :=
  (plaquetteHolonomy (fun i x => U (i, x)) p.1 p.2).val.trace.im

theorem continuous_plaquetteCurrent {N : ℕ} (p : Face × Site) :
    Continuous (fun U : InfiniteConfig N => plaquetteCurrent U p) :=
  Complex.continuous_im.comp (Continuous.matrix_trace
    (continuous_subtype_val.comp (continuous_plaquetteHolonomy p)))

def wilsonVariationScore {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ)
    (U : InfiniteConfig N) : ℝ :=
  ∑ p ∈ affectedPlaquettes Λ, β * d₁ α p.1 p.2 * plaquetteCurrent U p

theorem continuous_wilsonVariationScore {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ) :
    Continuous (wilsonVariationScore (N := N) Λ β α) :=
  continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_plaquetteCurrent p)

theorem centralLikelihood_zero {N : ℕ} (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ)
    (U : InfiniteConfig N) : centralLikelihood Λ β α 0 U = 1 := by
  rw [centralLikelihood, neg_zero, centralLinkVariation_zero]
  exact div_self (Real.exp_pos _).ne'

private theorem hasDerivAt_localWilsonWeight_inverse_zero {N : ℕ} (hN : 0 < N)
    (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ) (U : InfiniteConfig N) :
    HasDerivAt (fun t => localWilsonWeight Λ β (centralLinkVariation α (-t) U))
      (localWilsonWeight Λ β U * wilsonVariationScore Λ β α U) 0 := by
  have h := (hasDerivAt_inverse_wilson_links hN β (affectedPlaquettes Λ)
    (fun i x => U (i, x)) α).exp
  have hfun : (fun t : ℝ => Real.exp (∑ p ∈ affectedPlaquettes Λ, (N : ℝ) * β *
      (plaquetteHolonomy (fun i x => centralPhase N (Circle.exp (-(t * (α i x / N)))) * U (i, x))
        p.1 p.2).val.trace.re)) =
      fun t => localWilsonWeight Λ β (centralLinkVariation α (-t) U) := by
    funext t
    simp only [localWilsonWeight, centralLinkVariation, neg_mul, Finset.mul_sum]
  rw [hfun] at h
  have hz := congrFun hfun 0
  rw [neg_zero, centralLinkVariation_zero] at hz
  rw [hz] at h
  exact h

theorem hasDerivAt_centralLikelihood {N : ℕ} (hN : 0 < N) (Λ : Finset InfiniteLink) (β : ℝ)
    (α : OneForm ℝ) (t : ℝ) (U : InfiniteConfig N) :
    HasDerivAt (fun s => centralLikelihood Λ β α s U)
      (centralLikelihood Λ β α t U * wilsonVariationScore Λ β α (centralLinkVariation α (-t) U)) t := by
  let V := centralLinkVariation α (-t) U
  let F (s : ℝ) := localWilsonWeight Λ β (centralLinkVariation α (-s) V)
  have hbase : HasDerivAt F (localWilsonWeight Λ β V * wilsonVariationScore Λ β α V) (t - t) := by
    rw [sub_self]
    exact hasDerivAt_localWilsonWeight_inverse_zero hN Λ β α V
  have hs := (hasDerivAt_id' t).sub_const t
  have h := (hbase.comp t (h := fun s : ℝ => s - t) hs).div_const (localWilsonWeight Λ β U)
  have hfun : (fun s => (F ∘ fun z => z - t) s / localWilsonWeight Λ β U) =
      fun s => centralLikelihood Λ β α s U := by
    funext s
    change localWilsonWeight Λ β (centralLinkVariation α (-(s - t)) (centralLinkVariation α (-t) U)) /
      localWilsonWeight Λ β U = centralLikelihood Λ β α s U
    rw [centralLinkVariation_add, show -(s - t) + -t = -s by ring]
    rfl
  rw [hfun, mul_one] at h
  convert h using 1
  unfold centralLikelihood
  change localWilsonWeight Λ β V / localWilsonWeight Λ β U * wilsonVariationScore Λ β α V = _
  ring

theorem integral_periodicLimit_centralLinkVariation {N : ℕ}
    (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0)
    (t : ℝ) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (f : InfiniteConfig N → ℝ) (hf : Measurable f) :
    (∫ U, f (centralLinkVariation α t U) ∂μ.toMeasure) =
      ∫ U, centralLikelihood Λ β α t U * f U ∂μ.toMeasure := by
  have hV := measurable_centralLinkVariation (N := N) α t
  have hℓ := measurable_centralLikelihood_weight (N := N) Λ β α t
  rw [← integral_map hV.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable,
    map_periodicLimit_centralLinkVariation Λ β α hα t μ l hl hμ,
    integral_withDensity_eq_integral_toReal_smul hℓ (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (ae_of_all _ fun U => by
    change (ENNReal.ofReal (centralLikelihood Λ β α t U)).toReal * f U = _
    rw [ENNReal.toReal_ofReal (centralLikelihood_pos Λ β α t U).le])

/-- Differentiating the actual Wilson expectation gives the finite sum of
plaquette currents, for any integrable measurable observable. -/
theorem hasDerivAt_periodicLimit_centralLinkVariation {N : ℕ} (hN : 0 < N)
    (Λ : Finset InfiniteLink) (β : ℝ) (α : OneForm ℝ) (hα : ∀ e ∉ Λ, α e.1 e.2 = 0)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (f : InfiniteConfig N → ℝ) (hf : Measurable f) (hfint : Integrable f μ.toMeasure) :
    HasDerivAt (fun t => ∫ U, f (centralLinkVariation α t U) ∂μ.toMeasure)
      (∫ U, wilsonVariationScore Λ β α U * f U ∂μ.toMeasure) 0 := by
  let F (t : ℝ) (U : InfiniteConfig N) := centralLikelihood Λ β α t U * f U
  let D (t : ℝ) (U : InfiniteConfig N) :=
    centralLikelihood Λ β α t U * wilsonVariationScore Λ β α (centralLinkVariation α (-t) U)
  have hD : Continuous (fun p : ℝ × InfiniteConfig N => D p.1 p.2) :=
    (continuous_centralLikelihood Λ β α).mul
      ((continuous_wilsonVariationScore Λ β α).comp
        ((continuous_centralLinkVariation α).comp (continuous_fst.neg.prodMk continuous_snd)))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod
    (isCompact_univ : IsCompact (Set.univ : Set (InfiniteConfig N)))).bddAbove_image hD.norm.continuousOn
  have hs : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ zero_lt_one
  have hF (t : ℝ) : AEStronglyMeasurable (F t) μ.toMeasure := by
    have hp : Continuous (fun U : InfiniteConfig N => (t, U)) := continuous_const.prodMk continuous_id
    exact (((continuous_centralLikelihood Λ β α).comp hp).measurable.mul hf).aestronglyMeasurable
  have hF₀ : Integrable (F 0) μ.toMeasure := by simpa only [F, centralLikelihood_zero, one_mul] using hfint
  have hD₀ : AEStronglyMeasurable (fun U => D 0 U * f U) μ.toMeasure := by
    have hp : Continuous (fun U : InfiniteConfig N => ((0 : ℝ), U)) := continuous_const.prodMk continuous_id
    exact ((hD.comp hp).measurable.mul hf).aestronglyMeasurable
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := fun t U => D t U * f U)
    (bound := fun U => C * ‖f U‖) hs (Eventually.of_forall hF) hF₀ hD₀
    (ae_of_all _ fun U t ht => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hC ⟨(t, U), ⟨Metric.ball_subset_closedBall ht, Set.mem_univ _⟩, rfl⟩) (norm_nonneg _))
    (hfint.norm.const_mul C) (ae_of_all _ fun U t _ =>
      (hasDerivAt_centralLikelihood hN Λ β α t U).mul_const (f U))).2
  have hEq : (fun t => ∫ U, f (centralLinkVariation α t U) ∂μ.toMeasure) =
      fun t => ∫ U, F t U ∂μ.toMeasure :=
    funext fun t => integral_periodicLimit_centralLinkVariation Λ β α hα t μ l hl hμ f hf
  rw [hEq]
  simpa only [D, centralLikelihood_zero, neg_zero, centralLinkVariation_zero, one_mul] using h

end

end GaplessYangMills

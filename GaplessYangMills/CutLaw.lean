module

public import GaplessYangMills.CutAverages
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Probability.ProductMeasure

/-!
# The independent smooth cuts

The cuts have a common smooth density supported in a smaller interval
than the one allowed by the filling estimates. This leaves room for
small shifts of finitely many cuts.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped ENat ENNReal Topology

noncomputable section

def cutBump : ContDiffBump (0 : ℝ) where
  rIn := Real.pi / 64
  rOut := Real.pi / 32
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith [Real.pi_pos]

def cutDensity : ℝ → ℝ := cutBump.normed volume

theorem cutDensity_nonneg (x : ℝ) : 0 ≤ cutDensity x := cutBump.nonneg_normed x

theorem cutDensity_contDiff (n : ℕ∞) : ContDiff ℝ n cutDensity := cutBump.contDiff_normed

theorem cutDensity_hasCompactSupport : HasCompactSupport cutDensity := cutBump.hasCompactSupport_normed

theorem cutDensity_integral : ∫ x, cutDensity x = 1 := cutBump.integral_normed

theorem cutDensity_eq_zero_of_abs_ge {x : ℝ} (hx : Real.pi / 32 ≤ |x|) : cutDensity x = 0 := by
  apply not_not.mp
  change x ∉ Function.support (cutBump.normed volume)
  rw [cutBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
  exact not_lt_of_ge hx

def cutDisplacementLaw : Measure ℝ := volume.withDensity (ENNReal.ofReal ∘ cutDensity)

private theorem measurable_cutWeight : Measurable (ENNReal.ofReal ∘ cutDensity) :=
  (cutDensity_contDiff 0).continuous.measurable.ennreal_ofReal

instance cutDisplacementLaw_probability : IsProbabilityMeasure cutDisplacementLaw := by
  constructor
  rw [cutDisplacementLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ x, ENNReal.ofReal (cutDensity x)) = 1
  have hi : Integrable cutDensity (volume : Measure ℝ) := cutBump.integrable_normed
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ cutDensity_nonneg), cutDensity_integral, ENNReal.ofReal_one]

theorem cutDisplacementLaw_ae_abs_le : ∀ᵐ x ∂cutDisplacementLaw, |x| ≤ Real.pi / 32 := by
  rw [cutDisplacementLaw, ae_withDensity_iff measurable_cutWeight]
  exact ae_of_all _ fun x hx => le_of_not_gt fun h =>
    hx (by simp only [Function.comp_apply, cutDensity_eq_zero_of_abs_ge h.le, ENNReal.ofReal_zero])

def cutFieldEquiv : (Plaquette → ℝ) ≃ᵐ TwoForm ℝ where
  toFun a I x := a (I, x)
  invFun b p := b p.1 p.2
  left_inv a := by funext p; rfl
  right_inv b := by funext I x; rfl
  measurable_toFun := measurable_pi_iff.mpr fun I => measurable_pi_iff.mpr fun x =>
    measurable_pi_apply (I, x)
  measurable_invFun := measurable_pi_iff.mpr fun p =>
    (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

def iidCutLaw : Measure (TwoForm ℝ) :=
  (Measure.infinitePi fun _ : Plaquette => cutDisplacementLaw).map cutFieldEquiv

instance iidCutLaw_probability : IsProbabilityMeasure iidCutLaw := by
  unfold iidCutLaw
  exact (Measure.isProbabilityMeasure_map_iff cutFieldEquiv.measurable.aemeasurable).mpr inferInstance

theorem iidCutLaw_coordinate (I : Face) (x : Site) :
    MeasurePreserving (fun η : TwoForm ℝ => η I x) iidCutLaw cutDisplacementLaw := by
  have hm : Measurable (fun η : TwoForm ℝ => η I x) :=
    (measurable_pi_apply x).comp (measurable_pi_apply I)
  refine ⟨hm, ?_⟩
  rw [iidCutLaw, Measure.map_map hm cutFieldEquiv.measurable]
  exact (measurePreserving_eval_infinitePi (fun _ : Plaquette => cutDisplacementLaw) (I, x)).map_eq

theorem iidCutLaw_ae_abs_le : ∀ᵐ η ∂iidCutLaw, ∀ I x, |η I x| ≤ Real.pi / 32 := by
  refine ae_all_iff.mpr fun I => ae_all_iff.mpr fun x => ?_
  have hm := iidCutLaw_coordinate I x
  have h : ∀ᵐ u ∂iidCutLaw.map (fun η => η I x), |u| ≤ Real.pi / 32 := by
    rw [hm.map_eq]
    exact cutDisplacementLaw_ae_abs_le
  exact ae_of_ae_map hm.measurable.aemeasurable h

theorem iidCutLaw_allowed : ∀ᵐ η ∂iidCutLaw, ∀ I x, |η I x| ≤ Real.pi / 16 :=
  iidCutLaw_ae_abs_le.mono fun η hη I x => (hη I x).trans (by linarith [Real.pi_pos])

/-- The repaired flux with the smooth independent cut law satisfies (4). -/
theorem iidAveragedFlux_exponential_approximation_periodicLimit {N : ℕ} (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    (∃ C : ℝ, 0 < C ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ I x R,
      eLpNorm ((fun U => averagedFlux iidCutLaw U I x) -
        (fun U => averagedFluxApprox iidCutLaw R U I x)) 2 μ.toMeasure ≤ ENNReal.ofReal (C * t ^ R)) ∧
    ∀ I x, MemLp (fun U => averagedFlux iidCutLaw U I x) 2 μ.toMeasure ∧
      ∃ M : ℝ, ∀ R, eLpNorm (fun U => averagedFluxApprox iidCutLaw R U I x) 2 μ.toMeasure ≤ ENNReal.ofReal M :=
  averagedFlux_exponential_approximation_periodicLimit iidCutLaw iidCutLaw_allowed hN hβ μ l hl hμ

end

end GaplessYangMills

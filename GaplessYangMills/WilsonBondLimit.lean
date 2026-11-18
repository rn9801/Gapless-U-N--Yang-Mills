module

public import GaplessYangMills.PeriodicBondReflection
public import GaplessYangMills.FluxSymmetries

/-!
# Bond reflection positivity in a periodic weak limit

The continuous cylinder tests are gauge invariant and are supported on
links with both endpoints at nonnegative times. For large periods these
links lie in the strict positive half of the torus bond reflection.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped BoundedContinuousFunction Topology

def GaugeInvariantObservable {N : ℕ} (f : InfiniteConfig N → ℝ) : Prop :=
  ∀ g U, f (gaugeConfig g U) = f U

theorem extendPeriodic_gauge {L N : ℕ} (g : TorusSite L → UnitaryMatrix N) (U : TorusConfig L N) :
    extendPeriodic (periodicGaugeConfig g U) =
      gaugeConfig (fun x => g (fun i => (x i : ZMod L))) (extendPeriodic U) := by
  funext e
  obtain ⟨i, x⟩ := e
  have hx : (fun j => ((x + step i) j : ZMod L)) =
      (fun j => (x j : ZMod L)) + torusStep L i := by
    funext j
    by_cases hi : i = j <;> simp [Pi.add_apply, step, torusStep, hi]
  simp only [extendPeriodic, periodicGaugeConfig, gaugeConfig, hx]

theorem periodicLimit_bondReflection_nonneg {N : ℕ} (β : ℝ) (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (f : InfiniteConfig N → ℝ) (hf : Continuous f) (hg : GaugeInvariantObservable f)
    (hs : HalfSpaceCylinder τ 0 f) :
    0 ≤ ∫ U, f (reflectConfig τ (-1) U) * f U ∂μ.toMeasure := by
  let g : InfiniteConfig N →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun U => f (reflectConfig τ (-1) U) * f U, (hf.comp (continuous_reflectConfig τ (-1))).mul hf⟩
  obtain ⟨S, ht, hsupport⟩ := hs
  let m := S.sup (fun e => (e.2 τ).toNat)
  have htend := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ g
  apply ge_of_tendsto htend
  filter_upwards [hl.tendsto_atTop.eventually_ge_atTop m] with n hn
  let L := evenLength (l n)
  let F (U : TorusConfig L N) := f (extendPeriodic U)
  have hL : 4 ≤ L := by unfold L evenLength; omega
  have hL' : Even L := ⟨l n + 2, by unfold L evenLength; omega⟩
  have hF : Continuous F := hf.comp (continuous_extendPeriodic L N)
  have hG : PeriodicGaugeInvariant F := fun g U => by
    change f (extendPeriodic (periodicGaugeConfig g U)) = f (extendPeriodic U)
    rw [extendPeriodic_gauge, hg]
  have hS : ∀ U V : TorusConfig L N, (∀ p, bondCutInterior τ (normalLink τ) p → U p = V p) →
      F U = F V := by
    intro U V huv
    apply hsupport
    intro e he
    obtain ⟨i, x⟩ := e
    let y : TorusSite L := fun j => (x j : ZMod L)
    change U (i, y) = V (i, y)
    apply huv
    have hx : (x τ).toNat ≤ m := Finset.le_sup (f := fun e => (e.2 τ).toNat) he
    have hlen : m + 1 < L / 2 := by unfold L evenLength; omega
    have heq : (x τ : ZMod L) = ((x τ).toNat : ZMod L) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (ht (i, x) he)]
    have hval : (y τ).val = (x τ).toNat := by
      change (x τ : ZMod L).val = _
      rw [heq, ZMod.val_natCast_of_lt (by omega)]
    have hsmall : (y τ).val + 1 < L / 2 := by omega
    refine ⟨by change (y τ).val < L / 2; omega, fun h => ?_⟩
    have hs' : (y τ).val + 1 = L / 2 ∨ (y τ).val + 1 = L := h.2
    omega
  change 0 ≤ ∫ U, g U ∂Measure.map extendPeriodic (periodicWilson L N β)
  rw [integral_map (continuous_extendPeriodic L N).measurable.aemeasurable
    g.continuous.measurable.aestronglyMeasurable]
  change 0 ≤ ∫ U : TorusConfig L N, f (reflectConfig τ (-1) (extendPeriodic U)) * f (extendPeriodic U)
    ∂periodicWilson L N β
  simp_rw [reflectConfig_extendPeriodic, Int.cast_neg, Int.cast_one]
  exact periodicWilson_bondReflection_nonneg hL hL' τ β hβ F hF hG hS

end GaplessYangMills

module

public import GaplessYangMills.FiniteGibbs
public import GaplessYangMills.WilsonReflections
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Periodic gauge transformations and seam integration

Conditional on the links in a seam, the exterior links have independent
Haar reference. A gauge transformation sending the seam to identity
preserves that exterior reference and removes the seam integral for a
gauge-invariant test.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory

noncomputable section

def periodicGaugeConfig {L N : ℕ} (g : TorusSite L → UnitaryMatrix N) (U : TorusConfig L N) :
    TorusConfig L N :=
  fun (i, x) => g x * U (i, x) * (g (x + torusStep L i))⁻¹

def PeriodicGaugeInvariant {L N : ℕ} (f : TorusConfig L N → ℝ) : Prop :=
  ∀ g U, f (periodicGaugeConfig g U) = f U

theorem periodicHolonomy_gauge {L N : ℕ} (g : TorusSite L → UnitaryMatrix N) (U : TorusConfig L N)
    (I : Face) (x : TorusSite L) :
    periodicHolonomy (periodicGaugeConfig g U) I x =
      g x * periodicHolonomy U I x * (g x)⁻¹ := by
  simp only [periodicHolonomy, periodicGaugeConfig]
  rw [add_right_comm x (torusStep L I.axes.1) (torusStep L I.axes.2)]
  group

theorem periodicLogWeight_gauge {L N : ℕ} [NeZero L] (β : ℝ)
    (g : TorusSite L → UnitaryMatrix N) (U : TorusConfig L N) :
    periodicLogWeight β (periodicGaugeConfig g U) = periodicLogWeight β U := by
  unfold periodicLogWeight
  congr 1
  apply Finset.sum_congr rfl
  rintro ⟨I, x⟩ _
  rw [periodicHolonomy_gauge]
  have hi : ((g x)⁻¹).val * (g x).val = 1 :=
    congrArg (fun a : UnitaryMatrix N => a.val) (inv_mul_cancel (g x))
  change ((g x).val * (periodicHolonomy U I x).val * ((g x)⁻¹).val).trace.re = _
  rw [Matrix.trace_mul_cycle, hi, Matrix.one_mul]

theorem periodicGauge_reflect {L N : ℕ} (τ : Axis) (c : ZMod L)
    (g : TorusSite L → UnitaryMatrix N) (U : TorusConfig L N) :
    reflectPeriodic τ c (periodicGaugeConfig g U) =
      periodicGaugeConfig (g ∘ reflectSiteOn τ c) (reflectPeriodic τ c U) := by
  funext p
  obtain ⟨i, x⟩ := p
  by_cases hi : i = τ
  · subst i
    simp only [reflectPeriodic, reflectLinksOn_normal, periodicGaugeConfig, Function.comp_apply,
      reflectSiteOn_add_torusStep_normal, reflectSiteOn_lower_add_torusStep]
    group
  · simp only [reflectPeriodic, reflectLinksOn_tangent hi, periodicGaugeConfig, Function.comp_apply,
      reflectSiteOn_add_torusStep_tangent hi]

instance unitaryHaar_rightInvariant (N : ℕ) : (unitaryHaar N).IsMulRightInvariant where
  map_mul_right_eq_self u := by
    let h := Measure.measurePreserving_inv (unitaryHaar N)
    have ht := h.comp ((measurePreserving_mul_left (unitaryHaar N) u⁻¹).comp h)
    have he : (Inv.inv : UnitaryMatrix N → UnitaryMatrix N) ∘ ((u⁻¹ * ·) ∘ Inv.inv) =
        fun v => v * u := by
      funext v
      simp only [Function.comp_apply, mul_inv_rev, inv_inv]
    rw [he] at ht
    exact ht.map_eq

theorem periodicHaar_gauge_preserving {L N : ℕ} [NeZero L] (g : TorusSite L → UnitaryMatrix N) :
    MeasurePreserving (periodicGaugeConfig g) (periodicHaar L N) (periodicHaar L N) :=
  measurePreserving_pi (fun _ : TorusLink L => unitaryHaar N) (fun _ => unitaryHaar N)
    (f := fun p u => g p.2 * u * (g (p.2 + torusStep L p.1))⁻¹)
    (fun _ => (measurePreserving_mul_right _ _).comp (measurePreserving_mul_left _ _))

theorem periodicWilson_gauge_preserving {L N : ℕ} [NeZero L] (β : ℝ) (g : TorusSite L → UnitaryMatrix N) :
    MeasurePreserving (periodicGaugeConfig g) (periodicWilson L N β) (periodicWilson L N β) :=
  periodicWilson_preserving_of_logWeight β _ (periodicHaar_gauge_preserving g) (periodicLogWeight_gauge β g)

/-- A measurable integral of a continuous gauge-invariant test against the
Haar reference can fix a set of seam links to identity once a boundary
gauge sending their values to identity is given. -/
theorem integral_periodicHaar_gaugeFix {L N : ℕ} [NeZero L] (Λ : Finset (TorusLink L))
    (g : PeriodicBlock N Λ → TorusSite L → UnitaryMatrix N)
    (hg : ∀ a (e : {p // p ∈ Λ}), g a e.val.2 * a e *
      (g a (e.val.2 + torusStep L e.val.1))⁻¹ = 1)
    (f : TorusConfig L N → ℝ) (hf : Continuous f) (hfg : PeriodicGaugeInvariant f) :
    (∫ U, f U ∂periodicHaar L N) =
      ∫ b, f ((splitPeriodicLinks Λ).symm (1, b)) ∂exteriorHaar Λ := by
  let E := splitPeriodicLinks (N := N) Λ
  let V (a : PeriodicBlock N Λ) (b : PeriodicExterior N Λ) (p : {p // p ∉ Λ}) :=
    g a p.val.2 * b p * (g a (p.val.2 + torusStep L p.val.1))⁻¹
  have hV (a : PeriodicBlock N Λ) :
      MeasurePreserving (V a) (exteriorHaar (N := N) Λ) (exteriorHaar Λ) :=
    measurePreserving_pi (fun _ : {p // p ∉ Λ} => unitaryHaar N) (fun _ => unitaryHaar N)
      (f := fun p u => g a p.val.2 * u * (g a (p.val.2 + torusStep L p.val.1))⁻¹)
      (fun p => (measurePreserving_mul_right _ _).comp (measurePreserving_mul_left _ _))
  have heq (a : PeriodicBlock N Λ) (b : PeriodicExterior N Λ) :
      periodicGaugeConfig (g a) (E.symm (a, b)) = E.symm (1, V a b) := by
    funext p
    change g a p.2 * (splitPeriodicLinks Λ).symm (a, b) p * (g a (p.2 + torusStep L p.1))⁻¹ =
      (splitPeriodicLinks Λ).symm (1, V a b) p
    by_cases hp : p ∈ Λ
    · rw [joinPeriodic_eq_block a b hp, joinPeriodic_eq_block 1 (V a b) hp]
      exact hg a ⟨p, hp⟩
    · rw [joinPeriodic_eq_exterior a b hp, joinPeriodic_eq_exterior 1 (V a b) hp]
  have hA := (splitPeriodicLinks_preserving (N := N) Λ).symm E
  have hif : Integrable f (periodicHaar L N) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  rw [← hA.integral_comp' f]
  have hi : Integrable (fun b => f (E.symm b)) ((blockHaar Λ).prod (exteriorHaar Λ)) :=
    hA.integrable_comp_of_integrable hif
  rw [integral_prod _ hi]
  have hb : Measurable (fun b : PeriodicExterior N Λ => f (E.symm (1, b))) :=
    hf.measurable.comp (E.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hsub (a : PeriodicBlock N Λ) :
      (∫ b, f (E.symm (a, b)) ∂exteriorHaar Λ) = ∫ b, f (E.symm (1, b)) ∂exteriorHaar Λ := by
    calc
      _ = ∫ b, f (E.symm (1, V a b)) ∂exteriorHaar Λ := by
        apply integral_congr_ae
        exact ae_of_all _ fun b =>
          (hfg (g a) (E.symm (a, b))).symm.trans (congrArg f (heq a b))
      _ = _ := by
        nth_rewrite 2 [← (hV a).map_eq]
        exact (integral_map (hV a).measurable.aemeasurable hb.aestronglyMeasurable).symm
  simp_rw [hsub]
  simp [E]

end

end GaplessYangMills

module

public import GaplessYangMills.WilsonTranslations
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Group

/-!
# Coordinate reflections of the Wilson laws

The integer parameter records twice the time of the reflection plane. On a
normal link the reflected value is read at its reflected lower vertex and
inverted. A temporal plaquette therefore maps to a conjugate of the inverse
holonomy of the reflected plaquette.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory Filter
open scoped ENNReal Matrix Topology

/-- Inversion preserves the Haar probability. The two iterated integrals of
`g (x⁻¹ * y)` give this directly from left invariance. -/
instance unitaryHaar_invInvariant (N : ℕ) : (unitaryHaar N).IsInvInvariant where
  inv_eq_self := by
    let m := unitaryHaar N
    refine Measure.ext_of_lintegral _ fun g hg => ?_
    rw [Measure.inv_def, lintegral_map hg measurable_inv]
    let f (x y : UnitaryMatrix N) := g (x⁻¹ * y)
    have hf : Measurable (Function.uncurry f) :=
      hg.comp (measurable_fst.inv.mul measurable_snd)
    calc
      (∫⁻ x, g x⁻¹ ∂m) = ∫⁻ y, ∫⁻ x, f x y ∂m ∂m := by
        have he (y : UnitaryMatrix N) : (∫⁻ x, f x y ∂m) = ∫⁻ x, g x⁻¹ ∂m := by
          have h := (measurePreserving_mul_left m y⁻¹).lintegral_comp (hg.comp measurable_inv)
          simpa only [f, mul_inv_rev, inv_inv, Function.comp_apply] using h
        simp only [he, lintegral_const, measure_univ, mul_one]
      _ = ∫⁻ x, ∫⁻ y, f x y ∂m ∂m := (lintegral_lintegral_swap hf.aemeasurable).symm
      _ = ∫⁻ y, g y ∂m := by
        have he (x : UnitaryMatrix N) : (∫⁻ y, f x y ∂m) = ∫⁻ y, g y ∂m :=
          (measurePreserving_mul_left m x⁻¹).lintegral_comp hg
        simp only [he, lintegral_const, measure_univ, mul_one]

def reflectSiteOn {A : Type*} [Sub A] (τ : Axis) (c : A) (x : Axis → A) : Axis → A :=
  fun j => if j = τ then c - x j else x j

theorem reflectSiteOn_involutive {A : Type*} [AddCommGroup A] (τ : Axis) (c : A) :
    Function.Involutive (reflectSiteOn τ c) := by
  intro x
  funext j
  by_cases hj : j = τ <;> simp [reflectSiteOn, hj]

private def axisUnit {A : Type*} [Zero A] [One A] (i : Axis) : Axis → A :=
  fun j => if i = j then 1 else 0

private theorem reflectSiteOn_add_parallel {A : Type*} [AddCommGroup A] [One A]
    (τ : Axis) (c : A) (x : Axis → A) :
    reflectSiteOn τ c (x + axisUnit τ) = reflectSiteOn τ (c - 1) x := by
  funext j
  by_cases hj : j = τ
  · subst j
    simp only [reflectSiteOn, axisUnit, ite_eq_left, Pi.add_apply]
    abel
  · simp [reflectSiteOn, axisUnit, hj, Ne.symm hj]

private theorem reflectSiteOn_add_transverse {A : Type*} [AddCommGroup A] [One A]
    {τ i : Axis} (hi : i ≠ τ) (c : A) (x : Axis → A) :
    reflectSiteOn τ c (x + axisUnit i) = reflectSiteOn τ c x + axisUnit i := by
  funext j
  by_cases hj : j = τ
  · subst j
    simp [reflectSiteOn, axisUnit, hi]
  · simp [reflectSiteOn, axisUnit, hj]

private theorem reflectSiteOn_lower_add_parallel {A : Type*} [AddCommGroup A] [One A]
    (τ : Axis) (c : A) (x : Axis → A) :
    reflectSiteOn τ (c - 1) x + axisUnit τ = reflectSiteOn τ c x := by
  funext j
  by_cases hj : j = τ
  · subst j
    simp only [reflectSiteOn, axisUnit, ite_eq_left, Pi.add_apply]
    abel
  · simp [reflectSiteOn, axisUnit, hj, Ne.symm hj]

theorem reflectSiteOn_add_torusStep_normal {L : ℕ} (τ : Axis) (c : ZMod L) (x : TorusSite L) :
    reflectSiteOn τ c (x + torusStep L τ) = reflectSiteOn τ (c - 1) x :=
  reflectSiteOn_add_parallel τ c x

theorem reflectSiteOn_add_torusStep_tangent {L : ℕ} {τ i : Axis} (hi : i ≠ τ) (c : ZMod L)
    (x : TorusSite L) :
    reflectSiteOn τ c (x + torusStep L i) = reflectSiteOn τ c x + torusStep L i :=
  reflectSiteOn_add_transverse hi c x

theorem reflectSiteOn_lower_add_torusStep {L : ℕ} (τ : Axis) (c : ZMod L) (x : TorusSite L) :
    reflectSiteOn τ (c - 1) x + torusStep L τ = reflectSiteOn τ c x :=
  reflectSiteOn_lower_add_parallel τ c x

def reflectLinkIndex {A : Type*} [AddCommGroup A] [One A] (τ : Axis) (c : A) :
    (Axis × (Axis → A)) ≃ (Axis × (Axis → A)) where
  toFun e := (e.1, reflectSiteOn τ (if e.1 = τ then c - 1 else c) e.2)
  invFun e := (e.1, reflectSiteOn τ (if e.1 = τ then c - 1 else c) e.2)
  left_inv e := Prod.ext rfl (reflectSiteOn_involutive τ _ e.2)
  right_inv e := Prod.ext rfl (reflectSiteOn_involutive τ _ e.2)

def reflectLinksOn {A G : Type*} [AddCommGroup A] [One A] [Inv G]
    (τ : Axis) (c : A) (U : Axis × (Axis → A) → G) : Axis × (Axis → A) → G :=
  fun e => if e.1 = τ then (U (reflectLinkIndex τ c e))⁻¹ else U (reflectLinkIndex τ c e)

theorem reflectLinksOn_normal {A G : Type*} [AddCommGroup A] [One A] [Inv G]
    (τ : Axis) (c : A) (U : Axis × (Axis → A) → G) (x : Axis → A) :
    reflectLinksOn τ c U (τ, x) = (U (τ, reflectSiteOn τ (c - 1) x))⁻¹ := by
  simp [reflectLinksOn, reflectLinkIndex]

theorem reflectLinksOn_tangent {A G : Type*} [AddCommGroup A] [One A] [Inv G]
    {τ i : Axis} (hi : i ≠ τ) (c : A) (U : Axis × (Axis → A) → G) (x : Axis → A) :
    reflectLinksOn τ c U (i, x) = U (i, reflectSiteOn τ c x) := by
  simp [reflectLinksOn, reflectLinkIndex, hi]

def reflectConfig {N : ℕ} (τ : Axis) (c : ℤ) : InfiniteConfig N → InfiniteConfig N :=
  reflectLinksOn τ c

def reflectPeriodic {L N : ℕ} (τ : Axis) (c : ZMod L) : TorusConfig L N → TorusConfig L N :=
  reflectLinksOn τ c

theorem continuous_reflectLinksOn {A G : Type*} [AddCommGroup A] [One A] [Inv G]
    [TopologicalSpace G] [ContinuousInv G] (τ : Axis) (c : A) :
    Continuous (reflectLinksOn τ c : (Axis × (Axis → A) → G) → (Axis × (Axis → A) → G)) := by
  apply continuous_pi
  intro e
  change Continuous (fun U : Axis × (Axis → A) → G =>
    if e.1 = τ then (U (reflectLinkIndex τ c e))⁻¹ else U (reflectLinkIndex τ c e))
  by_cases h : e.1 = τ
  · simp only [ite_eq_left h]
    exact (continuous_apply (reflectLinkIndex τ c e)).inv
  · simp only [ite_eq_right h]
    exact continuous_apply (reflectLinkIndex τ c e)

theorem continuous_reflectConfig {N : ℕ} (τ : Axis) (c : ℤ) :
    Continuous (reflectConfig τ c : InfiniteConfig N → InfiniteConfig N) :=
  continuous_reflectLinksOn τ c

theorem continuous_reflectPeriodic {L N : ℕ} (τ : Axis) (c : ZMod L) :
    Continuous (reflectPeriodic τ c : TorusConfig L N → TorusConfig L N) :=
  continuous_reflectLinksOn τ c

theorem reflectConfig_involutive {N : ℕ} (τ : Axis) (c : ℤ) :
    Function.Involutive (reflectConfig (N := N) τ c) := by
  intro U
  funext e
  obtain ⟨i, x⟩ := e
  by_cases hi : i = τ
  · subst i
    simp only [reflectConfig, reflectLinksOn_normal, inv_inv]
    rw [reflectSiteOn_involutive τ (c - 1) x]
  · simp only [reflectConfig, reflectLinksOn_tangent hi]
    rw [reflectSiteOn_involutive τ c x]

theorem translateConfig_reflect_step {N : ℕ} (τ : Axis) (c : ℤ) (U : InfiniteConfig N) :
    translateConfig (step τ) (reflectConfig τ c U) = reflectConfig τ (c - 1) U := by
  funext e
  obtain ⟨i, x⟩ := e
  have h (d : ℤ) : reflectSiteOn τ d (x + step τ) = reflectSiteOn τ (d - 1) x :=
    reflectSiteOn_add_parallel τ d x
  by_cases hi : i = τ
  · subst i
    simp only [translateConfig, reflectConfig, reflectLinksOn_normal, h]
  · simp only [translateConfig, reflectConfig, reflectLinksOn_tangent hi, h]

theorem reflectConfig_translate_step {N : ℕ} (τ : Axis) (c : ℤ) (U : InfiniteConfig N) :
    reflectConfig τ c (translateConfig (step τ) U) = reflectConfig τ (c + 1) U := by
  funext e
  obtain ⟨i, x⟩ := e
  have h (d : ℤ) : reflectSiteOn τ d x + step τ = reflectSiteOn τ (d + 1) x := by
    change reflectSiteOn τ d x + axisUnit τ = _
    simpa only [add_sub_cancel_right] using reflectSiteOn_lower_add_parallel τ (d + 1) x
  by_cases hi : i = τ
  · subst i
    simp only [reflectConfig, reflectLinksOn_normal, translateConfig, h, sub_add_cancel, add_sub_cancel_right]
  · simp only [reflectConfig, reflectLinksOn_tangent hi, translateConfig, h]

private theorem unitaryTrace_re_inv {N : ℕ} (P : UnitaryMatrix N) :
    (P⁻¹).val.trace.re = P.val.trace.re := by
  change (P.valᴴ).trace.re = _
  rw [Matrix.trace_conjTranspose]
  rfl

private theorem unitaryTrace_conj {N : ℕ} (P Q : UnitaryMatrix N) :
    (Q * P * Q⁻¹).val.trace = P.val.trace := by
  have hi : (Q⁻¹).val * Q.val = 1 :=
    congrArg (fun V : UnitaryMatrix N => V.val) (inv_mul_cancel Q)
  change (Q.val * P.val * (Q⁻¹).val).trace = _
  rw [Matrix.trace_mul_cycle, hi, Matrix.one_mul]

def reflectedFaceBase {A : Type*} [Sub A] [One A] (τ : Axis) (c : A)
    (I : Face) (x : Axis → A) : Axis → A :=
  reflectSiteOn τ (if I.axes.1 = τ ∨ I.axes.2 = τ then c - 1 else c) x

theorem periodicHolonomy_reflect_re {L N : ℕ} (τ : Axis) (c : ZMod L)
    (U : TorusConfig L N) (I : Face) (x : TorusSite L) :
    (periodicHolonomy (reflectPeriodic τ c U) I x).val.trace.re =
      (periodicHolonomy U I (reflectedFaceBase τ c I x)).val.trace.re := by
  let i : Axis := I.axes.1
  let j : Axis := I.axes.2
  have hij : i ≠ j := by cases I <;> decide
  change (reflectLinksOn τ c U (i, x) * reflectLinksOn τ c U (j, x + axisUnit i) *
    (reflectLinksOn τ c U (i, x + axisUnit j))⁻¹ * (reflectLinksOn τ c U (j, x))⁻¹).val.trace.re = _
  by_cases hi : i = τ
  · have hj : j ≠ τ := fun h => hij (hi.trans h.symm)
    let y := reflectSiteOn τ (c - 1) x
    have hx : reflectSiteOn τ c x = y + axisUnit i := by
      rw [hi, ← reflectSiteOn_lower_add_parallel τ c x]
    have hbase : reflectedFaceBase τ c I x = y := by
      simp only [reflectedFaceBase, show I.axes.1 = τ from hi, true_or, ite_true, y]
    rw [hbase, reflectLinksOn_tangent hj, reflectLinksOn_tangent hj, hx,
      show reflectSiteOn τ c (x + axisUnit i) = y from hi.symm ▸ reflectSiteOn_add_parallel τ c x]
    rw [show reflectLinksOn τ c U (i, x) = (U (i, y))⁻¹ by rw [hi, reflectLinksOn_normal],
      show reflectLinksOn τ c U (i, x + axisUnit j) = (U (i, y + axisUnit j))⁻¹ by
        rw [hi, reflectLinksOn_normal, reflectSiteOn_add_transverse hj]]
    have hhol : (U (i, y))⁻¹ * U (j, y) * ((U (i, y + axisUnit j))⁻¹)⁻¹ *
        (U (j, y + axisUnit i))⁻¹ =
        (U (i, y))⁻¹ * (periodicHolonomy U I y)⁻¹ * ((U (i, y))⁻¹)⁻¹ := by
      change _ = (U (i, y))⁻¹ * (U (i, y) * U (j, y + axisUnit i) *
        (U (i, y + axisUnit j))⁻¹ * (U (j, y))⁻¹)⁻¹ * ((U (i, y))⁻¹)⁻¹
      group
    rw [hhol, unitaryTrace_conj, unitaryTrace_re_inv]
  · by_cases hj : j = τ
    · let y := reflectSiteOn τ (c - 1) x
      have hx : reflectSiteOn τ c x = y + axisUnit j := by
        rw [hj, ← reflectSiteOn_lower_add_parallel τ c x]
      have hbase : reflectedFaceBase τ c I x = y := by
        simp only [reflectedFaceBase, show I.axes.2 = τ from hj, or_true, ite_true, y]
      rw [hbase, reflectLinksOn_tangent hi, reflectLinksOn_tangent hi, hx,
        show reflectSiteOn τ c (x + axisUnit j) = y from hj.symm ▸ reflectSiteOn_add_parallel τ c x]
      rw [show reflectLinksOn τ c U (j, x) = (U (j, y))⁻¹ by rw [hj, reflectLinksOn_normal],
        show reflectLinksOn τ c U (j, x + axisUnit i) = (U (j, y + axisUnit i))⁻¹ by
          rw [hj, reflectLinksOn_normal, reflectSiteOn_add_transverse hi]]
      have hhol : U (i, y + axisUnit j) * (U (j, y + axisUnit i))⁻¹ * (U (i, y))⁻¹ *
          ((U (j, y))⁻¹)⁻¹ =
          (U (j, y))⁻¹ * (periodicHolonomy U I y)⁻¹ * ((U (j, y))⁻¹)⁻¹ := by
        change _ = (U (j, y))⁻¹ * (U (i, y) * U (j, y + axisUnit i) *
          (U (i, y + axisUnit j))⁻¹ * (U (j, y))⁻¹)⁻¹ * ((U (j, y))⁻¹)⁻¹
        group
      rw [hhol, unitaryTrace_conj, unitaryTrace_re_inv]
    · simp only [reflectedFaceBase, show I.axes.1 ≠ τ from hi, show I.axes.2 ≠ τ from hj,
        or_self, ite_false, reflectLinksOn_tangent hi, reflectLinksOn_tangent hj,
        reflectSiteOn_add_transverse hi, reflectSiteOn_add_transverse hj]
      rfl

theorem periodicLogWeight_reflect {L N : ℕ} [NeZero L] (β : ℝ) (τ : Axis)
    (c : ZMod L) (U : TorusConfig L N) :
    periodicLogWeight β (reflectPeriodic τ c U) = periodicLogWeight β U := by
  simp only [periodicLogWeight, periodicHolonomy_reflect_re]
  congr 1
  let e : Face × TorusSite L ≃ Face × TorusSite L :=
    ⟨fun p => (p.1, reflectedFaceBase τ c p.1 p.2), fun p => (p.1, reflectedFaceBase τ c p.1 p.2),
      fun p => Prod.ext rfl (reflectSiteOn_involutive _ _ _),
      fun p => Prod.ext rfl (reflectSiteOn_involutive _ _ _)⟩
  exact e.sum_comp fun p => (periodicHolonomy U p.1 p.2).val.trace.re

theorem periodicHaar_reflect_preserving {L N : ℕ} [NeZero L] (τ : Axis) (c : ZMod L) :
    MeasurePreserving (reflectPeriodic τ c : TorusConfig L N → TorusConfig L N)
      (periodicHaar L N) (periodicHaar L N) := by
  let e := reflectLinkIndex τ c
  let V : TorusConfig L N → TorusConfig L N := fun U p => U (e p)
  let M : TorusConfig L N → TorusConfig L N := fun U p => if p.1 = τ then (U p)⁻¹ else U p
  have hV : MeasurePreserving V (periodicHaar L N) (periodicHaar L N) := by
    have hv : ⇑(MeasurableEquiv.piCongrLeft (fun _ : TorusLink L => UnitaryMatrix N) e.symm) = V := by
      funext U p
      simpa only [V, Equiv.symm_apply_apply] using
        (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : TorusLink L => UnitaryMatrix N) e.symm U (e p))
    rw [← hv]
    exact measurePreserving_piCongrLeft (fun _ : TorusLink L => unitaryHaar N) e.symm
  have hM : MeasurePreserving M (periodicHaar L N) (periodicHaar L N) := by
    refine measurePreserving_pi (fun _ : TorusLink L => unitaryHaar N) (fun _ => unitaryHaar N)
      (f := fun i v => if i.1 = τ then v⁻¹ else v)
      (fun p => ?_)
    by_cases hp : p.1 = τ
    · simp only [ite_eq_left hp]
      exact Measure.measurePreserving_inv (unitaryHaar N)
    · simp only [ite_eq_right hp]
      exact MeasurePreserving.id (unitaryHaar N)
  exact hM.comp hV

theorem periodicWilson_reflect_preserving {L N : ℕ} [NeZero L] (β : ℝ) (τ : Axis) (c : ZMod L) :
    MeasurePreserving (reflectPeriodic τ c : TorusConfig L N → TorusConfig L N)
      (periodicWilson L N β) (periodicWilson L N β) :=
  periodicWilson_preserving_of_logWeight β _ (periodicHaar_reflect_preserving τ c)
    (periodicLogWeight_reflect β τ c)

theorem reflectConfig_extendPeriodic {L N : ℕ} (τ : Axis) (c : ℤ) (U : TorusConfig L N) :
    reflectConfig τ c (extendPeriodic U) = extendPeriodic (reflectPeriodic τ (c : ZMod L) U) := by
  funext e
  obtain ⟨i, x⟩ := e
  by_cases hi : i = τ
  · subst i
    simp only [reflectConfig, reflectPeriodic, reflectLinksOn_normal, extendPeriodic]
    congr 2
    refine Prod.ext ?_ ?_
    · rfl
    funext j
    by_cases hj : j = τ <;> simp [reflectSiteOn, hj]
  · simp only [reflectConfig, reflectPeriodic, reflectLinksOn_tangent hi, extendPeriodic]
    congr 1
    refine Prod.ext ?_ ?_
    · rfl
    funext j
    by_cases hj : j = τ <;> simp [reflectSiteOn, hj]

theorem extendedWilson_reflect {L N : ℕ} [NeZero L] (β : ℝ) (τ : Axis) (c : ℤ) :
    ProbabilityMeasure.map (extendedWilson L N β) (reflectConfig τ c) =
      extendedWilson L N β := by
  apply Subtype.ext
  change Measure.map (reflectConfig τ c) (Measure.map extendPeriodic (periodicWilson L N β)) =
    Measure.map extendPeriodic (periodicWilson L N β)
  have he := (continuous_extendPeriodic L N).measurable
  have hR := periodicWilson_reflect_preserving (N := N) β τ (c : ZMod L)
  have hf : (reflectConfig τ c : InfiniteConfig N → InfiniteConfig N) ∘ extendPeriodic =
      extendPeriodic ∘ reflectPeriodic τ (c : ZMod L) :=
    funext (reflectConfig_extendPeriodic τ c)
  rw [Measure.map_map (continuous_reflectConfig τ c).measurable he, hf,
    ← Measure.map_map he hR.measurable, hR.map_eq]

/-- Both site and bond coordinate reflections preserve every periodic weak
limit, since the reflection parameter ranges over all integers. -/
theorem periodicWilson_limit_reflect {N : ℕ} (β : ℝ) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (c : ℤ) : ProbabilityMeasure.map μ (reflectConfig τ c) = μ := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hμ
    (continuous_reflectConfig τ c)
  simp only [extendedWilson_reflect] at h
  exact tendsto_nhds_unique h hμ

end GaplessYangMills

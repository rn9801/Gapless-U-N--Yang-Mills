module

public import GaplessYangMills.GaugeAveraging
public import GaplessYangMills.WilsonHalfSpace
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Gauge-invariant continuous approximation

A bounded measurable invariant of a compact gauge action is approximable
by continuous invariants in L² for any probability law. Approximate in
the gauge-averaged law, then average the continuous approximant.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

theorem norm_L2_sq_eq_integral_of_ae {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (u : Lp ℝ 2 ν) {f : Ω → ℝ} (hf : (u : Ω → ℝ) =ᵐ[ν] f) :
    ‖u‖ ^ 2 = ∫ x, f x ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (hf.mono fun x hx => by
    change ⟪u x, u x⟫_ℝ = f x ^ 2
    rw [Real.inner_apply, hx, pow_two])

theorem norm_L2_sub_sq_eq_integral_of_ae {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (u v : Lp ℝ 2 ν) {f g : Ω → ℝ} (hf : (u : Ω → ℝ) =ᵐ[ν] f) (hg : (v : Ω → ℝ) =ᵐ[ν] g) :
    ‖u - v‖ ^ 2 = ∫ x, (f x - g x) ^ 2 ∂ν :=
  norm_L2_sq_eq_integral_of_ae (u - v) ((Lp.coeFn_sub u v).trans (hf.sub hg))

private theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {f : Ω → ℝ} (hf : MemLp f 2 ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ∫ x, f x ^ 2 ∂ν := by
  let a := ∫ x, f x ∂ν
  have h := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi : (∫ x, (f x - a)^2 ∂ν) = (∫ x, f x ^ 2 ∂ν) - a ^ 2 := by
    calc
      _ = ∫ x, f x ^ 2 - (2 * a) * f x + a ^ 2 ∂ν :=
        integral_congr_ae (ae_of_all _ fun _ => by ring)
      _ = _ := by
        let sq (x : Ω) := f x ^ 2
        let lin (x : Ω) := (2 * a) * f x
        have hsq : Integrable sq ν := hf.integrable_sq
        have hlin : Integrable lin ν := h.const_mul (2 * a)
        change (∫ x, (sq - lin) x + a ^ 2 ∂ν) = _
        rw [integral_add (hsq.sub hlin) (integrable_const _)]
        simp only [Pi.sub_apply]
        rw [integral_sub hsq hlin]
        change (∫ x, f x ^ 2 ∂ν) - (∫ x, (2 * a) * f x ∂ν) + (∫ _ : Ω, a ^ 2 ∂ν) = _
        rw [integral_const_mul, integral_const]
        simp only [probReal_univ, one_smul]
        change _ - (2 * a) * a + a ^ 2 = _
        ring
  have hp := integral_nonneg (μ := ν) (fun x => sq_nonneg (f x - a))
  rw [hi] at hp
  exact sub_nonneg.mp hp

set_option maxHeartbeats 600000 in
theorem exists_continuous_invariant_L2_approx {G X : Type*} [Group G] [PseudoMetricSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [IsTopologicalGroup G] [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [action : MulAction G X] [actionContinuous : ContinuousSMul G X]
    (η : Measure G) [IsProbabilityMeasure η] [η.IsMulRightInvariant]
    (ν : Measure X) [IsProbabilityMeasure ν] (f : X → ℝ) (hf : Measurable f)
    (hf₂ : MemLp f 2 ν) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (hInv : ∀ (g : G) (x : X), f (g • x) = f x) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : X →ᵇ ℝ, (∀ (g : G) (x : X), A (g • x) = A x) ∧
      ‖BoundedContinuousFunction.toLp 2 ν ℝ A - hf₂.toLp f‖ < ε := by
  let act (p : X × G) := p.2 • p.1
  have ha : Continuous act := continuous_snd.smul continuous_fst
  let ν' := Measure.map act (ν.prod η)
  let : IsProbabilityMeasure ν' := (Measure.isProbabilityMeasure_map_iff ha.measurable.aemeasurable).2 inferInstance
  have hf' : MemLp f 2 ν' := MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ ν' ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  obtain ⟨h, hh⟩ := Metric.mem_closure_range_iff.mp (hd (hf'.toLp f)) ε hε
  have hnear : ‖BoundedContinuousFunction.toLp 2 ν' ℝ h - hf'.toLp f‖ < ε := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hh
  let a (x : X) := ∫ g, h (g • x) ∂η
  have hac : Continuous a := continuous_integral_parameter η (h.continuous.comp ha)
  let A : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨a, hac⟩
  have hA (g : G) (x : X) : A (g • x) = A x := by
    change (∫ z, h (z • (g • x)) ∂η) = _
    simp only [← mul_smul]
    exact integral_mul_right_eq_self (μ := η) (fun z => h (z • x)) g
  refine ⟨A, hA, ?_⟩
  have hleft :
      ‖BoundedContinuousFunction.toLp 2 ν ℝ A - hf₂.toLp f‖ ^ 2 =
        ∫ x, (A x - f x) ^ 2 ∂ν :=
    norm_L2_sub_sq_eq_integral_of_ae _ _ (BoundedContinuousFunction.coeFn_toLp 2 ν ℝ A) hf₂.coeFn_toLp
  have hright :
      ‖BoundedContinuousFunction.toLp 2 ν' ℝ h - hf'.toLp f‖ ^ 2 =
        ∫ x, (h x - f x) ^ 2 ∂ν' :=
    norm_L2_sub_sq_eq_integral_of_ae _ _ (BoundedContinuousFunction.coeFn_toLp 2 ν' ℝ h) hf'.coeFn_toLp
  have hB : MemLp (fun x => A x - f x) 2 ν := by
    apply (MemLp.of_bound A.continuous.measurable.aestronglyMeasurable ‖A‖
      (ae_of_all _ A.norm_coe_le_norm)).sub hf₂
  let d (q : X × G) := h (act q) - f q.1
  have hD : MemLp d 2 (ν.prod η) := by
    refine MemLp.of_bound ((h.continuous.measurable.comp ha.measurable).sub
      (hf.comp measurable_fst)).aestronglyMeasurable (‖h‖ + C) (ae_of_all _ fun q => ?_)
    exact (norm_sub_le _ _).trans (add_le_add (h.norm_coe_le_norm _) (hC _))
  have hpoint (x : X) : (A x - f x) ^ 2 ≤ ∫ g, d (x, g) ^ 2 ∂η := by
    have hc : Continuous (fun g : G => h (g • x)) :=
      h.continuous.comp (continuous_id.smul continuous_const)
    have hi : Integrable (fun g : G => h (g • x)) η :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hx : MemLp (fun g : G => d (x, g)) 2 η :=
      (MemLp.of_bound hc.measurable.aestronglyMeasurable ‖h‖
        (ae_of_all _ fun g => h.norm_coe_le_norm (g • x))).sub (memLp_const (f x))
    have he : (∫ g, d (x, g) ∂η) = A x - f x := by
      change (∫ g, h (g • x) - f x ∂η) = a x - f x
      rw [integral_sub hi (integrable_const _), integral_const]
      simp only [probReal_univ, one_smul, a]
    simpa only [he] using sq_integral_le_integral_sq hx
  have hInt : (∫ x, (A x - f x) ^ 2 ∂ν) ≤ ∫ x, (h x - f x) ^ 2 ∂ν' := by
    have hm : Measurable (fun x => (h x - f x) ^ 2) :=
      (h.continuous.measurable.sub hf).pow_const _
    calc
      _ ≤ ∫ x, ∫ g, d (x, g) ^ 2 ∂η ∂ν :=
        integral_mono hB.integrable_sq hD.integrable_sq.integral_prod_left hpoint
      _ = ∫ q, d q ^ 2 ∂ν.prod η := (integral_prod _ hD.integrable_sq).symm
      _ = _ := by
        rw [show ν' = Measure.map act (ν.prod η) from rfl, integral_map ha.measurable.aemeasurable
          hm.aestronglyMeasurable]
        apply integral_congr_ae
        exact ae_of_all _ fun q => by simp only [d, act, hInv]
  rw [← hleft, ← hright] at hInt
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hInt).trans_lt hnear

set_option maxHeartbeats 800000 in
/-- Every bounded measurable gauge-invariant half-space cylinder belongs
to the Euclidean half-space defined by continuous cylinders. -/
theorem mem_wilsonHalfSpace_of_cylinder {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) (τ : Axis)
    (f : InfiniteConfig N → ℝ) (hf : Measurable f) (hf₂ : MemLp f 2 μ.toMeasure)
    (C : ℝ) (hC : ∀ U, ‖f U‖ ≤ C) (hInv : GaugeInvariantObservable f)
    (hCylinder : HalfSpaceCylinder τ 0 f) : hf₂.toLp f ∈ wilsonHalfSpace μ τ := by
  classical
  obtain ⟨S, hS, hsupport⟩ := hCylinder
  let V := S.image Prod.snd ∪ S.image (fun e => e.2 + step e.1)
  let tail (e : {e // e ∈ S}) : {x // x ∈ V} :=
    ⟨e.val.2, Finset.mem_union_left _ (Finset.mem_image_of_mem _ e.property)⟩
  let head (e : {e // e ∈ S}) : {x // x ∈ V} :=
    ⟨e.val.2 + step e.val.1, Finset.mem_union_right _ (Finset.mem_image_of_mem _ e.property)⟩
  let G := {x // x ∈ V} → UnitaryMatrix N
  let X := InfiniteBlock N S
  let gauge (g : G) (z : X) (e : {e // e ∈ S}) := g (tail e) * z e * (g (head e))⁻¹
  have hmul (g h : G) (x : {x // x ∈ V}) : (g * h) x = g x * h x := rfl
  have hone (x : {x // x ∈ V}) : (1 : G) x = 1 := rfl
  let cylinderAction : MulAction G X :=
    { smul := gauge
      one_smul := fun z => by
        funext e
        change gauge 1 z e = z e
        simp only [gauge, hone, one_mul, inv_one, mul_one]
      mul_smul := fun g h z => by
        funext e
        change gauge (g * h) z e = gauge g (gauge h z) e
        simp only [gauge, hmul]
        group }
  let : SMul G X := cylinderAction.toSMul
  let actionContinuous : ContinuousSMul G X := ⟨continuous_pi fun e => by
    change Continuous (fun p : G × X => p.1 (tail e) * p.2 e * (p.1 (head e))⁻¹)
    exact (((continuous_apply (tail e)).comp continuous_fst).mul
      ((continuous_apply e).comp continuous_snd)).mul
        ((continuous_apply (head e)).comp continuous_fst).inv⟩
  let η : Measure G := Measure.pi fun _ => unitaryHaar N
  let : IsProbabilityMeasure η := by dsimp [η, G]; infer_instance
  let : η.IsMulRightInvariant :=
    ⟨fun g => (measurePreserving_pi (fun _ : {x // x ∈ V} => unitaryHaar N) (fun _ => unitaryHaar N)
      (fun x => measurePreserving_mul_right (unitaryHaar N) (g x))).map_eq⟩
  let read (U : InfiniteConfig N) (e : {e // e ∈ S}) := U e.val
  let join (z : X) := replaceLinks S (1 : InfiniteConfig N) z
  have hread : Continuous read := continuous_pi fun e => continuous_apply e.val
  have hjoin : Continuous join := (continuous_replaceLinks (N := N) S).comp
    (continuous_const.prodMk continuous_id)
  let ν := Measure.map read μ.toMeasure
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hread.measurable.aemeasurable).2 inferInstance
  let F : X → ℝ := f ∘ join
  have hF : Measurable F := hf.comp hjoin.measurable
  have hF₂ : MemLp F 2 ν := MemLp.of_bound hF.aestronglyMeasurable C (ae_of_all _ fun z => hC (join z))
  have hrec (U : InfiniteConfig N) : F (read U) = f U := by
    apply hsupport
    intro e he
    simp only [join, replaceLinks, dite_eq_left he, read]
  have hG (g : G) (z : X) : F (gauge g z) = F z := by
    let lift (x : Site) := if hx : x ∈ V then g ⟨x, hx⟩ else 1
    calc
      _ = f (gaugeConfig lift (join z)) := by
        apply hsupport
        intro e he
        have ht : e.2 ∈ V := (tail ⟨e, he⟩).property
        have hh : e.2 + step e.1 ∈ V := (head ⟨e, he⟩).property
        change replaceLinks S 1 (gauge g z) e = gaugeConfig lift (replaceLinks S 1 z) e
        simp only [replaceLinks, dite_eq_left he]
        change gauge g z ⟨e, he⟩ =
          lift e.2 * (replaceLinks S 1 z) e * (lift (e.2 + step e.1))⁻¹
        simp only [gauge, tail, head, lift, dite_eq_left ht, dite_eq_left hh, replaceLinks, dite_eq_left he]
      _ = _ := hInv lift (join z)
  change hf₂.toLp f ∈ closure ((wilsonHalfSpaceCoreL2 μ τ).range : Set (WilsonL2 μ))
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨A, hA, hnear⟩ := exists_continuous_invariant_L2_approx (action := cylinderAction)
    (actionContinuous := actionContinuous) η ν F hF hF₂ C
    (fun z => hC (join z)) hG ε hε
  let B := A.compContinuous ⟨read, hread⟩
  have hB : B ∈ wilsonHalfSpaceCore N τ := by
    constructor
    · refine ⟨S, hS, fun U U' h => ?_⟩
      have hr : read U = read U' := funext fun e => h e.val e.property
      change A (read U) = A (read U')
      rw [hr]
    · intro g U
      exact hA (fun x => g x.val) (read U)
  let u := wilsonHalfSpaceCoreL2 μ τ ⟨B, hB⟩
  refine ⟨u, ⟨⟨B, hB⟩, rfl⟩, ?_⟩
  have hu : (u : InfiniteConfig N → ℝ) =ᵐ[μ.toMeasure] B :=
    BoundedContinuousFunction.coeFn_toLp 2 μ.toMeasure ℝ B
  have hnorm : ‖u - hf₂.toLp f‖ ^ 2 = ‖BoundedContinuousFunction.toLp 2 ν ℝ A - hF₂.toLp F‖ ^ 2 := by
    rw [norm_L2_sub_sq_eq_integral_of_ae _ _ hu hf₂.coeFn_toLp,
      norm_L2_sub_sq_eq_integral_of_ae _ _ (BoundedContinuousFunction.coeFn_toLp 2 ν ℝ A) hF₂.coeFn_toLp]
    have hm : Measurable (fun z => (A z - F z) ^ 2) := (A.continuous.measurable.sub hF).pow_const _
    change (∫ U, (A (read U) - f U) ^ 2 ∂μ.toMeasure) = ∫ z, (A z - F z) ^ 2 ∂Measure.map read μ.toMeasure
    rw [integral_map hread.measurable.aemeasurable hm.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun U => by simp only [hrec U])
  rw [dist_comm, dist_eq_norm]
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnorm.le).trans_lt hnear

end

end GaplessYangMills

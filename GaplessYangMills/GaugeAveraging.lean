module

public import GaplessYangMills.KernelCycleEstimate
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.Instances.Matrix

/-!
# Averaging kernels over the gauge action

Simultaneous gauge invariance and left Haar invariance turn a one-sided gauge
average into independent averages at the two endpoints. Positive sample
matrices are preserved by independent averaging.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped Matrix

noncomputable section

theorem continuous_integral_parameter {X Y : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] {f : X × Y → ℝ} (hf : Continuous f) :
    Continuous (fun x => ∫ y, f (x, y) ∂ν) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun q hq => ?_⟩
  have hi (a : X) : Integrable (fun y => f (a, y)) ν :=
    (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [dist_eq_norm, ← integral_sub (hi q) (hi p)]
  have hb (y : Y) : ‖f (q, y) - f (p, y)‖ ≤ ε / 2 := by
    have hp : dist (q, y) (p, y) < δ := by
      change max (dist q p) (dist y y) < δ
      rw [dist_self, max_lt_iff]
      exact ⟨hq, hδ⟩
    simpa only [dist_eq_norm] using (hd hp).le
  have hn : ‖∫ y, f (q, y) - f (p, y) ∂ν‖ ≤ ε / 2 := by
    simpa using norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hb)
  exact hn.trans_lt (by linarith)

/-- Positive definiteness of a real kernel on finite samples, with repeated
sample points allowed. -/
def PositiveKernel {X : Type*} (K : X → X → ℝ) : Prop :=
  ∀ (m : ℕ) (v : Fin m → X), (Matrix.of fun a b => K (v a) (v b)).PosSemidef

theorem PositiveKernel.sample {X I : Type*} [Fintype I] {K : X → X → ℝ}
    (hK : PositiveKernel K) (v : I → X) :
    (Matrix.of fun a b => K (v a) (v b)).PosSemidef := by
  classical
  let e := Fintype.equivFin I
  have h := (hK (Fintype.card I) (v ∘ e.symm)).submatrix e
  have he : (Matrix.of fun a b => K ((v ∘ e.symm) a) ((v ∘ e.symm) b)).submatrix e e =
      Matrix.of (fun a b => K (v a) (v b)) := by
    ext a b
    simp
  rwa [he] at h

/-- Multiplication by the same weight at each endpoint. -/
def weightedKernel {X : Type*} (w : X → ℝ) (K : X → X → ℝ) (a b : X) : ℝ :=
  w a * K a b * w b

theorem continuous_weightedKernel {X : Type*} [TopologicalSpace X] {w : X → ℝ}
    {K : X → X → ℝ} (hw : Continuous w) (hK : Continuous (fun p : X × X => K p.1 p.2)) :
    Continuous (fun p : X × X => weightedKernel w K p.1 p.2) :=
  ((hw.comp continuous_fst).mul hK).mul (hw.comp continuous_snd)

theorem PositiveKernel.weighted {X : Type*} {K : X → X → ℝ} (hK : PositiveKernel K)
    (w : X → ℝ) : PositiveKernel (weightedKernel w K) := by
  intro m v
  let D := Matrix.diagonal fun a : Fin m => w (v a)
  let M : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b => K (v a) (v b)
  have hD : Dᴴ = D := by simp [D]
  have he : D * M * D = Matrix.of (fun a b => weightedKernel w K (v a) (v b)) := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rfl
  have hM : M.PosSemidef := hK m v
  have hh := hM.conjTranspose_mul_mul_same D
  rwa [hD, he] at hh

theorem weightedKernel_sub {X : Type*} (w : X → ℝ) (R K : X → X → ℝ) (a b : X) :
    weightedKernel w (fun x y => R x y - K x y) a b =
      weightedKernel w R a b - weightedKernel w K a b := by
  simp only [weightedKernel, mul_sub, sub_mul]

private theorem finiteAverage_posSemidef {X : Type*} {m n : ℕ} {K : X → X → ℝ}
    (hK : PositiveKernel K) (v : Fin m → Fin n → X) (w : Fin n → ℝ) :
    (Matrix.of fun i j => ∑ a, ∑ b, w a * w b * K (v i a) (v j b)).PosSemidef := by
  let M : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
    Matrix.of fun p q => K (v p.1 p.2) (v q.1 q.2)
  let D : Matrix (Fin m × Fin n) (Fin m) ℝ :=
    Matrix.of fun p i => if p.1 = i then w p.2 else 0
  have hp : (Dᴴ * M * D).PosSemidef :=
    (hK.sample (fun p : Fin m × Fin n => v p.1 p.2)).conjTranspose_mul_mul_same D
  have he : Dᴴ * M * D =
      Matrix.of (fun i j => ∑ a, ∑ b, w a * w b * K (v i a) (v j b)) := by
    ext i j
    have hleft (b : Fin m × Fin n) : (Dᴴ * M) i b =
        ∑ a, w a * K (v i a) (v b.1 b.2) := by
      simp [Matrix.mul_apply, D, M, Fintype.sum_prod_type, ite_mul,
        Finset.sum_ite_irrel]
    simp only [Matrix.mul_apply (M := Dᴴ * M) (N := D), Matrix.of_apply, Fintype.sum_prod_type,
      hleft, D, mul_ite, mul_zero, Finset.sum_ite_irrel]
    simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rwa [he] at hp

private theorem integral_prod_finite_selector {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    [IsProbabilityMeasure ν] {n : ℕ} (q : Y → Fin n) (hq : Measurable q)
    (f : Fin n × Fin n → ℝ) :
    (∫ p : Y × Y, f (q p.1, q p.2) ∂ν.prod ν) =
      ∑ a, ∑ b, (ν.map q).real {a} * (ν.map q).real {b} * f (a, b) := by
  have hmap : Measurable (Prod.map q q) := (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
  have hf : Measurable f := measurable_of_countable f
  have hfin : Integrable f ((ν.map q).prod (ν.map q)) :=
    Integrable.of_bound hf.aestronglyMeasurable (∑ a, ‖f a‖)
      (Filter.Eventually.of_forall fun a => Finset.single_le_sum (fun b _ => norm_nonneg (f b))
        (Finset.mem_univ a))
  change (∫ p, f (Prod.map q q p) ∂ν.prod ν) = _
  rw [← integral_map hmap.aemeasurable hf.aestronglyMeasurable,
    ← Measure.map_prod_map ν ν hq hq, integral_fintype hfin, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : ({(a, b)} : Set (Fin n × Fin n)) = {a} ×ˢ {b} := by ext p; simp [Prod.ext_iff]
  simp only [he, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul, smul_eq_mul]

open scoped Matrix.Norms.Elementwise in
/-- Averaging the two endpoints independently preserves positive sample
matrices. Finite quadratures converge entrywise to the averaged sample. -/
theorem positiveKernel_doubleAverage {X Y : Type*} [TopologicalSpace X]
    [PseudoMetricSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]
    (F : Y → X → X) (hF : ∀ x, Continuous (fun g => F g x))
    {K : X → X → ℝ} (hc : Continuous (fun p : X × X => K p.1 p.2)) (hK : PositiveKernel K) :
    PositiveKernel (fun a b => ∫ p : Y × Y, K (F p.1 a) (F p.2 b) ∂ν.prod ν) := by
  intro m v
  let f (i j : Fin m) (p : Y × Y) := K (F p.1 (v i)) (F p.2 (v j))
  have hcont (i j : Fin m) : Continuous (f i j) :=
    hc.comp (((hF (v i)).comp continuous_fst).prodMk ((hF (v j)).comp continuous_snd))
  let M : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => ∫ p, f i j p ∂ν.prod ν
  let S : Set (Matrix (Fin m) (Fin m) ℝ) := {A | A.PosSemidef}
  have hs : IsClosed S := isClosed_setOfPred_posSemidef
  change M ∈ S
  apply hs.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let profile (p : Y × Y) (i : Fin m × Fin m) := f i.1 i.2 p
  have hp : Continuous profile := continuous_pi fun i => hcont i.1 i.2
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hp) (ε / 2) hhalf
  obtain ⟨n, points, q, hq, hnear⟩ := exists_finite_quadrature (X := Y) δ hδ
  let w (i : Fin n) := (ν.map q).real {i}
  let A : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.of fun i j => ∑ a, ∑ b, w a * w b * f i j (points a, points b)
  refine ⟨A, finiteAverage_posSemidef hK (fun i a => F (points a) (v i)) w, ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ((Matrix.norm_le_iff hhalf.le).mpr ?_) (by linarith)
  intro i j
  let g (p : Y × Y) := f i j (points (q p.1), points (q p.2))
  have hg (p : Y × Y) : ‖f i j p - g p‖ ≤ ε / 2 := by
    have hd : dist p (points (q p.1), points (q p.2)) < δ := max_lt (hnear p.1) (hnear p.2)
    simpa only [dist_eq_norm, profile, g] using ((dist_pi_lt_iff hhalf).mp (hu hd) (i, j)).le
  have him : Integrable (f i j) (ν.prod ν) :=
    (hcont i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he : (∫ p, g p ∂ν.prod ν) = A i j :=
    integral_prod_finite_selector ν q hq (fun p => f i j (points p.1, points p.2))
  have hig : Integrable g (ν.prod ν) := by
    let t : Y × Y → Fin n × Fin n := Prod.map q q
    have ht : Measurable t := (hq.comp measurable_fst).prodMk (hq.comp measurable_snd)
    let h (p : Fin n × Fin n) := f i j (points p.1, points p.2)
    have hall : Integrable h ((ν.prod ν).map t) := Integrable.of_bound
      (measurable_of_countable h).aestronglyMeasurable (∑ p, ‖h p‖)
      (Filter.Eventually.of_forall fun p => Finset.single_le_sum (fun j _ => norm_nonneg (h j))
        (Finset.mem_univ p))
    exact hall.comp_aemeasurable ht.aemeasurable
  change ‖(∫ p, f i j p ∂ν.prod ν) - A i j‖ ≤ _
  rw [← he, ← integral_sub him hig]
  simpa using norm_integral_le_of_norm_le_const (μ := ν.prod ν) (Filter.Eventually.of_forall hg)

/-- Average a kernel over gauges at the target slice. -/
def gaugeAverageKernel {G X : Type*} [MeasurableSpace G] [SMul G X]
    (ν : Measure G) (K : X → X → ℝ) (a b : X) : ℝ :=
  ∫ g, K a (g • b) ∂ν

theorem continuous_gaugeAverage {G X : Type*} [PseudoMetricSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [PseudoMetricSpace X] [CompactSpace X]
    [SMul G X] [ContinuousSMul G X] (ν : Measure G) [IsProbabilityMeasure ν]
    {K : X → X → ℝ} (hc : Continuous (fun p : X × X => K p.1 p.2)) :
    Continuous (fun p : X × X => gaugeAverageKernel ν K p.1 p.2) := by
  have hF : Continuous (fun p : (X × X) × G => K p.1.1 (p.2 • p.1.2)) :=
    hc.comp (continuous_fst.fst.prodMk (continuous_snd.smul continuous_fst.snd))
  exact continuous_integral_parameter ν hF

theorem PositiveKernel.integral_nonneg {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {K : X → X → ℝ} (hK : PositiveKernel K) (hc : Continuous (fun p : X × X => K p.1 p.2))
    (ν : Measure X) [IsProbabilityMeasure ν] :
    0 ≤ ∫ p : X × X, K p.1 p.2 ∂ν.prod ν := by
  classical
  let x : X := Classical.choice inferInstance
  have h := positiveKernel_doubleAverage ν (fun v (_ : X) => v) (fun _ => continuous_id) hc hK 1
    (fun _ => x)
  exact h.diag_nonneg (i := 0)

section Action

variable {G X : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (ν : Measure G) [IsProbabilityMeasure ν]

theorem gaugeAverage_eq_double [ν.IsMulLeftInvariant] {K : X → X → ℝ}
    (hc : Continuous (fun p : X × X => K p.1 p.2))
    (hinv : ∀ g : G, ∀ a b : X, K (g • a) (g • b) = K a b) (a b : X) :
    gaugeAverageKernel ν K a b = ∫ p : G × G, K (p.1 • a) (p.2 • b) ∂ν.prod ν := by
  let f (p : G × G) := K (p.1 • a) (p.2 • b)
  have hF : Continuous f := hc.comp
    ((continuous_fst.smul continuous_const).prodMk (continuous_snd.smul continuous_const))
  change (∫ g, K a (g • b) ∂ν) = ∫ p, f p ∂ν.prod ν
  rw [integral_prod f (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))]
  have he (g : G) : (∫ h, f (g, h) ∂ν) = ∫ h, K a (h • b) ∂ν := by
    calc
      (∫ h, f (g, h) ∂ν) = ∫ h, K a ((g⁻¹ * h) • b) ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun h => by
          simpa [f, ← mul_smul] using (hinv g⁻¹ (g • a) (h • b)).symm
      _ = _ := integral_mul_left_eq_self (μ := ν) (fun h => K a (h • b)) _
  simp_rw [he]
  simp

theorem PositiveKernel.gaugeAverage [ν.IsMulLeftInvariant] {K : X → X → ℝ}
    (hK : PositiveKernel K) (hc : Continuous (fun p : X × X => K p.1 p.2))
    (hinv : ∀ g : G, ∀ a b : X, K (g • a) (g • b) = K a b) :
    PositiveKernel (gaugeAverageKernel ν K) := by
  have he : gaugeAverageKernel ν K = fun a b => ∫ p : G × G, K (p.1 • a) (p.2 • b) ∂ν.prod ν := by
    funext a b
    exact gaugeAverage_eq_double ν hc hinv a b
  rw [he]
  exact positiveKernel_doubleAverage ν (· • ·) (fun _ => continuous_id.smul continuous_const) hc hK

omit [IsTopologicalGroup G] [SecondCountableTopology G] in
theorem gaugeAverageKernel_sub {K R : X → X → ℝ}
    (hK : Continuous (fun p : X × X => K p.1 p.2))
    (hR : Continuous (fun p : X × X => R p.1 p.2)) (a b : X) :
    gaugeAverageKernel ν (fun x y => R x y - K x y) a b =
      gaugeAverageKernel ν R a b - gaugeAverageKernel ν K a b := by
  have hi (F : X → X → ℝ) (hF : Continuous (fun p : X × X => F p.1 p.2)) :
      Integrable (fun g => F a (g • b)) ν :=
    (hF.comp (continuous_const.prodMk (continuous_id.smul continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_sub (hi R hR) (hi K hK)

end Action

end

end GaplessYangMills

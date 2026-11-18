module

public import GaplessYangMills.TraceCycle
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Finite quadrature for kernel cycles

A measurable finite selector gives an exact weighted matrix representation
for the pulled-back kernels. Compactness provides selectors of arbitrary
metric resolution.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory
open scoped Matrix

noncomputable section

/-- A compact metric space can be mapped measurably to finitely many points
with a uniform prescribed distance to the selected point. -/
theorem exists_finite_quadrature {X : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (points : Fin n → X) (q : X → Fin n),
      Measurable q ∧ ∀ x, dist x (points (q x)) < ε := by
  classical
  obtain ⟨s, _, hfinite, hcover⟩ := (isCompact_univ (X := X)).finite_cover_balls hε
  let e := hfinite.toFinset.equivFin
  let n := hfinite.toFinset.card
  let points (i : Fin n) : X := (e.symm i).val
  let choices (x : X) := Finset.univ.filter (fun i : Fin n => dist x (points i) < ε)
  have hn (x : X) : (choices x).Nonempty := by
    have hx := hcover (Set.mem_univ x)
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hys, hy⟩ := Set.mem_iUnion.mp hy
    let i := e ⟨y, hfinite.mem_toFinset.mpr hys⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [i, points] using hy
  let q (x : X) := (choices x).min' (hn x)
  have hq (x : X) : dist x (points (q x)) < ε :=
    (Finset.mem_filter.mp (Finset.min'_mem (choices x) (hn x))).2
  have hsingle (i : Fin n) : MeasurableSet (q ⁻¹' ({i} : Set (Fin n))) := by
    have hs : q ⁻¹' ({i} : Set (Fin n)) = Metric.ball (points i) ε ∩
      ⋂ j : Fin n, if j < i then (Metric.ball (points j) ε)ᶜ else Set.univ := by
      ext x
      change q x = i ↔ _
      constructor
      · intro hx
        refine ⟨hx ▸ hq x, Set.mem_iInter.mpr ?_⟩
        intro j
        by_cases hj : j < i
        · rw [ite_eq_left hj]
          intro hz
          have hm : j ∈ choices x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
          have hh : q x ≤ j := Finset.min'_le (choices x) j hm
          exact (not_le_of_gt hj) (hx ▸ hh)
        · simp [ite_eq_right hj]
      · intro hx
        have hm : i ∈ choices x := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1⟩
        refine le_antisymm (Finset.min'_le (choices x) i hm) (le_of_not_gt ?_)
        intro hlt
        have hz := Set.mem_iInter.mp hx.2 (q x)
        rw [ite_eq_left hlt] at hz
        exact hz (hq x)
    rw [hs]
    apply Metric.isOpen_ball.measurableSet.inter
    apply MeasurableSet.iInter
    intro j
    split_ifs <;> simp [Metric.isOpen_ball.measurableSet]
  refine ⟨n, points, q, ?_, hq⟩
  intro t _
  have ht : q ⁻¹' t = ⋃ i ∈ t, q ⁻¹' ({i} : Set (Fin n)) := by
    ext x
    simp
  rw [ht]
  exact MeasurableSet.biUnion t.to_countable (fun i _ => hsingle i)

/-- Composition of a nonempty list of kernels by integration over the
intermediate slice variables. -/
def kernelPath {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K : X → X → ℝ) (Ks : List (X → X → ℝ)) : X → X → ℝ :=
  List.rec (motive := fun _ => (X → X → ℝ) → X → X → ℝ) id
    (fun H _ previous K x y => ∫ z, K x z * previous H z y ∂μ) Ks K

@[simp] theorem kernelPath_nil {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K : X → X → ℝ) : kernelPath μ K [] = K := rfl

theorem kernelPath_cons {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K H : X → X → ℝ) (Ks : List (X → X → ℝ)) (x y : X) :
    kernelPath μ K (H :: Ks) x y = ∫ z, K x z * kernelPath μ H Ks z y ∂μ := rfl

/-- Integrate the diagonal of a composed nonempty path. -/
def kernelCycleIntegral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (K : X → X → ℝ) (Ks : List (X → X → ℝ)) : ℝ :=
  ∫ x, kernelPath μ K Ks x x ∂μ

private theorem integral_finite_selector {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {n : ℕ} (q : X → Fin n) (hq : Measurable q) (f : Fin n → ℝ) :
    (∫ x, f (q x) ∂μ) = ∑ i, (μ.map q).real {i} * f i := by
  have hf : Measurable f := measurable_of_countable _
  rw [← integral_map hq.aemeasurable hf.aestronglyMeasurable]
  have hin : Integrable f (μ.map q) := Integrable.of_bound hf.aestronglyMeasurable (∑ i, ‖f i‖)
    (Filter.Eventually.of_forall fun i => Finset.single_le_sum (fun j _ => norm_nonneg (f j))
      (Finset.mem_univ i))
  simpa only [smul_eq_mul] using integral_fintype hin

private def weightedPath {n : ℕ} (W K : Matrix (Fin n) (Fin n) ℝ)
    (Ks : List (Matrix (Fin n) (Fin n) ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  List.rec (motive := fun _ => Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) id
    (fun H _ previous K => K * W * previous H) Ks K

private theorem kernelPath_selector {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {n : ℕ} (q : X → Fin n) (hq : Measurable q)
    (K : Matrix (Fin n) (Fin n) ℝ) (Ks : List (Matrix (Fin n) (Fin n) ℝ)) (x y : X) :
    kernelPath μ (fun x y => K (q x) (q y))
      (Ks.map fun M x y => M (q x) (q y)) x y =
      weightedPath (Matrix.diagonal fun i => (μ.map q).real {i}) K Ks (q x) (q y) := by
  induction Ks generalizing K x with
  | nil => rfl
  | cons H Ks ih =>
    have hz (z : X) := ih H z
    simp only [List.map_cons, kernelPath_cons, hz]
    let W : Fin n → ℝ := fun i => (μ.map q).real {i}
    let B := weightedPath (Matrix.diagonal W) H Ks
    change (∫ z, K (q x) (q z) * B (q z) (q y) ∂μ) =
      (K * Matrix.diagonal W * B) (q x) (q y)
    rw [integral_finite_selector μ q hq (fun i => K (q x) i * B i (q y))]
    change (∑ i, (μ.map q).real {i} * (K (q x) i * B i (q y))) =
      ∑ i, (K * Matrix.diagonal W) (q x) i * B i (q y)
    simp only [Matrix.mul_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring

private theorem weightedPath_congruent_product {n : ℕ} (D W K : Matrix (Fin n) (Fin n) ℝ)
    (hD : D * D = W) (Ks : List (Matrix (Fin n) (Fin n) ℝ)) :
    ((K :: Ks).map fun M => D * M * D).prod = D * weightedPath W K Ks * D := by
  induction Ks generalizing K with
  | nil => simp [weightedPath]
  | cons H Ks ih =>
    change D * K * D * ((H :: Ks).map fun M => D * M * D).prod =
      D * (K * W * weightedPath W H Ks) * D
    rw [ih, ← hD]
    simp only [mul_assoc]

/-- For a finite selector of the slice variables, the integral cycle is
exactly the weighted matrix trace on the selected indices. -/
theorem kernelCycleIntegral_selector {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {n : ℕ} (q : X → Fin n) (hq : Measurable q)
    (K : Matrix (Fin n) (Fin n) ℝ) (Ks : List (Matrix (Fin n) (Fin n) ℝ)) :
    let D := Matrix.diagonal fun i : Fin n => Real.sqrt ((μ.map q).real {i})
    kernelCycleIntegral μ (fun x y => K (q x) (q y))
      (Ks.map fun M x y => M (q x) (q y)) =
      ((K :: Ks).map fun M => D * M * D).prod.trace := by
  intro D
  let w (i : Fin n) := (μ.map q).real {i}
  let W := Matrix.diagonal w
  let B := weightedPath W K Ks
  have hD : D * D = W := by
    change Matrix.diagonal (fun i => Real.sqrt (w i)) * Matrix.diagonal (fun i => Real.sqrt (w i)) =
      Matrix.diagonal w
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    simp only [← pow_two]
    exact Real.sq_sqrt measureReal_nonneg
  simp only [kernelCycleIntegral, kernelPath_selector μ q hq]
  change (∫ x, B (q x) (q x) ∂μ) = _
  rw [integral_finite_selector μ q hq (fun i => B i i), weightedPath_congruent_product D W K hD,
    Matrix.trace_mul_comm, ← mul_assoc, hD]
  simp [Matrix.trace, Matrix.diag, B, W, w]

end

end GaplessYangMills

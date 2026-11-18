module

public import GaplessYangMills.KernelQuadrature
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Stability of kernel cycle integrals

On a probability space, the error of a composed path is bounded by the
uniform single-kernel error times its length and the product of the other
kernel bounds.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory

variable {X J : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

private theorem probability_integral_norm_le {f : X → ℝ} {C : ℝ} (hf : ∀ x, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂μ‖ ≤ C := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hf)

private theorem kernelPath_measurable (K : J → X → X → ℝ)
    (hK : ∀ j, Measurable (fun z : X × X => K j z.1 z.2)) (j : J) (js : List J) :
    Measurable (fun z : X × X => kernelPath μ (K j) (js.map K) z.1 z.2) := by
  induction js generalizing j with
  | nil => exact hK j
  | cons i js ih =>
    have hg : Measurable (fun p : (X × X) × X => K j p.1.1 p.2) :=
      (hK j).comp (measurable_fst.fst.prodMk measurable_snd)
    have hh : Measurable (fun p : (X × X) × X =>
        kernelPath μ (K i) (js.map K) p.2 p.1.2) :=
      (ih i).comp (measurable_snd.prodMk measurable_fst.snd)
    simp only [List.map_cons, kernelPath_cons]
    exact ((hg.mul hh).stronglyMeasurable.integral_prod_right').measurable

private theorem kernelPath_norm_le (K : J → X → X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ j x y, ‖K j x y‖ ≤ C) (j : J) (js : List J) (x y : X) :
    ‖kernelPath μ (K j) (js.map K) x y‖ ≤ C ^ (js.length + 1) := by
  induction js generalizing j x with
  | nil => simpa using hK j x y
  | cons i js ih =>
    rw [List.map_cons, kernelPath_cons]
    apply probability_integral_norm_le
    intro z
    rw [norm_mul, List.length_cons, pow_succ, mul_comm (C ^ (js.length + 1))]
    exact mul_le_mul (hK j x z) (ih i z) (norm_nonneg _) hC

private theorem kernelPath_integrand_integrable (K : J → X → X → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ j x y, ‖K j x y‖ ≤ C)
    (hm : ∀ j, Measurable (fun z : X × X => K j z.1 z.2))
    (i j : J) (js : List J) (x y : X) :
    Integrable (fun z => K j x z * kernelPath μ (K i) (js.map K) z y) μ := by
  have hg : Measurable (fun z => K j x z) := (hm j).comp (measurable_const.prodMk measurable_id)
  have hh : Measurable (fun z => kernelPath μ (K i) (js.map K) z y) :=
    (kernelPath_measurable μ K hm i js).comp (measurable_id.prodMk measurable_const)
  refine Integrable.of_bound (hg.mul hh).aestronglyMeasurable (C * C ^ (js.length + 1)) ?_
  exact Filter.Eventually.of_forall fun z => by
    rw [norm_mul]
    exact mul_le_mul (hK j x z) (kernelPath_norm_le μ K C hC hK i js z y) (norm_nonneg _) hC

private theorem kernelPath_diff_le (K L : J → X → X → ℝ) (C δ : ℝ) (hC : 0 ≤ C)
    (hK : ∀ j x y, ‖K j x y‖ ≤ C) (hL : ∀ j x y, ‖L j x y‖ ≤ C)
    (hmK : ∀ j, Measurable (fun z : X × X => K j z.1 z.2))
    (hmL : ∀ j, Measurable (fun z : X × X => L j z.1 z.2))
    (hKL : ∀ j x y, ‖K j x y - L j x y‖ ≤ δ) (j : J) (js : List J) (x y : X) :
    ‖kernelPath μ (K j) (js.map K) x y - kernelPath μ (L j) (js.map L) x y‖ ≤
      ((js.length : ℝ) + 1) * C ^ js.length * δ := by
  induction js generalizing j x with
  | nil => simpa using hKL j x y
  | cons i js ih =>
    simp only [List.map_cons, kernelPath_cons]
    rw [← integral_sub (kernelPath_integrand_integrable μ K C hC hK hmK i j js x y)
      (kernelPath_integrand_integrable μ L C hC hL hmL i j js x y)]
    apply probability_integral_norm_le
    intro z
    let a := K j x z
    let b := L j x z
    let I := kernelPath μ (K i) (js.map K) z y
    let F := kernelPath μ (L i) (js.map L) z y
    have h : a * I - b * F = (a - b) * I + b * (I - F) := by ring
    change ‖a * I - b * F‖ ≤ _
    rw [h]
    calc
      _ ≤ ‖(a - b) * I‖ + ‖b * (I - F)‖ := norm_add_le _ _
      _ ≤ δ * C ^ (js.length + 1) + C * (((js.length : ℝ) + 1) * C ^ js.length * δ) := by
        simp only [norm_mul]
        refine add_le_add (mul_le_mul (hKL j x z) (kernelPath_norm_le μ K C hC hK i js z y)
          (norm_nonneg _) ((norm_nonneg _).trans (hKL j x z))) ?_
        exact mul_le_mul (hL j x z) (ih i z) (norm_nonneg _) hC
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one, pow_succ]; ring

theorem kernelCycleIntegral_diff_le (K L : J → X → X → ℝ) (C δ : ℝ) (hC : 0 ≤ C)
    (hK : ∀ j x y, ‖K j x y‖ ≤ C) (hL : ∀ j x y, ‖L j x y‖ ≤ C)
    (hmK : ∀ j, Measurable (fun z : X × X => K j z.1 z.2))
    (hmL : ∀ j, Measurable (fun z : X × X => L j z.1 z.2))
    (hKL : ∀ j x y, ‖K j x y - L j x y‖ ≤ δ) (j : J) (js : List J) :
    ‖kernelCycleIntegral μ (K j) (js.map K) - kernelCycleIntegral μ (L j) (js.map L)‖ ≤
      ((js.length : ℝ) + 1) * C ^ js.length * δ := by
  have hint (M : J → X → X → ℝ) (hM : ∀ j x y, ‖M j x y‖ ≤ C)
      (hm : ∀ j, Measurable (fun z : X × X => M j z.1 z.2)) :
      Integrable (fun x => kernelPath μ (M j) (js.map M) x x) μ := by
    have h : Measurable (fun x => kernelPath μ (M j) (js.map M) x x) :=
      (kernelPath_measurable μ M hm j js).comp (measurable_id.prodMk measurable_id)
    exact Integrable.of_bound h.aestronglyMeasurable (C ^ (js.length + 1))
      (Filter.Eventually.of_forall fun x => kernelPath_norm_le μ M C hC hM j js x x)
  rw [kernelCycleIntegral, kernelCycleIntegral, ← integral_sub (hint K hK hmK) (hint L hL hmL)]
  exact probability_integral_norm_le μ (fun x => kernelPath_diff_le μ K L C δ hC hK hL hmK hmL hKL j js x x)

open scoped Matrix

/-- Positive order on all finite samples bounds the integral of each even
cycle of continuous kernels by the constant reference cycle. -/
theorem kernelCycleIntegral_le_of_sampleOrder [PseudoMetricSpace X] [CompactSpace X]
    [SecondCountableTopology X] [BorelSpace X] [Fintype J] [Nonempty J]
    (K : J → X → X → ℝ) (R : X → X → ℝ)
    (hK : ∀ j, Continuous (fun p : X × X => K j p.1 p.2))
    (hR : Continuous (fun p : X × X => R p.1 p.2))
    (hpos : ∀ (m : ℕ) (v : Fin m → X) j,
      (Matrix.of fun a b => K j (v a) (v b)).PosSemidef)
    (horder : ∀ (m : ℕ) (v : Fin m → X) j,
      ((Matrix.of fun a b => R (v a) (v b)) -
        (Matrix.of fun a b => K j (v a) (v b))).PosSemidef)
    (j : J) (js : List J) {n : ℕ} (hn : 0 < n) (hsize : (j :: js).length = 2 * n) :
    kernelCycleIntegral μ (K j) (js.map K) ≤
      kernelCycleIntegral μ R (List.replicate js.length R) := by
  let F (i : Option J) : X → X → ℝ := i.elim R K
  have hnone : F none = R := rfl
  have hsome (i : J) : F (some i) = K i := rfl
  let profile (z : X × X) (i : Option J) := F i z.1 z.2
  have hF (i : Option J) : Continuous (fun z : X × X => F i z.1 z.2) := by
    cases i with
    | none => exact hR
    | some i => exact hK i
  have hc : Continuous profile := continuous_pi hF
  obtain ⟨c₀, hc₀⟩ := (isCompact_univ.image (continuous_norm.comp hc)).bddAbove
  let C := max 1 c₀
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hnorm (i : Option J) (x y : X) : ‖F i x y‖ ≤ C :=
    (norm_le_pi_norm (profile (x, y)) i).trans
      ((hc₀ ⟨(x, y), Set.mem_univ _, rfl⟩).trans (le_max_right _ _))
  have hm (i : Option J) : Measurable (fun p : X × X => F i p.1 p.2) := (hF i).measurable
  apply le_of_forall_pos_le_add
  intro ε hε
  let gain := ((js.length : ℝ) + 1) * C ^ js.length
  have hg : 0 < gain := by unfold gain; positivity
  let δ := ε / (2 * gain)
  have hδ : 0 < δ := by unfold δ; positivity
  have hgain : gain * δ = ε / 2 := by
    unfold δ
    field_simp [hg.ne']
  obtain ⟨r, hr, hnear⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) δ hδ
  obtain ⟨m, v, q, hq, hd⟩ := exists_finite_quadrature (X := X) r hr
  let Q (i : Option J) (x y : X) := F i (v (q x)) (v (q y))
  have hQ (i : Option J) : Measurable (fun z : X × X => Q i z.1 z.2) := by
    have hqv : Measurable (v ∘ q) := (measurable_of_countable v).comp hq
    exact (hm i).comp ((hqv.comp measurable_fst).prodMk (hqv.comp measurable_snd))
  have hdist (i : Option J) (x y : X) : ‖F i x y - Q i x y‖ ≤ δ := by
    have hp : dist (x, y) (v (q x), v (q y)) < r := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨hd x, hd y⟩
    simpa only [dist_eq_norm, profile, Q] using ((dist_pi_lt_iff hδ).mp (hnear hp) i).le
  let A (i : J) : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b => K i (v a) (v b)
  let B : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b => R (v a) (v b)
  let D := Matrix.diagonal fun a : Fin m => Real.sqrt ((μ.map q).real {a})
  have hD : Dᴴ = D := by simp [D]
  have hA (i : J) : (D * A i * D).PosSemidef := by
    simpa only [hD] using (hpos m v i).conjTranspose_mul_mul_same D
  have hB (i : J) : (D * B * D - D * A i * D).PosSemidef := by
    simpa only [hD, mul_sub, sub_mul] using (horder m v i).conjTranspose_mul_mul_same D
  have htrace := trace_even_word_le_reference (fun i => D * A i * D) (D * B * D) hA hB hn
    (j :: js) hsize
  have hleft : kernelCycleIntegral μ (Q (some j)) (js.map fun i => Q (some i)) =
      ((j :: js).map fun i => D * A i * D).prod.trace := by
    simpa only [Q, hsome, A, D, List.map_cons, List.map_map, Function.comp_def, Matrix.of_apply] using
      kernelCycleIntegral_selector μ q hq (A j) (js.map A)
  have hright : kernelCycleIntegral μ (Q none) (List.replicate js.length (Q none)) =
      ((D * B * D) ^ (2 * n)).trace := by
    have ht := kernelCycleIntegral_selector μ q hq B (List.replicate js.length B)
    have hlen : js.length + 1 = 2 * n := hsize
    simpa only [Q, hnone, B, D, List.map_replicate, List.map_cons, List.prod_cons, List.prod_replicate,
      Matrix.of_apply, ← pow_succ', hlen] using ht
  have hdisc : kernelCycleIntegral μ (Q (some j)) (js.map fun i => Q (some i)) ≤
      kernelCycleIntegral μ (Q none) (List.replicate js.length (Q none)) := by
    rw [hleft, hright]
    exact htrace
  have hleftError := kernelCycleIntegral_diff_le μ F Q C δ hC.le hnorm
    (fun i x y => hnorm i _ _) hm hQ hdist (some j) (js.map some)
  have hrightError := kernelCycleIntegral_diff_le μ F Q C δ hC.le hnorm
    (fun i x y => hnorm i _ _) hm hQ hdist none (List.replicate js.length none)
  have he₁ : ‖kernelCycleIntegral μ (K j) (js.map K) -
      kernelCycleIntegral μ (Q (some j)) (js.map fun i => Q (some i))‖ ≤ ε / 2 := by
    simpa only [List.length_map, ← hgain, gain, List.map_map, Function.comp_def, hsome] using hleftError
  have he₂ : ‖kernelCycleIntegral μ R (List.replicate js.length R) -
      kernelCycleIntegral μ (Q none) (List.replicate js.length (Q none))‖ ≤ ε / 2 := by
    simpa only [List.length_replicate, ← hgain, gain, List.map_replicate, hnone] using hrightError
  rw [Real.norm_eq_abs, abs_le] at he₁ he₂
  linarith only [he₁.2, he₂.1, hdisc]

end GaplessYangMills

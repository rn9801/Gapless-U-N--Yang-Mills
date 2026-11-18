module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Volume of the solid complex cap

In a product of one complex coordinate and a real normed space, the cap
condition compresses the remaining coordinates. The annular cross-section
has the area of the original ball cross-section at the rescaled point.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory Metric
open scoped ENNReal

private theorem complexShell_volume {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    volume {z : ℂ | a ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 < b} = ENNReal.ofReal (Real.pi * (b - a)) := by
  have hb : 0 ≤ b := ha.trans hab
  have hbvol (t : ℝ) (ht : 0 ≤ t) :
      volume (ball (0 : ℂ) (Real.sqrt t)) = ENNReal.ofReal (Real.pi * t) := by
    have hp : (↑NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
      simp [← NNReal.coe_real_pi]
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow (Real.sqrt_nonneg t), Real.sq_sqrt ht,
      hp, ← ENNReal.ofReal_mul ht, mul_comm t]
  have he : {z : ℂ | a ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 < b} =
      ball 0 (Real.sqrt b) \ ball 0 (Real.sqrt a) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, mem_ball_zero_iff, Real.lt_sqrt (norm_nonneg z)]
    exact and_comm.trans (by rw [not_lt])
  rw [he, measure_sdiff (ball_subset_ball (Real.sqrt_le_sqrt hab))
    isOpen_ball.measurableSet.nullMeasurableSet (measure_ball_lt_top.ne), hbvol _ hb, hbvol _ ha,
    ← ENNReal.ofReal_sub _ (mul_nonneg Real.pi_pos.le ha)]
  congr 1
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def complexUnitSet : Set (ℂ × E) := {p | ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 < 1}

def complexCapSet (s : ℝ) : Set (ℂ × E) :=
  complexUnitSet ∩ {p | ‖p.2‖ ^ 2 ≤ s ^ 2 * (‖p.1‖ ^ 2 + ‖p.2‖ ^ 2)}

private theorem complexCap_section_scaled (s : ℝ) (hs : 0 < s) (hs' : s ≤ 1) (y : E) :
    volume ((fun z : ℂ => (z, s • y)) ⁻¹' complexCapSet s) =
      volume ((fun z : ℂ => (z, y)) ⁻¹' complexUnitSet) := by
  let t := ‖y‖ ^ 2
  have ht : 0 ≤ t := by unfold t; positivity
  have hn : ‖s • y‖ ^ 2 = s ^ 2 * t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow]
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hs3 : s ^ 2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs') hs.le]
  have he :
      (fun z : ℂ => (z, s • y)) ⁻¹' complexCapSet s =
        {z | (1 - s ^ 2) * t ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 < 1 - s ^ 2 * t} := by
    ext z
    change (‖z‖ ^ 2 + ‖s • y‖ ^ 2 < 1 ∧
      ‖s • y‖ ^ 2 ≤ s ^ 2 * (‖z‖ ^ 2 + ‖s • y‖ ^ 2)) ↔ _
    rw [hn, mul_le_mul_iff_right₀ hs2]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> refine ⟨?_, ?_⟩ <;> linarith only [h₁, h₂]
  have hu : (fun z : ℂ => (z, y)) ⁻¹' (complexUnitSet : Set (ℂ × E)) =
      {z | (0 : ℝ) ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 < 1 - t} := by
    ext z
    change ‖z‖ ^ 2 + t < 1 ↔ _
    simp only [Set.mem_ofPred_eq, sq_nonneg, true_and, lt_sub_iff_add_lt]
  rw [he, hu]
  by_cases h : t ≤ 1
  · rw [complexShell_volume (mul_nonneg (sub_nonneg.mpr hs3) ht) (by linarith),
      complexShell_volume (by norm_num : (0 : ℝ) ≤ 0) (by linarith)]
    congr 1
    ring
  · have hempty : {z : ℂ | (1 - s ^ 2) * t ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 < 1 - s ^ 2 * t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨h₁, h₂⟩ := hz
      linarith only [h₁, h₂, lt_of_not_ge h]
    have he₀ : {z : ℂ | (0 : ℝ) ≤ ‖z‖ ^ 2 ∧ ‖z‖ ^ 2 < 1 - t} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨h₁, h₂⟩ := hz
      linarith only [h₁, h₂, lt_of_not_ge h]
    rw [hempty, he₀]

/-- The solid cap-to-ball volume ratio is the scaling factor in the
orthogonal coordinates. -/
theorem complexCap_volume [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (ν : Measure E) [ν.IsAddHaarMeasure] (s : ℝ) (hs : 0 < s) (hs' : s ≤ 1) :
    ((volume : Measure ℂ).prod ν) (complexCapSet s) =
      ENNReal.ofReal (s ^ Module.finrank ℝ E) *
        ((volume : Measure ℂ).prod ν) complexUnitSet := by
  have hnorm : Measurable (fun p : ℂ × E => ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) := by fun_prop
  have hu : MeasurableSet (complexUnitSet : Set (ℂ × E)) :=
    measurableSet_lt hnorm measurable_const
  have hc : MeasurableSet (complexCapSet s : Set (ℂ × E)) :=
    hu.inter (measurableSet_le (by fun_prop) (measurable_const.mul hnorm))
  let f (y : E) := volume ((fun z : ℂ => (z, y)) ⁻¹' complexCapSet s)
  have hf : Measurable f := measurable_measure_prodMk_right hc
  have hi : (∫⁻ y, f (s • y) ∂ν) =
      (ENNReal.ofReal (s ^ Module.finrank ℝ E))⁻¹ * ∫⁻ y, f y ∂ν := by
    rw [← lintegral_map hf (measurable_const_smul s), ν.map_addHaar_smul hs.ne',
      lintegral_smul_measure, smul_eq_mul, abs_of_nonneg (by positivity), ENNReal.ofReal_inv_of_pos (pow_pos hs _)]
  rw [Measure.prod_apply_symm hc, Measure.prod_apply_symm hu]
  change (∫⁻ y, f y ∂ν) = _
  simp_rw [← complexCap_section_scaled s hs hs']
  change (∫⁻ y, f y ∂ν) = ENNReal.ofReal (s ^ Module.finrank ℝ E) * ∫⁻ y, f (s • y) ∂ν
  rw [hi, ← mul_assoc, ENNReal.mul_inv_cancel (by simp [pow_pos hs]) ENNReal.ofReal_ne_top, one_mul]

end GaplessYangMills

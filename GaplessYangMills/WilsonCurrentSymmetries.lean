module

public import GaplessYangMills.WilsonAxisTransfer
public import GaplessYangMills.WilsonLocalObservables

/-!
# Orientation of plaquette currents under lattice symmetries

Reflecting a temporal plaquette, or reordering its axes, inverts its
holonomy up to conjugation. The imaginary trace changes sign, and the
same transformation holds for the centered current.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped Matrix Topology

noncomputable section

def plaquetteReflectionSign (τ : Axis) (I : Face) : ℝ :=
  if I.axes.1 = τ ∨ I.axes.2 = τ then -1 else 1

def plaquettePermutationSign (σ : Equiv.Perm Axis) (I : Face) : ℝ :=
  if (permuteFace σ I).axes = (σ I.axes.1, σ I.axes.2) then 1 else -1

theorem abs_plaquetteReflectionSign (τ : Axis) (I : Face) : |plaquetteReflectionSign τ I| = 1 := by
  unfold plaquetteReflectionSign
  split <;> norm_num

theorem abs_plaquettePermutationSign (σ : Equiv.Perm Axis) (I : Face) : |plaquettePermutationSign σ I| = 1 := by
  unfold plaquettePermutationSign
  split <;> norm_num

private theorem unitaryTrace_im_inv {N : ℕ} (P : UnitaryMatrix N) :
    (P⁻¹).val.trace.im = -P.val.trace.im := by
  change (P.valᴴ).trace.im = _
  rw [Matrix.trace_conjTranspose]
  rfl

theorem plaquetteCurrent_reflectConfig {N : ℕ} (τ : Axis) (c : ℤ) (U : InfiniteConfig N)
    (I : Face) (x : Site) :
    plaquetteCurrent (reflectConfig τ c U) (I, x) =
      plaquetteReflectionSign τ I * plaquetteCurrent U (I, reflectedFaceBase τ c I x) := by
  let i : Axis := I.axes.1
  let j : Axis := I.axes.2
  have hij : i ≠ j := by cases I <;> decide
  let P (y : Site) := plaquetteHolonomy (fun k z => U (k, z)) I y
  change (reflectLinksOn τ c U (i, x) * reflectLinksOn τ c U (j, x + step i) *
    (reflectLinksOn τ c U (i, x + step j))⁻¹ * (reflectLinksOn τ c U (j, x))⁻¹).val.trace.im =
      plaquetteReflectionSign τ I * (P (reflectedFaceBase τ c I x)).val.trace.im
  by_cases hi : i = τ
  · have hj : j ≠ τ := fun h => hij (hi.trans h.symm)
    let y := reflectSiteOn τ (c - 1) x
    have hx : reflectSiteOn τ c x = y + step i := by
      rw [hi, ← reflectSiteOn_lower_add_step τ c x]
    have hbase : reflectedFaceBase τ c I x = y := by
      simp only [reflectedFaceBase, show I.axes.1 = τ from hi, true_or, ite_true, y]
    rw [hbase, reflectLinksOn_tangent hj, reflectLinksOn_tangent hj, hx,
      show reflectSiteOn τ c (x + step i) = y from hi.symm ▸ reflectSiteOn_add_step_normal τ c x]
    rw [show reflectLinksOn τ c U (i, x) = (U (i, y))⁻¹ by rw [hi, reflectLinksOn_normal],
      show reflectLinksOn τ c U (i, x + step j) = (U (i, y + step j))⁻¹ by
        rw [hi, reflectLinksOn_normal, reflectSiteOn_add_step_tangent hj]]
    have hh : (U (i, y))⁻¹ * U (j, y) * ((U (i, y + step j))⁻¹)⁻¹ * (U (j, y + step i))⁻¹ =
        (U (i, y))⁻¹ * (P y)⁻¹ * ((U (i, y))⁻¹)⁻¹ := by
      change _ = (U (i, y))⁻¹ * (U (i, y) * U (j, y + step i) *
        (U (i, y + step j))⁻¹ * (U (j, y))⁻¹)⁻¹ * ((U (i, y))⁻¹)⁻¹
      group
    rw [hh, unitaryTrace_conj, unitaryTrace_im_inv]
    simp [plaquetteReflectionSign, show I.axes.1 = τ from hi]
  · by_cases hj : j = τ
    · let y := reflectSiteOn τ (c - 1) x
      have hx : reflectSiteOn τ c x = y + step j := by
        rw [hj, ← reflectSiteOn_lower_add_step τ c x]
      have hbase : reflectedFaceBase τ c I x = y := by
        simp only [reflectedFaceBase, show I.axes.2 = τ from hj, or_true, ite_true, y]
      rw [hbase, reflectLinksOn_tangent hi, reflectLinksOn_tangent hi, hx,
        show reflectSiteOn τ c (x + step j) = y from hj.symm ▸ reflectSiteOn_add_step_normal τ c x]
      rw [show reflectLinksOn τ c U (j, x) = (U (j, y))⁻¹ by rw [hj, reflectLinksOn_normal],
        show reflectLinksOn τ c U (j, x + step i) = (U (j, y + step i))⁻¹ by
          rw [hj, reflectLinksOn_normal, reflectSiteOn_add_step_tangent hi]]
      have hh : U (i, y + step j) * (U (j, y + step i))⁻¹ * (U (i, y))⁻¹ *
          ((U (j, y))⁻¹)⁻¹ =
          (U (j, y))⁻¹ * (P y)⁻¹ * ((U (j, y))⁻¹)⁻¹ := by
        change _ = (U (j, y))⁻¹ * (U (i, y) * U (j, y + step i) *
          (U (i, y + step j))⁻¹ * (U (j, y))⁻¹)⁻¹ * ((U (j, y))⁻¹)⁻¹
        group
      rw [hh, unitaryTrace_conj, unitaryTrace_im_inv]
      simp [plaquetteReflectionSign, show I.axes.2 = τ from hj]
    · simp only [reflectedFaceBase, plaquetteReflectionSign, show I.axes.1 ≠ τ from hi, show I.axes.2 ≠ τ from hj,
        or_self, ite_false, reflectLinksOn_tangent hi, reflectLinksOn_tangent hj,
        reflectSiteOn_add_step_tangent hi, reflectSiteOn_add_step_tangent hj, one_mul]
      rfl

theorem plaquetteCurrent_permuteConfig {N : ℕ} (σ : Equiv.Perm Axis) (U : InfiniteConfig N)
    (I : Face) (x : Site) :
    plaquetteCurrent (permuteConfig σ U) (I, x) = plaquettePermutationSign σ I *
      plaquetteCurrent U (permuteFace σ I, permuteSite σ x) := by
  let y := permuteSite σ x
  let i := σ I.axes.1
  let j := σ I.axes.2
  let P (a b : Axis) := U (a, y) * U (b, y + step a) * (U (a, y + step b))⁻¹ * (U (b, y))⁻¹
  have hl : plaquetteHolonomy (fun k z => permuteConfig σ U (k, z)) I x = P i j := by
    simp only [plaquetteHolonomy, permuteConfig, permuteSite_add, permuteSite_step, P, i, j, y]
  change (plaquetteHolonomy (fun k z => permuteConfig σ U (k, z)) I x).val.trace.im =
    plaquettePermutationSign σ I * (plaquetteHolonomy (fun k z => U (k, z)) (permuteFace σ I) y).val.trace.im
  rw [hl]
  rcases permuteFace_axes σ I with h | h
  · simp [plaquettePermutationSign, h, plaquetteHolonomy, P, i, j]
  · have hn : (permuteFace σ I).axes ≠ (i, j) := by
      have hij : i ≠ j := σ.injective.ne (by cases I <;> decide)
      intro he
      exact hij (congrArg Prod.fst (he.symm.trans h))
    have hr : plaquetteHolonomy (fun k z => U (k, z)) (permuteFace σ I) y = (P i j)⁻¹ := by
      simp only [plaquetteHolonomy, h, P, i, j]
      group
    rw [hr, unitaryTrace_im_inv]
    simp [plaquettePermutationSign, show (permuteFace σ I).axes ≠ (σ I.axes.1, σ I.axes.2) from hn]

private theorem plaquetteCurrent_integral_transform {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N))
    (T : InfiniteConfig N → InfiniteConfig N) (hT : MeasurePreserving T μ.toMeasure μ.toMeasure)
    (p q : Plaquette) (s : ℝ) (h : ∀ U, plaquetteCurrent (T U) p = s * plaquetteCurrent U q) :
    (∫ V, plaquetteCurrent V p ∂μ.toMeasure) = s * ∫ V, plaquetteCurrent V q ∂μ.toMeasure := by
  calc
    _ = ∫ V, plaquetteCurrent V p ∂μ.toMeasure.map T := by rw [hT.map_eq]
    _ = ∫ V, plaquetteCurrent (T V) p ∂μ.toMeasure :=
      integral_map hT.measurable.aemeasurable (continuous_plaquetteCurrent p).measurable.aestronglyMeasurable
    _ = _ := by simp_rw [h, integral_const_mul]

private theorem centeredCurrent_transform {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N))
    (T : InfiniteConfig N → InfiniteConfig N) (hT : MeasurePreserving T μ.toMeasure μ.toMeasure)
    (p q : Plaquette) (s : ℝ) (h : ∀ U, plaquetteCurrent (T U) p = s * plaquetteCurrent U q)
    (U : InfiniteConfig N) :
    centeredPlaquetteCurrent μ.toMeasure (T U) p = s * centeredPlaquetteCurrent μ.toMeasure U q := by
  simp only [centeredPlaquetteCurrent, h, plaquetteCurrent_integral_transform μ T hT p q s h, mul_sub]

theorem centeredPlaquetteCurrent_reflectConfig {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (c : ℤ) (I : Face) (x : Site) (U : InfiniteConfig N) :
    centeredPlaquetteCurrent μ.toMeasure (reflectConfig τ c U) (I, x) =
      plaquetteReflectionSign τ I * centeredPlaquetteCurrent μ.toMeasure U (I, reflectedFaceBase τ c I x) :=
  centeredCurrent_transform μ _ (measurePreserving_reflectConfig μ hμ τ c) _ _ _
    (fun V => plaquetteCurrent_reflectConfig τ c V I x) U

theorem centeredPlaquetteCurrent_permuteConfig {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (I : Face) (x : Site) (U : InfiniteConfig N) :
    centeredPlaquetteCurrent μ.toMeasure (permuteConfig σ U) (I, x) =
      plaquettePermutationSign σ I * centeredPlaquetteCurrent μ.toMeasure U (permuteFace σ I, permuteSite σ x) :=
  centeredCurrent_transform μ _ (measurePreserving_permuteConfig μ hμ σ) _ _ _
    (fun V => plaquetteCurrent_permuteConfig σ V I x) U

theorem plaquetteCurrent_integral_eq_zero {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (I : Face) (x : Site) : (∫ U, plaquetteCurrent U (I, x) ∂μ.toMeasure) = 0 := by
  let τ := I.axes.1
  let y := reflectedFaceBase τ 0 I x
  have hs : plaquetteReflectionSign τ I = -1 := by simp [plaquetteReflectionSign, τ]
  have h := plaquetteCurrent_integral_transform μ (reflectConfig τ 0)
    (measurePreserving_reflectConfig μ hμ τ 0) (I, x) (I, y) (plaquetteReflectionSign τ I)
    (fun U => plaquetteCurrent_reflectConfig τ 0 U I x)
  have ht := integral_translateConfig β μ hμ (y - x) (fun U => plaquetteCurrent U (I, x))
    (continuous_plaquetteCurrent (I, x)).measurable
  have hy : x + (y - x) = y := by abel
  simp only [plaquetteCurrent_translateConfig, hy] at ht
  rw [hs, ht] at h
  linarith

theorem centeredPlaquetteCurrent_eq_current {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (U : InfiniteConfig N) (p : Plaquette) :
    centeredPlaquetteCurrent μ.toMeasure U p = plaquetteCurrent U p := by
  obtain ⟨I, x⟩ := p
  simp only [centeredPlaquetteCurrent, plaquetteCurrent_integral_eq_zero μ hμ, sub_zero]

end

end GaplessYangMills

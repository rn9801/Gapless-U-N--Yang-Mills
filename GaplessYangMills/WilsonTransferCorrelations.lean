module

public import GaplessYangMills.WilsonOS
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Removing the directional vacuum component

The Euclidean mean ergodic theorem identifies the plateau of a transfer
matrix element with the directional invariant projection. The Euclidean
norms then control the vacuum-subtracted matrix element.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped InnerProductSpace Topology

noncomputable section

theorem wilsonTranslateL2_nsmul {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (a : Site) (n : ℕ) :
    wilsonTranslateL2 μ hμ (n • a) = wilsonTranslateL2 μ hμ a ^ n := by
  induction n with
  | zero =>
    ext1 u
    rw [zero_nsmul, wilsonTranslateL2_zero, pow_zero, one_apply_eq_self]
  | succ n ih =>
    rw [succ_nsmul, ← wilsonTranslateL2_mul, ih, pow_succ]

theorem wilsonDirectionalProjection_shift {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (n : ℕ) (u : WilsonL2 μ) :
    wilsonDirectionalProjection μ hμ τ (wilsonTranslateL2 μ hμ (n • step τ) u) =
      wilsonDirectionalProjection μ hμ τ u := by
  let S := wilsonTranslateL2 μ hμ (step τ)
  let P := wilsonDirectionalProjection μ hμ τ
  have hSP : Commute S P :=
    commute_invariantProjection S S (norm_wilsonTranslateL2_le_one μ hμ (step τ)) (Commute.refl S)
  have hf : S (P u) = P u := by
    let W := wilsonInvariantSpace μ hμ τ
    change S (W.orthogonalProjectionOnto u).val = (W.orthogonalProjectionOnto u).val
    have hm := (LinearMap.mem_eqLocus.mp (W.orthogonalProjectionOnto u).property)
    exact hm
  have hpow : (S ^ n) (P u) = P u := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_apply_eq_comp, ih, hf]
  rw [wilsonTranslateL2_nsmul]
  calc
    P ((S ^ n) u) = (S ^ n) (P u) :=
      congrArg (fun A : WilsonL2 μ →L[ℝ] WilsonL2 μ => A u) (hSP.pow_left n).eq.symm
    _ = _ := hpow

theorem wilsonTransfer_matrixElement_plateau {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (P : (wilsonOSForm μ hl hμ τ).Hilbert →L[ℝ] (wilsonOSForm μ hl hμ τ).Hilbert)
    (hP : Tendsto (fun n : ℕ => wilsonTransfer hβ μ hl hμ τ ^ n) atTop (𝓝 P))
    (u v : wilsonHalfSpace μ τ) :
    ⟪wilsonReflectL2 μ hμ τ 0 u.val, wilsonDirectionalProjection μ hμ τ v.val⟫_ℝ =
      ⟪(wilsonOSForm μ hl hμ τ).ofVector u, P ((wilsonOSForm μ hl hμ τ).ofVector v)⟫_ℝ := by
  let B := wilsonOSForm μ hl hμ τ
  let S := wilsonTranslateL2 μ hμ (step τ)
  let R := wilsonReflectL2 μ hμ τ 0
  let c (n : ℕ) := ⟪R u.val, wilsonTranslateL2 μ hμ (n • step τ) v.val⟫_ℝ
  have hA : Continuous (fun Q : B.Hilbert →L[ℝ] B.Hilbert =>
      ⟪B.ofVector u, Q (B.ofVector v)⟫_ℝ) := by fun_prop
  have hconv : Tendsto c atTop (𝓝 ⟪B.ofVector u, P (B.ofVector v)⟫_ℝ) := by
    have heq : (fun n : ℕ => ⟪B.ofVector u, (wilsonTransfer hβ μ hl hμ τ ^ n) (B.ofVector v)⟫_ℝ) = c :=
      funext fun n => wilsonTransfer_matrixElement hβ μ hl hμ τ n u v
    rw [← heq]
    exact hA.continuousAt.tendsto.comp hP
  have hmean := S.tendsto_birkhoffAverage_orthogonalProjection
    (norm_wilsonTranslateL2_le_one μ hμ (step τ)) v.val
  have hB : Continuous (fun w : WilsonL2 μ => ⟪R u.val, w⟫_ℝ) := continuous_const.inner continuous_id
  have hlim : Tendsto (fun n => ⟪R u.val, birkhoffAverage ℝ S id n v.val⟫_ℝ) atTop
      (𝓝 ⟪R u.val, wilsonDirectionalProjection μ hμ τ v.val⟫_ℝ) :=
    hB.continuousAt.tendsto.comp hmean
  have he (n : ℕ) : S^[n] v.val = wilsonTranslateL2 μ hμ (n • step τ) v.val := by
    rw [wilsonTranslateL2_nsmul, pow_apply_eq_iterate]
  have hh : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, c k)
      atTop (𝓝 ⟪R u.val, wilsonDirectionalProjection μ hμ τ v.val⟫_ℝ) := by
    simpa only [birkhoffAverage, birkhoffSum, id_eq, he,
      real_inner_smul_right, inner_sum, c] using hlim
  exact tendsto_nhds_unique hh hconv.cesaro

set_option maxHeartbeats 600000 in
theorem wilsonTransfer_matrixElement_removeVacuum {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (P : (wilsonOSForm μ hl hμ τ).Hilbert →L[ℝ] (wilsonOSForm μ hl hμ τ).Hilbert)
    (hP : Tendsto (fun n : ℕ => wilsonTransfer hβ μ hl hμ τ ^ n) atTop (𝓝 P))
    (n : ℕ) (u v : wilsonHalfSpace μ τ) :
    ⟪wilsonReflectL2 μ hμ τ 0 u.val,
      (1 - wilsonDirectionalProjection μ hμ τ) (wilsonTranslateL2 μ hμ (n • step τ) v.val)⟫_ℝ =
        ⟪(wilsonOSForm μ hl hμ τ).ofVector u,
          (wilsonTransfer hβ μ hl hμ τ ^ n - P) ((wilsonOSForm μ hl hμ τ).ofVector v)⟫_ℝ := by
  simp only [sub_apply, one_apply_eq_self, inner_sub_right, wilsonDirectionalProjection_shift]
  exact congrArg₂ (· - ·) (wilsonTransfer_matrixElement hβ μ hl hμ τ n u v).symm
    (wilsonTransfer_matrixElement_plateau hβ μ hl hμ τ P hP u v)

set_option maxHeartbeats 600000 in
theorem wilsonTransfer_matrixElement_bound {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (P : (wilsonOSForm μ hl hμ τ).Hilbert →L[ℝ] (wilsonOSForm μ hl hμ τ).Hilbert)
    (hP : Tendsto (fun n : ℕ => wilsonTransfer hβ μ hl hμ τ ^ n) atTop (𝓝 P))
    (n : ℕ) (u v : wilsonHalfSpace μ τ) :
    |⟪wilsonReflectL2 μ hμ τ 0 u.val,
      (1 - wilsonDirectionalProjection μ hμ τ) (wilsonTranslateL2 μ hμ (n • step τ) v.val)⟫_ℝ| ≤
        ‖u.val‖ * ‖v.val‖ * ‖wilsonTransfer hβ μ hl hμ τ ^ n - P‖ := by
  let B := wilsonOSForm μ hl hμ τ
  let Q := wilsonTransfer hβ μ hl hμ τ ^ n - P
  calc
    _ = |⟪B.ofVector u, Q (B.ofVector v)⟫_ℝ| :=
      congrArg abs (wilsonTransfer_matrixElement_removeVacuum hβ μ hl hμ τ P hP n u v)
    _ ≤ ‖B.ofVector u‖ * ‖Q (B.ofVector v)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u.val‖ * (‖Q‖ * ‖v.val‖) :=
      mul_le_mul (wilsonOSVector_norm_le μ hl hμ τ u)
        ((Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left (wilsonOSVector_norm_le μ hl hμ τ v) (norm_nonneg _)))
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

end

end GaplessYangMills

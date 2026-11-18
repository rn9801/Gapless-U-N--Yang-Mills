module

public import GaplessYangMills.WilsonLocalObservables
public import GaplessYangMills.WilsonTransferCorrelations

/-!
# Transfer decay for separated local Wilson observables

Translate the two slabs together so that one lies strictly on the far
side of the reflection plane. Reflect that slab and apply the transfer
bound to the two positive-time vectors. The direction invariant
projection can be removed from either argument.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped Topology InnerProductSpace

noncomputable section

section WilsonLaw

variable {N : ℕ} {β : ℝ} {l : ℕ → ℕ} (μ : ProbabilityMeasure (InfiniteConfig N))
variable (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))

theorem wilsonTranslateL2_commute_projection (a : Site) (τ : Axis) :
    Commute (wilsonTranslateL2 μ hμ a) (wilsonDirectionalProjection μ hμ τ) := by
  let A := wilsonTranslateL2 μ hμ a
  let S := wilsonTranslateL2 μ hμ (step τ)
  have h : Commute A S := by
    change wilsonTranslateL2 μ hμ a * wilsonTranslateL2 μ hμ (step τ) =
      wilsonTranslateL2 μ hμ (step τ) * wilsonTranslateL2 μ hμ a
    rw [wilsonTranslateL2_mul, wilsonTranslateL2_mul, add_comm]
  exact commute_invariantProjection A S (norm_wilsonTranslateL2_le_one μ hμ (step τ)) h

theorem wilsonProjection_complement_inner (τ : Axis) (u v : WilsonL2 μ) :
    ⟪(1 - wilsonDirectionalProjection μ hμ τ) u, v⟫_ℝ =
      ⟪u, (1 - wilsonDirectionalProjection μ hμ τ) v⟫_ℝ := by
  simp only [sub_apply, one_apply_eq_self, inner_sub_left, inner_sub_right]
  exact congrArg (⟪u, v⟫_ℝ - ·) ((wilsonInvariantSpace μ hμ τ).inner_starProjection_left_eq_right u v)

theorem wilsonProjection_complement_norm_le (τ : Axis) (u : WilsonL2 μ) :
    ‖(1 - wilsonDirectionalProjection μ hμ τ) u‖ ≤ ‖u‖ := by
  have h : ‖1 - wilsonDirectionalProjection μ hμ τ‖ ≤ 1 := by
    simpa only [removeWilsonDirections, List.foldr_cons, List.foldr_nil, mul_one] using
      removeWilsonDirections_norm_le_one μ hμ [τ]
  simpa only [one_mul] using (1 - wilsonDirectionalProjection μ hμ τ).le_of_opNorm_le h u

private theorem translated_projected_inner (τ : Axis) (a x : Site) (u v : WilsonL2 μ) :
    ⟪(1 - wilsonDirectionalProjection μ hμ τ) u, wilsonTranslateL2 μ hμ x v⟫_ℝ =
      ⟪(1 - wilsonDirectionalProjection μ hμ τ) (wilsonTranslateL2 μ hμ a u),
        wilsonTranslateL2 μ hμ (x + a) v⟫_ℝ := by
  let A := wilsonTranslateL2 μ hμ a
  let Q := 1 - wilsonDirectionalProjection μ hμ τ
  have h : A (Q u) = Q (A u) := by
    have hc := congrArg (fun L : WilsonL2 μ →L[ℝ] WilsonL2 μ => L u)
      (wilsonTranslateL2_commute_projection μ hμ a τ).eq
    simp only [mul_apply_eq_comp] at hc
    simp only [Q, sub_apply, one_apply_eq_self, map_sub]
    exact congrArg (fun z => A u - z) hc
  have g : A (wilsonTranslateL2 μ hμ x v) = wilsonTranslateL2 μ hμ (x + a) v := by
    rw [add_comm x a, ← wilsonTranslateL2_mul, mul_apply_eq_comp]
  calc
    _ = ⟪A (Q u), A (wilsonTranslateL2 μ hμ x v)⟫_ℝ :=
      ((Lp.compMeasurePreservingₗᵢ ℝ (translateConfig a) (measurePreserving_translateConfig μ hμ a)).inner_map_map
        (Q u) (wilsonTranslateL2 μ hμ x v)).symm
    _ = _ := by rw [h, g]

end WilsonLaw

set_option maxHeartbeats 1000000 in
theorem wilsonLocalCovariance_directional_decay {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis)
    (P : (wilsonOSForm μ hl hμ τ).Hilbert →L[ℝ] (wilsonOSForm μ hl hμ τ).Hilbert)
    (hP : Tendsto (fun n : ℕ => wilsonTransfer hβ μ hl hμ τ ^ n) atTop (𝓝 P))
    (r : ℝ) (hPow : ∀ n : ℕ, ‖wilsonTransfer hβ μ hl hμ τ ^ n - P‖ ≤ r ^ n)
    (b : ℕ) (A : WilsonSlabObservable N τ (-(b : ℤ)) b) (J : WilsonSlabObservable N τ 0 1)
    (x : Site) :
    |⟪(1 - wilsonDirectionalProjection μ hμ τ) (J.toL2 μ), wilsonTranslateL2 μ hμ x (A.toL2 μ)⟫_ℝ| ≤
      ‖A.toL2 μ‖ * ‖J.toL2 μ‖ * r ^ ((x τ).natAbs - (b + 2)) := by
  let Q := 1 - wilsonDirectionalProjection μ hμ τ
  let C := ‖A.toL2 μ‖ * ‖J.toL2 μ‖
  let n := (x τ).natAbs - (b + 2)
  let T := wilsonTranslateL2 μ hμ
  let R := wilsonReflectL2 μ hμ τ 0
  have Rnorm (u : WilsonL2 μ) : ‖R u‖ = ‖u‖ := (wilsonReflectL2Isometry μ hμ τ 0).norm_map _
  have hbound (u v : wilsonHalfSpace μ τ) :
      |⟪R u.val, Q (T (n • step τ) v.val)⟫_ℝ| ≤ ‖u.val‖ * ‖v.val‖ * r ^ n :=
    (wilsonTransfer_matrixElement_bound hβ μ hl hμ τ P hP n u v).trans
      (mul_le_mul_of_nonneg_left (hPow n) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  change |⟪Q (J.toL2 μ), T x (A.toL2 μ)⟫_ℝ| ≤ C * r ^ n
  by_cases hlarge : b + 2 ≤ (x τ).natAbs
  · have hn : (n : ℤ) = ((x τ).natAbs : ℤ) - (b + 2) := by dsimp only [n]; push_cast [Nat.cast_sub hlarge]; ring
    rw [Int.natCast_natAbs] at hn
    by_cases hx : 0 ≤ x τ
    · let a : Site := (-2 : ℤ) • step τ
      let y : Site := x + a - n • step τ
      have ha : a τ = -2 := by simp [a, step_same]
      have hnτ : (n • step τ : Site) τ = (n : ℤ) := by simp [step_same]
      have hy : y τ = b := by
        change x τ + a τ - (n • step τ : Site) τ = _
        rw [ha, hnτ, hn, abs_of_nonneg hx]
        ring
      let u : wilsonHalfSpace μ τ :=
        ⟨((J.translate a).reflect 0).toL2 μ,
          ((J.translate a).reflect 0).toL2_mem_halfSpace μ (by rw [ha]; norm_num)⟩
      let v : wilsonHalfSpace μ τ :=
        ⟨(A.translate y).toL2 μ, (A.translate y).toL2_mem_halfSpace μ (by rw [hy, neg_add_cancel])⟩
      have hu' : u.val = R (T a (J.toL2 μ)) := by
        change ((J.translate a).reflect 0).toL2 μ = _
        rw [WilsonSlabObservable.toL2_reflect _ μ hμ, WilsonSlabObservable.toL2_translate _ μ hμ]
      have hv0 : v.val = T y (A.toL2 μ) := WilsonSlabObservable.toL2_translate A μ hμ y
      have hu : R u.val = T a (J.toL2 μ) := by
        rw [hu']
        exact wilsonReflectL2_involutive μ hμ τ 0 _
      have hv : T (n • step τ) v.val = T (x + a) (A.toL2 μ) := by
        rw [hv0, ← mul_apply_eq_comp, wilsonTranslateL2_mul]
        congr 2
        dsimp only [y]
        abel
      have h := hbound u v
      rw [hu, hv, hu', hv0, Rnorm, norm_wilsonTranslateL2_apply, norm_wilsonTranslateL2_apply] at h
      rw [translated_projected_inner μ hμ τ a x, wilsonProjection_complement_inner μ hμ τ]
      simpa only [C, mul_comm ‖J.toL2 μ‖ ‖A.toL2 μ‖] using h
    · have hx' : x τ ≤ 0 := le_of_not_ge hx
      let a : Site := n • step τ
      let y : Site := x + a
      have ha : a τ = (n : ℤ) := by simp [a, step_same]
      have hy : y τ = -(b : ℤ) - 2 := by
        change x τ + a τ = _
        rw [ha, hn, abs_of_nonpos hx']
        ring
      let u : wilsonHalfSpace μ τ :=
        ⟨((A.translate y).reflect 0).toL2 μ,
          ((A.translate y).reflect 0).toL2_mem_halfSpace μ (by rw [hy]; omega)⟩
      let v : wilsonHalfSpace μ τ := ⟨J.toL2 μ, J.toL2_mem_halfSpace μ le_rfl⟩
      have hu' : u.val = R (T y (A.toL2 μ)) := by
        change ((A.translate y).reflect 0).toL2 μ = _
        rw [WilsonSlabObservable.toL2_reflect _ μ hμ, WilsonSlabObservable.toL2_translate _ μ hμ]
      have hu : R u.val = T y (A.toL2 μ) := by
        rw [hu']
        exact wilsonReflectL2_involutive μ hμ τ 0 _
      have h := hbound u v
      rw [hu, hu', Rnorm, norm_wilsonTranslateL2_apply] at h
      change |⟪T y (A.toL2 μ), Q (T a (J.toL2 μ))⟫_ℝ| ≤ C * r ^ n at h
      rw [translated_projected_inner μ hμ τ a x, real_inner_comm]
      exact h
  · have hn : n = 0 := by dsimp only [n]; omega
    rw [hn, pow_zero, mul_one]
    calc
      _ ≤ ‖Q (J.toL2 μ)‖ * ‖T x (A.toL2 μ)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖J.toL2 μ‖ * ‖A.toL2 μ‖ := by
        rw [norm_wilsonTranslateL2_apply]
        exact mul_le_mul_of_nonneg_right (wilsonProjection_complement_norm_le μ hμ τ _) (norm_nonneg _)
      _ = C := mul_comm _ _

end

end GaplessYangMills

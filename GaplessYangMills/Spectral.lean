module

public import GaplessYangMills.Decay
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# The vacuum projection and the gapped remainder

This is the spectral estimate used in Section 5. A bounded positive transfer
operator with a gap has spectrum in `[0, r] ∪ {1}`. Functional calculus gives
a single projection onto all of the spectral subspace at 1.
-/

@[expose] public section

namespace GaplessYangMills

open scoped ContinuousFunctionalCalculus
open Filter
open scoped Topology

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
variable {p : A → Prop} [IsometricContinuousFunctionalCalculus ℝ A p]

/-- An isolated point at 1 can be removed from the powers of a transfer
operator, with operator-norm decay controlled by the rest of the spectrum.
The statement also covers the case where 1 is outside the spectrum. -/
theorem exists_vacuum_projection {T : A} (hT : p T) {r : ℝ} (hr₀ : 0 ≤ r)
    (hr₁ : r < 1) (hσ : spectrum ℝ T ⊆ Set.Icc 0 r ∪ {1}) :
    ∃ P : A, IsSelfAdjoint P ∧ P * P = P ∧ T * P = P ∧
      ∀ n : ℕ, ‖T ^ n - P‖ ≤ r ^ n := by
  let cutoff (t : ℝ) := max 0 ((t - r) / (1 - r))
  have hr : 0 < 1 - r := sub_pos.mpr hr₁
  have hc : Continuous cutoff :=
    continuous_const.max ((continuous_id.sub continuous_const).div_const _)
  have hc₀ {t : ℝ} (ht : t ≤ r) : cutoff t = 0 :=
    max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hr.le)
  have hc₁ : cutoff 1 = 1 := by simp [cutoff, hr.ne']
  refine ⟨cfc cutoff T, ?_, ?_, ?_, ?_⟩
  · change star (cfc cutoff T) = cfc cutoff T
    simpa using (cfc_star cutoff T).symm
  · rw [← cfc_mul cutoff cutoff T hc.continuousOn hc.continuousOn]
    apply cfc_congr
    intro t ht
    rcases hσ ht with ht | ht
    · simp [hc₀ ht.2]
    · have h : t = 1 := ht
      simp [h, hc₁]
  · calc
      T * cfc cutoff T = cfc (fun t => t * cutoff t) T := by
        rw [cfc_mul (fun t : ℝ => t) cutoff T continuous_id.continuousOn hc.continuousOn,
          cfc_id' ℝ T (ha := hT)]
      _ = cfc cutoff T := by
        apply cfc_congr
        intro t ht
        rcases hσ ht with ht | ht
        · simp [hc₀ ht.2]
        · have h : t = 1 := ht
          simp [h]
  · intro n
    have hcPow : Continuous (fun t : ℝ => t ^ n) := continuous_id.pow n
    rw [← cfc_pow_id T n (R := ℝ) (ha := hT),
      ← cfc_sub _ cutoff T hcPow.continuousOn hc.continuousOn]
    refine norm_cfc_le (pow_nonneg hr₀ n) fun t ht => ?_
    rcases hσ ht with ht | ht
    · rw [hc₀ ht.2, sub_zero, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1 n)]
      exact pow_le_pow_left₀ ht.1 ht.2 n
    · have h : t = 1 := ht
      simp [h, hc₁, pow_nonneg hr₀]

/-- The kernel obstruction forces spectral points near 1 when local correlation
estimates are controlled by powers of the transfer operator. The kernel is
the one with directional means removed, and the local bound is imposed for
the norm limit of the powers when that limit exists. Axis-equivalent transfer
operators can use the same norm bound.

The hypotheses on `K` and its local approximants are the conditions to
establish for the infinite-volume Wilson state in the application. -/
theorem spectrum_near_one_of_ward (T : A) (hT : p T)
    (hσ : spectrum ℝ T ⊆ Set.Icc 0 1) (β : ℝ) (K S : Kernel)
    (localApprox : ℕ → Kernel) (hclosed : ∀ J, d₂ (fun I => K I J) = 0)
    (hresponse : WardResponse β K S) (hS : ∀ I J, Summable (S I J))
    (hnormalize : ∑' x, S .xy .xy x = 0)
    (herror : ∀ I J, ∃ B c : ℝ, 0 ≤ B ∧ 0 < c ∧
      ∀ R x, |K I J x - localApprox R I J x| ≤ B * Real.exp (-c * R))
    (hlocal : ∀ P : A, Tendsto (fun n : ℕ => T ^ n) atTop (𝓝 P) →
      ∀ I J, ∃ (C : ℝ) (width : ℕ), 0 ≤ C ∧ ∀ R x,
        |localApprox R I J x| ≤ C * ‖T ^ (radius x - (3 * R + width)) - P‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t ∈ spectrum ℝ T, t ∈ Set.Ioo (Real.exp (-ε)) 1 := by
  by_contra hgap
  let r := Real.exp (-ε)
  have hr₀ : 0 ≤ r := Real.exp_nonneg _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hε)
  have hσ' : spectrum ℝ T ⊆ Set.Icc 0 r ∪ {1} := by
    intro t ht
    by_cases h : t = 1
    · exact Or.inr h
    · have ht₁ := lt_of_le_of_ne (hσ ht).2 h
      exact Or.inl ⟨(hσ ht).1, le_of_not_gt fun hrt => hgap ⟨t, ht, ⟨hrt, ht₁⟩⟩⟩
  obtain ⟨P, -, -, -, hP⟩ := exists_vacuum_projection hT hr₀ hr₁ hσ'
  have hlim : Tendsto (fun n : ℕ => T ^ n) atTop (𝓝 P) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [dist_eq_norm] using
      squeeze_zero (fun n => norm_nonneg (T ^ n - P)) hP
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁)
  apply no_exponential_clustering_of_ward β K S hclosed hresponse hS hnormalize
  intro I J
  obtain ⟨B, c, hB, hc, herr⟩ := herror I J
  obtain ⟨C, width, hC, hmatrix⟩ := hlocal P hlim I J
  apply exp_bound_of_local_approximants (K I J) (fun R => localApprox R I J)
    hC hB hc hε herr
  intro R x
  let n := radius x - (3 * R + width)
  have hn₁ : radius x ≤ n + (3 * R + width) := by dsimp [n]; omega
  have hn₂ : (radius x : ℝ) ≤ n + (3 * (R : ℝ) + (width : ℝ)) := by exact_mod_cast hn₁
  have hn : (radius x : ℝ) - (3 * R + width) ≤ n := by linarith
  calc
    |localApprox R I J x| ≤ C * ‖T ^ n - P‖ := hmatrix R x
    _ ≤ C * r ^ n := mul_le_mul_of_nonneg_left (hP n) hC
    _ = C * Real.exp (-ε * n) := by
      dsimp only [r]
      rw [← Real.exp_nat_mul, mul_comm (n : ℝ)]
    _ ≤ C * Real.exp (-ε * ((radius x : ℝ) - (3 * R + width))) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hn (neg_nonpos.mpr hε.le))) hC

end GaplessYangMills

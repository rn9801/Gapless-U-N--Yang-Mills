module

public import GaplessYangMills.WeakCoupling
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Scalar gain of a rank-one twist

The gain at an eigenvalue extends to its one-eighth neighbourhood, with the
choice of twist sign kept fixed.
-/

@[expose] public section

namespace GaplessYangMills

private theorem cos_gain (t : ℝ) (ht : Real.pi / 4 ≤ t) (ht' : t ≤ Real.pi) :
    badPenalty ≤ Real.cos (t - Real.pi / 4) - Real.cos t := by
  have hπ := Real.pi_pos
  have hs : Real.sin (Real.pi / 8) ≤ Real.sin (t - Real.pi / 8) := by
    by_cases h : t - Real.pi / 8 ≤ Real.pi / 2
    · exact Real.monotoneOn_sin ⟨by linarith, by linarith⟩ ⟨by linarith, h⟩ (by linarith)
    · rw [← Real.sin_pi_sub (t - Real.pi / 8)]
      exact Real.monotoneOn_sin ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩ (by linarith)
  have hsin : 0 ≤ Real.sin (Real.pi / 8) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have h₀ : 1 - Real.cos (Real.pi / 4) = 2 * Real.sin (Real.pi / 8) ^ 2 := by
    rw [show Real.pi / 4 = 2 * (Real.pi / 8) by ring, Real.cos_two_mul_eq_one_sub]
    ring
  unfold badPenalty
  rw [h₀, Real.cos_sub_cos]
  have ha : (t - Real.pi / 4 + t) / 2 = t - Real.pi / 8 := by ring
  have hb : (t - Real.pi / 4 - t) / 2 = -(Real.pi / 8) := by ring
  rw [ha, hb, Real.sin_neg]
  nlinarith [mul_nonneg hsin (sub_nonneg.mpr hs)]

private theorem twist_real_gain (s θ : ℝ) :
    (((Circle.exp s : ℂ) - 1) * (Circle.exp θ : ℂ)).re =
      Real.cos (s + θ) - Real.cos θ := by
  rw [sub_mul, one_mul, ← Circle.coe_mul, ← Circle.exp_add, Complex.sub_re,
    Circle.coe_exp, Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re]

/-- The same sign that gives the eigenvalue gain provides at least half of
that gain for an expectation value within one eighth of the eigenvalue. -/
theorem exists_cap_twist_gain (θ : ℝ) (hθ : Real.pi / 4 ≤ |θ|) (hπ : |θ| ≤ Real.pi)
    (z : ℂ) (hz : ‖z - (Circle.exp θ : ℂ)‖ ≤ 1 / 8) :
    ∃ s : ℝ, |s| = Real.pi / 4 ∧
      badPenalty / 2 ≤ (((Circle.exp s : ℂ) - 1) * z).re := by
  have hpos : 0 ≤ Real.pi / 4 := by positivity
  have hs (s : ℝ) (h : |s| = Real.pi / 4) : ‖(Circle.exp s : ℂ) - 1‖ ≤ 1 := by
    have hsq := Complex.norm_sub_one_sq_eq_of_norm_eq_one (Circle.norm_coe (Circle.exp s))
    have hre : (Circle.exp s : ℂ).re = Real.cos (Real.pi / 4) := by
      rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, ← Real.cos_abs s, h]
    rw [hre] at hsq
    have hc : 1 / 2 ≤ Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    nlinarith [norm_nonneg ((Circle.exp s : ℂ) - 1)]
  have hg : ∃ s : ℝ, |s| = Real.pi / 4 ∧
      badPenalty ≤ (((Circle.exp s : ℂ) - 1) * (Circle.exp θ : ℂ)).re := by
    by_cases h : 0 ≤ θ
    · rw [abs_of_nonneg h] at hθ hπ
      refine ⟨-(Real.pi / 4), by simp [abs_of_nonneg hpos], ?_⟩
      rw [twist_real_gain, neg_add_eq_sub]
      exact cos_gain θ hθ hπ
    · rw [abs_of_neg (lt_of_not_ge h)] at hθ hπ
      refine ⟨Real.pi / 4, abs_of_nonneg hpos, ?_⟩
      rw [twist_real_gain, ← Real.cos_neg θ, ← Real.cos_neg (Real.pi / 4 + θ)]
      simpa only [neg_add_rev, sub_eq_add_neg] using cos_gain (-θ) hθ hπ
  obtain ⟨s, hs', hg'⟩ := hg
  refine ⟨s, hs', ?_⟩
  have herror : ‖((Circle.exp s : ℂ) - 1) * (z - (Circle.exp θ : ℂ))‖ ≤ 1 / 8 := by
    rw [norm_mul]
    exact (mul_le_mul (hs s hs') hz (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hre := Complex.abs_re_le_norm (((Circle.exp s : ℂ) - 1) * (z - (Circle.exp θ : ℂ)))
  have hb := hre.trans herror
  rw [mul_sub, Complex.sub_re] at hb
  linarith [(abs_le.mp hb).1, badPenalty_lower]

end GaplessYangMills

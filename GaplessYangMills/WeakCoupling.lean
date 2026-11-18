module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Numerical estimates at weak coupling

The cap comparison and the exponential tail parameter use the same Wilson
normalization and constants as Sections 2 and 3 of the paper.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

def badPenalty : ℝ := 1 - Real.cos (Real.pi / 4)

theorem badPenalty_lower : (29 : ℝ) / 100 ≤ badPenalty := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have h : Real.sqrt 2 ≤ (71 : ℝ) / 50 := by
    by_contra! h
    nlinarith [sq_nonneg (Real.sqrt 2 - (71 : ℝ) / 50)]
  unfold badPenalty
  rw [Real.cos_pi_div_four]
  linarith

theorem cap_exponential_bound {β : ℝ} (hβ : 40 ≤ β) :
    16 ≤ Real.exp (β * badPenalty / 4) := by
  have hb : 0 ≤ badPenalty := by linarith [badPenalty_lower]
  have hbase : (29 : ℝ) / 10 ≤ β * badPenalty / 4 := by
    have h := mul_le_mul_of_nonneg_right hβ hb
    linarith [badPenalty_lower]
  apply le_trans _ (Real.exp_le_exp.mpr hbase)
  refine le_trans ?_ (Real.sum_le_exp_of_nonneg (x := (29 : ℝ) / 10) (by norm_num) 7)
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The cap probability and the one-quarter weight in the modified kernel
leave the exponential lower bound required in Lemma 2. -/
theorem cap_weight_lower_bound (N : ℕ) {β : ℝ} (hβ : 40 ≤ β) :
    Real.exp ((N : ℝ) * β * badPenalty / 4) ≤
      (4 / (16 : ℝ) ^ N) * Real.exp ((N : ℝ) * β * badPenalty / 2) := by
  let t : ℝ := (N : ℝ) * β * badPenalty / 4
  have hpow : (16 : ℝ) ^ N ≤ Real.exp t := by
    calc
      (16 : ℝ) ^ N ≤ Real.exp (β * badPenalty / 4) ^ N :=
        pow_le_pow_left₀ (by norm_num) (cap_exponential_bound hβ) N
      _ = Real.exp t := by rw [← Real.exp_nat_mul]; congr 1; unfold t; ring
  have hc : (1 : ℝ) ≤ 4 * Real.exp t / (16 : ℝ) ^ N := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [one_mul]
    linarith [Real.exp_pos t]
  calc
    Real.exp t = Real.exp t * 1 := (mul_one _).symm
    _ ≤ Real.exp t * (4 * Real.exp t / (16 : ℝ) ^ N) :=
      mul_le_mul_of_nonneg_left hc (Real.exp_nonneg t)
    _ = _ := by
      have hexp : Real.exp ((N : ℝ) * β * badPenalty / 2) = Real.exp t * Real.exp t := by
        rw [← Real.exp_add]
        congr 1
        unfold t
        ring
      rw [hexp]
      ring

def defectTailRate (N : ℕ) (β : ℝ) : ℝ :=
  (14 : ℝ) ^ 2 * Real.sqrt 6 * Real.exp (-(badPenalty * N * β / 192))

/-- The rate used for the cut-uniform (L^2) tail in equation (2) is less
than one for all positive ranks at the sufficient coupling of Theorem 1. -/
theorem defectTailRate_lt_one {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β) :
    defectTailRate N β < 1 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hβ' : 0 ≤ β := by linarith
  have hbase : (13 : ℝ) ≤ badPenalty * (N : ℝ) * β / 192 := by
    have hpositive : 0 ≤ badPenalty := by linarith [badPenalty_lower]
    have hfirst := mul_le_mul_of_nonneg_left hN' hpositive
    have hsecond := mul_le_mul_of_nonneg_right hfirst hβ'
    have hthird := mul_le_mul_of_nonneg_right (show (1 : ℝ) / 4 ≤ badPenalty by
      linarith [badPenalty_lower]) hβ'
    linarith
  have hs : Real.sqrt 6 ≤ 3 := by
    have he := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    have hn := Real.sqrt_nonneg (6 : ℝ)
    by_contra! h
    nlinarith [sq_nonneg (Real.sqrt 6 - 3)]
  have hexp : (14 : ℝ) ^ 2 * Real.sqrt 6 < Real.exp 13 := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (13 : ℝ)) (by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at hsum ⊢
    linarith
  unfold defectTailRate
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
  exact hexp.trans_le (Real.exp_le_exp.mpr hbase)

end

end GaplessYangMills

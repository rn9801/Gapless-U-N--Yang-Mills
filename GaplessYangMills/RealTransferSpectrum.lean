module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Spectral estimates for real self-adjoint transfers

An irreducible real polynomial is linear or quadratic. A quadratic
without real roots, after completing the square, is invertible at a
self-adjoint operator by coercivity. This gives polynomial spectral
mapping over the real field and the norm convergence of gapped powers.
-/

@[expose] public section

namespace GaplessYangMills

open Filter Polynomial
open scoped ENNReal InnerProductSpace Polynomial Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem isUnit_sq_add_scalar (A : H →L[ℝ] H) (hA : IsSelfAdjoint A) {d : ℝ} (hd : 0 < d) :
    IsUnit (A ^ 2 + algebraMap ℝ (H →L[ℝ] H) d) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c := ⟨d, hd.le⟩) hd
  intro x
  simp only [add_apply, pow_two A, mul_apply_eq_comp, ContinuousLinearMap.algebraMap_apply, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, Real.norm_eq_abs]
  change ‖x‖ ^ 2 * d ≤ |⟪A (A x), x⟫_ℝ + d * ‖x‖ ^ 2|
  have he : ⟪A (A x), x⟫_ℝ = ⟪A x, A x⟫_ℝ := hA.isSymmetric (A x) x
  rw [he, real_inner_self_eq_norm_sq, mul_comm (‖x‖ ^ 2) d]
  exact (le_add_of_nonneg_left (by positivity : 0 ≤ ‖A x‖ ^ 2)).trans (le_abs_self _)

private theorem isUnit_aeval_irreducible (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (p : ℝ[X]) (hp : Irreducible p) (h : ∀ t ∈ spectrum ℝ T, eval t p ≠ 0) :
    IsUnit (aeval T p) := by
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  have hq : p = C a * X ^ 2 + C b * X + C c := eq_quadratic_of_degree_le_two hp.degree_le_two
  by_cases ha : a = 0
  · have hp₁ : p = C b * X + C c := by rw [hq, ha]; simp
    by_cases hb : b = 0
    · have hc : c ≠ 0 := by
        intro hc
        exact hp.ne_zero (by rw [hp₁, hb, hc]; simp)
      rw [hp₁, hb]
      simp only [map_zero, zero_mul, zero_add, aeval_C]
      exact (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ (H →L[ℝ] H))
    · let t := -c / b
      have hbt : -(b * t) = c := by dsimp [t]; field_simp
      have he : p = C b * (X - C t) := by
        rw [hp₁, ← hbt, map_neg, map_mul]
        ring
      have hnot : t ∉ spectrum ℝ T := fun ht => h t ht (by simp [he])
      have hu : IsUnit (T - algebraMap ℝ (H →L[ℝ] H) t) :=
        IsUnit.sub_iff.mp (spectrum.notMem_iff.mp hnot)
      rw [he, map_mul, map_sub, aeval_X, aeval_C, aeval_C]
      exact ((isUnit_iff_ne_zero.mpr hb).map (algebraMap ℝ (H →L[ℝ] H))).mul hu
  · let u := b / (2 * a)
    let d := c / a - u ^ 2
    have hb : 2 * a * u = b := by dsimp [u]; field_simp
    have hc : a * (u ^ 2 + d) = c := by dsimp [d]; field_simp; ring
    have he : p = C a * ((X + C u) ^ 2 + C d) := by
      rw [hq, ← hb, ← hc, map_mul, map_mul, map_mul, map_add, map_pow, map_ofNat]
      ring
    have hd : 0 < d := by
      by_contra! hd
      have hdeg : p.natDegree ≠ 1 := fun he => ha (coeff_eq_zero_of_natDegree_lt (by rw [he]; decide))
      apply hp.not_isRoot_of_natDegree_ne_one hdeg (x := -u + Real.sqrt (-d))
      rw [IsRoot, he]
      simp only [eval_mul, eval_C, eval_add, eval_pow, eval_X]
      rw [show -u + Real.sqrt (-d) + u = Real.sqrt (-d) by ring, Real.sq_sqrt (by linarith)]
      ring
    have hU : IsSelfAdjoint (T + algebraMap ℝ (H →L[ℝ] H) u) := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact hT.add ((show IsSelfAdjoint u from star_trivial u).smul
        (show IsSelfAdjoint (1 : H →L[ℝ] H) from star_one (H →L[ℝ] H)))
    rw [he, map_mul, map_add, map_pow, map_add, aeval_X, aeval_C, aeval_C, aeval_C]
    exact ((isUnit_iff_ne_zero.mpr ha).map (algebraMap ℝ (H →L[ℝ] H))).mul
      (isUnit_sq_add_scalar _ hU hd)

private theorem isUnit_aeval_of_no_spectral_root (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (p : ℝ[X]) (hp : p ≠ 0) (h : ∀ t ∈ spectrum ℝ T, eval t p ≠ 0) :
    IsUnit (aeval T p) := by
  revert hp h
  refine WfDvdMonoid.induction_on_irreducible p ?_ ?_ ?_
  · exact fun hp => (hp rfl).elim
  · intro p hp _ _
    exact hp.map (aeval T)
  · intro q p hq hp ih _ h
    rw [map_mul]
    exact (isUnit_aeval_irreducible T hT p hp fun t ht hz => h t ht (by rw [eval_mul, hz, zero_mul])).mul
      (ih hq fun t ht hz => h t ht (by rw [eval_mul, hz, mul_zero]))

private theorem real_spectrum_nonempty [Nontrivial H] (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) :
    (spectrum ℝ T).Nonempty := by
  by_cases h : T = 0
  · subst T
    exact ⟨0, spectrum.zero_mem ℝ not_isUnit_zero⟩
  · by_contra! he
    have hzero : spectralRadius ℝ T = 0 := by
      rw [spectralRadius_eq_of_unital]
      simp [he]
    exact h (by
      have hz : (‖T‖₊ : ℝ≥0∞) = 0 := (T.spectralRadius_eq_nnNorm hT).symm.trans hzero
      exact nnNorm_eq_zero.mp (ENNReal.coe_eq_zero.mp hz))

theorem realSelfAdjoint_spectrum_aeval_subset (T : H →L[ℝ] H) [Nontrivial H] (hT : IsSelfAdjoint T)
    (p : ℝ[X]) : spectrum ℝ (aeval T p) ⊆ (fun t => eval t p) '' spectrum ℝ T := by
  intro s hs
  by_contra h
  have hn (t : ℝ) (ht : t ∈ spectrum ℝ T) : eval t (p - C s) ≠ 0 := by
    intro he
    rw [eval_sub, eval_C] at he
    exact h ⟨t, ht, sub_eq_zero.mp he⟩
  obtain ⟨t, ht⟩ := real_spectrum_nonempty T hT
  have hp : p - C s ≠ 0 := fun hp => hn t ht (by rw [hp, eval_zero])
  have hu := isUnit_aeval_of_no_spectral_root T hT (p - C s) hp hn
  rw [map_sub, aeval_C] at hu
  exact hs (IsUnit.sub_iff.mp hu)

private theorem isSelfAdjoint_aeval (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) (p : ℝ[X]) :
    IsSelfAdjoint (aeval T p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n a =>
    rw [aeval_monomial, ← Algebra.smul_def]
    exact (show IsSelfAdjoint a from star_trivial a).smul (hT.pow n)

theorem norm_realSelfAdjoint_aeval_le (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (p : ℝ[X]) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ t ∈ spectrum ℝ T, |eval t p| ≤ C) :
    ‖aeval T p‖ ≤ C := by
  by_cases h : Subsingleton H
  · have hz : aeval T p = 0 := Subsingleton.elim _ _
    simpa only [hz, norm_zero] using hC
  let : Nontrivial H := not_subsingleton_iff_nontrivial.mp h
  have h := (aeval T p).spectralRadius_eq_nnNorm (isSelfAdjoint_aeval T hT p)
  have hR : spectralRadius ℝ (aeval T p) ≤ ENNReal.ofReal C := by
    rw [spectralRadius_eq_of_unital]
    apply iSup₂_le
    intro t ht
    obtain ⟨u, hu, rfl⟩ := realSelfAdjoint_spectrum_aeval_subset T hT p ht
    change ‖eval u p‖ₑ ≤ ENNReal.ofReal C
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hbound u hu)
  rw [h] at hR
  change ‖aeval T p‖ₑ ≤ ENNReal.ofReal C at hR
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hC] at hR
  exact hR

theorem realPositiveContraction_spectrum_subset (T : H →L[ℝ] H)
    (hT : T.IsPositive) (hNorm : ‖T‖ ≤ 1) : spectrum ℝ T ⊆ Set.Icc 0 1 := by
  intro t ht
  have h₀ : 0 ≤ t := SpectrumRestricts.nnreal_iff.mp hT.spectrumRestricts t ht
  have h₁ : ‖t‖ ≤ ‖T‖ * ‖(1 : H →L[ℝ] H)‖ :=
    spectrum.norm_le_norm_mul_of_mem (a := T) (k := t) ht
  have hi : ‖(1 : H →L[ℝ] H)‖ ≤ (1 : ℝ) := ContinuousLinearMap.norm_id_le
  have hi₀ : 0 ≤ ‖(1 : H →L[ℝ] H)‖ := norm_nonneg (1 : H →L[ℝ] H)
  exact ⟨h₀, (Real.le_norm_self _).trans (h₁.trans
    ((mul_le_mul hNorm hi hi₀ zero_le_one).trans_eq (one_mul 1)))⟩

/-- The powers converge in operator norm under a gap in the real spectrum.
The limit removes the entire vacuum component with the stated norm error. -/
theorem exists_realTransfer_power_limit (T : H →L[ℝ] H) (hT : IsSelfAdjoint T) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hσ : spectrum ℝ T ⊆ Set.Icc 0 r ∪ {1}) :
    ∃ P : H →L[ℝ] H, Tendsto (fun n : ℕ => T ^ n) atTop (𝓝 P) ∧ ∀ n : ℕ, ‖T ^ n - P‖ ≤ r ^ n := by
  have hdiff (n k : ℕ) : ‖T ^ n - T ^ (n + k)‖ ≤ r ^ n := by
    have h := norm_realSelfAdjoint_aeval_le T hT (X ^ n - X ^ (n + k)) (pow_nonneg hr₀ _) (fun t ht => by
      simp only [eval_sub, eval_pow, eval_X]
      rcases hσ ht with h | h
      · have h₁ := pow_le_one₀ h.1 (h.2.trans hr₁.le) (n := k)
        have hp : 0 ≤ t ^ n - t ^ (n + k) := by
          rw [pow_add]
          exact sub_nonneg.mpr (mul_le_of_le_one_right (pow_nonneg h.1 _) h₁)
        rw [abs_of_nonneg hp]
        exact (sub_le_self _ (pow_nonneg h.1 _)).trans (pow_le_pow_left₀ h.1 h.2 _)
      · have ht : t = 1 := h
        simp only [ht, one_pow, sub_self, abs_zero]
        exact pow_nonneg hr₀ _)
    simpa only [map_sub, map_pow, aeval_X] using h
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁
  have hc : CauchySeq (fun n : ℕ => T ^ n) := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
    obtain ⟨n, hn⟩ := (hpow.eventually (gt_mem_nhds hε)).exists
    refine ⟨n, fun k hk => ?_⟩
    rw [dist_comm, dist_eq_norm, show k = n + (k - n) by omega]
    exact (hdiff n (k - n)).trans_lt hn
  obtain ⟨P, hP⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨P, hP, fun n => ?_⟩
  apply le_of_tendsto (tendsto_const_nhds.sub hP).norm
  filter_upwards [eventually_ge_atTop n] with k hk
  simpa only [Nat.add_sub_of_le hk] using hdiff n (k - n)

end

end GaplessYangMills

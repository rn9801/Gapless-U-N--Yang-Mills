module

public import GaplessYangMills.RealTransferSpectrum
public import GaplessYangMills.WilsonAxisTransfer
public import GaplessYangMills.WilsonProjectedDecay

/-!
# Weak-coupling gaplessness of the Wilson U(N) transfer

The projected Ward identity makes the covariance nonsummable. A gap
would yield transfer decay in every direction, and the local flux
approximation would then make the same covariance summable.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology

noncomputable section

def wilsonFluxApproxL2 {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) (R : ℕ) (I : Face) : WilsonL2 μ :=
  (wilsonFluxApproxObservable N 0 R I).toL2 μ

private theorem wilsonFluxApprox_bound {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (I : Face) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R, ‖wilsonFluxApproxL2 μ R I‖ ≤ M := by
  obtain ⟨M, hM⟩ := ((iidAveragedFlux_exponential_approximation_periodicLimit hN hβ μ l hl hμ).2 I 0).2
  refine ⟨max M 0, le_max_right _ _, fun R => ?_⟩
  have hs : ‖wilsonFluxApproxL2 μ R I‖ =
      (eLpNorm (fun U => averagedFluxApprox iidCutLaw R U I 0) 2 μ.toMeasure).toReal :=
    Lp.norm_toLp _ ((wilsonFluxApproxObservable N 0 R I).memLp μ)
  rw [hs]
  have h := (hM R).trans (ENNReal.ofReal_le_ofReal (le_max_left M 0))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal (le_max_right _ _))

private theorem wilsonFluxApprox_error {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ I R,
      ‖wilsonFluxL2 hN hβ μ l hl hμ I 0 - wilsonFluxApproxL2 μ R I‖ ≤ C * Real.exp (-c * R) := by
  obtain ⟨C, hC, t, ht₀, ht₁, hE⟩ :=
    (iidAveragedFlux_exponential_approximation_periodicLimit hN hβ μ l hl hμ).1
  let s := max t (1 / 2)
  have hs : 0 < s := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_right _ _)
  have hs₁ : s < 1 := max_lt ht₁ (by norm_num)
  refine ⟨C, -Real.log s, hC.le, neg_pos.mpr (Real.log_neg hs hs₁), fun I R => ?_⟩
  change ‖(memLp_iidAveragedFlux hN hβ μ l hl hμ I 0).toLp _ -
    ((wilsonFluxApproxObservable N 0 R I).memLp μ).toLp _‖ ≤ _
  rw [← MemLp.toLp_sub, Lp.norm_toLp]
  have h := (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hE I 0 R)).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg hC.le (pow_nonneg ht₀ _)))
  refine h.trans ?_
  simp only [neg_neg]
  rw [mul_comm (Real.log s), Real.exp_nat_mul, Real.exp_log hs]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht₀ (le_max_left _ _) _) hC.le

private theorem projectedWilsonCovariance_eq_correlation {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (I J : Face) (x : Site) :
    projectedWilsonCovariance hN hβ μ l hl hμ I J x =
      wilsonProjectedL2Correlation μ hμ (wilsonCurrentL2 μ (J, 0)) (wilsonFluxL2 hN hβ μ l hl hμ I 0) x := by
  unfold wilsonProjectedL2Correlation
  rw [wilsonTranslateL2_flux hN hβ μ l hl hμ, zero_add]
  rfl

def projectedWilsonLocalCovariance {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (R : ℕ) (I J : Face) (x : Site) : ℝ :=
  wilsonProjectedL2Correlation μ hμ (wilsonCurrentL2 μ (J, 0)) (wilsonFluxApproxL2 μ R I) x

private theorem projectedWilsonLocalCovariance_error {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (I J : Face) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ R x,
      |projectedWilsonCovariance hN hβ μ l hl hμ I J x - projectedWilsonLocalCovariance μ hμ R I J x| ≤
        C * Real.exp (-c * R) := by
  obtain ⟨C, c, hC, hc, hE⟩ := wilsonFluxApprox_error hN hβ μ l hl hμ
  let j := wilsonCurrentL2 μ (J, 0)
  let P := removeWilsonDirections μ hμ [0, 1, 2, 3]
  have hP : ‖P j‖ ≤ ‖j‖ := by
    simpa only [one_mul] using P.le_of_opNorm_le (removeWilsonDirections_norm_le_one μ hμ _) j
  refine ⟨‖j‖ * C, c, mul_nonneg (norm_nonneg _) hC, hc, fun R x => ?_⟩
  rw [projectedWilsonCovariance_eq_correlation hN hβ μ l hl hμ, projectedWilsonLocalCovariance]
  let E := wilsonFluxL2 hN hβ μ l hl hμ I 0 - wilsonFluxApproxL2 μ R I
  unfold wilsonProjectedL2Correlation
  rw [← inner_sub_right, ← map_sub]
  calc
    _ ≤ ‖P j‖ * ‖wilsonTranslateL2 μ hμ x E‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖j‖ * (C * Real.exp (-c * R)) := by
      rw [norm_wilsonTranslateL2_apply]
      exact mul_le_mul hP (hE I R) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

set_option maxHeartbeats 800000 in
theorem wilsonTransfer_spectrum_subset {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (τ : Axis) :
    spectrum ℝ (wilsonTransfer hβ μ hl hμ τ) ⊆ Set.Icc 0 1 := by
  let T := wilsonTransfer hβ μ hl hμ τ
  intro t ht
  have h₀ : 0 ≤ t :=
    SpectrumRestricts.nnreal_iff.mp (wilsonTransfer_positive hβ μ hl hμ τ).spectrumRestricts t ht
  have h₁ : ‖t‖ ≤ ‖T‖ * ‖(1 : (wilsonOSForm μ hl hμ τ).Hilbert →L[ℝ] (wilsonOSForm μ hl hμ τ).Hilbert)‖ :=
    spectrum.norm_le_norm_mul_of_mem (a := T) (k := t) ht
  have hT : ‖T‖ ≤ (1 : ℝ) := wilsonTransfer_norm_le_one hβ μ hl hμ τ
  have hi : ‖(1 : (wilsonOSForm μ hl hμ τ).Hilbert →L[ℝ] (wilsonOSForm μ hl hμ τ).Hilbert)‖ ≤ (1 : ℝ) :=
    ContinuousLinearMap.norm_id_le
  have hi₀ : 0 ≤ ‖(1 : (wilsonOSForm μ hl hμ τ).Hilbert →L[ℝ] (wilsonOSForm μ hl hμ τ).Hilbert)‖ :=
    norm_nonneg (1 : (wilsonOSForm μ hl hμ τ).Hilbert →L[ℝ] (wilsonOSForm μ hl hμ τ).Hilbert)
  refine ⟨h₀, (Real.le_norm_self _).trans (h₁.trans ?_)⟩
  exact (mul_le_mul hT hi hi₀ zero_le_one).trans_eq (one_mul 1)

set_option maxHeartbeats 1000000 in
private theorem projectedWilsonLocalCovariance_gap_decay {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (I J : Face)
    (ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ τ : Axis, spectrum ℝ (wilsonTransfer (by linarith) μ hl hμ τ) ⊆ Set.Icc 0 (Real.exp (-ε)) ∪ {1}) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R x, |projectedWilsonLocalCovariance μ hμ R I J x| ≤
      A * Real.exp (-ε * ((radius x : ℝ) - (4 * R + 6))) := by
  let r := Real.exp (-ε)
  have hr₀ : 0 ≤ r := Real.exp_nonneg _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hε)
  have hβ₀ : 0 ≤ β := by linarith
  obtain ⟨M, hM, hnorm⟩ := wilsonFluxApprox_bound hN hβ μ l hl hμ I
  let j := wilsonCurrentL2 μ (J, 0)
  refine ⟨8 * (M * ‖j‖), by positivity, fun R x => ?_⟩
  obtain ⟨τ, _, hτ⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset Axis)
    Finset.univ_nonempty (fun i => (x i).natAbs)
  let A := wilsonFluxApproxObservable N τ R I
  let J₀ := wilsonCurrentObservable μ τ J
  let b := 4 * R + 4
  let T := wilsonTransfer hβ₀ μ hl hμ τ
  obtain ⟨P, hP, hPow⟩ := exists_realTransfer_power_limit T
    (wilsonTransfer_positive hβ₀ μ hl hμ τ).isSelfAdjoint hr₀ hr₁ (hgap τ)
  let D (y : Site) := ‖A.toL2 μ‖ * ‖J₀.toL2 μ‖ * r ^ ((y τ).natAbs - (b + 2))
  have hline (i : Axis) (hi : i ≠ τ) (y : Site) (k : ℕ) : D (y + k • step i) = D y := by
    simp [D, Pi.add_apply, step, hi]
  have hdir := wilsonLocalCovariance_directional_decay hβ₀ μ hl hμ τ P hP r hPow b A J₀
  have hlocal := wilsonProjectedL2Correlation_bound_transverse μ hμ τ (J₀.toL2 μ) (A.toL2 μ) D hline hdir x
  let n := radius x - (b + 2)
  have he : D x = ‖wilsonFluxApproxL2 μ R I‖ * ‖j‖ * r ^ n := by
    change ‖wilsonFluxApproxL2 μ R I‖ * ‖j‖ * r ^ ((x τ).natAbs - (b + 2)) = _
    rw [← hτ]
    rfl
  have htNat : radius x ≤ n + (b + 2) := by dsimp only [n]; omega
  have htReal : (radius x : ℝ) ≤ n + (4 * (R : ℝ) + 6) := by
    dsimp only [b] at htNat
    exact_mod_cast htNat
  have hExp : r ^ n ≤ Real.exp (-ε * ((radius x : ℝ) - (4 * R + 6))) := by
    dsimp only [r]
    rw [← Real.exp_nat_mul, mul_comm (n : ℝ)]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr hε.le)
  calc
    _ ≤ 8 * D x := hlocal
    _ = 8 * (‖wilsonFluxApproxL2 μ R I‖ * ‖j‖) * r ^ n := by rw [he]; ring
    _ ≤ 8 * (M * ‖j‖) * Real.exp (-ε * ((radius x : ℝ) - (4 * R + 6))) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hnorm R) (norm_nonneg _)) (by norm_num))
        hExp (pow_nonneg hr₀ _) (by positivity)

set_option maxHeartbeats 1000000 in
/-- Theorem 1. Every periodic weak Wilson limit at the stated coupling
has transfer spectrum arbitrarily close to one from below, in every
coordinate direction. -/
theorem wilson_transfer_gapless {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (ε : ℝ) (hε : 0 < ε) :
    ∃ t ∈ spectrum ℝ (wilsonTransfer (by linarith) μ hl hμ τ), t ∈ Set.Ioo (Real.exp (-ε)) 1 := by
  let hβ₀ : 0 ≤ β := by linarith
  by_contra hn
  have hσ (i : Axis) : spectrum ℝ (wilsonTransfer hβ₀ μ hl hμ i) =
      spectrum ℝ (wilsonTransfer hβ₀ μ hl hμ τ) := by
    have he : (Equiv.swap τ i) τ = i := Equiv.swap_apply_left τ i
    have h := wilsonTransfer_spectrum_permute hβ₀ μ hl hμ (Equiv.swap τ i) τ
    rw [he] at h
    exact h
  have hgap (i : Axis) : spectrum ℝ (wilsonTransfer hβ₀ μ hl hμ i) ⊆ Set.Icc 0 (Real.exp (-ε)) ∪ {1} := by
    intro t ht
    have h := wilsonTransfer_spectrum_subset hβ₀ μ hl hμ i ht
    by_cases he : t = 1
    · exact Or.inr he
    · have ht₁ : t < 1 := lt_of_le_of_ne h.2 he
      exact Or.inl ⟨h.1, le_of_not_gt (fun hr => hn ⟨t, hσ i ▸ ht, hr, ht₁⟩)⟩
  apply projectedWilsonCovariance_not_summable hN hβ μ l hl hμ
  intro I J
  obtain ⟨C, c, hC, hc, hErr⟩ := projectedWilsonLocalCovariance_error hN hβ μ l hl hμ I J
  obtain ⟨A, hA, hD⟩ := projectedWilsonLocalCovariance_gap_decay hN hβ μ l hl hμ I J ε hε hgap
  obtain ⟨M, m, hm, hb⟩ := exp_bound_of_local_approximants_linear _ _ hA hC hc hε
    (slope := 4) (by norm_num) hErr hD
  exact summable_of_exp_bound _ hm hb

theorem wilson_transfer_positive_energies {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (ε : ℝ) (hε : 0 < ε) :
    ∃ t ∈ spectrum ℝ (wilsonTransfer (by linarith) μ hl hμ τ),
      0 < t ∧ -Real.log t ∈ Set.Ioo 0 ε := by
  obtain ⟨t, ht, hlo, hhi⟩ := wilson_transfer_gapless hN hβ μ l hl hμ τ ε hε
  have hp : 0 < t := (Real.exp_pos _).trans hlo
  refine ⟨t, ht, hp, neg_pos.mpr (Real.log_neg hp hhi), ?_⟩
  have h := Real.log_lt_log (Real.exp_pos _) hlo
  rw [Real.log_exp] at h
  linarith

end

end GaplessYangMills

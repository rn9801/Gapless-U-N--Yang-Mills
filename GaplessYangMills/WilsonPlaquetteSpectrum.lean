module

public import GaplessYangMills.CyclicTransfer
public import GaplessYangMills.WilsonGapless
public import GaplessYangMills.WilsonPlaquetteVectors

/-!
# Low-energy spectral support of a local Wilson plaquette

Decay on a single plaquette vector suffices to bound its correlations
with the local flux approximants. If all six plaquettes had gaps on
their cyclic subspaces, axis symmetry would give those bounds in
every direction and contradict the projected Ward identity.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped InnerProductSpace Topology

noncomputable section

private theorem power_decay_isometry {H K : Type*} [NormedAddCommGroup H] [NormedAddCommGroup K]
    [NormedSpace ℝ H] [NormedSpace ℝ K] (I : H ≃ₗᵢ[ℝ] K) (S : H →L[ℝ] H) (T : K →L[ℝ] K)
    (u w : H) (v : K) (s M r : ℝ) (hs : |s| = 1) (hI : I u = s • v)
    (hPow : ∀ n : ℕ, I ((S ^ n) u) = (T ^ n) (I u))
    (hw : Tendsto (fun n : ℕ => (S ^ n) u) atTop (𝓝 w))
    (hb : ∀ n : ℕ, ‖(S ^ n) u - w‖ ≤ M * r ^ n) :
    Tendsto (fun n : ℕ => (T ^ n) v) atTop (𝓝 (s • I w)) ∧
      ∀ n : ℕ, ‖(T ^ n) v - s • I w‖ ≤ M * r ^ n := by
  have hs₂ : s ^ 2 = 1 := by rw [← sq_abs, hs, one_pow]
  have he (n : ℕ) : (T ^ n) v = s • I ((S ^ n) u) := by
    rw [hPow n, hI, map_smul, smul_smul, ← pow_two, hs₂, one_smul]
  refine ⟨?_, fun n => ?_⟩
  · simp only [he]
    exact (I.continuous.const_smul s).continuousAt.tendsto.comp hw
  · rw [he, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, hs, one_mul, I.norm_map]
    exact hb n

private theorem power_decay_signed_shift {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : H →L[ℝ] H) (hT : ‖T‖ ≤ 1) (u w : H) (s M r : ℝ) (hs : |s| = 1) (k : ℕ)
    (hw : Tendsto (fun n : ℕ => (T ^ n) u) atTop (𝓝 w))
    (hb : ∀ n : ℕ, ‖(T ^ n) u - w‖ ≤ M * r ^ n) :
    Tendsto (fun n : ℕ => (T ^ n) (s • (T ^ k) u)) atTop (𝓝 (s • (T ^ k) w)) ∧
      ∀ n : ℕ, ‖(T ^ n) (s • (T ^ k) u) - s • (T ^ k) w‖ ≤ M * r ^ n := by
  have he (n : ℕ) : (T ^ n) (s • (T ^ k) u) = s • (T ^ k) ((T ^ n) u) := by
    rw [map_smul]
    congr 1
    exact congrArg (fun A : H →L[ℝ] H => A u) (Commute.pow_pow_self T n k).eq
  refine ⟨?_, fun n => ?_⟩
  · simp only [he]
    exact ((T ^ k).continuous.const_smul s).continuousAt.tendsto.comp hw
  · have hk : ‖T ^ k‖ ≤ 1 := by
      cases k with
      | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using
          (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := H))
      | succ k =>
        exact (norm_pow_le' T (Nat.succ_pos k)).trans (pow_le_one₀ (norm_nonneg T) hT)
    rw [he, ← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs, hs, one_mul]
    exact ((T ^ k).le_of_opNorm_le hk _).trans (by rw [one_mul]; exact hb n)

def WilsonCurrentPowerDecay {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (J : Face) (r : ℝ) : Prop :=
  ∃ w : (wilsonOSForm μ hl hμ τ).Hilbert,
    Tendsto (fun n : ℕ => (wilsonTransfer hβ μ hl hμ τ ^ n) (wilsonCurrentOSVector μ hl hμ τ J)) atTop (𝓝 w) ∧
    ∀ n : ℕ, ‖(wilsonTransfer hβ μ hl hμ τ ^ n) (wilsonCurrentOSVector μ hl hμ τ J) - w‖ ≤
      ‖wilsonCurrentL2 μ (J, 0)‖ * r ^ n

set_option maxHeartbeats 800000 in
private theorem wilsonCurrentPowerDecay_permute {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (σ : Equiv.Perm Axis) (τ : Axis) (J : Face) (r : ℝ)
    (h : WilsonCurrentPowerDecay hβ μ hl hμ τ J r) :
    WilsonCurrentPowerDecay hβ μ hl hμ (σ τ) (permuteFace σ J) r := by
  obtain ⟨w, hw, hb⟩ := h
  let I := wilsonTransferAxisIsometry μ hl hμ σ τ
  let S := wilsonTransfer hβ μ hl hμ τ
  let T := wilsonTransfer hβ μ hl hμ (σ τ)
  let u := wilsonCurrentOSVector μ hl hμ τ J
  let v := wilsonCurrentOSVector μ hl hμ (σ τ) (permuteFace σ J)
  let s := plaquettePermutationSign σ J
  have hs : |s| = 1 := abs_plaquettePermutationSign σ J
  have hI : I u = s • v := wilsonCurrentOSVector_permute μ hl hμ σ τ J
  have hPow (n : ℕ) : I ((S ^ n) u) = (T ^ n) (I u) :=
    wilsonTransferAxisIsometry_pow hβ μ hl hμ σ τ u n
  obtain ⟨ht, ha⟩ := power_decay_isometry I S T u w v s ‖wilsonCurrentL2 μ (J, 0)‖ r hs hI hPow hw hb
  refine ⟨s • I w, ht, fun n => (ha n).trans_eq ?_⟩
  exact congrArg (fun M : ℝ => M * r ^ n) (norm_wilsonCurrentL2_permute μ hμ σ J)

set_option maxHeartbeats 900000 in
private theorem wilsonCurrent_matrixElement_decay {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N)) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (J : Face) (r : ℝ) (h : WilsonCurrentPowerDecay hβ μ hl hμ τ J r)
    (n : ℕ) (u v : wilsonHalfSpace μ τ)
    (huv : u.val = wilsonReflectL2 μ hμ τ 0
        (wilsonTranslateL2 μ hμ ((-2 : ℤ) • step τ) (wilsonCurrentL2 μ (J, 0))) ∨
      v.val = wilsonCurrentL2 μ (J, 0)) :
    |⟪wilsonReflectL2 μ hμ τ 0 u.val, (1 - wilsonDirectionalProjection μ hμ τ)
      (wilsonTranslateL2 μ hμ (n • step τ) v.val)⟫_ℝ| ≤ ‖u.val‖ * ‖v.val‖ * r ^ n := by
  obtain ⟨w, hw, hb⟩ := h
  let B := wilsonOSForm μ hl hμ τ
  let T := wilsonTransfer hβ μ hl hμ τ
  let j := wilsonCurrentOSVector μ hl hμ τ J
  let s := plaquetteReflectionSign τ J
  let k := reflectedCurrentTime τ J
  rcases huv with hu | hv
  · have hu' : B.ofVector u = s • (T ^ k) j := wilsonCurrentOSVector_reflect hβ μ hl hμ τ J u hu
    let a := (-2 : ℤ) • step τ
    let j₂ := wilsonCurrentL2 μ (J, 0)
    have hnorm : ‖u.val‖ = ‖j₂‖ := calc
      _ = ‖wilsonReflectL2 μ hμ τ 0 (wilsonTranslateL2 μ hμ a j₂)‖ := congrArg norm hu
      _ = ‖wilsonTranslateL2 μ hμ a j₂‖ := (wilsonReflectL2Isometry μ hμ τ 0).norm_map _
      _ = _ := norm_wilsonTranslateL2_apply μ hμ a j₂
    obtain ⟨ht', ha'⟩ := power_decay_signed_shift T (wilsonTransfer_norm_le_one hβ μ hl hμ τ)
      j w s ‖j₂‖ r (abs_plaquetteReflectionSign τ J) k hw hb
    have ht : Tendsto (fun m : ℕ => (T ^ m) (B.ofVector u)) atTop (𝓝 (s • (T ^ k) w)) := hu' ▸ ht'
    have ha : ‖(T ^ n) (B.ofVector u) - s • (T ^ k) w‖ ≤ ‖u.val‖ * r ^ n := calc
      _ = ‖(T ^ n) (s • (T ^ k) j) - s • (T ^ k) w‖ :=
        congrArg (fun z : B.Hilbert => ‖(T ^ n) z - s • (T ^ k) w‖) hu'
      _ ≤ ‖j₂‖ * r ^ n := ha' n
      _ = _ := congrArg (fun M : ℝ => M * r ^ n) hnorm.symm
    refine (wilsonTransfer_matrixElement_left_vector_bound hβ μ hl hμ τ n u v _ ht).trans ?_
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg v.val)).trans_eq
      (mul_right_comm ‖u.val‖ (r ^ n) ‖v.val‖)
  · have hv' : v = wilsonCurrentHalfVector μ τ J := Subtype.ext hv
    subst v
    refine (wilsonTransfer_matrixElement_right_vector_bound hβ μ hl hμ τ n u
      (wilsonCurrentHalfVector μ τ J) w hw).trans ?_
    exact (mul_le_mul_of_nonneg_left (hb n) (norm_nonneg u.val)).trans_eq
      (mul_assoc ‖u.val‖ ‖wilsonCurrentL2 μ (J, 0)‖ (r ^ n)).symm

set_option maxHeartbeats 1200000 in
/-- In each time direction, a plaquette current has cyclic transfer
spectrum in every interval `(exp (-ε), 1)`. The cyclic spectrum
is the support of that vector's spectral measure. -/
theorem wilson_plaquette_low_energy_spectrum {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) :
    ∃ J : Face, ∀ ε > 0, ∃ t ∈ spectrum ℝ (cyclicTransfer
      (wilsonTransfer (by linarith) μ hl hμ τ) (wilsonCurrentOSVector μ hl hμ τ J)),
      t ∈ Set.Ioo (Real.exp (-ε)) 1 := by
  classical
  let hβ₀ : 0 ≤ β := by linarith
  let T := wilsonTransfer hβ₀ μ hl hμ τ
  let C (J : Face) := cyclicTransfer T (wilsonCurrentOSVector μ hl hμ τ J)
  change ∃ J : Face, ∀ ε > 0, ∃ t ∈ spectrum ℝ (C J), t ∈ Set.Ioo (Real.exp (-ε)) 1
  by_contra hn
  have hsep (J : Face) : ∃ ε : ℝ, 0 < ε ∧ ¬ ∃ t ∈ spectrum ℝ (C J), t ∈ Set.Ioo (Real.exp (-ε)) 1 := by
    by_contra h
    apply hn
    refine ⟨J, fun ε hε => ?_⟩
    by_contra he
    exact h ⟨ε, hε, he⟩
  choose η hη hs using hsep
  let faces : Finset Face := Finset.univ
  have hfaces : faces.Nonempty := ⟨.xy, Finset.mem_univ _⟩
  let ε := faces.inf' hfaces η
  have hε : 0 < ε := (Finset.lt_inf'_iff hfaces).mpr (fun J _ => hη J)
  let r := Real.exp (-ε)
  have hr₀ : 0 ≤ r := Real.exp_nonneg _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hε)
  have hsource (J : Face) : WilsonCurrentPowerDecay hβ₀ μ hl hμ τ J r := by
    let u := wilsonCurrentOSVector μ hl hμ τ J
    have hT : T.IsPositive := wilsonTransfer_positive hβ₀ μ hl hμ τ
    have hσ := realPositiveContraction_spectrum_subset (C J) (cyclicTransfer_positive T hT u)
      ((cyclicTransfer_norm_le T u).trans (wilsonTransfer_norm_le_one hβ₀ μ hl hμ τ))
    have hgap : spectrum ℝ (C J) ⊆ Set.Icc 0 r ∪ {1} := by
      intro t ht
      have h := hσ ht
      by_cases he : t = 1
      · exact Or.inr he
      · have hηJ : ε ≤ η J := Finset.inf'_le η (Finset.mem_univ J)
        have hrJ : Real.exp (-η J) ≤ r := Real.exp_le_exp.mpr (neg_le_neg hηJ)
        exact Or.inl ⟨h.1, le_of_not_gt (fun ht' => hs J ⟨t, ht, hrJ.trans_lt ht', lt_of_le_of_ne h.2 he⟩)⟩
    obtain ⟨w, hw, hb⟩ := exists_realTransfer_vector_limit T hT u hr₀ hr₁ hgap
    refine ⟨w, hw, fun n => (hb n).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (wilsonOSVector_norm_le μ hl hμ τ (wilsonCurrentHalfVector μ τ J))
      (pow_nonneg hr₀ _)
  have htarget (i : Axis) (J : Face) : WilsonCurrentPowerDecay hβ₀ μ hl hμ i J r := by
    let σ := Equiv.swap τ i
    let J₀ := (permuteFaceEquiv σ).symm J
    have hτ : σ τ = i := Equiv.swap_apply_left τ i
    have hJ : permuteFace σ J₀ = J := (permuteFaceEquiv σ).apply_symm_apply J
    have h := wilsonCurrentPowerDecay_permute hβ₀ μ hl hμ σ τ J₀ r (hsource J₀)
    rw [hτ, hJ] at h
    exact h
  refine projectedWilson_directional_decay_impossible hN hβ μ l hl hμ ε hε (fun I J i R x => ?_)
  exact wilsonLocalCovariance_directional_decay_of_vector_bound μ hμ i r (4 * R + 4)
    (wilsonFluxApproxObservable N i R I) (wilsonCurrentObservable μ i J)
    (wilsonCurrent_matrixElement_decay hβ₀ μ hl hμ i J r (htarget i J)) x

end

end GaplessYangMills

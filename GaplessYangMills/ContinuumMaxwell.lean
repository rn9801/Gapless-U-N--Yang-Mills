module

public import GaplessYangMills.ContinuumSplit
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Small positive energies in the free Maxwell sector

In the standard momentum representation the one-photon energy at
momentum `p` is `‖p‖`. The field-strength component with indices 0 and 1
has transverse momentum profile `ρ(p)(p₀ e₁ - p₁ e₀)`. Smooth compact
momentum smearings give nonzero states in every small positive energy band.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped ENat InnerProductSpace Topology

noncomputable section

abbrev PhotonMomentum := EuclideanSpace ℝ (Fin 3)
abbrev PhotonMomentumL2 := Lp PhotonMomentum 2 (volume : Measure PhotonMomentum)

def maxwellSmearingProfile (ρ : PhotonMomentum → ℝ) (p : PhotonMomentum) : PhotonMomentum :=
  ρ p • (p 0 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) -
    p 1 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))

theorem maxwellSmearingProfile_transverse (ρ : PhotonMomentum → ℝ) (p : PhotonMomentum) :
    ⟪p, maxwellSmearingProfile ρ p⟫_ℝ = 0 := by
  simp only [maxwellSmearingProfile, inner_sub_right, real_inner_smul_right, EuclideanSpace.inner_single_right,
    RCLike.conj_to_real, one_mul]
  ring

private theorem maxwellSmearingProfile_continuous {ρ : PhotonMomentum → ℝ} (hρ : Continuous ρ) :
    Continuous (maxwellSmearingProfile ρ) := by
  have h₀ : Continuous (fun p : PhotonMomentum => p 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0
  have h₁ : Continuous (fun p : PhotonMomentum => p 1) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1
  have h₂ : Continuous (fun p : PhotonMomentum => p 0 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) -
      p 1 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) :=
    (h₀.smul continuous_const).sub (h₁.smul continuous_const)
  exact hρ.smul h₂

theorem exists_maxwell_fieldStrength_packet_near (E δ : ℝ) (hE : 0 < E) (hδ : 0 < δ) :
    ∃ ρ : PhotonMomentum → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ρ ∧ HasCompactSupport ρ ∧
      ∃ A : PhotonMomentumL2, A ≠ 0 ∧
        (A : PhotonMomentum → PhotonMomentum) =ᵐ[volume] maxwellSmearingProfile ρ ∧
        ∀ᵐ p ∂(volume : Measure PhotonMomentum), A p ≠ 0 → |‖p‖ - E| < δ := by
  let q : PhotonMomentum := EuclideanSpace.single 0 E
  let b : ContDiffBump q := ⟨δ / 2, δ, by linarith, by linarith⟩
  let F := maxwellSmearingProfile b
  have hc : Continuous F := maxwellSmearingProfile_continuous b.continuous
  have hs : Function.support F ⊆ Function.support b := by
    intro p hp
    change F p ≠ 0 at hp
    exact fun hb => hp (by simp [F, maxwellSmearingProfile, hb])
  have hF := hc.memLp_of_hasCompactSupport (p := 2) (μ := volume) (b.hasCompactSupport.mono hs)
  let A := hF.toLp F
  have hA : (A : PhotonMomentum → PhotonMomentum) =ᵐ[volume] F := hF.coeFn_toLp
  have hb : b q = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt b.rIn_pos))
  have hFq : F q ≠ 0 := by
    intro hz
    have hj := congrArg (fun p : PhotonMomentum => p (1 : Fin 3)) hz
    simp [F, maxwellSmearingProfile, hb, q] at hj
    linarith
  have hne : A ≠ 0 := by
    intro hz
    have hz' := (Lp.eq_zero_iff_ae_eq_zero.mp hz)
    have he := (hc.ae_eq_iff_eq volume continuous_zero).mp (hA.symm.trans hz')
    exact hFq (congrFun he q)
  refine ⟨b, b.contDiff, b.hasCompactSupport, A, hne, hA, ?_⟩
  filter_upwards [hA] with p hp hn
  have hbp : p ∈ Function.support b := hs (show F p ≠ 0 from hp ▸ hn)
  have hd : dist p q < δ := by simpa only [b.support_eq, Metric.mem_ball] using hbp
  have hq : ‖q‖ = E := by
    rw [show ‖q‖ = ‖E‖ from PiLp.norm_single 2 (fun _ : Fin 3 => ℝ) 0 E,
      Real.norm_eq_abs, abs_of_pos hE]
  have ha := abs_norm_sub_norm_le p q
  rw [← dist_eq_norm, hq] at ha
  exact ha.trans_lt hd

/-- A smooth field-strength smearing gives a nonzero transverse packet
in every band `0 < ‖p‖ < ε`. -/
theorem exists_maxwell_fieldStrength_packet (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : PhotonMomentum → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) ρ ∧ HasCompactSupport ρ ∧
      ∃ A : PhotonMomentumL2, A ≠ 0 ∧
        (A : PhotonMomentum → PhotonMomentum) =ᵐ[volume] maxwellSmearingProfile ρ ∧
        ∀ᵐ p ∂(volume : Measure PhotonMomentum), A p ≠ 0 → ‖p‖ ∈ Set.Ioo 0 ε := by
  obtain ⟨ρ, hρ, hc, A, hA, hprof, hband⟩ :=
    exists_maxwell_fieldStrength_packet_near (ε / 2) (ε / 2) (by linarith) (by linarith)
  refine ⟨ρ, hρ, hc, A, hA, hprof, ?_⟩
  filter_upwards [hband] with p hp hn
  have h := abs_lt.mp (hp hn)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The real transverse one-photon Hilbert space in the flat momentum representation. -/
def maxwellPhotonSpace : Submodule ℝ PhotonMomentumL2 where
  carrier := {A | ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, A p⟫_ℝ = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero PhotonMomentum 2 (volume : Measure PhotonMomentum)] with p hp
    change ⟪p, (0 : PhotonMomentumL2) p⟫_ℝ = 0
    rw [hp, Pi.zero_apply, inner_zero_right]
  add_mem' := by
    intro A B hA hB
    change ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, A p⟫_ℝ = 0 at hA
    change ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, B p⟫_ℝ = 0 at hB
    change ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, (A + B) p⟫_ℝ = 0
    filter_upwards [Lp.coeFn_add A B, hA, hB] with p hp h₁ h₂
    rw [hp, Pi.add_apply, inner_add_right, h₁, h₂, add_zero]
  smul_mem' := by
    intro c A hA
    change ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, A p⟫_ℝ = 0 at hA
    change ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, (c • A) p⟫_ℝ = 0
    filter_upwards [Lp.coeFn_smul c A, hA] with p hp h
    rw [hp, Pi.smul_apply, real_inner_smul_right, h, mul_zero]

theorem maxwellPhotonSpace_closed : IsClosed (maxwellPhotonSpace : Set PhotonMomentumL2) := by
  apply IsSeqClosed.isClosed
  intro A B hA hB
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hB).exists_seq_tendsto_ae
  have hterm : ∀ n : ℕ, ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, A (φ n) p⟫_ℝ = 0 :=
    fun n => hA (φ n)
  change ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, B p⟫_ℝ = 0
  filter_upwards [ae_all_iff.mpr hterm, hφ] with p hp ht
  have hc : Continuous (fun y : PhotonMomentum => ⟪p, y⟫_ℝ) := continuous_const.inner continuous_id
  have h : Tendsto (fun n : ℕ => ⟪p, A (φ n) p⟫_ℝ) atTop (𝓝 ⟪p, B p⟫_ℝ) :=
    hc.continuousAt.tendsto.comp ht
  simp only [hp] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

instance : CompleteSpace maxwellPhotonSpace :=
  maxwellPhotonSpace_closed.isComplete.completeSpace_coe

theorem norm_maxwellTransfer_smul_le (p x : PhotonMomentum) :
    ‖Real.exp (-‖p‖) • x‖ ≤ ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (norm_nonneg _)))

theorem maxwellTransfer_memLp (A : PhotonMomentumL2) :
    MemLp (fun p => Real.exp (-‖p‖) • A p) 2 (volume : Measure PhotonMomentum) := by
  apply (Lp.memLp A).of_le
    ((Real.continuous_exp.comp continuous_norm.neg).aestronglyMeasurable.smul (Lp.aestronglyMeasurable A))
  exact ae_of_all _ fun p => norm_maxwellTransfer_smul_le p (A p)

def maxwellMomentumTransferValue (A : PhotonMomentumL2) : PhotonMomentumL2 :=
  (maxwellTransfer_memLp A).toLp _

theorem maxwellMomentumTransferValue_ae (A : PhotonMomentumL2) :
    (maxwellMomentumTransferValue A : PhotonMomentum → PhotonMomentum) =ᵐ[volume]
      fun p => Real.exp (-‖p‖) • A p :=
  (maxwellTransfer_memLp A).coeFn_toLp

def maxwellMomentumTransfer : PhotonMomentumL2 →L[ℝ] PhotonMomentumL2 := by
  let M : PhotonMomentumL2 →ₗ[ℝ] PhotonMomentumL2 :=
    { toFun := maxwellMomentumTransferValue
      map_add' := fun A B => by
        apply Lp.ext
        filter_upwards [maxwellMomentumTransferValue_ae (A + B), maxwellMomentumTransferValue_ae A,
          maxwellMomentumTransferValue_ae B, Lp.coeFn_add A B,
          Lp.coeFn_add (maxwellMomentumTransferValue A) (maxwellMomentumTransferValue B)] with p h hA hB hAB hadd
        rw [h, hadd, Pi.add_apply, hA, hB, hAB, Pi.add_apply, smul_add]
      map_smul' := fun c A => by
        change maxwellMomentumTransferValue (c • A) = c • maxwellMomentumTransferValue A
        apply Lp.ext
        filter_upwards [maxwellMomentumTransferValue_ae (c • A), maxwellMomentumTransferValue_ae A,
          Lp.coeFn_smul c A, Lp.coeFn_smul c (maxwellMomentumTransferValue A)] with p h hA h₁ h₂
        rw [h, h₂, Pi.smul_apply, hA, h₁, Pi.smul_apply, smul_comm] }
  refine M.mkContinuous 1 fun A => ?_
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [maxwellMomentumTransferValue_ae A] with p h
  change ‖maxwellMomentumTransferValue A p‖ ≤ ‖A p‖
  rw [h]
  exact norm_maxwellTransfer_smul_le p (A p)

/-- The Maxwell one-photon transfer acts by the multiplier `exp (-‖p‖)`. -/
def maxwellPhotonTransfer : maxwellPhotonSpace →L[ℝ] maxwellPhotonSpace :=
  (maxwellMomentumTransfer.comp maxwellPhotonSpace.subtypeL).codRestrict _ fun A => by
    have hA : ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, A.val p⟫_ℝ = 0 := A.property
    change ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, maxwellMomentumTransferValue A.val p⟫_ℝ = 0
    filter_upwards [maxwellMomentumTransferValue_ae A.val, hA] with p hp h
    rw [hp, real_inner_smul_right, h, mul_zero]

theorem maxwellPhotonTransfer_ae (A : maxwellPhotonSpace) :
    ((maxwellPhotonTransfer A).val : PhotonMomentum → PhotonMomentum) =ᵐ[volume]
      fun p => Real.exp (-‖p‖) • A.val p :=
  maxwellMomentumTransferValue_ae A.val

theorem maxwellPhotonTransfer_norm_le_one : ‖maxwellPhotonTransfer‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  change ‖(maxwellPhotonTransfer A).val‖ ≤ ‖A.val‖
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [maxwellPhotonTransfer_ae A] with p hp
  rw [hp]
  exact norm_maxwellTransfer_smul_le p (A.val p)

theorem maxwellPhotonTransfer_positive : maxwellPhotonTransfer.IsPositive := by
  refine ⟨fun A B => ?_, fun A => ?_⟩
  · change ⟪(maxwellPhotonTransfer A).val, B.val⟫_ℝ = ⟪A.val, (maxwellPhotonTransfer B).val⟫_ℝ
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [maxwellPhotonTransfer_ae A, maxwellPhotonTransfer_ae B] with p hA hB
    rw [hA, hB, real_inner_smul_left, real_inner_smul_right]
  · change 0 ≤ ⟪(maxwellPhotonTransfer A).val, A.val⟫_ℝ
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [maxwellPhotonTransfer_ae A] with p hp
    rw [hp, real_inner_smul_left]
    exact mul_nonneg (Real.exp_nonneg _) (real_inner_self_nonneg)

private theorem exists_maxwell_approximate_eigenvector (E η : ℝ) (hE : 0 < E) (hη : 0 < η) :
    ∃ A : maxwellPhotonSpace, A ≠ 0 ∧
      ‖maxwellPhotonTransfer A - Real.exp (-E) • A‖ ≤ η * ‖A‖ := by
  have hc : Continuous (fun k : ℝ => Real.exp (-k)) := Real.continuous_exp.comp continuous_neg
  have hcAt : ContinuousAt (fun k : ℝ => Real.exp (-k)) E := hc.continuousAt
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hcAt η hη
  obtain ⟨ρ, _, _, A, hA, hprof, hband⟩ := exists_maxwell_fieldStrength_packet_near E δ hE hδ
  have htrans : A ∈ maxwellPhotonSpace := by
    change ∀ᵐ p ∂(volume : Measure PhotonMomentum), ⟪p, A p⟫_ℝ = 0
    filter_upwards [hprof] with p hp
    rw [hp, maxwellSmearingProfile_transverse]
  let B : maxwellPhotonSpace := ⟨A, htrans⟩
  let t := Real.exp (-E)
  refine ⟨B, fun hb => hA (congrArg Subtype.val hb), ?_⟩
  change ‖(maxwellPhotonTransfer B).val - t • A‖ ≤ η * ‖A‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [maxwellPhotonTransfer_ae B, Lp.coeFn_smul t A,
    Lp.coeFn_sub (maxwellPhotonTransfer B).val (t • A), hband] with p hp hs hd hband'
  change ‖((maxwellPhotonTransfer B).val - t • A) p‖ ≤ η * ‖A p‖
  rw [hd, Pi.sub_apply, hp, hs, Pi.smul_apply]
  change ‖Real.exp (-‖p‖) • A p - t • A p‖ ≤ η * ‖A p‖
  by_cases hz : A p = 0
  · simp [hz]
  · rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    have hdE : dist ‖p‖ E < δ := by simpa only [Real.dist_eq] using hband' hz
    have hn := hnear hdE
    rw [Real.dist_eq] at hn
    exact mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)

/-- In a product quantization with an isometric copy of the one-photon
sector and the usual action of the transfer on it, each positive photon
energy gives a spectral value of the product transfer. -/
theorem maxwell_product_transfer_spectrum {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : H →L[ℝ] H) (I : maxwellPhotonSpace →ₗᵢ[ℝ] H)
    (hI : ∀ A, T (I A) = I (maxwellPhotonTransfer A)) (E : ℝ) (hE : 0 < E) :
    Real.exp (-E) ∈ spectrum ℝ T := by
  let t := Real.exp (-E)
  by_contra ht
  have hu : IsUnit (T - algebraMap ℝ (H →L[ℝ] H) t) :=
    IsUnit.sub_iff.mp (spectrum.notMem_iff.mp ht)
  obtain ⟨V, hV⟩ := hu
  let K := ‖(↑V⁻¹ : H →L[ℝ] H)‖
  let η := (K + 1)⁻¹
  have hK : 0 ≤ K := norm_nonneg _
  have hη : 0 < η := inv_pos.mpr (by positivity)
  obtain ⟨A, hA, hApprox⟩ := exists_maxwell_approximate_eigenvector E η hE hη
  have h := (↑V⁻¹ : H →L[ℝ] H).le_opNorm ((T - algebraMap ℝ (H →L[ℝ] H) t) (I A))
  have hEq : ((↑V⁻¹ : H →L[ℝ] H) * (T - algebraMap ℝ (H →L[ℝ] H) t)) (I A) = I A := by
    rw [← hV, Units.inv_mul, one_apply_eq_self]
  rw [← mul_apply_eq_comp, hEq, I.norm_map, sub_apply, ContinuousLinearMap.algebraMap_apply,
    hI, ← map_smul, ← map_sub, I.norm_map] at h
  have hbound : ‖A‖ ≤ K * (η * ‖A‖) := h.trans (mul_le_mul_of_nonneg_left hApprox hK)
  have hprod : K * η < 1 := by
    rw [show K * η = K / (K + 1) from (div_eq_mul_inv _ _).symm]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  exact (not_lt_of_ge hbound) (by
    rw [← mul_assoc]
    exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hA) hprod)

theorem maxwell_photon_transfer_spectrum (E : ℝ) (hE : 0 < E) :
    Real.exp (-E) ∈ spectrum ℝ maxwellPhotonTransfer := by
  let I : maxwellPhotonSpace →ₗᵢ[ℝ] maxwellPhotonSpace := LinearIsometry.id
  exact maxwell_product_transfer_spectrum maxwellPhotonTransfer I (fun _ => rfl) E hE

end

end GaplessYangMills

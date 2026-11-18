module

public import GaplessYangMills.CapGain
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Stability of the unitary expectation on a spherical cap
-/

@[expose] public section

namespace GaplessYangMills

open scoped InnerProductSpace ComplexConjugate

theorem norm_unitary_expectation_sub_eigenvalue {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : E ≃ₗᵢ[ℂ] E) (v₀ v : E) (z : Circle)
    (hv₀ : ‖v₀‖ = 1) (hv : ‖v‖ = 1) (heig : P v₀ = (z : ℂ) • v₀) :
    ‖⟪v, P v⟫_ℂ - (z : ℂ)‖ ≤ 2 * (1 - ‖⟪v₀, v⟫_ℂ‖ ^ 2) := by
  let α := ⟪v₀, v⟫_ℂ
  let u : E := α • v₀
  let w : E := v - u
  have hdecomp : u + w = v := by simp [w]
  have hu : P u = (z : ℂ) • u := by
    simp [u, heig, smul_smul, mul_comm]
  have horth₀ : ⟪v₀, w⟫_ℂ = 0 := by
    simp [w, u, α, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv₀]
  have horth : ⟪u, w⟫_ℂ = 0 := by simp [u, inner_smul_left, horth₀]
  have hright : ⟪u, P w⟫_ℂ = 0 := by
    have h := P.inner_map_map u w
    rw [hu, inner_smul_left, horth] at h
    exact (mul_eq_zero.mp h).resolve_left (by simp)
  have hleft : ⟪w, P u⟫_ℂ = 0 := by
    rw [hu, inner_smul_right, inner_eq_zero_symm.mp horth, mul_zero]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u w horth
  rw [hdecomp, hv, one_mul, ← pow_two, ← pow_two] at hpy
  have huNorm : ‖u‖ = ‖α‖ := by simp [u, norm_smul, hv₀]
  have hnorm : (‖u‖ : ℂ) ^ 2 - 1 = -(‖w‖ : ℂ) ^ 2 := by
    exact_mod_cast (show ‖u‖ ^ 2 - 1 = -‖w‖ ^ 2 by linarith)
  have hdiff : ⟪v, P v⟫_ℂ - (z : ℂ) =
      -(z : ℂ) * (‖w‖ : ℂ) ^ 2 + ⟪w, P w⟫_ℂ := by
    rw [← hdecomp, map_add, inner_add_left, inner_add_right, inner_add_right,
      hright, hleft, hu, inner_smul_right, inner_self_eq_norm_sq_to_K]
    linear_combination (z : ℂ) * hnorm
  rw [hdiff]
  calc
    _ ≤ ‖-(z : ℂ) * (‖w‖ : ℂ) ^ 2‖ + ‖⟪w, P w⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := by
      have hw := norm_inner_le_norm (𝕜 := ℂ) w (P w)
      rw [P.norm_map, ← pow_two] at hw
      simp only [norm_mul, norm_neg, Circle.norm_coe, norm_pow, Complex.norm_real, norm_norm, one_mul]
      exact add_le_add_right hw _
    _ = _ := by rw [← huNorm]; linarith

/-- A cap of squared overlap at least fifteen sixteenths lies in the range
where the scalar half-penalty estimate applies. -/
theorem exists_unitary_cap_gain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : E ≃ₗᵢ[ℂ] E) (v₀ v : E) (θ : ℝ)
    (hv₀ : ‖v₀‖ = 1) (hv : ‖v‖ = 1)
    (heig : P v₀ = (Circle.exp θ : ℂ) • v₀)
    (hθ : Real.pi / 4 ≤ |θ|) (hπ : |θ| ≤ Real.pi)
    (hcap : (15 : ℝ) / 16 ≤ ‖⟪v₀, v⟫_ℂ‖ ^ 2) :
    ∃ s : ℝ, |s| = Real.pi / 4 ∧
      badPenalty / 2 ≤ (((Circle.exp s : ℂ) - 1) * ⟪v, P v⟫_ℂ).re := by
  apply exists_cap_twist_gain θ hθ hπ
  have h := norm_unitary_expectation_sub_eigenvalue P v₀ v (Circle.exp θ) hv₀ hv heig
  linarith

end GaplessYangMills

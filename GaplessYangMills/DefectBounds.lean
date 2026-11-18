module

public import GaplessYangMills.Wilson
public import GaplessYangMills.MarkedEdges

/-!
# Bounds on the lifted integer defect

The six oriented face terms give a uniform bound at every rank and the
good-cube vanishing criterion in rank one.
-/

@[expose] public section

namespace GaplessYangMills

private theorem abs_three_le (u v w C : ℝ)
    (hu : |u| ≤ 2 * C) (hv : |v| ≤ 2 * C) (hw : |w| ≤ 2 * C) :
    |u - v + w| ≤ 6 * C := by
  have h := (abs_add_le (u - v) w).trans (add_le_add_left (abs_sub u v) _)
  linarith

theorem abs_d₂_le (a : TwoForm ℝ) (C : ℝ) (h : ∀ I x, |a I x| ≤ C)
    (c : Cube) (x : Site) : |d₂ a c x| ≤ 6 * C := by
  have hd (i : Axis) (I : Face) : |diff i (a I) x| ≤ 2 * C := by
    exact (abs_sub _ _).trans (by linarith [h I (x + step i), h I x])
  cases c <;>
    simp only [d₂, Pi.add_apply, Pi.sub_apply] <;>
    exact abs_three_le _ _ _ C (hd _ _) (hd _ _) (hd _ _)

theorem abs_defect_le_of_abs_flux_le (a : TwoForm ℝ)
    (hexp : ∀ c x, Circle.exp (d₂ a c x) = 1)
    (C : ℝ) (h : ∀ I x, |a I x| ≤ C) (c : Cube) (x : Site) :
    |(defect a c x : ℝ)| ≤ 6 * C / (2 * Real.pi) := by
  apply (le_div_iff₀ Real.two_pi_pos).mpr
  have hd := abs_defect_aux a hexp c x
  rw [mul_comm, hd]
  exact abs_d₂_le a C h c x
where
  abs_defect_aux (a : TwoForm ℝ) (hexp : ∀ c x, Circle.exp (d₂ a c x) = 1)
      (c : Cube) (x : Site) :
      2 * Real.pi * |(defect a c x : ℝ)| = |d₂ a c x| := by
    rw [← abs_of_pos Real.two_pi_pos, ← abs_mul]
    simp only [defect_exact a hexp]

theorem abs_liftAngle_le {η θ : ℝ} (hη : |η| ≤ Real.pi / 16) :
    |liftAngle η θ| ≤ 17 * Real.pi / 16 := by
  obtain ⟨hl, hu⟩ := liftAngle_mem η θ
  obtain ⟨h₁, h₂⟩ := abs_le.mp hη
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_unitaryDefect_le {N : ℕ} (U : OneForm (UnitaryMatrix N))
    (η : TwoForm ℝ) (θ : Angles N)
    (hθ : ∀ I x, (∏ j, Circle.exp (θ I x j)) = unitaryDet N (plaquetteHolonomy U I x))
    (hη : ∀ I x, |η I x| ≤ Real.pi / 16) (c : Cube) (x : Site) :
    |(defect (liftFlux η θ) c x : ℝ)| ≤ 4 * N := by
  have hflux (I : Face) (y : Site) : |liftFlux η θ I y| ≤ N * (17 * Real.pi / 16) := by
    unfold liftFlux
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _j : Fin N, 17 * Real.pi / 16 :=
        Finset.sum_le_sum fun _ _ => abs_liftAngle_le (hη I y)
      _ = _ := by simp [nsmul_eq_mul]
  refine (abs_defect_le_of_abs_flux_le _ (unitary_liftFlux_exp_closed U η θ hθ)
    _ hflux c x).trans ?_
  apply (div_le_iff₀ Real.two_pi_pos).mpr
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) Real.pi_pos.le]


theorem defect_eq_zero_of_small (a : TwoForm ℝ)
    (hexp : ∀ c x, Circle.exp (d₂ a c x) = 1) (c : Cube) (x : Site)
    (hsmall : |d₂ a c x| < 2 * Real.pi) :
    defect a c x = 0 := by
  rw [← defect_exact a hexp c x, abs_mul, abs_of_pos Real.two_pi_pos] at hsmall
  have hlt : |(defect a c x : ℝ)| < 1 := by
    apply (mul_lt_mul_iff_right₀ Real.two_pi_pos).mp
    simpa only [one_mul, mul_comm] using hsmall
  have hz : |defect a c x| < 1 := by exact_mod_cast hlt
  obtain ⟨hl, hu⟩ := abs_lt.mp hz
  omega

theorem abs_d₂_le_of_cubeFaces (a : TwoForm ℝ) (C : ℝ) (c : Cube) (x : Site)
    (h : ∀ p ∈ cubeFaces (c, x), |a p.1 p.2| ≤ C) : |d₂ a c x| ≤ 6 * C := by
  have hd (i : Axis) (I : Face) (h₁ : (I, x + step i) ∈ cubeFaces (c, x))
      (h₂ : (I, x) ∈ cubeFaces (c, x)) : |diff i (a I) x| ≤ 2 * C :=
    (abs_sub _ _).trans (by linarith [h _ h₁, h _ h₂])
  cases c <;> simp only [d₂, Pi.add_apply, Pi.sub_apply]
  all_goals
    refine abs_three_le _ _ _ C (hd _ _ ?_ ?_) (hd _ _ ?_ ?_) (hd _ _ ?_ ?_)
    all_goals simp [mem_cubeFaces_list, cubeFaceList]

/-- In rank one the six good-face angle bounds already force zero winding. -/
theorem rankOne_defect_eq_zero_on_goodCube (U : OneForm (UnitaryMatrix 1))
    (η : TwoForm ℝ) (θ : Angles 1)
    (hθ : ∀ I x, (∏ j, Circle.exp (θ I x j)) = unitaryDet 1 (plaquetteHolonomy U I x))
    (c : Cube) (x : Site)
    (hη : ∀ p ∈ cubeFaces (c, x), |η p.1 p.2| ≤ Real.pi / 16)
    (hgood : ∀ p ∈ cubeFaces (c, x), |θ p.1 p.2 0| ≤ Real.pi / 4) :
    defect (liftFlux η θ) c x = 0 := by
  apply defect_eq_zero_of_small _ (unitary_liftFlux_exp_closed U η θ hθ)
  apply (abs_d₂_le_of_cubeFaces _ (Real.pi / 4) c x ?_).trans_lt
  · linarith [Real.pi_pos]
  · intro p hp
    simpa [liftFlux, liftAngle_of_good (hη p hp) (hgood p hp)] using hgood p hp

end GaplessYangMills

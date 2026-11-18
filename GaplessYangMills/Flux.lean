module

public import GaplessYangMills.Lattice
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Lifted determinant flux

The branch interval, the integer defect, and the exact central-shift identity
are the algebraic parts of Sections 3 and 4. The input angle field lists the
eigenangles of each positive plaquette. The repair is parameterized by a filling
that depends only on the integer current.
-/

@[expose] public section

namespace GaplessYangMills

open scoped BigOperators

noncomputable section

/-- The lift of one angle with the half-open branch convention of the paper. -/
def liftAngle (η θ : ℝ) : ℝ :=
  toIocMod Real.two_pi_pos (η - Real.pi) θ

theorem liftAngle_mem (η θ : ℝ) :
    liftAngle η θ ∈ Set.Ioc (η - Real.pi) (η + Real.pi) := by
  have h : η - Real.pi + 2 * Real.pi = η + Real.pi := by ring
  simpa only [liftAngle, h] using toIocMod_mem_Ioc Real.two_pi_pos (η - Real.pi) θ

theorem liftAngle_of_good {η θ : ℝ} (hη : |η| ≤ Real.pi / 16)
    (hθ : |θ| ≤ Real.pi / 4) : liftAngle η θ = θ := by
  unfold liftAngle
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  obtain ⟨hηl, hηu⟩ := abs_le.mp hη
  obtain ⟨hθl, hθu⟩ := abs_le.mp hθ
  exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem exp_liftAngle (η θ : ℝ) : Circle.exp (liftAngle η θ) = Circle.exp θ := by
  symm
  exact Circle.exp_eq_exp.mpr ⟨toIocDiv Real.two_pi_pos (η - Real.pi) θ,
    (toIocMod_add_toIocDiv_mul Real.two_pi_pos (η - Real.pi) θ).symm⟩

theorem liftAngle_shift (η θ v : ℝ) :
    liftAngle η (θ + v) = liftAngle (η - v) θ + v := by
  unfold liftAngle
  rw [toIocMod_add_right_eq_add, sub_right_comm η Real.pi v]

abbrev Angles (N : ℕ) := TwoForm (Fin N → ℝ)

def liftFlux {N : ℕ} (η : TwoForm ℝ) (θ : Angles N) : TwoForm ℝ :=
  fun I x => ∑ j, liftAngle (η I x) (θ I x j)

theorem exp_liftFlux {N : ℕ} (η : TwoForm ℝ) (θ : Angles N) (I : Face) (x : Site) :
    Circle.exp (liftFlux η θ I x) = ∏ j, Circle.exp (θ I x j) := by
  change Additive.toMul (Circle.expHom (∑ j, liftAngle (η I x) (θ I x j))) = _
  rw [map_sum]
  simp [exp_liftAngle]

/-- The unscaled integer representative of the three-form. Under the determinant
cube identity, the quotient being rounded here is exactly integral. -/
def defect (a : TwoForm ℝ) : ThreeForm ℤ :=
  fun c x => ⌈d₂ a c x / (2 * Real.pi)⌉

private def periodTimesInt : ℤ →+ ℝ :=
  (AddMonoidHom.mulLeft (2 * Real.pi)).comp (Int.castAddHom ℝ)

theorem defect_exact (a : TwoForm ℝ) (h : ∀ c x, Circle.exp (d₂ a c x) = 1)
    (c : Cube) (x : Site) : 2 * Real.pi * (defect a c x : ℝ) = d₂ a c x := by
  obtain ⟨z, hz⟩ := Circle.exp_eq_one.mp (h c x)
  have hd : defect a c x = z := by
    unfold defect
    rw [hz, mul_div_cancel_right₀ _ Real.two_pi_pos.ne', Int.ceil_intCast]
  rw [hd, hz, mul_comm]

/-- A circle-valued closed lift has a closed integer defect. -/
theorem defect_closed (a : TwoForm ℝ) (h : ∀ c x, Circle.exp (d₂ a c x) = 1) :
    d₃ (defect a) = 0 := by
  funext x
  have hlift : (fun c y => periodTimesInt (defect a c y)) = d₂ a := by
    funext c y
    exact defect_exact a h c y
  have hzero : periodTimesInt (d₃ (defect a) x) = 0 := by
    rw [← d₃_map, hlift, d₃_d₂]
    rfl
  change (2 * Real.pi) * ((d₃ (defect a) x : ℤ) : ℝ) = 0 at hzero
  have hz := (mul_eq_zero.mp hzero).resolve_left Real.two_pi_pos.ne'
  exact_mod_cast hz

def repairFlux (fill : ThreeForm ℤ → TwoForm ℤ) (a : TwoForm ℝ) : TwoForm ℝ :=
  a - fun I x => 2 * Real.pi * (fill (defect a) I x : ℝ)

theorem repairFlux_closed (fill : ThreeForm ℤ → TwoForm ℤ) (a : TwoForm ℝ)
    (h : ∀ c x, Circle.exp (d₂ a c x) = 1) (hfill : d₂ (fill (defect a)) = defect a) :
    d₂ (repairFlux fill a) = 0 := by
  funext c x
  unfold repairFlux
  rw [d₂_sub]
  change d₂ a c x - d₂ (fun I y => periodTimesInt (fill (defect a) I y)) c x = 0
  rw [d₂_map, hfill, sub_eq_zero]
  exact (defect_exact a h c x).symm

def shiftAngles {N : ℕ} (θ : Angles N) (f : TwoForm ℝ) : Angles N :=
  fun I x j => θ I x j + f I x / N

def shiftCuts (η f : TwoForm ℝ) (N : ℕ) : TwoForm ℝ :=
  fun I x => η I x - f I x / N

/-- Shifting every eigenangle by the same central angle and translating the cut
recovers the full determinant angle shift. -/
theorem liftFlux_central_shift {N : ℕ} (hN : 0 < N) (η : TwoForm ℝ) (θ : Angles N)
    (f : TwoForm ℝ) : liftFlux η (shiftAngles θ f) = liftFlux (shiftCuts η f N) θ + f := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext I x
  simp only [liftFlux, shiftAngles, shiftCuts, liftAngle_shift, Finset.sum_add_distrib, Pi.add_apply,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_div_cancel₀ _ hn]

/-- The exact cut-shift equality preceding equation (5), for any fixed rule
which fills a given integer current. The perturbation `f` is already the total
plaquette angle shift and includes the factor `t` in the paper. -/
theorem repairFlux_central_shift {N : ℕ} (hN : 0 < N)
    (fill : ThreeForm ℤ → TwoForm ℤ) (η : TwoForm ℝ) (θ : Angles N) (f : TwoForm ℝ)
    (hf : d₂ f = 0) :
    repairFlux fill (liftFlux η (shiftAngles θ f)) =
      repairFlux fill (liftFlux (shiftCuts η f N) θ) + f := by
  rw [liftFlux_central_shift hN]
  have hdefect : defect (liftFlux (shiftCuts η f N) θ + f) =
      defect (liftFlux (shiftCuts η f N) θ) := by
    unfold defect
    rw [d₂_add, hf, add_zero]
  simp only [repairFlux, hdefect]
  abel

end

end GaplessYangMills

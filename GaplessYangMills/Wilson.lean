module

public import GaplessYangMills.Flux
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary plaquette holonomy and central rotation

This file fixes link and plaquette orientations, proves the determinant cube
identity, and identifies the central rotation on an actual unitary plaquette.
-/

@[expose] public section

namespace GaplessYangMills

open scoped ComplexConjugate

/-- The ordered holonomy around a positive plaquette. -/
def plaquetteHolonomy {G : Type*} [Group G] (U : OneForm G) (I : Face) (x : Site) : G :=
  let (i, j) := I.axes
  U i x * U j (x + step i) * (U i (x + step j))⁻¹ * (U j x)⁻¹

theorem map_plaquetteHolonomy {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (U : OneForm G) (I : Face) (x : Site) :
    φ (plaquetteHolonomy U I x) = plaquetteHolonomy (fun i y => φ (U i y)) I x := by
  cases I <;> simp [plaquetteHolonomy, Face.axes]

theorem plaquetteHolonomy_comm {G : Type*} [CommGroup G] (U : OneForm G) (I : Face) (x : Site) :
    Additive.ofMul (plaquetteHolonomy U I x) = d₁ (fun i y => Additive.ofMul (U i y)) I x := by
  cases I <;> simp only [d₁, diff, Pi.sub_apply, plaquetteHolonomy, Face.axes,
    ofMul_mul, ofMul_inv] <;> abel

noncomputable section

abbrev UnitaryMatrix (N : ℕ) := Matrix.unitaryGroup (Fin N) ℂ

/-- Determinant with its natural circle codomain. -/
def unitaryDet (N : ℕ) : UnitaryMatrix N →* Circle where
  toFun U := ⟨U.val.det, by
    apply mem_sphere_zero_iff_norm.mpr
    have h := (Matrix.det_of_mem_unitary U.property).2
    rw [Complex.star_def, Complex.mul_conj] at h
    have hs : Complex.normSq U.val.det = 1 := by
      simpa only [Complex.ofReal_re, Complex.one_re] using congrArg Complex.re h
    rw [Complex.normSq_eq_norm_sq] at hs
    nlinarith [norm_nonneg U.val.det]⟩
  map_one' := by
    apply Circle.ext
    exact Matrix.det_one
  map_mul' A B := by
    apply Circle.ext
    exact Matrix.det_mul A.val B.val

theorem determinant_closed {N : ℕ} (U : OneForm (UnitaryMatrix N)) :
    d₂ (fun I x => Additive.ofMul (unitaryDet N (plaquetteHolonomy U I x))) = 0 := by
  have h : (fun I x => Additive.ofMul (unitaryDet N (plaquetteHolonomy U I x))) =
      d₁ (fun i x => Additive.ofMul (unitaryDet N (U i x))) := by
    funext I x
    rw [map_plaquetteHolonomy, plaquetteHolonomy_comm]
  rw [h, d₂_d₁]

/-- The cube identity for the lifted angle field of a unitary connection. -/
theorem unitary_liftFlux_exp_closed {N : ℕ} (U : OneForm (UnitaryMatrix N))
    (η : TwoForm ℝ) (θ : Angles N)
    (hθ : ∀ I x, (∏ j, Circle.exp (θ I x j)) = unitaryDet N (plaquetteHolonomy U I x)) :
    ∀ c x, Circle.exp (d₂ (liftFlux η θ) c x) = 1 := by
  intro c x
  have h : (fun I y => Circle.expHom (liftFlux η θ I y)) =
      fun I y => Additive.ofMul (unitaryDet N (plaquetteHolonomy U I y)) := by
    funext I y
    exact (exp_liftFlux η θ I y).trans (hθ I y)
  have hc := d₂_map Circle.expHom (liftFlux η θ) c x
  rw [h, determinant_closed] at hc
  exact hc.symm

/-- The central subgroup of the fundamental unitary representation. -/
def centralPhase (N : ℕ) : Circle →* UnitaryMatrix N where
  toFun z := ⟨(z : ℂ) • 1, by
    apply Matrix.mem_unitaryGroup_iff.mpr
    change ((z : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) * star ((z : ℂ) • 1) = 1
    rw [star_smul, star_one, smul_mul_assoc, one_mul, smul_smul, Complex.star_def, Complex.mul_conj,
      Circle.normSq_coe, Complex.ofReal_one, one_smul]⟩
  map_one' := by
    apply Subtype.ext
    exact one_smul ℂ _
  map_mul' z w := by
    apply Subtype.ext
    change ((z : ℂ) * (w : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ) = ((z : ℂ) • 1) * ((w : ℂ) • 1)
    rw [smul_mul_assoc, one_mul, smul_smul]

theorem centralPhase_commute {N : ℕ} (z : Circle) (U : UnitaryMatrix N) :
    Commute (centralPhase N z) U := by
  apply Subtype.ext
  change ((z : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) * U.val = U.val * ((z : ℂ) • 1)
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

private theorem central_mul {N : ℕ} (a b : Circle) (U V : UnitaryMatrix N) :
    (centralPhase N a * U) * (centralPhase N b * V) =
      centralPhase N (a * b) * (U * V) := by
  calc
    _ = centralPhase N a * (U * centralPhase N b) * V := by simp only [mul_assoc]
    _ = centralPhase N a * (centralPhase N b * U) * V := by
      rw [(centralPhase_commute b U).eq.symm]
    _ = _ := by simp only [map_mul, mul_assoc]

private theorem central_inv {N : ℕ} (a : Circle) (U : UnitaryMatrix N) :
    (centralPhase N a * U)⁻¹ = centralPhase N a⁻¹ * U⁻¹ := by
  rw [mul_inv_rev, ← map_inv]
  exact (centralPhase_commute a⁻¹ U⁻¹).eq.symm

/-- A central rotation of the link variables by their link angles rotates each
plaquette by the exterior difference of those angles. -/
theorem plaquetteHolonomy_central {N : ℕ} (U : OneForm (UnitaryMatrix N))
    (α : OneForm ℝ) (I : Face) (x : Site) :
    plaquetteHolonomy (fun i y => centralPhase N (Circle.exp (α i y)) * U i y) I x =
      centralPhase N (Circle.exp (d₁ α I x)) * plaquetteHolonomy U I x := by
  have hexp := (d₁_map Circle.expHom α I x).symm
  change Additive.ofMul (Circle.exp (d₁ α I x)) =
    d₁ (fun i y => Additive.ofMul (Circle.exp (α i y))) I x at hexp
  rw [← plaquetteHolonomy_comm] at hexp
  rw [Additive.ofMul.injective hexp]
  cases I <;> simp only [plaquetteHolonomy, Face.axes, central_inv, central_mul]

/-- The central phase multiplies the ordinary complex trace by that phase. -/
theorem trace_centralPhase {N : ℕ} (z : Circle) (U : UnitaryMatrix N) :
    (centralPhase N z * U).val.trace = (z : ℂ) * U.val.trace := by
  change (((z : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) * U.val).trace = _
  rw [smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul]

end

end GaplessYangMills

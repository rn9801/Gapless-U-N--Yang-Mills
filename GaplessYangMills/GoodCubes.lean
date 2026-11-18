module

public import GaplessYangMills.BadEvents
public import GaplessYangMills.CubeHolonomy
public import GaplessYangMills.ShortUnitaryProducts

/-!
# Good cubes have zero lifted defect

The transported face holonomies give a six-factor loop. Each good face has a
Hermitian logarithm of operator norm at most π/4, and the principal trace
phases therefore sum to zero with the boundary orientation signs.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix.Norms.L2Operator
open selfAdjoint

private theorem good_root_angle {N : ℕ} {U : UnitaryMatrix N} (hU : ¬ badUnitary U)
    {z : ℂ} (hz : z ∈ U.val.charpoly.roots) :
    |Complex.arg z| ≤ Real.pi / 4 :=
  le_of_not_gt fun h => hU ⟨z, hz, h⟩

private theorem goodUnitary_conj {N : ℕ} (V : UnitaryMatrix N) {U : UnitaryMatrix N}
    (hU : ¬ badUnitary U) : ¬ badUnitary (V * U * V⁻¹) := by
  simpa only [badUnitary, unitaryCharpoly_conj] using hU

private theorem short_log_of_good {N : ℕ} (U : UnitaryMatrix N) (hU : ¬ badUnitary U) :
    ∃ X : HermitianMatrix N, expUnitary X = U ∧ ‖X‖ ≤ Real.pi / 4 ∧
      principalAngleSum U = phaseTrace X := by
  have hroot {z : ℂ} (hz : z ∈ spectrum ℂ U.val) : z ∈ U.val.charpoly.roots :=
    (Polynomial.mem_roots U.val.charpoly_monic.ne_zero).mpr
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz)
  have hnorm : ‖U.val - 1‖ < 2 := by
    apply (Unitary.norm_sub_one_lt_two_iff U.property).mpr
    intro h
    have ha := good_root_angle hU (hroot h)
    rw [Complex.arg_neg_one, abs_of_pos Real.pi_pos] at ha
    linarith [Real.pi_pos]
  have hlog : ‖Unitary.argSelfAdjoint U‖ ≤ Real.pi / 4 := by
    change ‖(Unitary.argSelfAdjoint U).val‖ ≤ Real.pi / 4
    rw [Unitary.argSelfAdjoint_coe]
    apply norm_cfc_le (by positivity)
    intro z hz
    simpa only [Complex.norm_real, Real.norm_eq_abs] using good_root_angle hU (hroot hz)
  exact ⟨Unitary.argSelfAdjoint U, expUnitary_argSelfAdjoint hnorm, hlog,
    principalAngleSum_eq_phaseTrace_arg U hnorm⟩

private theorem six_good_factors_phase {N : ℕ} (A B C D E F : UnitaryMatrix N)
    (hA : ¬ badUnitary A) (hB : ¬ badUnitary B) (hC : ¬ badUnitary C)
    (hD : ¬ badUnitary D) (hE : ¬ badUnitary E) (hF : ¬ badUnitary F)
    (h : A * B * C * D⁻¹ * E⁻¹ * F⁻¹ = 1) :
    principalAngleSum A + principalAngleSum B + principalAngleSum C -
      principalAngleSum D - principalAngleSum E - principalAngleSum F = 0 := by
  obtain ⟨X, rfl, hX, htx⟩ := short_log_of_good A hA
  obtain ⟨Y, rfl, hY, hty⟩ := short_log_of_good B hB
  obtain ⟨Z, rfl, hZ, htz⟩ := short_log_of_good C hC
  obtain ⟨U, rfl, hU, htu⟩ := short_log_of_good D hD
  obtain ⟨V, rfl, hV, htv⟩ := short_log_of_good E hE
  obtain ⟨W, rfl, hW, htw⟩ := short_log_of_good F hF
  have hzero := phaseTrace_six_eq_zero X Y Z (-U) (-V) (-W) hX hY hZ
    (by simpa only [norm_neg] using hU) (by simpa only [norm_neg] using hV)
    (by simpa only [norm_neg] using hW) (by simpa only [expUnitary_neg] using h)
  rw [htx, hty, htz, htu, htv, htw]
  simp only [phaseTrace_neg] at hzero
  linarith

theorem eigenAngleLift_of_good {N : ℕ} (U : UnitaryMatrix N) (η : ℝ)
    (hη : |η| ≤ Real.pi / 16) (hU : ¬ badUnitary U) :
    eigenAngleLift U η = principalAngleSum U := by
  unfold eigenAngleLift principalAngleSum
  exact congrArg Multiset.sum (Multiset.map_congr rfl
    (fun _ hz => liftAngle_of_good hη (good_root_angle hU hz)))

theorem plaquetteDefect_eq_zero_on_goodCube {N : ℕ} (U : OneForm (UnitaryMatrix N))
    (η : TwoForm ℝ) (c : Cube) (x : Site)
    (hη : ∀ p ∈ cubeFaces (c, x), |η p.1 p.2| ≤ Real.pi / 16)
    (hgood : ∀ p ∈ cubeFaces (c, x), ¬ badUnitary (plaquetteHolonomy U p.1 p.2)) :
    defect (liftFlux η (plaquetteEigenangles U)) c x = 0 := by
  let a := liftFlux η (plaquetteEigenangles U)
  have hlift (I : Face) (y : Site) (hp : (I, y) ∈ cubeFaces (c, x)) :
      a I y = principalAngleSum (plaquetteHolonomy U I y) := by
    change liftFlux η (plaquetteEigenangles U) I y = _
    rw [liftFlux_eq_eigenAngleLift, eigenAngleLift_of_good (plaquetteHolonomy U I y) (η I y)
      (hη (I, y) hp) (hgood (I, y) hp)]
  have hexp : ∀ c x, Circle.exp (d₂ a c x) = 1 :=
    unitary_liftFlux_exp_closed U η (plaquetteEigenangles U) (prod_exp_plaquetteEigenangles U)
  apply defect_eq_zero_of_small a hexp c x
  let i := c.axes.1
  let j := c.axes.2.1
  let k := c.axes.2.2
  let ij := c.orientations.1
  let ik := c.orientations.2.1
  let jk := c.orientations.2.2
  let P := plaquetteHolonomy U
  let A := U i x * P jk (x + step i) * (U i x)⁻¹
  let B := P ik x
  let C := U k x * P ij (x + step k) * (U k x)⁻¹
  let D := P jk x
  let E := U j x * P ik (x + step j) * (U j x)⁻¹
  let F := P ij x
  have ha : (jk, x + step i) ∈ cubeFaces (c, x) := by
    cases c <;> simp [jk, i, Cube.axes, Cube.orientations, mem_cubeFaces_list, cubeFaceList]
  have hb : (ik, x) ∈ cubeFaces (c, x) := by
    cases c <;> simp [ik, Cube.orientations, mem_cubeFaces_list, cubeFaceList]
  have hc : (ij, x + step k) ∈ cubeFaces (c, x) := by
    cases c <;> simp [ij, k, Cube.axes, Cube.orientations, mem_cubeFaces_list, cubeFaceList]
  have hd : (jk, x) ∈ cubeFaces (c, x) := by
    cases c <;> simp [jk, Cube.orientations, mem_cubeFaces_list, cubeFaceList]
  have he : (ik, x + step j) ∈ cubeFaces (c, x) := by
    cases c <;> simp [ik, j, Cube.axes, Cube.orientations, mem_cubeFaces_list, cubeFaceList]
  have hf : (ij, x) ∈ cubeFaces (c, x) := by
    cases c <;> simp [ij, Cube.orientations, mem_cubeFaces_list, cubeFaceList]
  have hprod : A * B * C * D⁻¹ * E⁻¹ * F⁻¹ = 1 := by
    have hp := transportedCubeProduct_eq_one U c x
    change A * B * C * D⁻¹ * (U j x * (P ik (x + step j))⁻¹ * (U j x)⁻¹) * F⁻¹ = 1 at hp
    have heq : E⁻¹ = U j x * (P ik (x + step j))⁻¹ * (U j x)⁻¹ := by
      simp only [E, mul_inv_rev, inv_inv, mul_assoc]
    rw [heq]
    exact hp
  have hga : ¬ badUnitary A :=
    goodUnitary_conj (U i x) (U := P jk (x + step i)) (hgood (jk, x + step i) ha)
  have hgb : ¬ badUnitary B := hgood (ik, x) hb
  have hgc : ¬ badUnitary C :=
    goodUnitary_conj (U k x) (U := P ij (x + step k)) (hgood (ij, x + step k) hc)
  have hgd : ¬ badUnitary D := hgood (jk, x) hd
  have hge : ¬ badUnitary E :=
    goodUnitary_conj (U j x) (U := P ik (x + step j)) (hgood (ik, x + step j) he)
  have hgf : ¬ badUnitary F := hgood (ij, x) hf
  have hs := six_good_factors_phase A B C D E F hga hgb hgc hgd hge hgf hprod
  simp only [A, B, C, D, E, F, principalAngleSum_conj] at hs
  have hform : d₂ a c x =
      (a jk (x + step i) - a jk x) - (a ik (x + step j) - a ik x) +
        (a ij (x + step k) - a ij x) := by cases c <;> rfl
  have hz : d₂ a c x = 0 := by
    rw [hform, hlift jk (x + step i) ha, hlift jk x hd, hlift ik (x + step j) he,
      hlift ik x hb, hlift ij (x + step k) hc, hlift ij x hf]
    change principalAngleSum (P jk (x + step i)) - principalAngleSum (P jk x) -
      (principalAngleSum (P ik (x + step j)) - principalAngleSum (P ik x)) +
      (principalAngleSum (P ij (x + step k)) - principalAngleSum (P ij x)) = 0
    linarith only [hs]
  change |d₂ a c x| < 2 * Real.pi
  simpa [hz] using Real.two_pi_pos

/-- Every cube with a nonzero defect has a bad face, uniformly over the
allowed cuts. -/
theorem has_bad_face_of_nonzero_defect {N : ℕ} (U : InfiniteConfig N)
    (η : TwoForm ℝ) (e : DualEdge) (hη : ∀ p ∈ cubeFaces e, |η p.1 p.2| ≤ Real.pi / 16)
    (hq : defect (liftFlux η (plaquetteEigenangles (fun i x => U (i, x)))) e.1 e.2 ≠ 0) :
    ∃ p ∈ cubeFaces e, U ∈ badPlaquette p := by
  classical
  by_contra! h
  exact hq (plaquetteDefect_eq_zero_on_goodCube (fun i x => U (i, x)) η e.1 e.2 hη h)

end GaplessYangMills

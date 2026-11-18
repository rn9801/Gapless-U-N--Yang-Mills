module

public import GaplessYangMills.DefectBounds
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Eigenangles of the fundamental plaquette matrix

The characteristic roots retain multiplicities. The unitary spectrum lies on
the circle, so their principal angles lift the determinant.
-/

@[expose] public section

namespace GaplessYangMills

open scoped Matrix.Norms.L2Operator

noncomputable section

def characteristicRoots {N : ℕ} (U : UnitaryMatrix N) : List ℂ :=
  U.val.charpoly.roots.toList

theorem characteristicRoots_length {N : ℕ} (U : UnitaryMatrix N) :
    (characteristicRoots U).length = N := by
  rw [characteristicRoots, Multiset.length_toList,
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim]
  exact Fintype.card_fin N

def unitaryRoot {N : ℕ} (U : UnitaryMatrix N) (j : Fin N) : ℂ :=
  (characteristicRoots U).get (Fin.cast (characteristicRoots_length U).symm j)

theorem norm_charpoly_root {N : ℕ} (U : UnitaryMatrix N) {z : ℂ}
    (hz : z ∈ U.val.charpoly.roots) : ‖z‖ = 1 :=
  spectrum.norm_eq_one_of_unitary U.property <|
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (Polynomial.isRoot_of_mem_roots hz)

theorem unitaryRoot_norm {N : ℕ} (U : UnitaryMatrix N) (j : Fin N) :
    ‖unitaryRoot U j‖ = 1 := by
  exact norm_charpoly_root U (Multiset.mem_toList.mp (List.get_mem _ _))

def unitaryEigenvalue {N : ℕ} (U : UnitaryMatrix N) (j : Fin N) : Circle :=
  ⟨unitaryRoot U j, mem_sphere_zero_iff_norm.mpr (unitaryRoot_norm U j)⟩

private theorem list_prod_cast {M : Type*} [CommMonoid M] (l : List M) {n : ℕ}
    (h : l.length = n) : (∏ j : Fin n, l.get (Fin.cast h.symm j)) = l.prod := by
  subst n
  exact Fin.prod_univ_getElem l

theorem prod_unitaryEigenvalue {N : ℕ} (U : UnitaryMatrix N) :
    (∏ j, unitaryEigenvalue U j) = unitaryDet N U := by
  apply Circle.ext
  change Circle.coeHom (∏ j, unitaryEigenvalue U j) = U.val.det
  rw [map_prod, Matrix.det_eq_prod_roots_charpoly]
  change (∏ j : Fin N, (characteristicRoots U).get
    (Fin.cast (characteristicRoots_length U).symm j)) = U.val.charpoly.roots.prod
  rw [list_prod_cast _ (characteristicRoots_length U)]
  exact congrArg Multiset.prod (Multiset.coe_toList _)

def plaquetteEigenangles {N : ℕ} (U : OneForm (UnitaryMatrix N)) : Angles N :=
  fun I x j => Complex.arg (unitaryEigenvalue (plaquetteHolonomy U I x) j : ℂ)

theorem prod_exp_plaquetteEigenangles {N : ℕ} (U : OneForm (UnitaryMatrix N))
    (I : Face) (x : Site) :
    (∏ j, Circle.exp (plaquetteEigenangles U I x j)) =
      unitaryDet N (plaquetteHolonomy U I x) := by
  simpa only [plaquetteEigenangles, Circle.exp_arg] using
    prod_unitaryEigenvalue (plaquetteHolonomy U I x)

/-- The determinant identity is available for the actual characteristic-root
lift of any link configuration. -/
theorem plaquetteDefect_closed {N : ℕ} (U : OneForm (UnitaryMatrix N)) (η : TwoForm ℝ) :
    d₃ (defect (liftFlux η (plaquetteEigenangles U))) = 0 :=
  defect_closed _ (unitary_liftFlux_exp_closed U η _ (prod_exp_plaquetteEigenangles U))

theorem charpoly_smul_eq_scaleRoots {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    {z : ℂ} (hz : z ≠ 0) :
    (z • U).charpoly = U.charpoly.scaleRoots z := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hall : {t : ℂ | Polynomial.eval t (z • U).charpoly =
      Polynomial.eval t (U.charpoly.scaleRoots z)} = Set.univ := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    obtain ⟨r, rfl⟩ : ∃ r : ℂ, z * r = t := ⟨t / z, by field_simp⟩
    rw [Polynomial.scaleRoots_eval_mul, Matrix.eval_charpoly, Matrix.eval_charpoly,
      Matrix.charpoly_natDegree_eq_dim]
    have hmat : Matrix.scalar (Fin N) (z * r) - z • U =
        z • (Matrix.scalar (Fin N) r - U) := by
      rw [smul_sub]
      congr 1
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij, smul_eq_mul]
    rw [hmat, Matrix.det_smul]
  rw [hall]
  exact Set.infinite_univ

theorem characteristicRoots_centralPhase {N : ℕ} (U : UnitaryMatrix N) (z : Circle) :
    ((centralPhase N z * U).val.charpoly.roots) =
      U.val.charpoly.roots.map (fun w => (z : ℂ) * w) := by
  have hmat : (centralPhase N z * U).val = (z : ℂ) • U.val := by
    change ((z : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) * U.val = _
    rw [smul_mul_assoc, one_mul]
  rw [hmat, charpoly_smul_eq_scaleRoots U.val z.coe_ne_zero,
    Polynomial.roots_scaleRoots _ (isUnit_iff_ne_zero.mpr z.coe_ne_zero)]


/-- The total of the lifted angles depends on the multiset of eigenvalues. -/
def eigenAngleLift {N : ℕ} (U : UnitaryMatrix N) (η : ℝ) : ℝ :=
  (U.val.charpoly.roots.map (fun z => liftAngle η (Complex.arg z))).sum

private theorem list_sum_map_cast {R D : Type*} [AddCommMonoid R] (l : List D) {n : ℕ}
    (h : l.length = n) (g : D → R) :
    (∑ j : Fin n, g (l.get (Fin.cast h.symm j))) = (l.map g).sum := by
  subst n
  rw [← Fin.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map l g)

theorem liftFlux_eq_eigenAngleLift {N : ℕ} (U : OneForm (UnitaryMatrix N))
    (η : TwoForm ℝ) (I : Face) (x : Site) :
    liftFlux η (plaquetteEigenangles U) I x =
      eigenAngleLift (plaquetteHolonomy U I x) (η I x) := by
  let P := plaquetteHolonomy U I x
  let g : ℂ → ℝ := fun z => liftAngle (η I x) (Complex.arg z)
  change (∑ j : Fin N, g ((characteristicRoots P).get
    (Fin.cast (characteristicRoots_length P).symm j))) = (P.val.charpoly.roots.map g).sum
  rw [list_sum_map_cast _ (characteristicRoots_length P)]
  exact congrArg (fun v : Multiset ℂ => (v.map g).sum) (Multiset.coe_toList _)

private theorem liftAngle_exp_congr {η θ φ : ℝ} (h : Circle.exp θ = Circle.exp φ) :
    liftAngle η θ = liftAngle η φ := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  rw [hm, liftAngle, liftAngle, toIocMod_add_intCast_mul]

theorem eigenAngleLift_centralPhase {N : ℕ} (U : UnitaryMatrix N) (η t : ℝ) :
    eigenAngleLift (centralPhase N (Circle.exp t) * U) η =
      eigenAngleLift U (η - t) + (N : ℝ) * t := by
  have hangle (w : ℂ) (hw : w ∈ U.val.charpoly.roots) :
      liftAngle η (Complex.arg ((Circle.exp t : ℂ) * w)) =
      liftAngle (η - t) (Complex.arg w) + t := by
    let z : Circle := ⟨w, mem_sphere_zero_iff_norm.mpr (norm_charpoly_root U hw)⟩
    have hangleExp : Circle.exp (Complex.arg ((Circle.exp t : ℂ) * w)) =
        Circle.exp (Complex.arg w + t) := by
      change Circle.exp (Complex.arg (((Circle.exp t) * z : Circle) : ℂ)) =
        Circle.exp (Complex.arg (z : ℂ) + t)
      rw [Circle.exp_arg, Circle.exp_add, Circle.exp_arg, mul_comm]
    rw [liftAngle_exp_congr hangleExp, liftAngle_shift]
  have hcard : U.val.charpoly.roots.card = N := by
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  unfold eigenAngleLift
  rw [characteristicRoots_centralPhase, Multiset.map_map]
  dsimp only [Function.comp_def]
  rw [Multiset.map_congr rfl hangle, Multiset.sum_map_add]
  simp [hcard, nsmul_eq_mul]

/-- The central link rotation gives the exact shift of the actual plaquette
lift, with multiplicities taken from the characteristic polynomial. -/
theorem liftFlux_central_links {N : ℕ} (hN : 0 < N) (U : OneForm (UnitaryMatrix N))
    (α : OneForm ℝ) (η : TwoForm ℝ) :
    liftFlux η (plaquetteEigenangles (fun i x =>
        centralPhase N (Circle.exp (α i x / N)) * U i x)) =
      liftFlux (shiftCuts η (d₁ α) N) (plaquetteEigenangles U) + d₁ α := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext I x
  simp only [Pi.add_apply, liftFlux_eq_eigenAngleLift]
  rw [plaquetteHolonomy_central, eigenAngleLift_centralPhase]
  have hscale : d₁ (fun i y => α i y / N) I x = d₁ α I x / N := by
    cases I <;> simp only [d₁, diff, Pi.sub_apply] <;> ring
  rw [hscale, mul_div_cancel₀ _ hn]
  rfl

theorem repairFlux_central_links {N : ℕ} (hN : 0 < N) (U : OneForm (UnitaryMatrix N))
    (α : OneForm ℝ) (η : TwoForm ℝ) (fill : ThreeForm ℤ → TwoForm ℤ) :
    repairFlux fill (liftFlux η (plaquetteEigenangles (fun i x =>
        centralPhase N (Circle.exp (α i x / N)) * U i x))) =
      repairFlux fill (liftFlux (shiftCuts η (d₁ α) N) (plaquetteEigenangles U)) + d₁ α := by
  rw [liftFlux_central_links hN]
  exact repairFlux_add_closed fill _ _ (d₂_d₁ α)

end

end GaplessYangMills

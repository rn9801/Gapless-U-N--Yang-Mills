module

public import GaplessYangMills.Wilson
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The central quotient of the unitary group

Multiplication of a special unitary matrix by a unit phase gives the
quotient presentation of U(N). Its kernel is the group of complex
N-th roots of unity. Central phases cancel in the adjoint action,
while the single-face Wilson trace retains the phase.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

abbrev SpecialUnitaryMatrix (N : ℕ) := Matrix.specialUnitaryGroup (Fin N) ℂ

def specialUnitaryEmbed (N : ℕ) : SpecialUnitaryMatrix N →* UnitaryMatrix N :=
  Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup

theorem specialUnitaryEmbed_injective (N : ℕ) : Function.Injective (specialUnitaryEmbed N) := by
  intro A B h
  exact Subtype.ext (congrArg (fun U : UnitaryMatrix N => U.val) h)

def scalarUnitary (N : ℕ) : Circle →* UnitaryMatrix N where
  toFun z := ⟨(z : ℂ) • 1, Matrix.mem_unitaryGroup_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.one_mul, smul_smul, Complex.star_def, Complex.mul_conj,
      Circle.normSq_coe, Complex.ofReal_one, one_smul])⟩
  map_one' := Subtype.ext (by change (1 : ℂ) • _ = _; simp)
  map_mul' z w := Subtype.ext (by
    change ((z : ℂ) * (w : ℂ)) • 1 = ((z : ℂ) • 1) * ((w : ℂ) • 1)
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul])

theorem scalarUnitary_commute {N : ℕ} (z : Circle) (U : UnitaryMatrix N) :
    Commute (scalarUnitary N z) U := by
  apply Subtype.ext
  change ((z : ℂ) • 1) * U.val = U.val * ((z : ℂ) • 1)
  simp

theorem unitaryDet_scalarUnitary {N : ℕ} (z : Circle) :
    unitaryDet N (scalarUnitary N z) = z ^ N := by
  apply Circle.ext
  change ((z : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).det = (z : ℂ) ^ N
  rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]

def unitaryProduct (N : ℕ) : SpecialUnitaryMatrix N × Circle →* UnitaryMatrix N where
  toFun p := scalarUnitary N p.2 * specialUnitaryEmbed N p.1
  map_one' := by change scalarUnitary N 1 * specialUnitaryEmbed N 1 = 1; simp
  map_mul' A B := by
    change scalarUnitary N (A.2 * B.2) * specialUnitaryEmbed N (A.1 * B.1) =
      (scalarUnitary N A.2 * specialUnitaryEmbed N A.1) *
        (scalarUnitary N B.2 * specialUnitaryEmbed N B.1)
    simp only [map_mul, mul_assoc]
    rw [← mul_assoc (scalarUnitary N B.2) (specialUnitaryEmbed N A.1),
      (scalarUnitary_commute B.2 (specialUnitaryEmbed N A.1)).eq, mul_assoc]

theorem unitaryProduct_val {N : ℕ} (S : SpecialUnitaryMatrix N) (z : Circle) :
    (unitaryProduct N (S, z)).val = (z : ℂ) • S.val := by
  change ((z : ℂ) • 1) * S.val = (z : ℂ) • S.val
  simp

theorem unitaryDet_unitaryProduct {N : ℕ} (S : SpecialUnitaryMatrix N) (z : Circle) :
    unitaryDet N (unitaryProduct N (S, z)) = z ^ N := by
  apply Circle.ext
  change (unitaryProduct N (S, z)).val.det = (z : ℂ) ^ N
  have hS : S.val.det = 1 := S.property.2
  rw [unitaryProduct_val, Matrix.det_smul, Fintype.card_fin, hS, mul_one]

theorem unitaryProduct_surjective {N : ℕ} (hN : 0 < N) :
    Function.Surjective (unitaryProduct N) := by
  intro U
  let d := unitaryDet N U
  let z := Circle.exp (Complex.arg d / N)
  have hN₀ : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hz : z ^ N = d := by
    change Circle.exp (Complex.arg d / N) ^ N = d
    rw [← Circle.exp_natCast_mul, mul_div_cancel₀ _ hN₀, Circle.exp_arg]
  let V := (scalarUnitary N z)⁻¹ * U
  have hV : unitaryDet N V = 1 := by
    change unitaryDet N ((scalarUnitary N z)⁻¹ * U) = 1
    rw [map_mul, map_inv, unitaryDet_scalarUnitary, hz]
    exact inv_mul_cancel d
  let S : SpecialUnitaryMatrix N := ⟨V.val, V.property, congrArg (fun w : Circle => (w : ℂ)) hV⟩
  refine ⟨(S, z), ?_⟩
  change scalarUnitary N z * ((scalarUnitary N z)⁻¹ * U) = U
  rw [← mul_assoc, mul_inv_cancel, one_mul]

theorem unitaryProduct_kernel_phase {N : ℕ} (x : (unitaryProduct N).ker) : x.val.2 ^ N = 1 := by
  have h := congrArg (unitaryDet N) (MonoidHom.mem_ker.mp x.property)
  rw [map_one] at h
  exact (unitaryDet_unitaryProduct x.val.1 x.val.2).symm.trans h

def unitaryProductKernelEquivRoots {N : ℕ} (hN : 0 < N) :
    (unitaryProduct N).ker ≃* rootsOfUnity N ℂ := by
  let : NeZero N := ⟨hN.ne'⟩
  let f : (unitaryProduct N).ker →* rootsOfUnity N ℂ :=
    { toFun := fun x => ⟨Circle.toUnits x.val.2, (_root_.mem_rootsOfUnity N _).mpr
        (by rw [← map_pow, unitaryProduct_kernel_phase x, map_one])⟩
      map_one' := Subtype.ext (Circle.toUnits.map_one)
      map_mul' := fun x y => Subtype.ext (Circle.toUnits.map_mul x.val.2 y.val.2) }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    have hz : x.val.2 = y.val.2 := Circle.ext (congrArg
      (fun ζ : rootsOfUnity N ℂ => ((ζ.val : ℂˣ) : ℂ)) h)
    have hx := MonoidHom.mem_ker.mp x.property
    have hy := MonoidHom.mem_ker.mp y.property
    apply Subtype.ext
    refine Prod.ext ?_ hz
    apply specialUnitaryEmbed_injective N
    apply mul_left_cancel (a := scalarUnitary N x.val.2)
    change unitaryProduct N x.val = scalarUnitary N x.val.2 * specialUnitaryEmbed N y.val.1
    rw [hx, hz]
    exact hy.symm
  · intro ζ
    let z : Circle := ⟨(ζ.val : ℂ), mem_sphere_zero_iff_norm.mpr
      (Complex.norm_eq_one_of_mem_rootsOfUnity ζ.property)⟩
    have hz : z ^ N = 1 := Circle.ext ((_root_.mem_rootsOfUnity' N ζ.val).mp ζ.property)
    let V := (scalarUnitary N z)⁻¹
    have hV : unitaryDet N V = 1 := by
      change unitaryDet N ((scalarUnitary N z)⁻¹) = 1
      rw [map_inv, unitaryDet_scalarUnitary, hz, inv_one]
    let S : SpecialUnitaryMatrix N := ⟨V.val, V.property, congrArg (fun w : Circle => (w : ℂ)) hV⟩
    have hk : (S, z) ∈ (unitaryProduct N).ker := MonoidHom.mem_ker.mpr (mul_inv_cancel _)
    refine ⟨⟨(S, z), hk⟩, Subtype.ext (Units.ext ?_)⟩
    rfl

/-- The quotient of SU(N) × U(1) by its diagonal cyclic kernel. -/
def unitaryProductQuotient {N : ℕ} (hN : 0 < N) :
    (SpecialUnitaryMatrix N × Circle) ⧸ (unitaryProduct N).ker ≃* UnitaryMatrix N :=
  QuotientGroup.quotientKerEquivOfSurjective (unitaryProduct N) (unitaryProduct_surjective hN)

theorem unitaryProduct_kernel_card {N : ℕ} (hN : 0 < N) :
    Nat.card (unitaryProduct N).ker = N := by
  let : NeZero N := ⟨hN.ne'⟩
  exact (Nat.card_congr (unitaryProductKernelEquivRoots hN).toEquiv).trans (Complex.card_rootsOfUnity N)

theorem unitaryProduct_kernel_isCyclic {N : ℕ} (hN : 0 < N) : IsCyclic (unitaryProduct N).ker := by
  let : NeZero N := ⟨hN.ne'⟩
  exact (unitaryProductKernelEquivRoots hN).isCyclic.mpr inferInstance

theorem unitaryProduct_curvature_conj {N : ℕ} (S : SpecialUnitaryMatrix N) (z : Circle)
    (F : Matrix (Fin N) (Fin N) ℂ) :
    (unitaryProduct N (S, z)).val * F * ((unitaryProduct N (S, z))⁻¹).val =
      S.val * F * ((specialUnitaryEmbed N S)⁻¹).val := by
  change ((scalarUnitary N z * specialUnitaryEmbed N S).val) * F *
    ((scalarUnitary N z * specialUnitaryEmbed N S)⁻¹).val = _
  rw [mul_inv_rev, ← map_inv (scalarUnitary N)]
  change (((z : ℂ) • 1) * S.val) * F * (((specialUnitaryEmbed N S)⁻¹).val * ((z⁻¹ : Circle) : ℂ) • 1) = _
  simp [smul_smul, Circle.coe_inv, Circle.coe_ne_zero]

theorem unitaryCurvature_trace_conj {N : ℕ} (U : UnitaryMatrix N) (F : Matrix (Fin N) (Fin N) ℂ) :
    (U.val * F * (U⁻¹).val).trace = F.trace := by
  have hu : (U⁻¹).val * U.val = 1 :=
    congrArg (fun V : UnitaryMatrix N => V.val) (inv_mul_cancel U)
  rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul]

theorem unitaryProduct_wilson_trace {N : ℕ} (S : SpecialUnitaryMatrix N) (z : Circle) :
    (unitaryProduct N (S, z)).val.trace.re = ((z : ℂ) * S.val.trace).re := by
  rw [unitaryProduct_val, Matrix.trace_smul, smul_eq_mul]

end

end GaplessYangMills

module

public import GaplessYangMills.TransferForm
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completing a positive reflection form

A positive semidefinite reflection form gives a Hilbert space by
separating its seminorm and completing. A symmetric shift with bounded
orbits and a positive reflected form gives a positive transfer contraction.
-/

@[expose] public section

namespace GaplessYangMills

open UniformSpace
open scoped RealInnerProductSpace

noncomputable section

structure PositiveReflectionForm (E : Type*) [AddCommGroup E] [Module ℝ E] where
  form : LinearMap.BilinForm ℝ E
  symmetric : LinearMap.IsSymm form
  nonnegative : ∀ v, 0 ≤ form v v

namespace PositiveReflectionForm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def FormSpace (_B : PositiveReflectionForm E) : Type _ := E

instance (B : PositiveReflectionForm E) : AddCommGroup B.FormSpace := inferInstanceAs (AddCommGroup E)

instance (B : PositiveReflectionForm E) : Module ℝ B.FormSpace := inferInstanceAs (Module ℝ E)

instance innerCore (B : PositiveReflectionForm E) : PreInnerProductSpace.Core ℝ B.FormSpace where
  inner u v := B.form u v
  conj_inner_symm u v := B.symmetric.eq _ _
  re_inner_nonneg u := B.nonnegative u
  add_left u v w := by
    let f : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := B.form
    let a : E := u
    let b : E := v
    let c : E := w
    change f (a + b) c = f a c + f b c
    rw [f.map_add, LinearMap.add_apply]
  smul_left u v r := by
    let f : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := B.form
    let a : E := u
    let b : E := v
    change f (r • a) b = r * f a b
    rw [f.map_smul, LinearMap.smul_apply, smul_eq_mul]

instance (B : PositiveReflectionForm E) : SeminormedAddCommGroup B.FormSpace :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

instance (B : PositiveReflectionForm E) : InnerProductSpace ℝ B.FormSpace :=
  InnerProductSpace.ofCore B.innerCore

abbrev Hilbert (B : PositiveReflectionForm E) := Completion B.FormSpace

def ofVector (B : PositiveReflectionForm E) (u : E) : B.Hilbert :=
  (show B.FormSpace from u)

@[simp] theorem inner_ofVector (B : PositiveReflectionForm E) (u v : E) :
    ⟪B.ofVector u, B.ofVector v⟫ = B.form u v := by
  calc
    _ = ⟪(show B.FormSpace from u), (show B.FormSpace from v)⟫ :=
      Completion.inner_coe (𝕜 := ℝ) (E := B.FormSpace) u v
    _ = _ := rfl

theorem norm_ofVector (B : PositiveReflectionForm E) (u : E) :
    ‖B.ofVector u‖ = Real.sqrt (B.form u u) := by
  calc
    _ = ‖(show B.FormSpace from u)‖ := Completion.norm_coe (E := B.FormSpace) u
    _ = _ := rfl

theorem ofVector_eq_zero_iff (B : PositiveReflectionForm E) (u : E) :
    B.ofVector u = 0 ↔ B.form u u = 0 := by
  exact norm_eq_zero.symm.trans
    ((congrArg (· = 0) (B.norm_ofVector u)).to_iff.trans (Real.sqrt_eq_zero (B.nonnegative u)))

structure Shift (B : PositiveReflectionForm E) where
  operator : E →ₗ[ℝ] E
  symmetric : ∀ u v, B.form (operator u) v = B.form u (operator v)
  nonnegative : ∀ u, 0 ≤ B.form (operator u) u
  boundedOrbit : ∀ u, ∃ C : ℝ, ∀ n : ℕ, B.form ((operator ^ n) u) ((operator ^ n) u) ≤ C

namespace Shift

variable {B : PositiveReflectionForm E}

theorem contracts (S : B.Shift) (u : E) : B.form (S.operator u) (S.operator u) ≤ B.form u u := by
  obtain ⟨C, hC⟩ := S.boundedOrbit u
  exact reflectionShift_contracts (E := E) B.form B.symmetric B.nonnegative S.operator S.symmetric u C hC

def asContinuous (S : B.Shift) : B.FormSpace →L[ℝ] B.FormSpace :=
  (show B.FormSpace →ₗ[ℝ] B.FormSpace from S.operator).mkContinuous 1 fun u => by
    change Real.sqrt (B.form (S.operator u) (S.operator u)) ≤ 1 * Real.sqrt (B.form u u)
    rw [one_mul]
    exact Real.sqrt_le_sqrt (S.contracts u)

def transfer (S : B.Shift) : B.Hilbert →L[ℝ] B.Hilbert :=
  S.asContinuous.completion

@[simp] theorem transfer_ofVector (S : B.Shift) (u : E) :
    S.transfer (B.ofVector u) = B.ofVector (S.operator u) :=
  S.asContinuous.completion_apply_coe u

theorem transfer_norm_le_one (S : B.Shift) : ‖S.transfer‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  refine Completion.induction_on u (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro v
  let v₀ : E := v
  change ‖S.transfer (B.ofVector v₀)‖ ≤ ‖B.ofVector v₀‖
  simp only [transfer_ofVector, norm_ofVector]
  exact Real.sqrt_le_sqrt (S.contracts v₀)

theorem transfer_symmetric (S : B.Shift) : S.transfer.toLinearMap.IsSymmetric := by
  intro u v
  refine Completion.induction_on₂ u v (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a b
  let a₀ : E := a
  let b₀ : E := b
  change ⟪S.transfer (B.ofVector a₀), B.ofVector b₀⟫ =
    ⟪B.ofVector a₀, S.transfer (B.ofVector b₀)⟫
  simpa only [transfer_ofVector, inner_ofVector] using S.symmetric a₀ b₀

theorem transfer_isSelfAdjoint (S : B.Shift) : IsSelfAdjoint S.transfer :=
  S.transfer_symmetric.isSelfAdjoint

theorem transfer_positive (S : B.Shift) : S.transfer.IsPositive := by
  refine ⟨S.transfer_symmetric, fun u => ?_⟩
  change 0 ≤ ⟪S.transfer u, u⟫
  refine Completion.induction_on u (isClosed_le continuous_const (by fun_prop)) ?_
  intro v
  let v₀ : E := v
  change 0 ≤ ⟪S.transfer (B.ofVector v₀), B.ofVector v₀⟫
  simpa only [transfer_ofVector, inner_ofVector] using S.nonnegative v₀

theorem transfer_pow_ofVector (S : B.Shift) (n : ℕ) (v : E) :
    (S.transfer ^ n) (B.ofVector v) = B.ofVector ((S.operator ^ n) v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, ih, transfer_ofVector]
    rfl

theorem inner_transfer_pow (S : B.Shift) (n : ℕ) (u v : E) :
    ⟪B.ofVector u, (S.transfer ^ n) (B.ofVector v)⟫ = B.form u ((S.operator ^ n) v) := by
  rw [transfer_pow_ofVector, inner_ofVector]

end Shift

end PositiveReflectionForm

end

end GaplessYangMills

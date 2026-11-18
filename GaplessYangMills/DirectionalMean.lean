module

public import GaplessYangMills.Ward
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FinCases

/-!
# Removing directional Cesàro means

Equation (8) follows from equation (7) once the directional means exist.
This step only uses the scalar two-point functions and the mean limits.
-/

@[expose] public section

namespace GaplessYangMills

open Filter
open scoped Topology

noncomputable def averageAlong (i : Axis) (f : Site → ℝ) (n : ℕ) (x : Site) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (x + k • step i)

def HasDirectionalMean (i : Axis) (f g : Site → ℝ) : Prop :=
  ∀ x, Tendsto (fun n => averageAlong i f n x) atTop (𝓝 (g x))

namespace HasDirectionalMean

variable {i : Axis} {f g u v : Site → ℝ}

theorem unique (hf : HasDirectionalMean i f u) (hg : HasDirectionalMean i f v) : u = v := by
  funext x
  exact tendsto_nhds_unique (hf x) (hg x)

theorem zero : HasDirectionalMean i 0 0 := by
  intro x
  simp [averageAlong]

theorem add (hf : HasDirectionalMean i f u) (hg : HasDirectionalMean i g v) :
    HasDirectionalMean i (f + g) (u + v) := by
  intro x
  simpa only [averageAlong, Pi.add_apply, Finset.sum_add_distrib, mul_add] using
    (hf x).add (hg x)

theorem sub (hf : HasDirectionalMean i f u) (hg : HasDirectionalMean i g v) :
    HasDirectionalMean i (f - g) (u - v) := by
  intro x
  simpa only [averageAlong, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub] using
    (hf x).sub (hg x)

theorem neg (hf : HasDirectionalMean i f u) : HasDirectionalMean i (-f) (-u) := by
  simpa only [zero_sub] using zero.sub hf

theorem const_mul (hf : HasDirectionalMean i f u) (a : ℝ) :
    HasDirectionalMean i (fun x => a * f x) (fun x => a * u x) := by
  intro x
  simpa only [averageAlong, Finset.mul_sum, mul_left_comm a] using
    (tendsto_const_nhds (x := a)).mul (hf x)

theorem diff (hf : HasDirectionalMean i f u) (j : Axis) :
    HasDirectionalMean i (GaplessYangMills.diff j f) (GaplessYangMills.diff j u) := by
  intro x
  have hshift (k : ℕ) : x + k • step i + step j = x + step j + k • step i :=
    add_right_comm _ _ _
  simpa only [averageAlong, GaplessYangMills.diff, Finset.sum_sub_distrib, mul_sub, hshift] using
    (hf (x + step j)).sub (hf x)

theorem of_summable (hf : Summable f) : HasDirectionalMean i f 0 := by
  intro x
  have hinj : Function.Injective (fun k : ℕ => x + k • step i) := by
    intro k l h
    simpa [step_same] using congrFun h i
  have hsum := (hf.comp_injective hinj).hasSum.tendsto_sum_nat
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa only [averageAlong, Function.comp_def, zero_mul, Pi.zero_apply] using hinv.mul hsum

end HasDirectionalMean

private theorem mean_d₂ {i : Axis} {F G : TwoForm ℝ} (h : ∀ I, HasDirectionalMean i (F I) (G I))
    (c : Cube) : HasDirectionalMean i (d₂ F c) (d₂ G c) := by
  cases c
  · exact (((h .yz).diff 0).sub ((h .xz).diff 1)).add ((h .xy).diff 2)
  · exact (((h .yw).diff 0).sub ((h .xw).diff 1)).add ((h .xy).diff 3)
  · exact (((h .zw).diff 0).sub ((h .xw).diff 2)).add ((h .xz).diff 3)
  · exact (((h .zw).diff 1).sub ((h .yw).diff 2)).add ((h .yz).diff 3)

private theorem mean_rightDerivative {i : Axis} {K P : Kernel}
    (h : ∀ I J, HasDirectionalMean i (K I J) (P I J)) (I : Face) (j : Axis) :
    HasDirectionalMean i (rightDerivative K I j) (rightDerivative P I j) := by
  fin_cases j
  · exact ((((h I .xy).diff 1).neg).sub ((h I .xz).diff 2)).sub ((h I .xw).diff 3)
  · exact (((h I .xy).diff 0).sub ((h I .yz).diff 2)).sub ((h I .yw).diff 3)
  · exact (((h I .xz).diff 0).add ((h I .yz).diff 1)).sub ((h I .zw).diff 3)
  · exact (((h I .xw).diff 0).add ((h I .yw).diff 1)).add ((h I .zw).diff 2)

/-- Subtracting any one directional mean preserves the response and closedness.
The result can be applied successively in all four directions. -/
theorem ward_subtract_mean (β : ℝ) (K S P : Kernel) (i : Axis)
    (hmean : ∀ I J, HasDirectionalMean i (K I J) (P I J))
    (hclosed : ∀ J, d₂ (fun I => K I J) = 0)
    (hresponse : WardResponse β K S) (hS : ∀ I J, Summable (S I J)) :
    (∀ J, d₂ (fun I => (K - P) I J) = 0) ∧ WardResponse β (K - P) S := by
  constructor
  · intro J
    have hp : d₂ (fun I => P I J) = 0 := by
      funext c
      have hm := mean_d₂ (fun I => hmean I J) c
      rw [hclosed J] at hm
      exact hm.unique HasDirectionalMean.zero
    change d₂ ((fun I => K I J) - (fun I => P I J)) = 0
    rw [d₂_sub, hclosed, hp, sub_zero]
  · let R : Kernel := fun I J x => β * K I J x - (identityKernel I J x + S I J x)
    let B : Kernel := fun I J x => β * P I J x
    have hR (I J : Face) : HasDirectionalMean i (R I J) (B I J) := by
      have hs : HasDirectionalMean i (identityKernel I J + S I J) 0 :=
        HasDirectionalMean.of_summable (((identityKernel_hasSum I J).summable).add (hS I J))
      have hr : R I J = (fun x => β * K I J x) - (identityKernel I J + S I J) := by
        funext x
        simp only [R, Pi.sub_apply, Pi.add_apply]
      rw [hr]
      change HasDirectionalMean i _ (fun x => β * P I J x)
      simpa only [sub_zero] using ((hmean I J).const_mul β).sub hs
    have hB (I : Face) (j : Axis) : rightDerivative B I j = 0 := by
      have hm := mean_rightDerivative hR I j
      have hz : rightDerivative R I j = 0 := congrFun (hresponse I) j
      rw [hz] at hm
      exact hm.unique HasDirectionalMean.zero
    have hkernel : (fun I J x => β * (K - P) I J x - (identityKernel I J x + S I J x)) =
        R - B := by
      funext I J x
      simp only [R, B, Pi.sub_apply, mul_sub]
      abel
    intro I
    rw [hkernel]
    funext j
    have hz : rightDerivative R I j = 0 := congrFun (hresponse I) j
    have hsub : rightDerivative (R - B) I j = rightDerivative R I j - rightDerivative B I j := by
      fin_cases j <;> simp [rightDerivative, diff_sub] <;> abel
    simp only [hsub, hz, hB, sub_zero, Pi.zero_apply]

end GaplessYangMills

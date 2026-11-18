module

public import GaplessYangMills.Marginal
public import Mathlib.Data.Fin.VecNotation

/-!
# The Ward identity obstruction

This is the analytic implication used in Section 5 of the paper. Its hypotheses
are the two kernel identities and the zero-momentum normalization on the response
correction. Transverse summation proves the same incompatibility as the two
directional Fourier limits.
-/

@[expose] public section

namespace GaplessYangMills

abbrev Kernel := Face → Face → Site → ℝ

noncomputable def identityKernel : Kernel := by
  classical
  exact fun I J x => if I = J ∧ x = 0 then 1 else 0

/-- The kernel of convolution on the right by `d₁`, evaluated on a unit test
link at the origin in each of the four directions. -/
def rightDerivative (K : Kernel) (I : Face) : OneForm ℝ :=
  ![-diff 1 (K I .xy) - diff 2 (K I .xz) - diff 3 (K I .xw),
    diff 0 (K I .xy) - diff 2 (K I .yz) - diff 3 (K I .yw),
    diff 0 (K I .xz) + diff 1 (K I .yz) - diff 3 (K I .zw),
    diff 0 (K I .xw) + diff 1 (K I .yw) + diff 2 (K I .zw)]

/-- The response identity `β K d₁ = (I + S) d₁` in displacement coordinates. -/
def WardResponse (β : ℝ) (K S : Kernel) : Prop :=
  ∀ I, rightDerivative (fun I J x => β * K I J x - (identityKernel I J x + S I J x)) I = 0

private theorem three_masses_eq_zero {f g h : Site → ℝ}
    (hf : Summable f) (hg : Summable g) (hh : Summable h)
    {i j k : Axis} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hclosed : diff i f - diff j g + diff k h = 0) :
    (∑' x, f x) = 0 ∧ (∑' x, g x) = 0 ∧ (∑' x, h x) = 0 := by
  have hm (l : Axis) (n : ℤ) :
      marginal l (diff i f) n - marginal l (diff j g) n + marginal l (diff k h) n = 0 := by
    have hfg : Summable (diff i f - diff j g) :=
      (summable_diff hf i).sub (summable_diff hg j)
    rw [← marginal_sub (summable_diff hf i) (summable_diff hg j),
      ← marginal_add hfg (summable_diff hh k)]
    simp [hclosed]
  refine ⟨tsum_eq_zero_of_marginal_diff hf i ?_, tsum_eq_zero_of_marginal_diff hg j ?_,
    tsum_eq_zero_of_marginal_diff hh k ?_⟩
  · intro n
    simpa [marginal_diff_across hg hij.symm, marginal_diff_across hh hik.symm] using hm i n
  · intro n
    simpa [marginal_diff_across hf hij, marginal_diff_across hh hjk.symm] using hm j n
  · intro n
    simpa [marginal_diff_across hf hik, marginal_diff_across hg hjk] using hm k n

/-- Every orientation of a summable closed two-form has zero total flux.
This also applies to the finite-support cut differences in Section 4. -/
theorem tsum_closed_twoForm_eq_zero (F : TwoForm ℝ) (hF : ∀ I, Summable (F I))
    (hclosed : d₂ F = 0) (I : Face) : ∑' x, F I x = 0 := by
  have hxyz := three_masses_eq_zero (hF .yz) (hF .xz) (hF .xy)
    (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide) (congrFun hclosed .xyz)
  have hxyw := three_masses_eq_zero (hF .yw) (hF .xw) (hF .xy)
    (i := 0) (j := 1) (k := 3) (by decide) (by decide) (by decide) (congrFun hclosed .xyw)
  have hxzw := three_masses_eq_zero (hF .zw) (hF .xw) (hF .xz)
    (i := 0) (j := 2) (k := 3) (by decide) (by decide) (by decide) (congrFun hclosed .xzw)
  cases I
  · exact hxyz.2.2
  · exact hxyz.2.1
  · exact hxyw.2.1
  · exact hxyz.1
  · exact hxyw.1
  · exact hxzw.1

theorem identityKernel_hasSum (I J : Face) :
    HasSum (identityKernel I J) (if I = J then 1 else 0) := by
  classical
  by_cases h : I = J
  · have hid : identityKernel I J = (fun x => if x = 0 then 1 else 0) := by
      funext x
      simp [identityKernel, h]
    rw [hid, ite_eq_left h]
    exact hasSum_ite_eq (0 : Site) (1 : ℝ)
  · have hid : identityKernel I J = 0 := by
      funext x
      simp [identityKernel, h]
    rw [hid, ite_eq_right h]
    exact hasSum_zero

/-- No entrywise summable kernel satisfies the closedness and normalized Ward
response of equations (7) or (8). It suffices to assume zero total mass of the
`xy, xy` entry of the correction, as follows from equation (6). -/
theorem not_summable_of_ward (β : ℝ) (K S : Kernel)
    (hclosed : ∀ J, d₂ (fun I => K I J) = 0)
    (hresponse : WardResponse β K S)
    (hS : ∀ I J, Summable (S I J))
    (hnormalize : ∑' x, S .xy .xy x = 0) :
    ¬ (∀ I J, Summable (K I J)) := by
  intro hK
  have hzero := tsum_closed_twoForm_eq_zero (fun I => K I .xy)
    (fun I => hK I .xy) (hclosed .xy) .xy
  let R : Kernel := fun I J x => β * K I J x - (identityKernel I J x + S I J x)
  have hR (J : Face) : Summable (R .xy J) :=
    ((hK .xy J).mul_left β).sub ((identityKernel_hasSum .xy J).summable.add (hS .xy J))
  have hresponseXY : diff 0 (R .xy .xy) - diff 2 (R .xy .yz) - diff 3 (R .xy .yw) = 0 :=
    congrFun (hresponse .xy) (1 : Axis)
  have hmass : ∑' x, R .xy .xy x = 0 := by
    apply tsum_eq_zero_of_marginal_diff (hR .xy) 0
    intro n
    have hs := congrArg (fun f => marginal 0 f n) hresponseXY
    have hdiff : Summable (diff 0 (R .xy .xy) - diff 2 (R .xy .yz)) :=
      (summable_diff (hR .xy) 0).sub (summable_diff (hR .yz) 2)
    rw [marginal_sub hdiff
      (summable_diff (hR .yw) 3), marginal_sub (summable_diff (hR .xy) 0)
      (summable_diff (hR .yz) 2), marginal_diff_across (hR .yz) (by decide),
      marginal_diff_across (hR .yw) (by decide)] at hs
    simpa using hs
  have hsum := (((hK .xy .xy).hasSum.mul_left β).sub
    ((identityKernel_hasSum .xy .xy).add (hS .xy .xy).hasSum)).tsum_eq
  have hneg : (∑' x, R .xy .xy x) = -1 := by
    simpa [hzero, hnormalize] using hsum
  exact (neg_ne_zero.mpr one_ne_zero) (hneg.symm.trans hmass)

end GaplessYangMills

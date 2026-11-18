module

public import GaplessYangMills.BadEvents
public import GaplessYangMills.UnitaryLog
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurability of the cut flux

On the open set without the eigenvalue minus one, the principal angle sum
is the trace of the continuous Hermitian logarithm. A small downward
rotation approximates the angle sum from the side specified by the
half-open branch convention, including at the cut.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology

noncomputable section

private theorem eigenAngleLift_zero {N : ℕ} (U : UnitaryMatrix N) :
    eigenAngleLift U 0 = principalAngleSum U := by
  unfold eigenAngleLift principalAngleSum
  congr 1
  apply Multiset.map_congr rfl
  intro z _
  unfold liftAngle
  refine (toIocMod_eq_self Real.two_pi_pos).mpr ⟨?_, ?_⟩
  · simpa using Complex.neg_pi_lt_arg z
  · linarith [Complex.arg_le_pi z]

private theorem exists_angle_margin {N : ℕ} (U : UnitaryMatrix N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ U.val.charpoly.roots, δ ≤ Complex.arg z + Real.pi := by
  classical
  let S := U.val.charpoly.roots.toFinset
  by_cases hS : S.Nonempty
  · let d := S.inf' hS (fun z => Complex.arg z + Real.pi)
    obtain ⟨z, _, hz⟩ := Finset.exists_mem_eq_inf' hS (fun z => Complex.arg z + Real.pi)
    have hpos : 0 < d := by
      change 0 < S.inf' hS (fun z => Complex.arg z + Real.pi)
      rw [hz]
      linarith [Complex.neg_pi_lt_arg z]
    exact ⟨d, hpos, fun z hz => Finset.inf'_le _ (Multiset.mem_toFinset.mpr hz)⟩
  · refine ⟨1, by norm_num, fun z hz => ?_⟩
    exact (hS ⟨z, Multiset.mem_toFinset.mpr hz⟩).elim

private theorem rotate_down_angleSum {N : ℕ} (U : UnitaryMatrix N) (δ : ℝ)
    (hδ : ∀ z ∈ U.val.charpoly.roots, δ ≤ Complex.arg z + Real.pi)
    {t : ℝ} (ht : 0 < t) (htt : t < δ) :
    let V := centralPhase N (Circle.exp (-t)) * U
    ‖V.val - 1‖ < 2 ∧ principalAngleSum V = principalAngleSum U - (N : ℝ) * t := by
  let V := centralPhase N (Circle.exp (-t)) * U
  have hgood (z : ℂ) (hz : z ∈ U.val.charpoly.roots) :
      -Real.pi < Complex.arg z - t ∧ Complex.arg z - t < Real.pi := by
    exact ⟨by linarith [hδ z hz], by linarith [Complex.arg_le_pi z]⟩
  have hV : ‖V.val - 1‖ < 2 := by
    apply (Unitary.norm_sub_one_lt_two_iff V.property).mpr
    intro hz
    have hm : (-1 : ℂ) ∈ V.val.charpoly.roots :=
      (Polynomial.mem_roots V.val.charpoly_monic.ne_zero).mpr
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz)
    change (-1 : ℂ) ∈ (centralPhase N (Circle.exp (-t)) * U).val.charpoly.roots at hm
    rw [characteristicRoots_centralPhase] at hm
    obtain ⟨z, hz, heq⟩ := Multiset.mem_map.mp hm
    let w : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr (norm_charpoly_root U hz)⟩
    have he : Circle.exp (Complex.arg z - t) = Circle.exp (-t) * w := by
      change Circle.exp (Complex.arg (w : ℂ) + -t) = _
      rw [Circle.exp_add, Circle.exp_arg, mul_comm]
    have he' : (Circle.exp (Complex.arg z - t) : ℂ) = -1 := by
      rw [he]
      exact heq
    have ha := Circle.arg_exp (hgood z hz).1 (hgood z hz).2.le
    rw [he', Complex.arg_neg_one] at ha
    linarith [(hgood z hz).2]
  have hlift : eigenAngleLift U t = principalAngleSum U := by
    unfold eigenAngleLift principalAngleSum
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    unfold liftAngle
    exact (toIocMod_eq_self Real.two_pi_pos).mpr ⟨by linarith [(hgood z hz).1],
      by linarith [Complex.arg_le_pi z]⟩
  refine ⟨hV, ?_⟩
  have he := eigenAngleLift_centralPhase U 0 (-t)
  simp only [eigenAngleLift_zero, zero_sub, neg_neg, hlift, mul_neg, ← sub_eq_add_neg] at he
  exact he

theorem measurable_principalAngleSum (N : ℕ) : Measurable (principalAngleSum (N := N)) := by
  classical
  let s := Metric.ball (1 : UnitaryMatrix N) 2
  let traceLog := fun V : UnitaryMatrix N => phaseTrace (Unitary.argSelfAdjoint V)
  let g := s.piecewise traceLog (fun _ => (0 : ℝ))
  have hg : Measurable g := ContinuousOn.measurable_piecewise
    ((continuous_phaseTrace N).comp_continuousOn Unitary.continuousOn_argSelfAdjoint)
    continuous_const.continuousOn Metric.isOpen_ball.measurableSet
  let t (n : ℕ) := (1 : ℝ) / (n + 1)
  let f (n : ℕ) (U : UnitaryMatrix N) := g (centralPhase N (Circle.exp (-t n)) * U)
  apply measurable_of_tendsto_metrizable (f := f)
    (fun n => hg.comp (continuous_const.mul continuous_id).measurable)
  rw [tendsto_pi_nhds]
  intro U
  obtain ⟨δ, hδ, hm⟩ := exists_angle_margin U
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have he : (fun n => f n U) =ᶠ[atTop] fun n => principalAngleSum U - (N : ℝ) * t n := by
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn
    let V := centralPhase N (Circle.exp (-t n)) * U
    obtain ⟨hV, hVsum⟩ := rotate_down_angleSum U δ hm (show 0 < t n by dsimp [t]; positivity) hn
    have hv : V ∈ s := by
      change dist V 1 < 2
      rw [Subtype.dist_eq, dist_eq_norm]
      exact hV
    change s.piecewise traceLog (fun _ => 0) V = _
    rw [Set.piecewise_eq_of_mem _ _ _ hv]
    exact (principalAngleSum_eq_phaseTrace_arg V hV).symm.trans hVsum
  have hconst : Tendsto (fun _ : ℕ => (N : ℝ)) atTop (𝓝 (N : ℝ)) := tendsto_const_nhds
  have hlim := (tendsto_const_nhds (x := principalAngleSum U)).sub (hconst.mul ht)
  simpa only [mul_zero, sub_zero] using hlim.congr' he.symm

theorem measurable_eigenAngleLift (N : ℕ) :
    Measurable (fun p : UnitaryMatrix N × ℝ => eigenAngleLift p.1 p.2) := by
  have hc : Continuous (centralPhase N) := by
    have h : Continuous (fun z : Circle => (z : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) :=
      continuous_subtype_val.smul continuous_const
    exact h.subtype_mk _
  have hshift : Continuous (fun p : UnitaryMatrix N × ℝ =>
      centralPhase N (Circle.exp (-p.2)) * p.1) :=
    (hc.comp (Circle.exp.continuous.comp continuous_snd.neg)).mul continuous_fst
  have he (p : UnitaryMatrix N × ℝ) : eigenAngleLift p.1 p.2 =
      principalAngleSum (centralPhase N (Circle.exp (-p.2)) * p.1) + (N : ℝ) * p.2 := by
    have h := eigenAngleLift_centralPhase p.1 0 (-p.2)
    simp only [eigenAngleLift_zero, zero_sub, neg_neg, mul_neg] at h
    linarith
  simp_rw [he]
  exact ((measurable_principalAngleSum N).comp hshift.measurable).add
    (measurable_const.mul measurable_snd)

set_option maxHeartbeats 600000 in
theorem measurable_cutFlux_coordinate {N : ℕ} (I : Face) (x : Site) :
    Measurable (fun p : InfiniteConfig N × TwoForm ℝ =>
      liftFlux p.2 (plaquetteEigenangles (fun i y => p.1 (i, y))) I x) := by
  simp_rw [liftFlux_eq_eigenAngleLift]
  let X := InfiniteConfig N × TwoForm ℝ
  have hfst : Measurable (Prod.fst : X → InfiniteConfig N) := measurable_fst
  have hP : Measurable (fun p : X => plaquetteHolonomy (fun i y => p.1 (i, y)) I x) := by
    simpa only [Function.comp_def] using
      (continuous_plaquetteHolonomy (N := N) (I, x)).measurable.comp hfst
  have hI : Measurable (fun f : TwoForm ℝ => f I) := measurable_pi_apply I
  have hx : Measurable (fun f : Site → ℝ => f x) := measurable_pi_apply x
  have hη : Measurable (fun p : X => p.2 I x) := hx.comp (hI.comp measurable_snd)
  simpa only [Function.comp_def] using (measurable_eigenAngleLift N).comp (hP.prodMk hη)

theorem measurable_cutDefect_coordinate {N : ℕ} (c : Cube) (x : Site) :
    Measurable (fun p : InfiniteConfig N × TwoForm ℝ =>
      defect (liftFlux p.2 (plaquetteEigenangles (fun i y => p.1 (i, y)))) c x) := by
  apply Int.measurable_ceil.comp
  apply Measurable.div_const
  have hd (i : Axis) (I : Face) :
      Measurable (fun p : InfiniteConfig N × TwoForm ℝ =>
        diff i (liftFlux p.2 (plaquetteEigenangles (fun j y => p.1 (j, y))) I) x) :=
    (measurable_cutFlux_coordinate I (x + step i)).sub (measurable_cutFlux_coordinate I x)
  cases c <;> exact ((hd _ _).sub (hd _ _)).add (hd _ _)

end

end GaplessYangMills

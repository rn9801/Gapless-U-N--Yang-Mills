module

public import GaplessYangMills.CutFluxApproximation
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Square-integrable tails of the cut repair

A finite current component contributes only on the event that all its
edges are marked. The mass bound for the filling and the number of
possible component boxes give a summable square-integrable estimate.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory SimpleGraph
open scoped ENNReal Topology

noncomputable section

private theorem natAbs_le_chainMass {E : Type*} (q : E →₀ ℤ) (e : E) :
    (q e).natAbs ≤ chainMass q := by
  classical
  by_cases he : e ∈ q.support
  · exact Finset.single_le_sum (f := fun j => (q j).natAbs) (fun _ _ => Nat.zero_le _) he
  · simp [Finsupp.notMem_support_iff.mp he]

private theorem boxWidth_le_of_connected
    (r : EdgeChain) (S : Finset OrientedEdge) (hrS : r.support ⊆ S)
    (hconn : ∃ e ∈ S, ∀ f ∈ S, ∃ w : dualEdgeGraph.Walk e f, ∀ g ∈ w.support, g ∈ S) :
    boxWidth (edgeChainLower r) (edgeChainUpper r) ≤ 4 * (4 * S.card + 1) := by
  classical
  by_cases hr : r.support.Nonempty
  · obtain ⟨e, he, h⟩ := hconn
    obtain ⟨p, hp, hlen⟩ := exists_closedWalk_with_support dualEdgeGraph S he h
    unfold boxWidth
    calc
      _ ≤ ∑ _i : Axis, (4 * S.card + 1 : ℕ) := by
        apply Finset.sum_le_sum
        intro i _
        obtain ⟨a, ha, hmin⟩ := Finset.exists_mem_eq_inf' hr (fun f => f.1 i)
        obtain ⟨b, hb, hmax⟩ := Finset.exists_mem_eq_sup' hr (fun f => (f.1 + step f.2) i)
        have ha' : a ∈ p.support := List.mem_toFinset.mp (hp.symm ▸ hrS ha)
        have hb' : b ∈ p.support := List.mem_toFinset.mp (hp.symm ▸ hrS hb)
        have hlo := (walk_coordinate_bounds p ha' i).1
        have hhi := (walk_coordinate_bounds p hb' i).2
        rw [edgeChainLower, edgeChainUpper, dite_eq_left hr, dite_eq_left hr, hmin, hmax]
        simp only [Pi.add_apply, step]
        split <;> omega
      _ = _ := by simp
  · simp [edgeChainLower, edgeChainUpper, hr, boxWidth]

theorem natAbs_certifiedFillValue_le (q : OrientedEdge → ℤ) (S : Finset OrientedEdge)
    (I : Face) (x : Site) (hdiv : ∀ y, currentDivergence q y = 0)
    (B : ℕ) (hB : ∀ e, (q e).natAbs ≤ B) :
    (certifiedFillValue q S I x).natAbs ≤ 20 * B * (S.card + 1) ^ 2 := by
  classical
  by_cases hS : certifiesCurrentComponent q S
  · let r := finiteEdgeChain S (fun e => q e.val)
    let s := translatedChainFilling r
    have hs : (primalFilling s I x).natAbs ≤ chainMass s := by
      cases I <;> first
        | exact natAbs_le_chainMass s _
        | simpa only [primalFilling, Int.natAbs_neg] using natAbs_le_chainMass s _
    have hrS : r.support ⊆ S := finiteEdgeChain_support_subset q S
    have hm : chainMass r ≤ B * S.card := by
      calc
        _ ≤ ∑ _e ∈ r.support, B := Finset.sum_le_sum fun e he => by
          have hv : r e = q e := by
            rw [show r e = restrictCurrent q S e from congrFun (finiteEdgeChain_coe q S) e,
              restrictCurrent, Set.indicator_of_mem (hrS he)]
          rw [hv]
          exact hB e
        _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm B]
          exact Nat.mul_le_mul_right B (Finset.card_le_card hrS)
    have hw := boxWidth_le_of_connected r S hrS ((certifiesCurrentComponent_iff q S).mp hS).2.2
    simp only [certifiedFillValue, ite_eq_left hS]
    calc
      _ ≤ chainMass s := hs
      _ ≤ chainMass r * boxWidth (edgeChainLower r) (edgeChainUpper r) :=
        (translatedChainFilling_spec r (finiteEdgeChain_boundary₁_eq_zero q hdiv hS)).2.2
      _ ≤ (B * S.card) * (4 * (4 * S.card + 1)) := Nat.mul_le_mul hm hw
      _ = B * (S.card * (4 * (4 * S.card + 1))) := by ring
      _ ≤ B * (20 * (S.card + 1) ^ 2) := Nat.mul_le_mul_left B (by nlinarith)
      _ = _ := by ring
  · simp [certifiedFillValue, hS]

section Measure

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable (mark : OrientedEdge → Set Ω) (hm : ∀ e, MeasurableSet (mark e))
variable (a : ℝ) (ha : 0 ≤ a)
variable (hjoint : ∀ S, μ (allBad mark S) ≤ ENNReal.ofReal (a ^ S.card))
variable (B : ℕ)

def componentCoverWeight (S : Finset OrientedEdge) : Ω → ℝ :=
  (allBad mark S).indicator fun _ => 20 * (B : ℝ) * ((S.card : ℝ) + 1) ^ 2

omit [MeasurableSpace Ω] in
theorem componentCoverWeight_nonneg (S : Finset OrientedEdge) (ω : Ω) :
    0 ≤ componentCoverWeight mark B S ω := Set.indicator_nonneg (fun _ _ => by positivity) _

omit [MeasurableSpace Ω] in
theorem abs_certifiedFillValue_le_componentCoverWeight (q : OrientedEdge → ℤ) (ω : Ω)
    (hdiv : ∀ x, currentDivergence q x = 0) (hB : ∀ e, (q e).natAbs ≤ B)
    (hs : ∀ e, q e ≠ 0 → ω ∈ mark e) (S : Finset OrientedEdge) (I : Face) (x : Site) :
    |(certifiedFillValue q S I x : ℝ)| ≤ componentCoverWeight mark B S ω := by
  classical
  unfold componentCoverWeight
  by_cases hω : ω ∈ allBad mark S
  · rw [Set.indicator_of_mem hω, ← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast natAbs_certifiedFillValue_le q S I x hdiv B hB
  · rw [Set.indicator_of_notMem hω]
    have hn : ¬certifiesCurrentComponent q S := fun hc =>
      hω (fun e he => hs e ((certifiesCurrentComponent_iff q S).mp hc |>.1 e he))
    simp [certifiedFillValue, hn]

include hm in
theorem measurableSet_allBad (S : Finset OrientedEdge) : MeasurableSet (allBad mark S) := by
  change MeasurableSet {ω | ∀ e ∈ S, ω ∈ mark e}
  rw [show {ω | ∀ e ∈ S, ω ∈ mark e} = ⋂ e ∈ S, mark e by ext; simp]
  exact MeasurableSet.biInter S.countable_toSet (fun e _ => hm e)

include hm ha hjoint in
theorem eLpNorm_componentCoverWeight_le (S : Finset OrientedEdge) :
    eLpNorm (componentCoverWeight mark B S) 2 μ ≤
      ENNReal.ofReal (20 * (B : ℝ) * ((S.card : ℝ) + 1) ^ 2 * (Real.sqrt a) ^ S.card) := by
  let E := allBad mark S
  let b := 20 * (B : ℝ) * ((S.card : ℝ) + 1) ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hp : 1 / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
  calc
    _ ≤ ‖b‖ₑ * μ E ^ (1 / (2 : ℝ≥0∞).toReal) :=
      eLpNorm_indicator_const_le b 2 (measurableSet_allBad mark hm S).nullMeasurableSet
    _ ≤ ENNReal.ofReal (b * (Real.sqrt a) ^ S.card) := by
      rw [hp, Real.eNorm_eq_ofReal hb, ENNReal.ofReal_mul hb, Real.sqrt_eq_rpow,
        ← Real.rpow_mul_natCast ha, mul_comm (1 / 2 : ℝ), Real.rpow_mul ha,
        Real.rpow_natCast, ← ENNReal.ofReal_rpow_of_nonneg (pow_nonneg ha _) (by norm_num)]
      exact mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow (hjoint S) (by norm_num))
        (by positivity)

def componentCoverBlock (x : Site) (n : ℕ) : Ω → ℝ :=
  ∑ S ∈ connectedBoxCover x n, componentCoverWeight mark B S

omit [MeasurableSpace Ω] in
theorem componentCoverBlock_nonneg (x : Site) (n : ℕ) (ω : Ω) :
    0 ≤ componentCoverBlock mark B x n ω := by
  rw [componentCoverBlock, Finset.sum_apply]
  exact Finset.sum_nonneg fun S _ => componentCoverWeight_nonneg mark B S ω

include hm in
theorem measurable_componentCoverBlock (x : Site) (n : ℕ) :
    Measurable (componentCoverBlock mark B x n) := by
  have h (S : Finset OrientedEdge) : Measurable (componentCoverWeight mark B S) :=
    measurable_const.indicator (measurableSet_allBad mark hm S)
  simpa only [componentCoverBlock, ← Finset.sum_apply] using
    (Finset.measurable_sum (connectedBoxCover x n) fun S _ => h S)

include hm ha hjoint in
theorem eLpNorm_componentCoverBlock_le (x : Site) (n : ℕ) :
    eLpNorm (componentCoverBlock mark B x n) 2 μ ≤
      ENNReal.ofReal (20480 * (B : ℝ) * ((n : ℝ) + 1) ^ 6 * ((14 : ℝ) ^ 2 * Real.sqrt a) ^ n) := by
  let C := connectedBoxCover x n
  let b := 20 * (B : ℝ) * ((n : ℝ) + 1) ^ 2 * (Real.sqrt a) ^ n
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcard : (C.card : ℝ) ≤ 4 * (4 * (n : ℝ) + 3) ^ 4 * (14 : ℝ) ^ (2 * n) := by
    exact_mod_cast (card_connectedBoxCover_le x n).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
  have hpoly : 4 * (4 * (n : ℝ) + 3) ^ 4 ≤ 1024 * ((n : ℝ) + 1) ^ 4 := by
    calc
      _ ≤ 4 * (4 * ((n : ℝ) + 1)) ^ 4 := by
        gcongr
        linarith
      _ = _ := by ring
  calc
    _ ≤ ∑ S ∈ C, eLpNorm (componentCoverWeight mark B S) 2 μ :=
      eLpNorm_sum_le (by norm_num)
    _ ≤ ∑ _S ∈ C, ENNReal.ofReal b := by
      refine Finset.sum_le_sum fun S hS => ?_
      simpa only [card_eq_of_mem_connectedBoxCover hS] using
        eLpNorm_componentCoverWeight_le μ mark hm a ha hjoint B S
    _ = ENNReal.ofReal ((C.card : ℝ) * b) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (4 * (4 * (n : ℝ) + 3) ^ 4 * (14 : ℝ) ^ (2 * n)) * b :=
          mul_le_mul_of_nonneg_right hcard hb
        _ ≤ (1024 * ((n : ℝ) + 1) ^ 4 * (14 : ℝ) ^ (2 * n)) * b :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly (by positivity)) hb
        _ = _ := by dsimp only [b]; rw [pow_mul, mul_pow]; ring

omit [MeasurableSpace Ω] in
theorem componentCoverBlock_eq_zero_of_notMem (x : Site) (n : ℕ) (ω : Ω)
    (h : ω ∉ markedBoxEvent mark x n) : componentCoverBlock mark B x n ω = 0 := by
  rw [componentCoverBlock, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro S hS
  obtain ⟨e, he, hcover⟩ := Finset.mem_biUnion.mp hS
  have hn : ω ∉ allBad mark S := fun hm =>
    h (Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he,
      Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hcover, hm⟩⟩⟩⟩)
  exact Set.indicator_of_notMem hn _

def componentCoverTail (x : Site) (R : ℕ) (ω : Ω) : ℝ :=
  (∑' n : ℕ, ENNReal.ofReal (componentCoverBlock mark B x (n + R) ω)).toReal

omit [MeasurableSpace Ω] in
theorem componentCoverTail_nonneg (x : Site) (R : ℕ) (ω : Ω) :
    0 ≤ componentCoverTail mark B x R ω := ENNReal.toReal_nonneg

include hm in
theorem measurable_componentCoverTail (x : Site) (R : ℕ) :
    Measurable (componentCoverTail mark B x R) :=
  (Measurable.tsum fun n => (measurable_componentCoverBlock mark hm B x (n + R)).ennreal_ofReal).ennreal_toReal

omit [MeasurableSpace Ω] in
theorem summable_componentCoverTail_of_eventually_zero (x : Site) (R : ℕ) (ω : Ω)
    (h : ∀ᶠ n in atTop, componentCoverBlock mark B x n ω = 0) :
    Summable (fun n : ℕ => componentCoverBlock mark B x (n + R) ω) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp h
  exact summable_of_ne_finset_zero (s := Finset.range K)
    fun n hn => hK (n + R) (by simp only [Finset.mem_range] at hn; omega)

omit [MeasurableSpace Ω] in
theorem componentCoverTail_eq_tsum (x : Site) (R : ℕ) (ω : Ω)
    (h : Summable (fun n : ℕ => componentCoverBlock mark B x (n + R) ω)) :
    componentCoverTail mark B x R ω = ∑' n : ℕ, componentCoverBlock mark B x (n + R) ω := by
  have hn (n : ℕ) := componentCoverBlock_nonneg mark B x (n + R) ω
  rw [componentCoverTail, ← ENNReal.ofReal_tsum_of_nonneg hn h, ENNReal.toReal_ofReal (tsum_nonneg hn)]

private theorem summable_sixth_geometric {t : ℝ} (h₀ : 0 ≤ t) (ht : t < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 6 * t ^ n) := by
  have hn : ‖t‖ < 1 := by simpa only [Real.norm_of_nonneg h₀] using ht
  have h := (summable_pow_mul_geometric_of_norm_lt_one 6 hn).mul_left (2 ^ 6)
  apply (summable_nat_add_iff 1).mp
  refine ((summable_nat_add_iff 1).mpr h).of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
  have hle : ((n + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ 6 * t ^ (n + 1) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hle 6) (pow_nonneg h₀ _)
    _ = _ := by rw [mul_pow]; ring

include hm ha hjoint in
theorem eLpNorm_componentCoverTail_le (hρ : (14 : ℝ) ^ 2 * Real.sqrt a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ x R,
      eLpNorm (componentCoverTail mark B x R) 2 μ ≤ ENNReal.ofReal (C * t ^ R) := by
  let ρ := (14 : ℝ) ^ 2 * Real.sqrt a
  let t := Real.sqrt ρ
  let b (n : ℕ) := ((n : ℝ) + 1) ^ 6 * t ^ n
  have hρ₀ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have ht₀ : 0 ≤ t := Real.sqrt_nonneg _
  have hts : t ^ 2 = ρ := Real.sq_sqrt hρ₀
  have ht : t < 1 := by nlinarith
  have hs : Summable b := summable_sixth_geometric ht₀ ht
  have hb (n : ℕ) : 0 ≤ b n := by dsimp [b]; positivity
  let C := 1 + 20480 * (B : ℝ) * ∑' n : ℕ, b n
  have hC : 0 < C := by
    have hsum : 0 ≤ (∑' n : ℕ, b n) := tsum_nonneg hb
    dsimp [C]
    positivity
  have hsmall : (14 : ℝ) ^ 2 * a < 1 := by
    have hsqrt : Real.sqrt a < 1 := by
      have hle : Real.sqrt a ≤ (14 : ℝ) ^ 2 * Real.sqrt a := by
        nlinarith only [Real.sqrt_nonneg a]
      exact hle.trans_lt hρ
    have hle : a ≤ Real.sqrt a := by nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]
    exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans_lt hρ
  refine ⟨C, hC, t, ht₀, ht, fun x R => ?_⟩
  let g (M : ℕ) : Ω → ℝ := ∑ j ∈ Finset.range M, componentCoverBlock mark B x (j + R)
  have hg (M : ℕ) : Measurable (g M) := by
    simpa only [g, ← Finset.sum_apply] using
      (Finset.measurable_sum (Finset.range M) fun j _ =>
        measurable_componentCoverBlock mark hm B x (j + R))
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := g) ?_ (fun M => (hg M).aestronglyMeasurable)
    (measurable_componentCoverTail mark hm B x R).aestronglyMeasurable ?_
  · refine Eventually.of_forall fun M => ?_
    let W (n : ℕ) := 20480 * (B : ℝ) * ((n : ℝ) + 1) ^ 6 * ρ ^ n
    have hW (n : ℕ) : 0 ≤ W n := by dsimp [W]; positivity
    have hWt (n : ℕ) (hn : R ≤ n) : W n ≤ (20480 * (B : ℝ) * t ^ R) * b n := by
      have hpow : t ^ n ≤ t ^ R := pow_le_pow_of_le_one ht₀ ht.le hn
      calc
        _ = (20480 * (B : ℝ) * t ^ n) * b n := by
          dsimp only [W, b]
          rw [← hts, ← pow_mul, Nat.mul_comm 2 n, pow_mul, pow_two]
          ring
        _ ≤ _ := by
          gcongr
    calc
      _ ≤ ∑ j ∈ Finset.range M, eLpNorm (componentCoverBlock mark B x (j + R)) 2 μ :=
        eLpNorm_sum_le (by norm_num)
      _ ≤ ∑ j ∈ Finset.range M, ENNReal.ofReal (W (j + R)) :=
        Finset.sum_le_sum fun j _ => eLpNorm_componentCoverBlock_le μ mark hm a ha hjoint B x (j + R)
      _ = ENNReal.ofReal (∑ j ∈ Finset.range M, W (j + R)) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => hW (j + R)).symm
      _ ≤ ENNReal.ofReal (C * t ^ R) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ ∑ j ∈ Finset.range M, (20480 * (B : ℝ) * t ^ R) * b (j + R) :=
            Finset.sum_le_sum fun j _ => hWt (j + R) (by omega)
          _ ≤ (20480 * (B : ℝ) * t ^ R) * ∑' n : ℕ, b n := by
            rw [← Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hinj : Function.Injective (fun j : ℕ => j + R) := fun _ _ h => Nat.add_right_cancel h
            let e : ℕ ↪ ℕ := ⟨_, hinj⟩
            calc
              _ = ∑ j ∈ (Finset.range M).map e, b j := (Finset.sum_map _ e b).symm
              _ ≤ _ := hs.sum_le_tsum _ (fun n _ => hb n)
          _ ≤ _ := by
            dsimp only [C]
            nlinarith only [pow_nonneg ht₀ R]
  · filter_upwards [eventually_notMem_markedBoxEvent_ae μ mark a ha hsmall hjoint x] with ω hω
    have hzero := hω.mono (fun n hn => componentCoverBlock_eq_zero_of_notMem mark B x n ω hn)
    have h := summable_componentCoverTail_of_eventually_zero mark B x R ω hzero
    rw [componentCoverTail_eq_tsum mark B x R ω h]
    simpa only [g, Finset.sum_apply] using h.hasSum.tendsto_sum_nat

end Measure

private theorem cast_fillDefectApprox_sum (q : ThreeForm ℤ) (R : ℕ) (I : Face) (x : Site) :
    (fillDefectApprox q R I x : ℝ) = ∑ n ∈ Finset.range (R + 1),
      ∑ S ∈ connectedBoxCover (-x) n, (certifiedFillValue (dualCurrent q) S I x : ℝ) := by
  have h : (↑(Finset.range (R + 1)) : Set ℕ).PairwiseDisjoint (connectedBoxCover (-x)) := by
    intro m _ n _ hmn
    apply Finset.disjoint_left.mpr
    intro S hm hn
    exact hmn ((card_eq_of_mem_connectedBoxCover hm).symm.trans (card_eq_of_mem_connectedBoxCover hn))
  unfold fillDefectApprox boundedBoxCover
  push_cast
  exact Finset.sum_biUnion h

private theorem abs_fillDefectApprox_sub_le_tail {Ω : Type*}
    (mark : OrientedEdge → Set Ω) (B : ℕ) (ω : Ω) (q : ThreeForm ℤ)
    (hq : d₃ q = 0) (hB : ∀ e, (dualCurrent q e).natAbs ≤ B)
    (hm : ∀ e, dualCurrent q e ≠ 0 → ω ∈ mark e) (I : Face) (x : Site) {R K : ℕ} (hRK : R ≤ K)
    (hs : Summable (fun n : ℕ => componentCoverBlock mark B (-x) (n + (R + 1)) ω)) :
    |(fillDefectApprox q K I x : ℝ) - (fillDefectApprox q R I x : ℝ)| ≤
      componentCoverTail mark B (-x) (R + 1) ω := by
  let c (n : ℕ) := ∑ S ∈ connectedBoxCover (-x) n, (certifiedFillValue (dualCurrent q) S I x : ℝ)
  have hdiv (y : Site) : currentDivergence (dualCurrent q) y = 0 := by
    rw [currentDivergence_dualCurrent, hq, Pi.zero_apply]
  have hc (n : ℕ) : |c n| ≤ componentCoverBlock mark B (-x) n ω := by
    rw [componentCoverBlock, Finset.sum_apply]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun S _ =>
        abs_certifiedFillValue_le_componentCoverWeight mark B (dualCurrent q) ω hdiv hB hm S I x)
  have hdiff : (fillDefectApprox q K I x : ℝ) - (fillDefectApprox q R I x : ℝ) =
      ∑ n ∈ Finset.range (K - R), c (n + (R + 1)) := by
    rw [cast_fillDefectApprox_sum, cast_fillDefectApprox_sum]
    change (∑ n ∈ Finset.range (K + 1), c n) - (∑ n ∈ Finset.range (R + 1), c n) = _
    rw [show K + 1 = (R + 1) + (K - R) by omega, Finset.sum_range_add, add_sub_cancel_left]
    simp only [Nat.add_comm (R + 1)]
  rw [hdiff, componentCoverTail_eq_tsum mark B (-x) (R + 1) ω hs]
  calc
    _ ≤ ∑ n ∈ Finset.range (K - R), |c (n + (R + 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (K - R), componentCoverBlock mark B (-x) (n + (R + 1)) ω :=
      Finset.sum_le_sum fun n _ => hc _
    _ ≤ _ := hs.sum_le_tsum _ (fun n _ => componentCoverBlock_nonneg mark B (-x) _ ω)

private theorem natAbs_dualCurrent_le (q : ThreeForm ℤ) (B : ℕ)
    (h : ∀ c x, |(q c x : ℝ)| ≤ B) (e : OrientedEdge) : (dualCurrent q e).natAbs ≤ B := by
  have h' (c : Cube) (x : Site) : (q c x).natAbs ≤ B := by
    have hc := h c x
    rw [← Int.cast_abs, ← Nat.cast_natAbs] at hc
    exact_mod_cast hc
  obtain ⟨y, i⟩ := e
  fin_cases i
  · simpa [dualCurrent] using h' .yzw (-y)
  · simpa [dualCurrent] using h' .xzw (-y)
  · simpa [dualCurrent] using h' .xyw (-y)
  · simpa [dualCurrent] using h' .xyz (-y)

theorem natAbs_cutDefect_le {N : ℕ} (U : OneForm (UnitaryMatrix N)) (η : TwoForm ℝ)
    (hη : ∀ J y, |η J y| ≤ Real.pi / 16) (e : OrientedEdge) :
    (dualCurrent (defect (liftFlux η (plaquetteEigenangles U))) e).natAbs ≤ 4 * N := by
  apply natAbs_dualCurrent_le
  intro c y
  push_cast
  exact abs_unitaryDefect_le U η _ (prod_exp_plaquetteEigenangles U) hη c y

theorem measurableSet_markedDualLink {N : ℕ} (hN : 0 < N) (e : OrientedEdge) :
    MeasurableSet (markedDualLink (badPlaquette (N := N)) e) := by
  rw [show markedDualLink (badPlaquette (N := N)) e = ⋃ p ∈ cubeFaces (edgeCubeEquiv e),
      badPlaquette p by ext; simp [markedDualLink]]
  exact MeasurableSet.biUnion (cubeFaces (edgeCubeEquiv e)).countable_toSet
    (fun p _ => (isOpen_badPlaquette hN p).measurableSet)

def cutFluxErrorBound {N : ℕ} (R : ℕ) (x : Site) (U : InfiniteConfig N) : ℝ :=
  2 * Real.pi * componentCoverTail (markedDualLink badPlaquette) (4 * N) (-x) (R + 1) U

theorem cutFluxErrorBound_nonneg {N : ℕ} (R : ℕ) (x : Site) (U : InfiniteConfig N) :
    0 ≤ cutFluxErrorBound R x U :=
  mul_nonneg Real.two_pi_pos.le (componentCoverTail_nonneg _ _ _ _ _)

theorem measurable_cutFluxErrorBound {N : ℕ} (hN : 0 < N) (R : ℕ) (x : Site) :
    Measurable (cutFluxErrorBound (N := N) R x) :=
  measurable_const.mul (measurable_componentCoverTail _ (measurableSet_markedDualLink hN) _ _ _)

private theorem periodicLimit_markedCoverBound {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (S : Finset OrientedEdge) :
    μ.toMeasure (allBad (markedDualLink badPlaquette) S) ≤
      ENNReal.ofReal ((6 * Real.exp (-(badPenalty * (N : ℝ) * β / 96))) ^ S.card) := by
  rw [allBad_markedDualLink]
  simpa only [Finset.card_map] using
    measure_periodicLimit_allMarked_le hN (by linarith) μ l hl hμ (S.map edgeCubeEquiv.toEmbedding)

/-- One measurable error bound works for all allowed cut configurations. -/
theorem abs_repairedCutFlux_sub_approx_le_periodicLimit_ae {N : ℕ} (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂μ.toMeasure, ∀ I x R η, (∀ J y, |η J y| ≤ Real.pi / 16) →
      |repairedCutFlux (fun i y => U (i, y)) η I x -
        repairedCutFluxApprox R (fun i y => U (i, y)) η I x| ≤ cutFluxErrorBound R x U := by
  have hevent : ∀ᵐ U ∂μ.toMeasure, ∀ y,
      ∀ᶠ n in atTop, U ∉ markedBoxEvent (markedDualLink badPlaquette) y n :=
    ae_all_iff.mpr fun y => eventually_notMem_markedBoxEvent_ae μ.toMeasure _ _ (by positivity)
      (markedEdgeRate_subcritical hN hβ) (periodicLimit_markedCoverBound hN hβ μ l hl hμ) y
  filter_upwards [hevent, repairedCutFluxApprox_eventually_eq_periodicLimit hN hβ μ l hl hμ] with U hU hApprox
  intro I x R η hη
  obtain ⟨K, hK⟩ := hApprox I x
  let V : OneForm (UnitaryMatrix N) := fun i y => U (i, y)
  let a := liftFlux η (plaquetteEigenangles V)
  let q := defect a
  have hq := plaquetteDefect_closed V η
  have hsum := summable_componentCoverTail_of_eventually_zero
    (markedDualLink badPlaquette) (4 * N) (-x) (R + 1) U
    ((hU (-x)).mono (fun n hn => componentCoverBlock_eq_zero_of_notMem _ _ _ _ _ hn))
  have htail := abs_fillDefectApprox_sub_le_tail (markedDualLink badPlaquette) (4 * N)
    U q hq (natAbs_cutDefect_le V η hη) (fun e he => cutDefect_supported_in_marks U η hη he) I x
    (le_max_right K R) hsum
  rw [← hK (max K R) (le_max_left K R) η hη]
  change |(a I x - 2 * Real.pi * (fillDefectApprox q (max K R) I x : ℝ)) -
    (a I x - 2 * Real.pi * (fillDefectApprox q R I x : ℝ))| ≤ _
  rw [show (a I x - 2 * Real.pi * (fillDefectApprox q (max K R) I x : ℝ)) -
      (a I x - 2 * Real.pi * (fillDefectApprox q R I x : ℝ)) =
      -(2 * Real.pi * ((fillDefectApprox q (max K R) I x : ℝ) - (fillDefectApprox q R I x : ℝ))) by ring,
    abs_neg, abs_mul, abs_of_nonneg Real.two_pi_pos.le]
  exact mul_le_mul_of_nonneg_left htail Real.two_pi_pos.le

theorem eLpNorm_cutFluxErrorBound_periodicLimit_le {N : ℕ} (hN : 0 < N) {β : ℝ}
    (hβ : 10000 ≤ β) (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ ∀ x R,
      eLpNorm (cutFluxErrorBound R x) 2 μ.toMeasure ≤ ENNReal.ofReal (C * t ^ R) := by
  let q : ℝ := 6 * Real.exp (-(badPenalty * (N : ℝ) * β / 96))
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hexp : (Real.exp (-(badPenalty * (N : ℝ) * β / 192))) ^ 2 =
      Real.exp (-(badPenalty * (N : ℝ) * β / 96)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hρ : (14 : ℝ) ^ 2 * Real.sqrt q < 1 := by
    unfold q
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6), ← hexp, Real.sqrt_sq (Real.exp_nonneg _)]
    simpa only [defectTailRate, mul_assoc] using defectTailRate_lt_one hN hβ
  obtain ⟨C, hC, t, ht₀, ht, h⟩ := eLpNorm_componentCoverTail_le μ.toMeasure
    (markedDualLink badPlaquette) (measurableSet_markedDualLink hN) q hq
    (periodicLimit_markedCoverBound hN hβ μ l hl hμ) (4 * N) hρ
  refine ⟨2 * Real.pi * C, mul_pos Real.two_pi_pos hC, t, ht₀, ht, fun x R => ?_⟩
  change eLpNorm ((2 * Real.pi) • componentCoverTail (markedDualLink badPlaquette) (4 * N)
    (-x) (R + 1)) 2 μ.toMeasure ≤ _
  rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal Real.two_pi_pos.le,
    mul_assoc, ENNReal.ofReal_mul Real.two_pi_pos.le]
  refine mul_le_mul_of_nonneg_left ((h (-x) (R + 1)).trans (ENNReal.ofReal_le_ofReal ?_)) (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ht₀ ht.le (Nat.le_succ _)) hC.le

end

end GaplessYangMills

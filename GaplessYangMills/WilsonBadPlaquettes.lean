module

public import GaplessYangMills.BadPlaquetteEstimate
public import GaplessYangMills.PeriodicWilsonComparison
public import GaplessYangMills.RankOneTwistLaw

/-!
# The joint bad-plaquette and marked-edge estimates

The periodic Wilson partition comparison gives the finite-volume estimate.
Reduction modulo the side length is eventually injective on any prescribed
finite set of plaquettes, so the bound passes to periodic weak limits.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

def badTorusPlaquette {L N : ℕ} (p : TorusPlaquette L) : Set (TorusConfig L N) :=
  {U | badUnitary (periodicHolonomy U p.1 p.2)}

theorem isOpen_badTorusPlaquette {L N : ℕ} (hN : 0 < N) (p : TorusPlaquette L) :
    IsOpen (badTorusPlaquette (N := N) p) :=
  (isOpen_badUnitary hN).preimage (continuous_periodicHolonomy p.1 p.2)

/-- The finite-volume version of Lemma 2. -/
theorem measure_periodicWilson_allBad_le {L N : ℕ} [NeZero L] (hL : Even L) (hN : 0 < N)
    {β : ℝ} (hβ : 40 ≤ β) (S : Finset (TorusPlaquette L)) :
    periodicWilson L N β (allBad badTorusPlaquette S) ≤
      ENNReal.ofReal (Real.exp (-(badPenalty * (N : ℝ) * β / 24) * S.card)) := by
  let : NeZero N := ⟨hN.ne'⟩
  let a := (N : ℝ) * β * badPenalty / 4
  let M (p : TorusPlaquette L) (U : TorusConfig L N) :=
    ENNReal.ofReal (wilsonTwistMultiplier (rankOneTwistLaw N) β (periodicHolonomy U p.1 p.2))
  have hb : 0 ≤ β := by linarith
  have hpen : 0 ≤ badPenalty := by linarith [badPenalty_lower]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hM (p : TorusPlaquette L) (U : TorusConfig L N) (hp : U ∈ badTorusPlaquette p) :
      ENNReal.ofReal (Real.exp a) ≤ M p U :=
    ENNReal.ofReal_le_ofReal (rankOneTwistMultiplier_bad_lower hN hβ _ hp)
  have hE (I : Face) (P : Finset (TorusPlaquette L)) (hP : ∀ p ∈ P, p.1 = I) :
      (∫⁻ U, (∏ p ∈ P, M p U) ∂periodicWilson L N β) ≤ 1 :=
    lintegral_periodicWilson_twistMultiplier_le_one hL (rankOneTwistLaw N)
      rankOneTwistLaw_conjugation β hb P I.axes.1 (fun p hp =>
        Or.inl (congrArg (fun J : Face => J.axes.1) (hP p hp)))
  have he : -(a / 6) = -(badPenalty * (N : ℝ) * β / 24) := by dsimp [a]; ring
  simpa only [he] using badEvent_le_of_orientationExpectations (periodicWilson L N β)
    badTorusPlaquette (fun p => (isOpen_badTorusPlaquette hN p).measurableSet) M a ha hM hE S

private def torusPlaquetteReduction (L : ℕ) (p : Plaquette) : TorusPlaquette L :=
  (p.1, fun i => (p.2 i : ZMod L))

private theorem torusSite_reduction_step (L : ℕ) (x : Site) (i : Axis) :
    (fun j => ((x + step i) j : ZMod L)) =
      (fun j => (x j : ZMod L)) + torusStep L i := by
  funext j
  simp only [Pi.add_apply, Int.cast_add, torusStep]
  by_cases h : i = j <;> simp [step, h]

private theorem badTorusPlaquette_extendPeriodic {L N : ℕ} (U : TorusConfig L N) (p : Plaquette) :
    extendPeriodic U ∈ badPlaquette p ↔ U ∈ badTorusPlaquette (torusPlaquetteReduction L p) := by
  simp only [badPlaquette, badTorusPlaquette, Set.mem_ofPred_eq, plaquetteHolonomy,
    periodicHolonomy, torusPlaquetteReduction, extendPeriodic, torusSite_reduction_step]

private theorem allBad_extendPeriodic {L N : ℕ} (S : Finset Plaquette) :
    (extendPeriodic : TorusConfig L N → InfiniteConfig N) ⁻¹' allBad badPlaquette S =
      allBad badTorusPlaquette (S.image (torusPlaquetteReduction L)) := by
  classical
  ext U
  constructor
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (badTorusPlaquette_extendPeriodic U q).mp (h q hq)
  · intro h p hp
    exact (badTorusPlaquette_extendPeriodic U p).mpr (h _ (Finset.mem_image_of_mem _ hp))

private def plaquetteRadius (S : Finset Plaquette) : ℕ :=
  S.sup (fun p => Finset.univ.sup (fun i : Axis => (p.2 i).natAbs))

private theorem torusPlaquetteReduction_injOn {L : ℕ} (S : Finset Plaquette)
    (hL : 2 * plaquetteRadius S < L) : Set.InjOn (torusPlaquetteReduction L) (↑S : Set Plaquette) := by
  intro p hp q hq h
  have hface : p.1 = q.1 := congrArg (fun t : TorusPlaquette L => t.1) h
  refine Prod.ext hface (funext fun i => ?_)
  have hm : (p.2 i : ZMod L) = (q.2 i : ZMod L) := congrFun (congrArg Prod.snd h) i
  have hd : (L : ℤ) ∣ q.2 i - p.2 i := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hm
  have hd' : L ∣ (q.2 i - p.2 i).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hb (r : Plaquette) (hr : r ∈ S) : (r.2 i).natAbs ≤ plaquetteRadius S :=
    (Finset.le_sup (f := fun j : Axis => (r.2 j).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (s := S) (f := fun p : Plaquette =>
        Finset.univ.sup (fun j : Axis => (p.2 j).natAbs)) hr)
  have hbp := hb p hp
  have hbq := hb q hq
  by_contra hne
  have hpos : 0 < (q.2 i - p.2 i).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hlo := Nat.le_of_dvd hpos hd'
  have hhi := Int.natAbs_sub_le (q.2 i) (p.2 i)
  omega

/-- Lemma 2 for any periodic weak limit along even lengths. -/
theorem measure_periodicLimit_allBad_le {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 40 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (S : Finset Plaquette) :
    (μ : Measure (InfiniteConfig N)) (allBad badPlaquette S) ≤
      ENNReal.ofReal (Real.exp (-(badPenalty * (N : ℝ) * β / 24) * S.card)) := by
  classical
  apply weakLimit_open_bound_eventually _ μ hμ _ (isOpen_allBadPlaquettes hN S) _
  refine Filter.eventually_atTop.mpr ⟨2 * plaquetteRadius S, fun n hn => ?_⟩
  let L := evenLength (l n)
  have hL : 2 * plaquetteRadius S < L := by
    have hln : n ≤ l n := hl.id_le n
    dsimp only [L, evenLength]
    omega
  have he : Even L := ⟨l n + 2, by dsimp only [L, evenLength]; omega⟩
  let T := S.image (torusPlaquetteReduction L)
  have hcard : T.card = S.card :=
    Finset.card_image_of_injOn (torusPlaquetteReduction_injOn S hL)
  have hbad := measure_periodicWilson_allBad_le he hN hβ T
  rw [hcard] at hbad
  change (Measure.map (extendPeriodic : TorusConfig L N → InfiniteConfig N) (periodicWilson L N β))
    (allBad badPlaquette S) ≤ _
  rw [Measure.map_apply (continuous_extendPeriodic L N).measurable
    (isOpen_allBadPlaquettes hN S).measurableSet, allBad_extendPeriodic]
  exact hbad

/-- Equation (1) for the marked dual edges in a periodic weak limit. -/
theorem measure_periodicLimit_allMarked_le {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 40 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (S : Finset DualEdge) :
    (μ : Measure (InfiniteConfig N)) (allMarked badPlaquette S) ≤
      ENNReal.ofReal ((6 * Real.exp (-(badPenalty * (N : ℝ) * β / 96))) ^ S.card) := by
  let a := badPenalty * (N : ℝ) * β / 24
  have hb : 0 ≤ β := by linarith
  have hpen : 0 ≤ badPenalty := by linarith [badPenalty_lower]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : a / 4 = badPenalty * (N : ℝ) * β / 96 := by dsimp [a]; ring
  simpa only [he] using measure_allMarked_le μ.toMeasure badPlaquette a ha
    (measure_periodicLimit_allBad_le hN hβ μ l hl hμ) S

end

end GaplessYangMills

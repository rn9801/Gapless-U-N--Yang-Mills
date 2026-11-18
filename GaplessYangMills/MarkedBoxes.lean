module

public import GaplessYangMills.MarkedComponents
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Int.Interval
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Local finiteness of the marked component boxes

A connected edge set whose box reaches a given vertex has an anchor in a
larger box of radius linear in its size. The polynomial number of possible
anchors is summable against the marked-set estimate.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory SimpleGraph
open scoped ENNReal Topology

noncomputable section

private theorem incident_coordinate_bounds {e : OrientedEdge} {x : Site} (h : incident e x)
    (i : Axis) : e.1 i ≤ x i ∧ x i ≤ e.1 i + 1 := by
  rcases h with rfl | rfl
  · omega
  · simp only [Pi.add_apply, step]
    split <;> omega

theorem adjacent_coordinate_bounds {e f : OrientedEdge} (h : dualEdgeGraph.Adj e f)
    (i : Axis) : e.1 i ≤ f.1 i + 1 ∧ f.1 i ≤ e.1 i + 1 := by
  obtain ⟨_, x, he, hf⟩ := h
  have h₁ := incident_coordinate_bounds he i
  have h₂ := incident_coordinate_bounds hf i
  omega

theorem walk_coordinate_bounds {e f : OrientedEdge} (p : dualEdgeGraph.Walk e f)
    {g : OrientedEdge} (hg : g ∈ p.support) (i : Axis) :
    e.1 i ≤ g.1 i + p.length ∧ g.1 i ≤ e.1 i + p.length := by
  induction p with
  | nil =>
    obtain rfl := Walk.mem_support_nil_iff.mp hg
    simp
  | @cons e e' f he p ih =>
    rcases List.mem_cons.mp hg with heq | htail
    · subst g
      simp
      positivity
    · have h := ih htail
      have hb := adjacent_coordinate_bounds he i
      simp only [Walk.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- The vertices incident to the edges in a finite set. -/
def edgeVertices (S : Finset OrientedEdge) : Finset Site :=
  (S.image Prod.fst) ∪ (S.image fun e => e.1 + step e.2)

private theorem mem_edgeVertices (S : Finset OrientedEdge) (x : Site) :
    x ∈ edgeVertices S ↔ ∃ e ∈ S, incident e x := by
  simp only [edgeVertices, Finset.mem_union, Finset.mem_image, incident]
  constructor
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    · exact ⟨e, he, Or.inl hx⟩
    · exact ⟨e, he, Or.inr hx⟩
  · rintro ⟨e, he, hx | hx⟩
    · exact Or.inl ⟨e, he, hx⟩
    · exact Or.inr ⟨e, he, hx⟩

/-- A vertex lies in the coordinate box of an edge set when each coordinate
is bracketed by coordinates of its incident vertices. -/
def edgeBoxContains (S : Finset OrientedEdge) (x : Site) : Prop :=
  ∀ i : Axis, (∃ a ∈ edgeVertices S, a i ≤ x i) ∧ (∃ b ∈ edgeVertices S, x i ≤ b i)

def edgesNearVertex (x : Site) (R : ℕ) : Finset OrientedEdge :=
  (Fintype.piFinset fun i : Axis => Finset.Icc (x i - (R : ℤ)) (x i + R)) ×ˢ Finset.univ

theorem mem_edgesNearVertex_iff (x : Site) (R : ℕ) (e : OrientedEdge) :
    e ∈ edgesNearVertex x R ↔ ∀ i : Axis, x i - (R : ℤ) ≤ e.1 i ∧ e.1 i ≤ x i + R := by
  simp [edgesNearVertex, Fintype.mem_piFinset, Finset.mem_Icc]

private theorem edgesNearVertex_card (x : Site) (R : ℕ) :
    (edgesNearVertex x R).card = 4 * (2 * R + 1) ^ 4 := by
  have h (i : Axis) : (Finset.Icc (x i - (R : ℤ)) (x i + R)).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    omega
  simp [edgesNearVertex, Fintype.card_piFinset, h, mul_comm]

private theorem connected_box_has_anchor (S : Finset OrientedEdge) (x : Site)
    (hbox : edgeBoxContains S x) (hconn : ∃ e ∈ S, ∀ f ∈ S,
      ∃ w : dualEdgeGraph.Walk e f, ∀ g ∈ w.support, g ∈ S) :
    ∃ e ∈ edgesNearVertex x (2 * S.card + 1), S ∈ connectedSetCover dualEdgeGraph e S.card := by
  obtain ⟨e, he, h⟩ := hconn
  obtain ⟨p, hp, hlen⟩ := exists_closedWalk_with_support dualEdgeGraph S he h
  have hle : (p.length : ℤ) ≤ 2 * (S.card : ℤ) := by omega
  have hbound (f : OrientedEdge) (hf : f ∈ S) (i : Axis) :
      e.1 i ≤ f.1 i + 2 * S.card ∧ f.1 i ≤ e.1 i + 2 * S.card := by
    have hf' : f ∈ p.support := List.mem_toFinset.mp (hp.symm ▸ hf)
    have := walk_coordinate_bounds p hf' i
    omega
  refine ⟨e, ?_, mem_connectedSetCover dualEdgeGraph S he h⟩
  apply Finset.mem_product.mpr
  refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), Finset.mem_univ _⟩
  obtain ⟨⟨a, ha, hax⟩, b, hb, hxb⟩ := hbox i
  obtain ⟨f, hf, hfa⟩ := (mem_edgeVertices S a).mp ha
  obtain ⟨g, hg, hgb⟩ := (mem_edgeVertices S b).mp hb
  have hfa' := incident_coordinate_bounds hfa i
  have hgb' := incident_coordinate_bounds hgb i
  have h₁ := (hbound f hf i).1
  have h₂ := (hbound g hg i).2
  apply Finset.mem_Icc.mpr
  constructor <;> push_cast <;> omega

/-- The size-`n` sets that need to be checked for a box reaching `x`. -/
def connectedBoxCover (x : Site) (n : ℕ) : Finset (Finset OrientedEdge) :=
  (edgesNearVertex x (2 * n + 1)).biUnion fun e => connectedSetCover dualEdgeGraph e n

theorem mem_connectedBoxCover (S : Finset OrientedEdge) (x : Site)
    (hbox : edgeBoxContains S x) (hconn : ∃ e ∈ S, ∀ f ∈ S,
      ∃ w : dualEdgeGraph.Walk e f, ∀ g ∈ w.support, g ∈ S) :
    S ∈ connectedBoxCover x S.card := by
  obtain ⟨e, he, hS⟩ := connected_box_has_anchor S x hbox hconn
  exact Finset.mem_biUnion.mpr ⟨e, he, hS⟩

theorem card_eq_of_mem_connectedBoxCover {S : Finset OrientedEdge} {x : Site} {n : ℕ}
    (hS : S ∈ connectedBoxCover x n) : S.card = n := by
  obtain ⟨_, _, h⟩ := Finset.mem_biUnion.mp hS
  exact (Finset.mem_filter.mp h).2

theorem card_connectedBoxCover_le (x : Site) (n : ℕ) :
    (connectedBoxCover x n).card ≤ 4 * (4 * n + 3) ^ 4 * 14 ^ (2 * (n - 1)) := by
  unfold connectedBoxCover
  refine Finset.card_biUnion_le.trans ?_
  calc
    _ ≤ ∑ _e ∈ edgesNearVertex x (2 * n + 1), (14 : ℕ) ^ (2 * (n - 1)) :=
      Finset.sum_le_sum fun e _ => card_connectedSetCover_le dualEdgeGraph 14 dualEdgeGraph_degree_le e n
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, edgesNearVertex_card,
        show 2 * (2 * n + 1) + 1 = 4 * n + 3 by omega]
      norm_cast

variable {Ω : Type*} [MeasurableSpace Ω]

def markedBoxEvent (mark : OrientedEdge → Set Ω) (x : Site) (n : ℕ) : Set Ω :=
  ⋃ e ∈ edgesNearVertex x (2 * n + 1), markedConnectedSetEvent dualEdgeGraph mark e n

theorem measure_markedBoxEvent_le (μ : Measure Ω) (mark : OrientedEdge → Set Ω) (q : ℝ)
    (hq : 0 ≤ q) (hjoint : ∀ S, μ (allBad mark S) ≤ ENNReal.ofReal (q ^ S.card))
    (x : Site) (n : ℕ) :
    μ (markedBoxEvent mark x n) ≤
      ENNReal.ofReal (4 * (4 * (n : ℝ) + 3) ^ 4 * ((14 : ℝ) ^ 2 * q) ^ n) := by
  let A := edgesNearVertex x (2 * n + 1)
  let r := (14 : ℝ) ^ 2 * q
  calc
    _ ≤ ∑ e ∈ A, μ (markedConnectedSetEvent dualEdgeGraph mark e n) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _e ∈ A, ENNReal.ofReal (r ^ n) := Finset.sum_le_sum fun e _ =>
      measure_markedConnectedSetEvent_le dualEdgeGraph μ mark 14 (by decide)
        dualEdgeGraph_degree_le q hq hjoint e n
    _ = ENNReal.ofReal ((A.card : ℝ) * r ^ n) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp
    _ = _ := by
      dsimp only [A, r]
      rw [edgesNearVertex_card]
      push_cast
      congr 1
      ring

private theorem summable_markedBoxBound {r : ℝ} (h₀ : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => 4 * (4 * (n : ℝ) + 3) ^ 4 * r ^ n) := by
  have hn : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg h₀] using hr
  have hs := (summable_pow_mul_geometric_of_norm_lt_one 4 hn).mul_left (4 * 7 ^ 4)
  apply (summable_nat_add_iff 1).mp
  refine ((summable_nat_add_iff 1).mpr hs).of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
  have ht : 4 * ((n + 1 : ℕ) : ℝ) + 3 ≤ 7 * ((n + 1 : ℕ) : ℝ) := by
    have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    linarith
  calc
    _ ≤ 4 * (7 * ((n + 1 : ℕ) : ℝ)) ^ 4 * r ^ (n + 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht 4) (by positivity))
        (pow_nonneg h₀ _)
    _ = _ := by ring

def markedConnectedBoxes (M : Set OrientedEdge) (x : Site) : Set (Finset OrientedEdge) :=
  {S | (↑S : Set OrientedEdge) ⊆ M ∧ edgeBoxContains S x ∧
    ∃ e ∈ S, ∀ f ∈ S, ∃ w : dualEdgeGraph.Walk e f, ∀ g ∈ w.support, g ∈ S}

/-- Eventually no connected set in the size cover is entirely marked. -/
theorem eventually_notMem_markedBoxEvent_ae (μ : Measure Ω) (mark : OrientedEdge → Set Ω) (q : ℝ)
    (hq : 0 ≤ q) (hr : (14 : ℝ) ^ 2 * q < 1)
    (hjoint : ∀ S, μ (allBad mark S) ≤ ENNReal.ofReal (q ^ S.card)) (x : Site) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ markedBoxEvent mark x n := by
  have hs := summable_markedBoxBound (by positivity : 0 ≤ (14 : ℝ) ^ 2 * q) hr
  have hsum : (∑' n, μ (markedBoxEvent mark x n)) ≠ ⊤ :=
    ne_top_of_le_ne_top hs.tsum_ofReal_ne_top
      (tsum_le_tsum fun n => measure_markedBoxEvent_le μ mark q hq hjoint x n)
  exact ae_eventually_notMem hsum

/-- With a subcritical joint bound, finitely many marked connected boxes
meet each prescribed vertex, simultaneously at all vertices. -/
theorem markedConnectedBoxes_finite_ae (μ : Measure Ω) (mark : OrientedEdge → Set Ω) (q : ℝ)
    (hq : 0 ≤ q) (hr : (14 : ℝ) ^ 2 * q < 1)
    (hjoint : ∀ S, μ (allBad mark S) ≤ ENNReal.ofReal (q ^ S.card)) :
    ∀ᵐ ω ∂μ, ∀ x, (markedConnectedBoxes {e | ω ∈ mark e} x).Finite := by
  classical
  apply ae_all_iff.mpr
  intro x
  filter_upwards [eventually_notMem_markedBoxEvent_ae μ mark q hq hr hjoint x] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.mp hω
  let A := (Finset.range K).biUnion fun n => connectedBoxCover x n
  refine A.finite_toSet.subset ?_
  intro S hS
  obtain ⟨hm, hb, hc⟩ := hS
  obtain ⟨e, he, hcover⟩ := connected_box_has_anchor S x hb hc
  have hevent : ω ∈ markedBoxEvent mark x S.card :=
    Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he,
      Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hcover, fun f hf => hm hf⟩⟩⟩⟩
  have hsmall : S.card < K := lt_of_not_ge fun h => hK _ h hevent
  exact Finset.mem_biUnion.mpr ⟨S.card, Finset.mem_range.mpr hsmall,
    Finset.mem_biUnion.mpr ⟨e, he, hcover⟩⟩

/-- The cut-independent box finiteness event in a periodic Wilson limit. -/
theorem markedConnectedBoxes_finite_periodicLimit {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂(μ : Measure (InfiniteConfig N)), ∀ x,
      (markedConnectedBoxes {e | U ∈ markedDualLink badPlaquette e} x).Finite := by
  apply markedConnectedBoxes_finite_ae μ.toMeasure (markedDualLink badPlaquette) _
    (by positivity) (markedEdgeRate_subcritical hN hβ)
  intro S
  rw [allBad_markedDualLink]
  simpa only [Finset.card_map] using
    measure_periodicLimit_allMarked_le hN (by linarith) μ l hl hμ (S.map edgeCubeEquiv.toEmbedding)

end

end GaplessYangMills

module

public import GaplessYangMills.Components
public import GaplessYangMills.ConnectedSetCounting
public import GaplessYangMills.MarkedEdges
public import GaplessYangMills.WilsonBadPlaquettes

/-!
# Finiteness of the marked dual-edge components

Two distinct edges are adjacent when they meet at a vertex. Each endpoint
contributes at most seven other edges. The joint marked-edge estimate
therefore makes arbitrarily large connected sets through a fixed edge rare.
-/

@[expose] public section

namespace GaplessYangMills

open SimpleGraph MeasureTheory Filter
open scoped ENat ENNReal Topology

noncomputable section

section Graph

variable {V : Type*} (G : SimpleGraph V)

/-- Vertices reachable from the root using only marked vertices. -/
def markedComponent (M : Set V) (x : V) : Set V :=
  {y | ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ M}

variable [DecidableEq V]

private theorem component_has_connectedSet {M : Set V} {x : V} (n : ℕ)
    (hsize : (↑(n + 1) : ℕ∞) ≤ (markedComponent G M x).encard) :
    ∃ S : Finset V, S.card = n + 1 ∧ x ∈ S ∧ (↑S : Set V) ⊆ M ∧
      ∀ y ∈ S, ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ S := by
  classical
  induction n with
  | zero =>
    obtain ⟨y, hy⟩ := Set.one_le_encard_iff_nonempty.mp (by simpa using hsize)
    obtain ⟨p, hp⟩ := hy
    have hx : x ∈ M := hp x p.start_mem_support
    refine ⟨{x}, rfl, Finset.mem_singleton_self x, by simpa using hx, ?_⟩
    intro y hy
    obtain rfl := Finset.mem_singleton.mp hy
    exact ⟨.nil, by simp⟩
  | succ n ih =>
    have hn : (↑(n + 1) : ℕ∞) ≤ (markedComponent G M x).encard :=
      (show (↑(n + 1) : ℕ∞) ≤ ↑(n + 1 + 1) by exact_mod_cast Nat.le_succ (n + 1)).trans hsize
    obtain ⟨S, hcard, hx, hM, hS⟩ := ih hn
    obtain ⟨y, hy, hyS⟩ : ∃ y ∈ markedComponent G M x, y ∉ S := by
      by_contra! h
      have hle := Set.encard_le_encard (show markedComponent G M x ⊆ (↑S : Set V) from h)
      rw [Set.encard_coe_eq_coe_finsetCard, hcard] at hle
      have hbad := hsize.trans hle
      exact (not_le_of_gt (Nat.lt_succ_self (n + 1))) (by exact_mod_cast hbad)
    obtain ⟨p, hp⟩ := hy
    obtain ⟨a, ha, b, hb, hbS, hab⟩ := walk_crosses_finset G p S hx hyS
    refine ⟨insert b S, by rw [Finset.card_insert_of_notMem hbS, hcard],
      Finset.mem_insert_of_mem hx, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hp _ hb
      · exact hM hz
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · obtain ⟨q, hq⟩ := hS a ha
        refine ⟨q.append hab.toWalk, ?_⟩
        intro t ht
        rcases (Walk.mem_support_append_iff _ _).mp ht with ht | ht
        · exact Finset.mem_insert_of_mem (hq t ht)
        · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact Finset.mem_insert_of_mem ha
          · exact Finset.mem_insert_self _ _
      · obtain ⟨q, hq⟩ := hS z hz
        exact ⟨q, fun t ht => Finset.mem_insert_of_mem (hq t ht)⟩

variable [LocallyFinite G] {Ω : Type*} [MeasurableSpace Ω]

/-- Existence of a marked connected set of size `n` through `x`,
certified by a closed walk of the prescribed length. -/
def markedConnectedSetEvent (mark : V → Set Ω) (x : V) (n : ℕ) : Set Ω :=
  ⋃ S ∈ connectedSetCover G x n, allBad mark S

theorem measure_markedConnectedSetEvent_le (μ : Measure Ω) (mark : V → Set Ω) (d : ℕ)
    (hd : 0 < d) (hdegree : ∀ x, Fintype.card (G.neighborSet x) ≤ d)
    (q : ℝ) (hq : 0 ≤ q) (hjoint : ∀ S, μ (allBad mark S) ≤ ENNReal.ofReal (q ^ S.card))
    (x : V) (n : ℕ) :
    μ (markedConnectedSetEvent G mark x n) ≤ ENNReal.ofReal (((d : ℝ) ^ 2 * q) ^ n) := by
  let C := connectedSetCover G x n
  have hcard : C.card ≤ d ^ (2 * n) :=
    (card_connectedSetCover_le G d hdegree x n).trans (Nat.pow_le_pow_right hd (by omega))
  calc
    _ ≤ ∑ S ∈ C, μ (allBad mark S) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _S ∈ C, ENNReal.ofReal (q ^ n) := by
      apply Finset.sum_le_sum
      intro S hS
      have h := (Finset.mem_filter.mp hS).2
      simpa only [h] using hjoint S
    _ = ENNReal.ofReal ((C.card : ℝ) * q ^ n) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_pow, ← pow_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hq _)

/-- The size of a marked component through a prescribed vertex has a
geometric tail when the joint bound beats the connected-set count. -/
theorem measure_markedComponent_size_le (μ : Measure Ω) (mark : V → Set Ω) (d : ℕ)
    (hd : 0 < d) (hdegree : ∀ x, Fintype.card (G.neighborSet x) ≤ d)
    (q : ℝ) (hq : 0 ≤ q) (hjoint : ∀ S, μ (allBad mark S) ≤ ENNReal.ofReal (q ^ S.card))
    (x : V) (n : ℕ) :
    μ {ω | (↑(n + 1) : ℕ∞) ≤ (markedComponent G {e | ω ∈ mark e} x).encard} ≤
      ENNReal.ofReal (((d : ℝ) ^ 2 * q) ^ (n + 1)) := by
  apply le_trans (measure_mono (t := markedConnectedSetEvent G mark x (n + 1)) ?_)
    (measure_markedConnectedSetEvent_le G μ mark d hd hdegree q hq hjoint x (n + 1))
  intro ω hω
  obtain ⟨S, hc, hx, hm, hs⟩ := component_has_connectedSet G n hω
  have hc' : S ∈ connectedSetCover G x (n + 1) := hc ▸ mem_connectedSetCover G S hx hs
  exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨hc', fun e he => hm he⟩⟩

theorem markedComponent_finite_ae (μ : Measure Ω) (mark : V → Set Ω) (d : ℕ)
    (hd : 0 < d) (hdegree : ∀ x, Fintype.card (G.neighborSet x) ≤ d)
    (q : ℝ) (hq : 0 ≤ q) (hr : (d : ℝ) ^ 2 * q < 1)
    (hjoint : ∀ S, μ (allBad mark S) ≤ ENNReal.ofReal (q ^ S.card)) (x : V) :
    ∀ᵐ ω ∂μ, (markedComponent G {e | ω ∈ mark e} x).Finite := by
  let B := {ω | ¬(markedComponent G {e | ω ∈ mark e} x).Finite}
  have h (n : ℕ) : μ B ≤ ENNReal.ofReal (((d : ℝ) ^ 2 * q) ^ (n + 1)) := by
    refine (measure_mono ?_).trans (measure_markedComponent_size_le G μ mark d hd hdegree q hq hjoint x n)
    intro ω hω
    change (↑(n + 1) : ℕ∞) ≤ (markedComponent G {e | ω ∈ mark e} x).encard
    rw [Set.encard_eq_top hω]
    exact le_top
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (((d : ℝ) ^ 2 * q) ^ (n + 1))) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ (d : ℝ) ^ 2 * q) hr
    have hshift := hpow.comp (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hshift
  rw [ae_iff]
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hlim h) zero_le

end Graph

def dualEdgeGraph : SimpleGraph OrientedEdge where
  Adj e f := e ≠ f ∧ ∃ x, incident e x ∧ incident f x
  symm := ⟨fun _ _ ⟨hne, x, he, hf⟩ => ⟨hne.symm, x, hf, he⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def incidentEdgeFinset (x : Site) : Finset OrientedEdge :=
  (Finset.univ.image fun i : Axis => (x, i)) ∪
    (Finset.univ.image fun i : Axis => (x - step i, i))

private theorem mem_incidentEdgeFinset (x : Site) (e : OrientedEdge) :
    e ∈ incidentEdgeFinset x ↔ incident e x := by
  simp only [incidentEdgeFinset, incident, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (sub_add_cancel _ _)
  · rintro (h | h)
    · exact Or.inl ⟨e.2, Prod.ext h.symm rfl⟩
    · exact Or.inr ⟨e.2, Prod.ext (eq_sub_of_add_eq h).symm rfl⟩

private theorem card_incidentEdgeFinset_le (x : Site) : (incidentEdgeFinset x).card ≤ 8 := by
  unfold incidentEdgeFinset
  refine (Finset.card_union_le _ _).trans ?_
  have h (f : Axis → OrientedEdge) : (Finset.univ.image f).card ≤ 4 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := (Finset.univ : Finset Axis)) (f := f))
  exact Nat.add_le_add (h _) (h _)

def edgeNeighborFinset (e : OrientedEdge) : Finset OrientedEdge :=
  ((incidentEdgeFinset e.1).erase e) ∪ ((incidentEdgeFinset (e.1 + step e.2)).erase e)

theorem mem_edgeNeighborFinset (e f : OrientedEdge) :
    f ∈ edgeNeighborFinset e ↔ f ∈ dualEdgeGraph.neighborSet e := by
  change _ ↔ e ≠ f ∧ ∃ x, incident e x ∧ incident f x
  simp only [edgeNeighborFinset, Finset.mem_union, Finset.mem_erase, mem_incidentEdgeFinset]
  constructor
  · rintro (⟨hne, hf⟩ | ⟨hne, hf⟩)
    · exact ⟨hne.symm, e.1, Or.inl rfl, hf⟩
    · exact ⟨hne.symm, e.1 + step e.2, Or.inr rfl, hf⟩
  · rintro ⟨hne, x, he, hf⟩
    rcases he with rfl | rfl
    · exact Or.inl ⟨hne.symm, hf⟩
    · exact Or.inr ⟨hne.symm, hf⟩

instance dualEdgeGraph_locallyFinite : LocallyFinite dualEdgeGraph :=
  fun e => Fintype.ofFinset (edgeNeighborFinset e) (mem_edgeNeighborFinset e)

theorem dualEdgeGraph_degree_le (e : OrientedEdge) :
    Fintype.card (dualEdgeGraph.neighborSet e) ≤ 14 := by
  rw [Fintype.card_of_finset' (edgeNeighborFinset e) (mem_edgeNeighborFinset e)]
  unfold edgeNeighborFinset
  refine (Finset.card_union_le _ _).trans ?_
  have hl := Finset.card_erase_add_one ((mem_incidentEdgeFinset e.1 e).mpr (Or.inl rfl))
  have hr := Finset.card_erase_add_one ((mem_incidentEdgeFinset (e.1 + step e.2) e).mpr (Or.inr rfl))
  have hlo := card_incidentEdgeFinset_le e.1
  have hhi := card_incidentEdgeFinset_le (e.1 + step e.2)
  omega

/-- The primal indexing of an edge by its dual three-cube. -/
def edgeCubeEquiv : OrientedEdge ≃ DualEdge where
  toFun e := (if e.2 = 0 then .yzw else if e.2 = 1 then .xzw else if e.2 = 2 then .xyw else .xyz,
    -e.1)
  invFun p := (-p.2, match p.1 with | .yzw => 0 | .xzw => 1 | .xyw => 2 | .xyz => 3)
  left_inv e := by
    obtain ⟨x, i⟩ := e
    fin_cases i <;> simp
  right_inv p := by obtain ⟨c, x⟩ := p; cases c <;> simp

def markedDualLink {Ω : Type*} (bad : Plaquette → Set Ω) (e : OrientedEdge) : Set Ω :=
  {ω | ∃ p ∈ cubeFaces (edgeCubeEquiv e), ω ∈ bad p}

theorem allBad_markedDualLink {Ω : Type*} (bad : Plaquette → Set Ω)
    (S : Finset OrientedEdge) :
    allBad (markedDualLink bad) S = allMarked bad (S.map edgeCubeEquiv.toEmbedding) := by
  ext ω
  simp only [allBad, allMarked, Set.mem_ofPred_eq]
  constructor
  · intro h p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_map.mp hp
    exact h e he
  · intro h e he
    exact h (edgeCubeEquiv e) (Finset.mem_map.mpr ⟨e, he, rfl⟩)

theorem measure_dualMarkedComponent_size_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (bad : Plaquette → Set Ω) (q : ℝ) (hq : 0 ≤ q)
    (hjoint : ∀ S, μ (allMarked bad S) ≤ ENNReal.ofReal (q ^ S.card)) (x : OrientedEdge) (n : ℕ) :
    μ {ω | (↑(n + 1) : ℕ∞) ≤
      (markedComponent dualEdgeGraph {e | ω ∈ markedDualLink bad e} x).encard} ≤
        ENNReal.ofReal (((14 : ℝ) ^ 2 * q) ^ (n + 1)) := by
  apply measure_markedComponent_size_le dualEdgeGraph μ (markedDualLink bad) 14 (by decide)
    dualEdgeGraph_degree_le q hq _ x n
  intro S
  rw [allBad_markedDualLink]
  simpa only [Finset.card_map] using hjoint (S.map edgeCubeEquiv.toEmbedding)

/-- A joint marked-cube estimate with subcritical rate yields finite marked
components at every root almost surely. -/
theorem dualMarkedComponents_finite_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (bad : Plaquette → Set Ω) (q : ℝ) (hq : 0 ≤ q) (hr : (14 : ℝ) ^ 2 * q < 1)
    (hjoint : ∀ S, μ (allMarked bad S) ≤ ENNReal.ofReal (q ^ S.card)) :
    ∀ᵐ ω ∂μ, ∀ x, (markedComponent dualEdgeGraph {e | ω ∈ markedDualLink bad e} x).Finite := by
  apply ae_all_iff.mpr
  intro x
  apply markedComponent_finite_ae dualEdgeGraph μ (markedDualLink bad) 14 (by decide)
    dualEdgeGraph_degree_le q hq hr _ x
  intro S
  rw [allBad_markedDualLink]
  simpa only [Finset.card_map] using hjoint (S.map edgeCubeEquiv.toEmbedding)

theorem measure_periodicLimit_markedComponent_size_le {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 40 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (x : OrientedEdge) (n : ℕ) :
    (μ : Measure (InfiniteConfig N))
      {U | (↑(n + 1) : ℕ∞) ≤
        (markedComponent dualEdgeGraph {e | U ∈ markedDualLink badPlaquette e} x).encard} ≤
      ENNReal.ofReal (((14 : ℝ) ^ 2 * (6 * Real.exp (-(badPenalty * (N : ℝ) * β / 96)))) ^ (n + 1)) :=
  measure_dualMarkedComponent_size_le μ.toMeasure badPlaquette _ (by positivity)
    (measure_periodicLimit_allMarked_le hN hβ μ l hl hμ) x n

theorem markedEdgeRate_subcritical {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β) :
    (14 : ℝ) ^ 2 * (6 * Real.exp (-(badPenalty * (N : ℝ) * β / 96))) < 1 := by
  let q := 6 * Real.exp (-(badPenalty * (N : ℝ) * β / 96))
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hp : (Real.exp (-(badPenalty * (N : ℝ) * β / 192))) ^ 2 =
      Real.exp (-(badPenalty * (N : ℝ) * β / 96)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hρ : defectTailRate N β ^ 2 = (14 : ℝ) ^ 4 * q := by
    simp only [defectTailRate, q, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), hp]
    ring
  have hr : (14 : ℝ) ^ 2 * q < 1 := by
    calc
      _ ≤ (14 : ℝ) ^ 4 * q := mul_le_mul_of_nonneg_right (by norm_num) hq
      _ = defectTailRate N β ^ 2 := hρ.symm
      _ < 1 := by
        have hnonneg : 0 ≤ defectTailRate N β := by unfold defectTailRate; positivity
        simpa only [one_pow] using
          (sq_lt_sq₀ hnonneg zero_le_one).mpr (defectTailRate_lt_one hN hβ)
  exact hr

/-- At the coupling of Theorem 1 every marked component is finite, on
one event of full measure for the entire dual lattice. -/
theorem markedComponents_finite_periodicLimit {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ∀ᵐ U ∂(μ : Measure (InfiniteConfig N)), ∀ x,
      (markedComponent dualEdgeGraph {e | U ∈ markedDualLink badPlaquette e} x).Finite :=
  dualMarkedComponents_finite_ae μ.toMeasure badPlaquette _ (by positivity)
    (markedEdgeRate_subcritical hN hβ)
    (measure_periodicLimit_allMarked_le hN (by linarith) μ l hl hμ)

end

end GaplessYangMills

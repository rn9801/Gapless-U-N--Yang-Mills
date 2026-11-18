module

public import GaplessYangMills.FiniteGibbs
public import GaplessYangMills.WilsonLimits

/-!
# Finite changes on the infinite Wilson lattice

A finite set of links meets finitely many plaquettes. Reduction to a
sufficiently large torus is faithful on any specified finite set of cells.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

abbrev InfiniteLink := Axis × Site

def boundaryLinks (p : Face × Site) : Finset InfiniteLink :=
  {(p.1.axes.1, p.2), (p.1.axes.2, p.2 + step p.1.axes.1),
    (p.1.axes.1, p.2 + step p.1.axes.2), (p.1.axes.2, p.2)}

def plaquetteCandidates (e : InfiniteLink) : Finset (Face × Site) :=
  (Finset.univ : Finset Face) ×ˢ insert e.2 (Finset.univ.image fun j : Axis => e.2 - step j)

private theorem mem_candidates_of_mem_boundary {p : Face × Site} {e : InfiniteLink}
    (he : e ∈ boundaryLinks p) : p ∈ plaquetteCandidates e := by
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [boundaryLinks, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p.1.axes.1, Finset.mem_univ _, add_sub_cancel_right _ _⟩)
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p.1.axes.2, Finset.mem_univ _, add_sub_cancel_right _ _⟩)
  · exact Finset.mem_insert_self _ _

def affectedPlaquettes (Λ : Finset InfiniteLink) : Finset (Face × Site) :=
  (Λ.biUnion plaquetteCandidates).filter fun p => ¬Disjoint (boundaryLinks p) Λ

theorem mem_affectedPlaquettes_iff {Λ : Finset InfiniteLink} {p : Face × Site} :
    p ∈ affectedPlaquettes Λ ↔ ∃ e ∈ Λ, e ∈ boundaryLinks p := by
  have h : (¬Disjoint (boundaryLinks p) Λ) ↔ ∃ e ∈ Λ, e ∈ boundaryLinks p := by
    constructor
    · intro h
      by_contra hn
      apply h (Finset.disjoint_left.mpr ?_)
      intro e he hΛ
      exact hn ⟨e, hΛ, he⟩
    · rintro ⟨e, hΛ, he⟩ hd
      exact Finset.disjoint_left.mp hd he hΛ
  rw [affectedPlaquettes, Finset.mem_filter, h]
  constructor
  · exact And.right
  · rintro ⟨e, hΛ, he⟩
    exact ⟨Finset.mem_biUnion.mpr ⟨e, hΛ, mem_candidates_of_mem_boundary he⟩, e, hΛ, he⟩

theorem plaquetteHolonomy_congr_boundary {N : ℕ} {U V : InfiniteConfig N}
    (p : Face × Site) (h : ∀ e ∈ boundaryLinks p, U e = V e) :
    plaquetteHolonomy (fun i x => U (i, x)) p.1 p.2 =
      plaquetteHolonomy (fun i x => V (i, x)) p.1 p.2 := by
  have h₁ := h (p.1.axes.1, p.2) (by simp [boundaryLinks])
  have h₂ := h (p.1.axes.2, p.2 + step p.1.axes.1) (by simp [boundaryLinks])
  have h₃ := h (p.1.axes.1, p.2 + step p.1.axes.2) (by simp [boundaryLinks])
  have h₄ := h (p.1.axes.2, p.2) (by simp [boundaryLinks])
  obtain ⟨I, x⟩ := p
  cases I <;> simp only [plaquetteHolonomy, Face.axes] at * <;> rw [h₁, h₂, h₃, h₄]

theorem d₁_eq_zero_of_notMem_affectedPlaquettes {Λ : Finset InfiniteLink} (α : OneForm ℝ)
    (hα : ∀ e ∉ Λ, α e.1 e.2 = 0) {p : Face × Site} (hp : p ∉ affectedPlaquettes Λ) :
    d₁ α p.1 p.2 = 0 := by
  have h (e : InfiniteLink) (he : e ∈ boundaryLinks p) : α e.1 e.2 = 0 :=
    hα e (fun hΛ => hp (mem_affectedPlaquettes_iff.mpr ⟨e, hΛ, he⟩))
  have h₁ := h (p.1.axes.1, p.2) (by simp [boundaryLinks])
  have h₂ := h (p.1.axes.2, p.2 + step p.1.axes.1) (by simp [boundaryLinks])
  have h₃ := h (p.1.axes.1, p.2 + step p.1.axes.2) (by simp [boundaryLinks])
  have h₄ := h (p.1.axes.2, p.2) (by simp [boundaryLinks])
  obtain ⟨I, x⟩ := p
  cases I <;> simp only [d₁, diff, Pi.sub_apply, Face.axes] at * <;>
    rw [h₁, h₂, h₃, h₄] <;> norm_num

def torusCellReduction (L : ℕ) {ι : Type*} (p : ι × Site) : ι × TorusSite L :=
  (p.1, fun j => (p.2 j : ZMod L))

def cellSetRadius {ι : Type*} (S : Finset (ι × Site)) : ℕ :=
  S.sup fun p => Finset.univ.sup fun i : Axis => (p.2 i).natAbs

theorem torusCellReduction_injOn {ι : Type*} {L : ℕ} (S : Finset (ι × Site))
    (hL : 2 * cellSetRadius S < L) : Set.InjOn (torusCellReduction L) (↑S : Set (ι × Site)) := by
  intro p hp q hq h
  have htype : p.1 = q.1 := congrArg (fun t : ι × TorusSite L => t.1) h
  refine Prod.ext htype (funext fun i => ?_)
  have hm : (p.2 i : ZMod L) = (q.2 i : ZMod L) := congrFun (congrArg Prod.snd h) i
  have hd : (L : ℤ) ∣ q.2 i - p.2 i := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hm
  have hd' : L ∣ (q.2 i - p.2 i).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hb (r : ι × Site) (hr : r ∈ S) : (r.2 i).natAbs ≤ cellSetRadius S :=
    (Finset.le_sup (f := fun j : Axis => (r.2 j).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (s := S) (f := fun p : ι × Site =>
        Finset.univ.sup (fun j : Axis => (p.2 j).natAbs)) hr)
  have hbp := hb p hp
  have hbq := hb q hq
  by_contra hne
  have hpos : 0 < (q.2 i - p.2 i).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hlo := Nat.le_of_dvd hpos hd'
  have hhi := Int.natAbs_sub_le (q.2 i) (p.2 i)
  omega

theorem torusSiteReduction_step (L : ℕ) (x : Site) (i : Axis) :
    (fun j => ((x + step i) j : ZMod L)) =
      (fun j => (x j : ZMod L)) + torusStep L i := by
  funext j
  simp only [Pi.add_apply, Int.cast_add, torusStep]
  by_cases h : i = j <;> simp [step, h]

theorem torusBoundaryLinks_image {L : ℕ} [NeZero L] (p : Face × Site) :
    (boundaryLinks p).image (torusCellReduction L) =
      periodicBoundaryLinks (torusCellReduction L p) := by
  simp only [boundaryLinks, periodicBoundaryLinks, Finset.image_insert, Finset.image_singleton,
    torusCellReduction, torusSiteReduction_step]

private theorem torusSiteReduction_sub_step (L : ℕ) (x : Site) (i : Axis) :
    (fun j => ((x - step i) j : ZMod L)) =
      (fun j => (x j : ZMod L)) - torusStep L i := by
  have h := torusSiteReduction_step L (x - step i) i
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

private theorem torusPlaquette_lift_at_link {L : ℕ} [NeZero L] (e : InfiniteLink)
    (p : Face × TorusSite L) (he : torusCellReduction L e ∈ periodicBoundaryLinks p) :
    ∃ q : Face × Site, e ∈ boundaryLinks q ∧ torusCellReduction L q = p := by
  simp only [periodicBoundaryLinks, Finset.mem_insert, Finset.mem_singleton] at he
  have h₀ (j : Axis) (hj : torusCellReduction L e = (j, p.2)) :
      e.1 = j ∧ (fun i => (e.2 i : ZMod L)) = p.2 := Prod.mk.inj hj
  have h₁ (j k : Axis) (hj : torusCellReduction L e = (j, p.2 + torusStep L k)) :
      e.1 = j ∧ (fun i => ((e.2 - step k) i : ZMod L)) = p.2 := by
    obtain ⟨haxis, hbase⟩ := Prod.mk.inj hj
    exact ⟨haxis, by rw [torusSiteReduction_sub_step, hbase, add_sub_cancel_right]⟩
  rcases he with he | he | he | he
  · obtain ⟨hj, hx⟩ := h₀ _ he
    refine ⟨(p.1, e.2), ?_, Prod.ext rfl hx⟩
    simp only [boundaryLinks, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl (Prod.ext hj rfl)
  · obtain ⟨hj, hx⟩ := h₁ _ _ he
    refine ⟨(p.1, e.2 - step p.1.axes.1), ?_, Prod.ext rfl hx⟩
    have hEq : e = (p.1.axes.2, (e.2 - step p.1.axes.1) + step p.1.axes.1) :=
      Prod.ext hj (sub_add_cancel _ _).symm
    simp only [boundaryLinks, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inl hEq)
  · obtain ⟨hj, hx⟩ := h₁ _ _ he
    refine ⟨(p.1, e.2 - step p.1.axes.2), ?_, Prod.ext rfl hx⟩
    have hEq : e = (p.1.axes.1, (e.2 - step p.1.axes.2) + step p.1.axes.2) :=
      Prod.ext hj (sub_add_cancel _ _).symm
    simp only [boundaryLinks, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr (Or.inl hEq))
  · obtain ⟨hj, hx⟩ := h₀ _ he
    refine ⟨(p.1, e.2), ?_, Prod.ext rfl hx⟩
    have hEq : e = (p.1.axes.2, e.2) := Prod.ext hj rfl
    simp only [boundaryLinks, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr (Or.inr hEq))

private theorem mem_periodicAffectedPlaquettes_iff {L : ℕ} [NeZero L]
    {Λ : Finset (TorusLink L)} {p : Face × TorusSite L} :
    p ∈ periodicAffectedPlaquettes Λ ↔ ∃ e ∈ Λ, e ∈ periodicBoundaryLinks p := by
  rw [periodicAffectedPlaquettes, Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
  constructor
  · intro h
    by_contra hn
    apply h (Finset.disjoint_left.mpr ?_)
    intro e he hΛ
    exact hn ⟨e, hΛ, he⟩
  · rintro ⟨e, hΛ, he⟩ hd
    exact Finset.disjoint_left.mp hd he hΛ

theorem periodicAffectedPlaquettes_image {L : ℕ} [NeZero L] (Λ : Finset InfiniteLink) :
    periodicAffectedPlaquettes (Λ.image (torusCellReduction L)) =
      (affectedPlaquettes Λ).image (torusCellReduction L) := by
  ext p
  rw [mem_periodicAffectedPlaquettes_iff, Finset.mem_image]
  constructor
  · rintro ⟨e', he', hb⟩
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨q, hq, hr⟩ := torusPlaquette_lift_at_link e p hb
    exact ⟨q, mem_affectedPlaquettes_iff.mpr ⟨e, he, hq⟩, hr⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨e, he, hb⟩ := mem_affectedPlaquettes_iff.mp hq
    refine ⟨torusCellReduction L e, Finset.mem_image_of_mem _ he, ?_⟩
    rw [← torusBoundaryLinks_image]
    exact Finset.mem_image_of_mem _ hb

theorem periodicHolonomy_extendPeriodic {L N : ℕ} (U : TorusConfig L N) (p : Face × Site) :
    plaquetteHolonomy (fun i x => extendPeriodic U (i, x)) p.1 p.2 =
      periodicHolonomy U (torusCellReduction L p).1 (torusCellReduction L p).2 := by
  simp only [plaquetteHolonomy, periodicHolonomy, extendPeriodic, torusCellReduction, torusSiteReduction_step]

end

end GaplessYangMills

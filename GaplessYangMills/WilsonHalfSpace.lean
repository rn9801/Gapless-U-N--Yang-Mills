module

public import GaplessYangMills.WilsonBondLimit
public import GaplessYangMills.WilsonProjection
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Positive-time observables in Euclidean Wilson L²

The Euclidean half-space is the closure of the continuous, gauge-invariant
cylinder observables supported on positive-time links. An inward shift
preserves this closed subspace.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped BoundedContinuousFunction InnerProductSpace Topology

noncomputable section

namespace HalfSpaceCylinder

theorem zero {N : ℕ} (τ : Axis) (k : ℤ) : HalfSpaceCylinder (N := N) τ k 0 :=
  ⟨∅, fun _ h => (Finset.notMem_empty _ h).elim, fun _ _ _ => rfl⟩

theorem add {N : ℕ} {τ : Axis} {k : ℤ} {f g : InfiniteConfig N → ℝ}
    (hf : HalfSpaceCylinder τ k f) (hg : HalfSpaceCylinder τ k g) :
    HalfSpaceCylinder τ k (f + g) := by
  obtain ⟨S, hS, hs⟩ := hf
  obtain ⟨T, hT, ht⟩ := hg
  refine ⟨S ∪ T, fun e he => (Finset.mem_union.mp he).elim (hS e) (hT e), ?_⟩
  intro U V h
  exact congrArg₂ (· + ·) (hs U V fun e he => h e (Finset.mem_union_left _ he))
    (ht U V fun e he => h e (Finset.mem_union_right _ he))

theorem smul {N : ℕ} {τ : Axis} {k : ℤ} {f : InfiniteConfig N → ℝ}
    (hf : HalfSpaceCylinder τ k f) (c : ℝ) : HalfSpaceCylinder τ k (c • f) := by
  obtain ⟨S, hS, hs⟩ := hf
  exact ⟨S, hS, fun U V h => congrArg (c * ·) (hs U V h)⟩

theorem translate {N : ℕ} {τ : Axis} {k : ℤ} {f : InfiniteConfig N → ℝ}
    (hf : HalfSpaceCylinder τ k f) (a : Site) :
    HalfSpaceCylinder τ (k + a τ) (fun U => f (translateConfig a U)) := by
  classical
  obtain ⟨S, ht, hs⟩ := hf
  let E (e : Axis × Site) := (e.1, e.2 + a)
  refine ⟨S.image E, ?_, ?_⟩
  · intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    change k + a τ ≤ d.2 τ + a τ
    exact add_le_add (ht d hd) le_rfl
  · intro U V h
    exact hs _ _ fun e he => h (E e) (Finset.mem_image_of_mem E he)

theorem weaken {N : ℕ} {τ : Axis} {k k' : ℤ} {f : InfiniteConfig N → ℝ}
    (hf : HalfSpaceCylinder τ k f) (hk : k' ≤ k) : HalfSpaceCylinder τ k' f := by
  obtain ⟨S, hS, hs⟩ := hf
  exact ⟨S, fun e he => hk.trans (hS e he), hs⟩

end HalfSpaceCylinder

theorem translateConfig_gaugeConfig {N : ℕ} (a : Site) (g : Site → UnitaryMatrix N)
    (U : InfiniteConfig N) :
    translateConfig a (gaugeConfig g U) =
      gaugeConfig (fun x => g (x + a)) (translateConfig a U) := by
  funext e
  obtain ⟨i, x⟩ := e
  simp only [translateConfig, gaugeConfig, add_right_comm x a (step i)]

theorem GaugeInvariantObservable.translate {N : ℕ} {f : InfiniteConfig N → ℝ}
    (hf : GaugeInvariantObservable f) (a : Site) :
    GaugeInvariantObservable (fun U => f (translateConfig a U)) := by
  intro g U
  change f (translateConfig a (gaugeConfig g U)) = f (translateConfig a U)
  rw [translateConfig_gaugeConfig]
  exact hf _ _

def wilsonHalfSpaceCore (N : ℕ) (τ : Axis) : Submodule ℝ (InfiniteConfig N →ᵇ ℝ) where
  carrier := {f | HalfSpaceCylinder τ 0 f ∧ GaugeInvariantObservable f}
  zero_mem' := ⟨HalfSpaceCylinder.zero τ 0, fun _ _ => rfl⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, fun g U => congrArg₂ (· + ·) (hf.2 g U) (hg.2 g U)⟩
  smul_mem' := fun c _ hf => ⟨hf.1.smul c, fun g U => congrArg (c * ·) (hf.2 g U)⟩

def wilsonHalfSpaceCoreL2 {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) (τ : Axis) :
    wilsonHalfSpaceCore N τ →ₗ[ℝ] WilsonL2 μ :=
  (BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ).toLinearMap.comp (wilsonHalfSpaceCore N τ).subtype

def wilsonHalfSpace {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) (τ : Axis) :
    Submodule ℝ (WilsonL2 μ) :=
  (wilsonHalfSpaceCoreL2 μ τ).range.topologicalClosure

theorem wilsonHalfSpace_isClosed {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) (τ : Axis) :
    IsClosed (wilsonHalfSpace μ τ : Set (WilsonL2 μ)) :=
  Submodule.isClosed_topologicalClosure _

theorem wilsonTranslateL2_toLp {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (a : Site) (f : InfiniteConfig N →ᵇ ℝ) :
    wilsonTranslateL2 μ hμ a (BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ f) =
      BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ
        (f.compContinuous ⟨translateConfig a, continuous_translateConfig a⟩) := by
  let ha := measurePreserving_translateConfig μ hμ a
  let fl := BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ f
  let g := f.compContinuous ⟨translateConfig a, continuous_translateConfig a⟩
  change Lp.compMeasurePreserving _ ha fl = BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ g
  apply Lp.ext
  have hf : (fl : InfiniteConfig N → ℝ) =ᵐ[μ.toMeasure] f :=
    BoundedContinuousFunction.coeFn_toLp 2 μ.toMeasure ℝ f
  filter_upwards [Lp.coeFn_compMeasurePreserving fl ha, ha.quasiMeasurePreserving.ae hf,
    BoundedContinuousFunction.coeFn_toLp 2 μ.toMeasure ℝ g] with U h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

theorem wilsonTranslateL2_halfSpace {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (τ : Axis) (a : Site) (ha : 0 ≤ a τ) {u : WilsonL2 μ} (hu : u ∈ wilsonHalfSpace μ τ) :
    wilsonTranslateL2 μ hμ a u ∈ wilsonHalfSpace μ τ := by
  let S := wilsonTranslateL2 μ hμ a
  have hclosed := (wilsonHalfSpace_isClosed μ τ).preimage S.continuous
  apply (closure_minimal (s := ((wilsonHalfSpaceCoreL2 μ τ).range : Set (WilsonL2 μ))) _ hclosed) hu
  rintro _ ⟨f, rfl⟩
  let g : InfiniteConfig N →ᵇ ℝ := f.val.compContinuous ⟨translateConfig a, continuous_translateConfig a⟩
  have hg : g ∈ wilsonHalfSpaceCore N τ :=
    ⟨(f.property.1.translate a).weaken (by simpa only [zero_add] using ha), f.property.2.translate a⟩
  change S (BoundedContinuousFunction.toLp 2 μ.toMeasure ℝ f.val) ∈ wilsonHalfSpace μ τ
  rw [wilsonTranslateL2_toLp]
  exact Submodule.le_topologicalClosure _ ⟨⟨g, hg⟩, rfl⟩

end

end GaplessYangMills

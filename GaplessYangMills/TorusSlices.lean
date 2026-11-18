module

public import GaplessYangMills.FiniteWilson
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.Group

/-!
# Spatial slices of the periodic lattice

Tangential links in a slice and normal links to the next slice form disjoint
coordinates. A temporal plaquette compares a tangential link with the
corresponding link in the next slice after vertex gauge transport.
-/

@[expose] public section

namespace GaplessYangMills

open MeasureTheory

noncomputable section

abbrev SpatialAxis (τ : Axis) := {i : Axis // i ≠ τ}
abbrev SpatialSite (L : ℕ) (τ : Axis) := SpatialAxis τ → ZMod L
abbrev SpatialLink (L : ℕ) (τ : Axis) := SpatialAxis τ × SpatialSite L τ
abbrev SliceConfig (L N : ℕ) (τ : Axis) := SpatialLink L τ → UnitaryMatrix N
abbrev SliceGauge (L N : ℕ) (τ : Axis) := SpatialSite L τ → UnitaryMatrix N

/-- Insert the time coordinate into a spatial site. -/
def torusSliceSite {L : ℕ} (τ : Axis) (t : ZMod L) (x : SpatialSite L τ) : TorusSite L :=
  fun i => if h : i = τ then t else x ⟨i, h⟩

@[simp] theorem torusSliceSite_time {L : ℕ} {τ : Axis} (t : ZMod L) (x : SpatialSite L τ) :
    torusSliceSite τ t x τ = t := by simp [torusSliceSite]

@[simp] theorem torusSliceSite_space {L : ℕ} {τ : Axis} (t : ZMod L) (x : SpatialSite L τ)
    (i : SpatialAxis τ) : torusSliceSite τ t x i = x i := by simp [torusSliceSite, i.property]

def torusSliceSiteEquiv (L : ℕ) (τ : Axis) : ZMod L × SpatialSite L τ ≃ TorusSite L where
  toFun p := torusSliceSite τ p.1 p.2
  invFun x := (x τ, fun i => x i)
  left_inv p := by simp
  right_inv x := by
    funext i
    by_cases hi : i = τ
    · subst i
      exact torusSliceSite_time _ _
    · simp [torusSliceSite, hi]

def spatialStep (L : ℕ) {τ : Axis} (i : SpatialAxis τ) : SpatialSite L τ :=
  fun j => torusStep L i j

theorem torusSliceSite_step_time {L : ℕ} {τ : Axis} (t : ZMod L) (x : SpatialSite L τ) :
    torusSliceSite τ t x + torusStep L τ = torusSliceSite τ (t + 1) x := by
  funext i
  by_cases hi : i = τ
  · subst i
    simp [torusStep]
  · simp [torusSliceSite, torusStep, hi, Ne.symm hi]

theorem torusSliceSite_step_space {L : ℕ} {τ : Axis} (t : ZMod L) (x : SpatialSite L τ)
    (i : SpatialAxis τ) :
    torusSliceSite τ t x + torusStep L i = torusSliceSite τ t (x + spatialStep L i) := by
  funext j
  by_cases hj : j = τ
  · subst j
    simp [torusStep, i.property]
  · simp [torusSliceSite, spatialStep, hj]

def applySliceGauge {L N : ℕ} {τ : Axis} (g : SliceGauge L N τ) (U : SliceConfig L N τ) :
    SliceConfig L N τ :=
  fun e => g e.2 * U e * (g (e.2 + spatialStep L e.1))⁻¹

instance sliceGaugeAction (L N : ℕ) (τ : Axis) :
    MulAction (SliceGauge L N τ) (SliceConfig L N τ) where
  smul := applySliceGauge
  one_smul U := by
    funext e
    change (1 : UnitaryMatrix N) * U e * (1 : UnitaryMatrix N)⁻¹ = U e
    rw [one_mul, inv_one, mul_one]
  mul_smul g h U := by
    funext e
    change (g e.2 * h e.2) * U e *
      (g (e.2 + spatialStep L e.1) * h (e.2 + spatialStep L e.1))⁻¹ =
        g e.2 * (h e.2 * U e * (h (e.2 + spatialStep L e.1))⁻¹) *
          (g (e.2 + spatialStep L e.1))⁻¹
    group

theorem sliceGauge_smul_apply {L N : ℕ} {τ : Axis}
    (g : SliceGauge L N τ) (U : SliceConfig L N τ) (e : SpatialLink L τ) :
    (g • U) e = g e.2 * U e * (g (e.2 + spatialStep L e.1))⁻¹ := rfl

theorem sliceGauge_smul_eq {L N : ℕ} {τ : Axis}
    (g : SliceGauge L N τ) (U : SliceConfig L N τ) : g • U = applySliceGauge g U := rfl

instance sliceGaugeContinuous (L N : ℕ) (τ : Axis) :
    ContinuousSMul (SliceGauge L N τ) (SliceConfig L N τ) where
  continuous_smul := by
    apply continuous_pi
    intro e
    exact (((continuous_apply e.2).comp continuous_fst).mul
      ((continuous_apply e).comp continuous_snd)).mul
        ((continuous_apply (e.2 + spatialStep L e.1)).comp continuous_fst).inv

def sliceHaar (L N : ℕ) (τ : Axis) [NeZero L] : Measure (SliceConfig L N τ) :=
  Measure.pi fun _ => unitaryHaar N

def sliceGaugeHaar (L N : ℕ) (τ : Axis) [NeZero L] : Measure (SliceGauge L N τ) :=
  Measure.pi fun _ => unitaryHaar N

instance sliceHaar_probability (L N : ℕ) (τ : Axis) [NeZero L] :
    IsProbabilityMeasure (sliceHaar L N τ) := by
  unfold sliceHaar
  infer_instance

instance sliceGaugeHaar_probability (L N : ℕ) (τ : Axis) [NeZero L] :
    IsProbabilityMeasure (sliceGaugeHaar L N τ) := by
  unfold sliceGaugeHaar
  infer_instance

instance sliceGaugeHaar_leftInvariant (L N : ℕ) (τ : Axis) [NeZero L] :
    (sliceGaugeHaar L N τ).IsMulLeftInvariant where
  map_mul_left_eq_self g :=
    (measurePreserving_pi _ _ (fun x => measurePreserving_mul_left (unitaryHaar N) (g x))).map_eq

abbrev TorusSliceCoords (L N : ℕ) (τ : Axis) :=
  (ZMod L → SliceConfig L N τ) × (ZMod L → SliceGauge L N τ)

def torusSliceLinkEquiv (L : ℕ) (τ : Axis) : TorusLink L ≃
    (Σ _ : ZMod L, SpatialLink L τ) ⊕ (Σ _ : ZMod L, SpatialSite L τ) where
  toFun e := if h : e.1 = τ then .inr ⟨e.2 τ, fun i => e.2 i⟩
    else .inl ⟨e.2 τ, ⟨⟨e.1, h⟩, fun i => e.2 i⟩⟩
  invFun
    | .inl ⟨t, i, x⟩ => (i, torusSliceSite τ t x)
    | .inr ⟨t, x⟩ => (τ, torusSliceSite τ t x)
  left_inv e := by
    obtain ⟨i, x⟩ := e
    have h := (torusSliceSiteEquiv L τ).right_inv x
    change torusSliceSite τ (x τ) (fun j => x j) = x at h
    by_cases hi : i = τ <;> simp [hi, h]
  right_inv e := by
    rcases e with ⟨t, i, x⟩ | ⟨t, x⟩
    · simp [i.property]
    · simp

private theorem measurePreserving_curry {I : Type*} {J : I → Type*} [Fintype I]
    [∀ i, Fintype (J i)] {X : (i : I) → J i → Type*} [∀ i j, MeasurableSpace (X i j)]
    (μ : ∀ i j, Measure (X i j)) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry X) (Measure.pi fun ij => μ ij.1 ij.2)
      (Measure.pi fun i => Measure.pi (μ i)) := by
  let e := MeasurableEquiv.piCurry X
  refine MeasurePreserving.symm e.symm ⟨e.symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s _ => ?_).symm
  have he : e.symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i, j⟩)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, e, MeasurableEquiv.coe_piCurry_symm,
      Sigma.uncurry]
    exact ⟨fun h i j => h ⟨i, j⟩, fun h ij => h ij.1 ij.2⟩
  rw [e.symm.map_apply, he, Measure.pi_pi, Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun i _ => Measure.pi_pi _ _

/-- Assemble the torus links from the slice links and the normal links. -/
def periodicSliceAssembly (L N : ℕ) (τ : Axis) :
    TorusSliceCoords L N τ ≃ᵐ TorusConfig L N :=
  let ea := MeasurableEquiv.piCurry (fun (_ : ZMod L) (_ : SpatialLink L τ) => UnitaryMatrix N)
  let eg := MeasurableEquiv.piCurry (fun (_ : ZMod L) (_ : SpatialSite L τ) => UnitaryMatrix N)
  let es := MeasurableEquiv.sumPiEquivProdPi (fun _ => UnitaryMatrix N)
  let el := MeasurableEquiv.piCongrLeft (fun _ => UnitaryMatrix N) (torusSliceLinkEquiv L τ)
  ((ea.symm.prodCongr eg.symm).trans es.symm).trans el.symm

theorem periodicSliceAssembly_preserving (L N : ℕ) (τ : Axis) [NeZero L] :
    MeasurePreserving (periodicSliceAssembly L N τ)
      ((Measure.pi fun _ : ZMod L => sliceHaar L N τ).prod
        (Measure.pi fun _ : ZMod L => sliceGaugeHaar L N τ)) (periodicHaar L N) := by
  have ha := (measurePreserving_curry (X := fun (_ : ZMod L) (_ : SpatialLink L τ) =>
    UnitaryMatrix N) (fun _ _ => unitaryHaar N)).symm _
  have hg := (measurePreserving_curry (X := fun (_ : ZMod L) (_ : SpatialSite L τ) =>
    UnitaryMatrix N) (fun _ _ => unitaryHaar N)).symm _
  have hs := (measurePreserving_sumPiEquivProdPi (fun _ :
    (Σ _ : ZMod L, SpatialLink L τ) ⊕ (Σ _ : ZMod L, SpatialSite L τ) => unitaryHaar N)).symm _
  have hl := (measurePreserving_piCongrLeft (fun _ => unitaryHaar N)
    (torusSliceLinkEquiv L τ)).symm _
  exact hl.comp (hs.comp (ha.prod hg))

@[simp] theorem periodicSliceAssembly_tangent {L N : ℕ} {τ : Axis} (A : TorusSliceCoords L N τ)
    (t : ZMod L) (i : SpatialAxis τ) (x : SpatialSite L τ) :
    periodicSliceAssembly L N τ A (i, torusSliceSite τ t x) = A.1 t (i, x) := by
  have he : torusSliceLinkEquiv L τ (i, torusSliceSite τ t x) = .inl ⟨t, i, x⟩ := by
    simp [torusSliceLinkEquiv, i.property]
  change (Equiv.sumPiEquivProdPi (fun _ => UnitaryMatrix N)).symm
    (Sigma.uncurry A.1, Sigma.uncurry A.2)
    (torusSliceLinkEquiv L τ (i, torusSliceSite τ t x)) = _
  rw [he]
  rfl

@[simp] theorem periodicSliceAssembly_normal {L N : ℕ} {τ : Axis} (A : TorusSliceCoords L N τ)
    (t : ZMod L) (x : SpatialSite L τ) :
    periodicSliceAssembly L N τ A (τ, torusSliceSite τ t x) = A.2 t x := by
  have he : torusSliceLinkEquiv L τ (τ, torusSliceSite τ t x) = .inr ⟨t, x⟩ := by
    simp [torusSliceLinkEquiv]
  change (Equiv.sumPiEquivProdPi (fun _ => UnitaryMatrix N)).symm
    (Sigma.uncurry A.1, Sigma.uncurry A.2)
    (torusSliceLinkEquiv L τ (τ, torusSliceSite τ t x)) = _
  rw [he]
  rfl

/-- The ordered holonomy of a plaquette contained in one spatial slice. -/
def sliceHolonomy {L N : ℕ} {τ : Axis} (A : SliceConfig L N τ) (i j : SpatialAxis τ)
    (x : SpatialSite L τ) : UnitaryMatrix N :=
  A (i, x) * A (j, x + spatialStep L i) * (A (i, x + spatialStep L j))⁻¹ * (A (j, x))⁻¹

theorem sliceHolonomy_gauge {L N : ℕ} {τ : Axis} (A : SliceConfig L N τ)
    (g : SliceGauge L N τ) (i j : SpatialAxis τ) (x : SpatialSite L τ) :
    sliceHolonomy (g • A) i j x = g x * sliceHolonomy A i j x * (g x)⁻¹ := by
  simp only [sliceHolonomy, sliceGauge_smul_apply]
  rw [add_right_comm x (spatialStep L i) (spatialStep L j)]
  group

theorem periodicHolonomy_assembly_spatial {L N : ℕ} {τ : Axis} (A : TorusSliceCoords L N τ)
    (t : ZMod L) (I : Face) (x : SpatialSite L τ) (hi : I.axes.1 ≠ τ) (hj : I.axes.2 ≠ τ) :
    periodicHolonomy (periodicSliceAssembly L N τ A) I (torusSliceSite τ t x) =
      sliceHolonomy (A.1 t) ⟨I.axes.1, hi⟩ ⟨I.axes.2, hj⟩ x := by
  let i : SpatialAxis τ := ⟨I.axes.1, hi⟩
  let j : SpatialAxis τ := ⟨I.axes.2, hj⟩
  change periodicSliceAssembly L N τ A (i, torusSliceSite τ t x) *
    periodicSliceAssembly L N τ A (j, torusSliceSite τ t x + torusStep L i) *
    (periodicSliceAssembly L N τ A (i, torusSliceSite τ t x + torusStep L j))⁻¹ *
    (periodicSliceAssembly L N τ A (j, torusSliceSite τ t x))⁻¹ = _
  rw [torusSliceSite_step_space t x i, torusSliceSite_step_space t x j]
  rw [periodicSliceAssembly_tangent A t i x,
    periodicSliceAssembly_tangent A t j (x + spatialStep L i),
    periodicSliceAssembly_tangent A t i (x + spatialStep L j),
    periodicSliceAssembly_tangent A t j x]
  rfl

theorem periodicHolonomy_assembly_timeFirst {L N : ℕ} {τ : Axis} (A : TorusSliceCoords L N τ)
    (t : ZMod L) (I : Face) (x : SpatialSite L τ) (hi : I.axes.1 = τ) (hj : I.axes.2 ≠ τ) :
    periodicHolonomy (periodicSliceAssembly L N τ A) I (torusSliceSite τ t x) =
      (A.1 t (⟨I.axes.2, hj⟩, x) *
        ((A.2 t • A.1 (t + 1)) (⟨I.axes.2, hj⟩, x))⁻¹)⁻¹ := by
  let j : SpatialAxis τ := ⟨I.axes.2, hj⟩
  change periodicSliceAssembly L N τ A (I.axes.1, torusSliceSite τ t x) *
    periodicSliceAssembly L N τ A (j, torusSliceSite τ t x + torusStep L I.axes.1) *
    (periodicSliceAssembly L N τ A (I.axes.1, torusSliceSite τ t x + torusStep L j))⁻¹ *
    (periodicSliceAssembly L N τ A (j, torusSliceSite τ t x))⁻¹ = _
  rw [hi, torusSliceSite_step_time, torusSliceSite_step_space t x j]
  rw [periodicSliceAssembly_tangent A (t + 1) j x, periodicSliceAssembly_tangent A t j x]
  simp only [periodicSliceAssembly_normal, sliceGauge_smul_apply, j]
  group

theorem periodicHolonomy_assembly_timeSecond {L N : ℕ} {τ : Axis} (A : TorusSliceCoords L N τ)
    (t : ZMod L) (I : Face) (x : SpatialSite L τ) (hi : I.axes.1 ≠ τ) (hj : I.axes.2 = τ) :
    periodicHolonomy (periodicSliceAssembly L N τ A) I (torusSliceSite τ t x) =
      A.1 t (⟨I.axes.1, hi⟩, x) *
        ((A.2 t • A.1 (t + 1)) (⟨I.axes.1, hi⟩, x))⁻¹ := by
  let i : SpatialAxis τ := ⟨I.axes.1, hi⟩
  change periodicSliceAssembly L N τ A (i, torusSliceSite τ t x) *
    periodicSliceAssembly L N τ A (I.axes.2, torusSliceSite τ t x + torusStep L i) *
    (periodicSliceAssembly L N τ A (i, torusSliceSite τ t x + torusStep L I.axes.2))⁻¹ *
    (periodicSliceAssembly L N τ A (I.axes.2, torusSliceSite τ t x))⁻¹ = _
  rw [hj, torusSliceSite_step_space t x i, torusSliceSite_step_time]
  rw [periodicSliceAssembly_tangent A t i x, periodicSliceAssembly_tangent A (t + 1) i x]
  simp only [periodicSliceAssembly_normal, sliceGauge_smul_apply, i]
  group

end

end GaplessYangMills

module

public import GaplessYangMills.CutNormalization
public import GaplessYangMills.ShiftMeans
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Directional vacuum projections for the Wilson covariance

Each projection is the orthogonal projection in Euclidean `L²` onto the
invariant functions of a lattice translation. The projected two-point
function satisfies both Ward identities of equation (8).
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped InnerProductSpace Topology

noncomputable section

abbrev WilsonL2 {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) := Lp ℝ 2 μ.toMeasure

theorem measurePreserving_translateConfig {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (a : Site) :
    MeasurePreserving (translateConfig a) μ.toMeasure μ.toMeasure :=
  ⟨(continuous_translateConfig a).measurable,
    congrArg ProbabilityMeasure.toMeasure (periodicWilson_limit_translate β μ hμ a)⟩

def wilsonTranslateL2 {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (a : Site) :
    WilsonL2 μ →L[ℝ] WilsonL2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ (translateConfig a) (measurePreserving_translateConfig μ hμ a)).toContinuousLinearMap

theorem norm_wilsonTranslateL2_apply {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (a : Site)
    (f : WilsonL2 μ) : ‖wilsonTranslateL2 μ hμ a f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f (measurePreserving_translateConfig μ hμ a)

theorem norm_wilsonTranslateL2_le_one {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (a : Site) :
    ‖wilsonTranslateL2 μ hμ a‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [norm_wilsonTranslateL2_apply, one_mul]

theorem wilsonTranslateL2_mul {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (a b : Site) :
    wilsonTranslateL2 μ hμ a * wilsonTranslateL2 μ hμ b =
      wilsonTranslateL2 μ hμ (a + b) := by
  ext1 f
  let ha := measurePreserving_translateConfig μ hμ a
  let hb := measurePreserving_translateConfig μ hμ b
  change Lp.compMeasurePreserving _ ha (Lp.compMeasurePreserving _ hb f) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  have he : (translateConfig b : InfiniteConfig N → InfiniteConfig N) ∘ translateConfig a =
      translateConfig (a + b) := by
    funext U e
    obtain ⟨i, x⟩ := e
    simp only [Function.comp_apply, translateConfig]
    rw [add_assoc, add_comm b a]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (hb.comp ha),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_translateConfig μ hμ (a + b))] with U h₁ h₂
  exact h₁.trans ((congrArg (fun V => f V) (congrFun he U)).trans h₂.symm)

abbrev wilsonInvariantSpace {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (i : Axis) :
    Submodule ℝ (WilsonL2 μ) :=
  (wilsonTranslateL2 μ hμ (step i)).eqLocus (1 : WilsonL2 μ →L[ℝ] WilsonL2 μ)

def wilsonDirectionalProjection {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (i : Axis) :
    WilsonL2 μ →L[ℝ] WilsonL2 μ :=
  (wilsonInvariantSpace μ hμ i).starProjection

theorem wilsonDirectionalProjection_commute {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (i j : Axis) :
    Commute (wilsonDirectionalProjection μ hμ i) (wilsonDirectionalProjection μ hμ j) := by
  let S (k : Axis) := wilsonTranslateL2 μ hμ (step k)
  have hnorm (k : Axis) : ‖S k‖ ≤ 1 := norm_wilsonTranslateL2_le_one μ hμ (step k)
  have hc : Commute (S j) (S i) := by
    show S j * S i = S i * S j
    simp only [S, wilsonTranslateL2_mul, add_comm (step j) (step i)]
  exact commute_invariantProjection _ (S j) (hnorm j)
    (commute_invariantProjection (S j) (S i) (hnorm i) hc).symm

theorem memLp_iidAveragedFlux {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (I : Face) (x : Site) :
    MemLp (fun U => averagedFlux iidCutLaw U I x) 2 μ.toMeasure :=
  ((iidAveragedFlux_exponential_approximation_periodicLimit hN hβ μ l hl hμ).2 I x).1

def wilsonFluxL2 {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (I : Face) (x : Site) :
    WilsonL2 μ :=
  (memLp_iidAveragedFlux hN hβ μ l hl hμ I x).toLp _

theorem memLp_centeredPlaquetteCurrent {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) (p : Plaquette) :
    MemLp (fun U => centeredPlaquetteCurrent μ.toMeasure U p) 2 μ.toMeasure := by
  have h := continuous_centeredPlaquetteCurrent μ.toMeasure p
  obtain ⟨C, hC⟩ := (isCompact_univ.image h.norm).bddAbove
  exact MemLp.of_bound h.measurable.aestronglyMeasurable C (ae_of_all _ fun U => hC ⟨U, Set.mem_univ _, rfl⟩)

def wilsonCurrentL2 {N : ℕ} (μ : ProbabilityMeasure (InfiniteConfig N)) (p : Plaquette) : WilsonL2 μ :=
  (memLp_centeredPlaquetteCurrent μ p).toLp _

theorem wilsonTranslateL2_flux {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (a : Site) (I : Face) (x : Site) :
    wilsonTranslateL2 μ hμ a (wilsonFluxL2 hN hβ μ l hl hμ I x) =
      wilsonFluxL2 hN hβ μ l hl hμ I (x + a) := by
  let hf := memLp_iidAveragedFlux hN hβ μ l hl hμ I x
  let hf' := memLp_iidAveragedFlux hN hβ μ l hl hμ I (x + a)
  let ha := measurePreserving_translateConfig μ hμ a
  change Lp.compMeasurePreserving _ ha (hf.toLp _) = hf'.toLp _
  rw [Lp.toLp_compMeasurePreserving hf ha]
  exact MemLp.toLp_congr _ _ (ae_of_all _ fun U => iidAveragedFlux_translate a U I x)

def wilsonL2Covariance {N : ℕ} {μ : ProbabilityMeasure (InfiniteConfig N)}
    (F : Face → Site → WilsonL2 μ) (J : Face → WilsonL2 μ) : Kernel :=
  fun I K x => ⟪J K, F I x⟫_ℝ

theorem wilsonL2Covariance_eq {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    wilsonL2Covariance (wilsonFluxL2 hN hβ μ l hl hμ) (fun J => wilsonCurrentL2 μ (J, 0)) =
      wilsonFluxCurrentCovariance μ.toMeasure := by
  funext I J x
  rw [wilsonL2Covariance, wilsonFluxCurrentCovariance, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_iidAveragedFlux hN hβ μ l hl hμ I x).coeFn_toLp,
    (memLp_centeredPlaquetteCurrent μ (J, 0)).coeFn_toLp] with U hF hJ
  rw [Real.inner_apply]
  exact congrArg₂ (· * ·) hJ hF |>.trans (mul_comm _ _)

/-- Reflecting the mean between inner-product arguments realizes the
directional covariance average by a projection of the current. -/
theorem wilsonL2Covariance_hasDirectionalMean {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (i : Axis) (I : Face) (j : WilsonL2 μ) :
    HasDirectionalMean i (fun x => ⟪j, wilsonFluxL2 hN hβ μ l hl hμ I x⟫_ℝ)
      (fun x => ⟪wilsonDirectionalProjection μ hμ i j, wilsonFluxL2 hN hβ μ l hl hμ I x⟫_ℝ) := by
  let S := wilsonTranslateL2 μ hμ (step i)
  have h := hasDirectionalMean_of_hilbert_shift i S (norm_wilsonTranslateL2_le_one μ hμ (step i))
    j (wilsonFluxL2 hN hβ μ l hl hμ I) (wilsonTranslateL2_flux hN hβ μ l hl hμ (step i) I)
  have he : (fun x => ⟪j, wilsonDirectionalProjection μ hμ i (wilsonFluxL2 hN hβ μ l hl hμ I x)⟫_ℝ) =
      fun x => ⟪wilsonDirectionalProjection μ hμ i j, wilsonFluxL2 hN hβ μ l hl hμ I x⟫_ℝ :=
    funext fun x => ((wilsonInvariantSpace μ hμ i).inner_starProjection_left_eq_right j
      (wilsonFluxL2 hN hβ μ l hl hμ I x)).symm
  rw [← he]
  exact h

def removeWilsonDirections {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))
    (directions : List Axis) : WilsonL2 μ →L[ℝ] WilsonL2 μ :=
  directions.foldr (fun i T => (1 - wilsonDirectionalProjection μ hμ i) * T) 1

theorem removeWilsonDirections_norm_le_one {N : ℕ} {β : ℝ} {l : ℕ → ℕ}
    (μ : ProbabilityMeasure (InfiniteConfig N))
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) (ds : List Axis) :
    ‖removeWilsonDirections μ hμ ds‖ ≤ 1 := by
  induction ds with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons i ds ih =>
    have h : ‖1 - wilsonDirectionalProjection μ hμ i‖ ≤ 1 := by
      change ‖ContinuousLinearMap.id ℝ (WilsonL2 μ) - (wilsonInvariantSpace μ hμ i).starProjection‖ ≤ 1
      rw [← Submodule.starProjection_orthogonal]
      exact Submodule.starProjection_norm_le _
    change ‖(1 - wilsonDirectionalProjection μ hμ i) * removeWilsonDirections μ hμ ds‖ ≤ 1
    refine (norm_mul_le _ _).trans ?_
    exact (mul_le_mul h ih (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

def projectedWilsonCovariance {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) : Kernel :=
  wilsonL2Covariance (wilsonFluxL2 hN hβ μ l hl hμ)
    (fun J => removeWilsonDirections μ hμ [0, 1, 2, 3] (wilsonCurrentL2 μ (J, 0)))

theorem projectedWilsonCovariance_ward {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    (∀ J, d₂ (fun I => projectedWilsonCovariance hN hβ μ l hl hμ I J) = 0) ∧
      WardResponse β (projectedWilsonCovariance hN hβ μ l hl hμ) (wilsonCutResponseKernel μ.toMeasure) := by
  let F := wilsonFluxL2 hN hβ μ l hl hμ
  let S := wilsonCutResponseKernel μ.toMeasure
  let K (ds : List Axis) := wilsonL2Covariance F
    (fun J => removeWilsonDirections μ hμ ds (wilsonCurrentL2 μ (J, 0)))
  suffices h : ∀ ds, (∀ J, d₂ (fun I => K ds I J) = 0) ∧ WardResponse β (K ds) S from h [0, 1, 2, 3]
  intro ds
  induction ds with
  | nil =>
    have hK : K [] = wilsonFluxCurrentCovariance μ.toMeasure := by
      change wilsonL2Covariance F (fun J => (1 : WilsonL2 μ →L[ℝ] WilsonL2 μ)
        (wilsonCurrentL2 μ (J, 0))) = _
      simpa only [one_apply_eq_self] using wilsonL2Covariance_eq hN hβ μ l hl hμ
    rw [hK]
    exact ⟨wilsonFluxCurrentCovariance_closed hN hβ μ l hl hμ,
      wilsonFluxCurrentCovariance_wardResponse hN hβ μ l hl hμ⟩
  | cons i ds ih =>
    let M := wilsonL2Covariance F (fun J =>
      wilsonDirectionalProjection μ hμ i (removeWilsonDirections μ hμ ds (wilsonCurrentL2 μ (J, 0))))
    have hK : K (i :: ds) = K ds - M := by
      funext I J x
      change ⟪((1 - wilsonDirectionalProjection μ hμ i) *
        removeWilsonDirections μ hμ ds) (wilsonCurrentL2 μ (J, 0)), F I x⟫_ℝ =
        ⟪removeWilsonDirections μ hμ ds (wilsonCurrentL2 μ (J, 0)), F I x⟫_ℝ -
          ⟪wilsonDirectionalProjection μ hμ i (removeWilsonDirections μ hμ ds (wilsonCurrentL2 μ (J, 0))), F I x⟫_ℝ
      rw [mul_apply_eq_comp, sub_apply, one_apply_eq_self, inner_sub_left]
    rw [hK]
    exact ward_subtract_mean β (K ds) S M i
      (fun I J => wilsonL2Covariance_hasDirectionalMean hN hβ μ l hl hμ i I _)
      ih.1 ih.2 (fun I J => (wilsonCutResponseKernel_hasSum_zero hN hβ μ l hl hμ I J).summable)

theorem projectedWilsonCovariance_not_summable {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 10000 ≤ β)
    (μ : ProbabilityMeasure (InfiniteConfig N)) (l : ℕ → ℕ) (hl : StrictMono l)
    (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ)) :
    ¬ ∀ I J, Summable (projectedWilsonCovariance hN hβ μ l hl hμ I J) := by
  have h := projectedWilsonCovariance_ward hN hβ μ l hl hμ
  exact not_summable_of_ward β _ _ h.1 h.2
    (fun I J => (wilsonCutResponseKernel_hasSum_zero hN hβ μ l hl hμ I J).summable)
    (wilsonCutResponseKernel_hasSum_zero hN hβ μ l hl hμ .xy .xy).tsum_eq

end

end GaplessYangMills

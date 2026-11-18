module

public import GaplessYangMills.WilsonLocalDecay

/-!
# Applying the three transverse projections

A bound that depends only on the separation along one axis is preserved
by averaging along any other axis. Each transverse subtraction costs at
most a factor of two.
-/

@[expose] public section

namespace GaplessYangMills

open Filter MeasureTheory
open scoped InnerProductSpace Topology

noncomputable section

theorem HasDirectionalMean.abs_le_of_constant_bound_on_lines {i : Axis} {f g D : Site → ℝ}
    (h : HasDirectionalMean i f g) (hD : ∀ x, |f x| ≤ D x)
    (hline : ∀ x (k : ℕ), D (x + k • step i) = D x) (x : Site) : |g x| ≤ D x := by
  have ht : Tendsto (fun n => |averageAlong i f n x|) atTop (𝓝 |g x|) :=
    continuous_abs.continuousAt.tendsto.comp (h x)
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn₀ : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  rw [averageAlong, abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, |f (x + k • step i)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (n : ℝ)⁻¹ * ∑ _k ∈ Finset.range n, D x :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun k _ => (hD (x + k • step i)).trans_eq (hline x k))
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn₀, one_mul]

section Projections

variable {N : ℕ} {β : ℝ} {l : ℕ → ℕ} (μ : ProbabilityMeasure (InfiniteConfig N))
variable (hμ : Tendsto (fun n => extendedWilson (evenLength (l n)) N β) atTop (𝓝 μ))

theorem removeWilsonDirections_perm {ds ds' : List Axis} (h : ds.Perm ds') :
    removeWilsonDirections μ hμ ds = removeWilsonDirections μ hμ ds' := by
  let Q (i : Axis) := 1 - wilsonDirectionalProjection μ hμ i
  have hcomm (i j : Axis) : Commute (Q i) (Q j) := by
    have h : Commute (wilsonDirectionalProjection μ hμ i) (Q j) :=
      Commute.sub_right (Commute.one_right _) (wilsonDirectionalProjection_commute μ hμ i j)
    exact Commute.sub_left (Commute.one_left _) h
  change ds.foldr (fun i U => Q i * U) 1 = ds'.foldr (fun i U => Q i * U) 1
  induction h with
  | nil => rfl
  | cons i h ih => simp only [List.foldr_cons, ih]
  | swap i j ds =>
    simp only [List.foldr_cons]
    rw [← mul_assoc, ← mul_assoc, (hcomm j i).eq]
  | trans _ _ ha hb => exact ha.trans hb

theorem wilsonTranslationCovariance_mean (τ : Axis) (u v : WilsonL2 μ) :
    HasDirectionalMean τ (fun x => ⟪u, wilsonTranslateL2 μ hμ x v⟫_ℝ)
      (fun x => ⟪wilsonDirectionalProjection μ hμ τ u, wilsonTranslateL2 μ hμ x v⟫_ℝ) := by
  let S := wilsonTranslateL2 μ hμ (step τ)
  let a (x : Site) := wilsonTranslateL2 μ hμ x v
  have hs (x : Site) : S (a x) = a (x + step τ) := by
    change wilsonTranslateL2 μ hμ (step τ) (wilsonTranslateL2 μ hμ x v) =
      wilsonTranslateL2 μ hμ (x + step τ) v
    rw [← mul_apply_eq_comp, wilsonTranslateL2_mul, add_comm]
  have h := hasDirectionalMean_of_hilbert_shift τ S
    (norm_wilsonTranslateL2_le_one μ hμ (step τ)) u a hs
  have he : (fun x => ⟪u, wilsonDirectionalProjection μ hμ τ (a x)⟫_ℝ) =
      fun x => ⟪wilsonDirectionalProjection μ hμ τ u, a x⟫_ℝ :=
    funext fun x => ((wilsonInvariantSpace μ hμ τ).inner_starProjection_left_eq_right u (a x)).symm
  change HasDirectionalMean τ (fun x => ⟪u, a x⟫_ℝ) (fun x => ⟪wilsonDirectionalProjection μ hμ τ u, a x⟫_ℝ)
  rw [← he]
  exact h

def wilsonProjectedL2Correlation (u v : WilsonL2 μ) (x : Site) : ℝ :=
  ⟪removeWilsonDirections μ hμ [0, 1, 2, 3] u, wilsonTranslateL2 μ hμ x v⟫_ℝ

theorem wilsonProjectedL2Correlation_bound_transverse (τ : Axis) (u v : WilsonL2 μ) (D : Site → ℝ)
    (hline : ∀ i ≠ τ, ∀ x (k : ℕ), D (x + k • step i) = D x)
    (hτ : ∀ x, |⟪(1 - wilsonDirectionalProjection μ hμ τ) u, wilsonTranslateL2 μ hμ x v⟫_ℝ| ≤ D x) :
    ∀ x, |wilsonProjectedL2Correlation μ hμ u v x| ≤ 8 * D x := by
  let K (ds : List Axis) (x : Site) :=
    ⟪removeWilsonDirections μ hμ (ds ++ [τ]) u, wilsonTranslateL2 μ hμ x v⟫_ℝ
  have hK (ds : List Axis) (hds : ∀ i ∈ ds, i ≠ τ) (x : Site) :
      |K ds x| ≤ (2 : ℝ) ^ ds.length * D x := by
    induction ds generalizing x with
    | nil =>
      simpa only [K, List.nil_append, removeWilsonDirections, List.foldr_cons, List.foldr_nil,
        mul_one, List.length_nil, pow_zero, one_mul] using hτ x
    | cons i ds ih =>
      have hi := hds i (List.mem_cons_self ..)
      have hrest : ∀ j ∈ ds, j ≠ τ := fun j hj => hds j (List.mem_cons_of_mem _ hj)
      let a := removeWilsonDirections μ hμ (ds ++ [τ]) u
      let M (y : Site) := ⟪wilsonDirectionalProjection μ hμ i a, wilsonTranslateL2 μ hμ y v⟫_ℝ
      have hMean : HasDirectionalMean i (K ds) M := wilsonTranslationCovariance_mean μ hμ i a v
      have ha : |M x| ≤ (2 : ℝ) ^ ds.length * D x :=
        hMean.abs_le_of_constant_bound_on_lines (D := fun y => (2 : ℝ) ^ ds.length * D y) (ih hrest)
          (fun y k => congrArg ((2 : ℝ) ^ ds.length * ·) (hline i hi y k)) x
      have he : K (i :: ds) x = K ds x - M x := by
        change ⟪((1 - wilsonDirectionalProjection μ hμ i) * removeWilsonDirections μ hμ (ds ++ [τ])) u,
          wilsonTranslateL2 μ hμ x v⟫_ℝ = _
        rw [mul_apply_eq_comp, sub_apply, one_apply_eq_self, inner_sub_left]
      rw [he]
      calc
        _ ≤ |K ds x| + |M x| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (K ds x) (-M x)
        _ ≤ (2 : ℝ) ^ ds.length * D x + (2 : ℝ) ^ ds.length * D x := add_le_add (ih hrest x) ha
        _ = _ := by rw [List.length_cons, pow_succ]; ring
  let axes : List Axis := [0, 1, 2, 3]
  let ds := axes.erase τ
  have hn : axes.Nodup := by decide
  have ht : τ ∈ axes := by fin_cases τ <;> decide
  have hperm : axes.Perm (ds ++ [τ]) :=
    (List.perm_cons_erase ht).trans (List.perm_append_comm (l₁ := [τ]) (l₂ := ds))
  have hds : ∀ i ∈ ds, i ≠ τ := fun i hi h => hn.not_mem_erase (h ▸ hi)
  have hlen : ds.length = 3 := by simp [ds, List.length_erase_of_mem ht, axes]
  intro x
  have h := hK ds hds x
  rw [hlen] at h
  unfold wilsonProjectedL2Correlation
  rw [show ([0, 1, 2, 3] : List Axis) = axes from rfl, removeWilsonDirections_perm μ hμ hperm]
  norm_num at h
  exact h

end Projections

end

end GaplessYangMills

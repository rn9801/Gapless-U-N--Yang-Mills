module

public import GaplessYangMills.Duality
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Locally finite sums of fillings

The derivative is local. If each face receives only finitely many contributions,
the sum of component fillings has the sum of their boundaries.
-/

@[expose] public section

namespace GaplessYangMills

noncomputable section

def sumFillings {ι : Type*} (Y : ι → TwoForm ℤ) : TwoForm ℤ :=
  fun I x => ∑ᶠ k, Y k I x

theorem d₂_sumFillings {ι : Type*} (Y : ι → TwoForm ℤ)
    (hlocal : ∀ I x, (Function.support (fun k => Y k I x)).Finite)
    (c : Cube) (x : Site) :
    d₂ (sumFillings Y) c x = ∑ᶠ k, d₂ (Y k) c x := by
  have hdiff (i : Axis) (I : Face) :
      diff i (sumFillings Y I) x = ∑ᶠ k, diff i (Y k I) x := by
    exact (finsum_sub_distrib (hlocal I (x + step i)) (hlocal I x)).symm
  have hd (i : Axis) (I : Face) :
      (Function.support (fun k => diff i (Y k I) x)).Finite :=
    ((hlocal I (x + step i)).union (hlocal I x)).subset (Function.support_sub _ _)
  have hthree (i j k : Axis) (I J K : Face) :
      diff i (sumFillings Y I) x - diff j (sumFillings Y J) x + diff k (sumFillings Y K) x =
        (∑ᶠ t, (diff i (Y t I) x - diff j (Y t J) x + diff k (Y t K) x)) := by
    rw [hdiff, hdiff, hdiff, ← finsum_sub_distrib (hd i I) (hd j J)]
    exact (finsum_add_distrib
      (((hd i I).union (hd j J)).subset (Function.support_sub _ _)) (hd k K)).symm
  cases c
  · exact hthree 0 1 2 .yz .xz .xy
  · exact hthree 0 1 3 .yw .xw .xy
  · exact hthree 0 2 3 .zw .xw .xz
  · exact hthree 1 2 3 .zw .yw .yz

/-- A locally finite family that fills the individual defects yields a closed
repaired flux whenever those defects sum to the defect of the original lift. -/
theorem repairFlux_closed_of_component_fillings {ι : Type*} (a : TwoForm ℝ)
    (h : ∀ c x, Circle.exp (d₂ a c x) = 1)
    (Y : ι → TwoForm ℤ)
    (hlocal : ∀ I x, (Function.support (fun k => Y k I x)).Finite)
    (hdefect : ∀ c x, (∑ᶠ k, d₂ (Y k) c x) = defect a c x) :
    d₂ (repairFlux (fun _ => sumFillings Y) a) = 0 := by
  apply repairFlux_closed _ a h
  funext c x
  exact (d₂_sumFillings Y hlocal c x).trans (hdefect c x)

end

end GaplessYangMills

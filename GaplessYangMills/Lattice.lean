module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic.Abel

/-!
# Exterior differences on the four-dimensional cubic lattice

The coordinates are numbered from zero. For example, `Face.xy` denotes the paper's
orientation 12, and `Cube.xyz` denotes its orientation 123. A positive cell is
indexed by its lower vertex.
-/

@[expose] public section

namespace GaplessYangMills

abbrev Axis := Fin 4
abbrev Site := Axis → ℤ

inductive Face
  | xy | xz | xw | yz | yw | zw
  deriving DecidableEq

def Face.axes : Face → Axis × Axis
  | .xy => (0, 1)
  | .xz => (0, 2)
  | .xw => (0, 3)
  | .yz => (1, 2)
  | .yw => (1, 3)
  | .zw => (2, 3)

inductive Cube
  | xyz | xyw | xzw | yzw
  deriving DecidableEq

abbrev OneForm (R : Type*) := Axis → Site → R
abbrev TwoForm (R : Type*) := Face → Site → R
abbrev ThreeForm (R : Type*) := Cube → Site → R

/-- A positive unit step in direction `i`. -/
def step (i : Axis) : Site := fun j => if i = j then 1 else 0

theorem step_same (i : Axis) : step i i = 1 := by simp [step]

theorem step_other {i j : Axis} (h : i ≠ j) : step i j = 0 := by simp [step, h]

/-- The forward difference acting on a function of the base vertex. -/
def diff {R : Type*} [Sub R] (i : Axis) (u : Site → R) : Site → R :=
  fun x => u (x + step i) - u x

section AddCommGroup

variable {R : Type*} [AddCommGroup R]

theorem diff_sub (i : Axis) (u v : Site → R) :
    diff i (u - v) = diff i u - diff i v := by
  funext x
  change u (x + step i) - v (x + step i) - (u x - v x) =
    (u (x + step i) - u x) - (v (x + step i) - v x)
  abel

theorem diff_add (i : Axis) (u v : Site → R) :
    diff i (u + v) = diff i u + diff i v := by
  funext x
  change u (x + step i) + v (x + step i) - (u x + v x) =
    u (x + step i) - u x + (v (x + step i) - v x)
  abel

theorem diff_comm (i j : Axis) (u : Site → R) :
    diff i (diff j u) = diff j (diff i u) := by
  funext x
  simp only [diff]
  rw [add_right_comm x (step i) (step j)]
  abel

def d₁ (u : OneForm R) : TwoForm R
  | .xy => diff 0 (u 1) - diff 1 (u 0)
  | .xz => diff 0 (u 2) - diff 2 (u 0)
  | .xw => diff 0 (u 3) - diff 3 (u 0)
  | .yz => diff 1 (u 2) - diff 2 (u 1)
  | .yw => diff 1 (u 3) - diff 3 (u 1)
  | .zw => diff 2 (u 3) - diff 3 (u 2)

def d₂ (u : TwoForm R) : ThreeForm R
  | .xyz => diff 0 (u .yz) - diff 1 (u .xz) + diff 2 (u .xy)
  | .xyw => diff 0 (u .yw) - diff 1 (u .xw) + diff 3 (u .xy)
  | .xzw => diff 0 (u .zw) - diff 2 (u .xw) + diff 3 (u .xz)
  | .yzw => diff 1 (u .zw) - diff 2 (u .yw) + diff 3 (u .yz)

def d₃ (u : ThreeForm R) : Site → R :=
  diff 0 (u .yzw) - diff 1 (u .xzw) + diff 2 (u .xyw) - diff 3 (u .xyz)

theorem d₂_sub (u v : TwoForm R) : d₂ (u - v) = d₂ u - d₂ v := by
  funext c
  cases c <;> simp only [d₂, Pi.sub_apply, diff_sub] <;> abel

theorem d₂_add (u v : TwoForm R) : d₂ (u + v) = d₂ u + d₂ v := by
  funext c
  cases c <;> simp only [d₂, Pi.add_apply, diff_add] <;> abel

variable {S : Type*} [AddCommGroup S]

theorem d₁_map (φ : R →+ S) (u : OneForm R) (I : Face) (x : Site) :
    d₁ (fun i y => φ (u i y)) I x = φ (d₁ u I x) := by
  cases I <;> simp only [d₁, diff, Pi.sub_apply, map_sub]

theorem d₂_map (φ : R →+ S) (u : TwoForm R) (c : Cube) (x : Site) :
    d₂ (fun I y => φ (u I y)) c x = φ (d₂ u c x) := by
  cases c <;> simp only [d₂, diff, Pi.sub_apply, Pi.add_apply, map_sub, map_add]

theorem d₃_map (φ : R →+ S) (u : ThreeForm R) (x : Site) :
    d₃ (fun c y => φ (u c y)) x = φ (d₃ u x) := by
  simp only [d₃, diff, Pi.sub_apply, Pi.add_apply, map_sub, map_add]

/-- The exterior derivative of an exact two-form vanishes. -/
theorem d₂_d₁ (u : OneForm R) : d₂ (d₁ u) = 0 := by
  funext c
  cases c <;> simp only [d₂, d₁, diff_sub, diff_comm, Pi.zero_apply] <;> abel

/-- The exterior derivative of an exact three-form vanishes. -/
theorem d₃_d₂ (u : TwoForm R) : d₃ (d₂ u) = 0 := by
  simp only [d₃, d₂, diff_add, diff_sub, diff_comm]
  abel

end AddCommGroup

end GaplessYangMills

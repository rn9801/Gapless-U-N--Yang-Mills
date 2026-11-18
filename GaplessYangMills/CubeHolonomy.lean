module

public import GaplessYangMills.Wilson
public import Mathlib.Tactic.Group

/-!
# Nonabelian cube identity

The six terms compare successive axis orders for paths from one corner of the
cube to the opposite corner. Each term is a face holonomy transported to the
starting corner. The signs agree with the exterior derivative.
-/

@[expose] public section

namespace GaplessYangMills

def Cube.axes : Cube → Axis × Axis × Axis
  | .xyz => (0, 1, 2)
  | .xyw => (0, 1, 3)
  | .xzw => (0, 2, 3)
  | .yzw => (1, 2, 3)

def Cube.orientations : Cube → Face × Face × Face
  | .xyz => (.xy, .xz, .yz)
  | .xyw => (.xy, .xw, .yw)
  | .xzw => (.xz, .xw, .zw)
  | .yzw => (.yz, .yw, .zw)

/-- The product of the lifted faces, with short transports and a fixed order
so that the intermediate open paths cancel in the group. -/
def transportedCubeProduct {G : Type*} [Group G]
    (U : OneForm G) (c : Cube) (x : Site) : G :=
  let i := c.axes.1
  let j := c.axes.2.1
  let k := c.axes.2.2
  let ij := c.orientations.1
  let ik := c.orientations.2.1
  let jk := c.orientations.2.2
  (U i x * plaquetteHolonomy U jk (x + step i) * (U i x)⁻¹) *
    plaquetteHolonomy U ik x *
    (U k x * plaquetteHolonomy U ij (x + step k) * (U k x)⁻¹) *
    (plaquetteHolonomy U jk x)⁻¹ *
    (U j x * (plaquetteHolonomy U ik (x + step j))⁻¹ * (U j x)⁻¹) *
    (plaquetteHolonomy U ij x)⁻¹

theorem transportedCubeProduct_eq_one {G : Type*} [Group G]
    (U : OneForm G) (c : Cube) (x : Site) : transportedCubeProduct U c x = 1 := by
  cases c <;>
    simp only [transportedCubeProduct, Cube.axes, Cube.orientations, plaquetteHolonomy, Face.axes] <;>
    simp only [add_right_comm x (step 1) (step 0), add_right_comm x (step 2) (step 0),
      add_right_comm x (step 2) (step 1), add_right_comm x (step 3) (step 0),
      add_right_comm x (step 3) (step 1), add_right_comm x (step 3) (step 2)] <;>
    group

end GaplessYangMills

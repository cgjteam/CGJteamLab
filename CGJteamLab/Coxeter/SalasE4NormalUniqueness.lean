import CGJteamLab.SalasE4PlaneIncidence
import CGJteamLab.SalasE4Compatibility
import CGJteamLab.SalasE4Local3DCompatibility
import CGJteamLab.SalasE4PlaneHyperplane
import CGJteamLab.Coxeter.E4NormalUniqueness

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Salas E4 facade for normal uniqueness

This module exposes the existing corrected E4 normal-uniqueness theorems
on the public foundation

    SalasIncidence + E4Dimension + Hilbert Groups II-III.

No normal-uniqueness proof is repeated here.

The historical E4 incidence classes required by
`E4NormalUniqueness.lean` are reconstructed locally from Salas LP1-LP4
and the E4 dimension axiom.

In particular, Group IV is not needed.
-/

@[instance_reducible]
local instance salasE4Primitive_normalUniqueness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)

local instance salasE4PlaneIncidence_normalUniqueness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)

local instance salasE4DimensionFree_normalUniqueness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)

local instance salasE4HyperplaneCore_normalUniqueness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)

local instance salasE4AmbientIncidence_normalUniqueness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)

local instance salasE4Local3D_normalUniqueness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)

local instance salasE4PlaneHyperplane_normalUniqueness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)

/-!
## Public Salas-facing uniqueness theorems
-/

/--
On the Salas E4 foundation, a normal line to a fixed hyperplane at a
fixed foot is unique.

Only Hilbert Groups II and III are additionally required.
-/
theorem salas_e4_normal_same_foot_unique
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : SpaceHyperplane4 Geo)
    (l m : Geo.Line)
    (F : Geo.Point)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma F) :
    l = m :=
  hilbert4D_normal_same_foot_unique_corrected
    (Geo := Geo)
    Sigma l m F
    hLNormal hMNormal

/--
On the Salas E4 foundation, the perpendicular foot of a fixed point on
a fixed hyperplane is unique.

Only Hilbert Groups II and III are additionally required.
-/
theorem salas_e4_hyperplane_perpendicular_foot_unique
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : SpaceHyperplane4 Geo)
    (P F G : Geo.Point)
    (hPerpF :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P)
    (hPerpG :
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma G P) :
    F = G :=
  hyperplane_perpendicular_foot_unique4_corrected
    (Geo := Geo)
    Sigma P F G
    hPerpF hPerpG

end Geometry

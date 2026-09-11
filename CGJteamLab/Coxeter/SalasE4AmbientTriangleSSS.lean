import CGJteamLab.Coxeter.SalasE4AmbientTriangleSAS
import CGJteamLab.Coxeter.E4AmbientTriangleSSS

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Ambient E4 SSS on the Salas foundation

Public incidence foundation:

    SalasIncidence + E4Dimension

Additional geometric assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence

No ambient Euclidean axiom is required for this SSS layer.
Historical E4 incidence classes are installed only as local
compatibility instances.
-/

@[instance_reducible]
local instance salasE4Primitive_ambientSSS
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_ambientSSS
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_ambientSSS
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_ambientSSS
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


/--
Ambient E4 SSS, angle-at-the-first-vertex form, on the Salas incidence
foundation.

The source triangle `ABC` is ambient.  The target triangle `A'B'C'`
lies in the explicit ambient plane `sigma`.
-/
theorem salas_e4_ambient_sss_angleA_in_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (sigma : S.Plane)
    (A B C : Geo.Point)
    (A' B' C' : PlanePoint Geo sigma)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hA'B'C' :
      Not
        (PrimCollinear
          Geo A'.1 B'.1 C'.1))
    (hAB :
      Geo.Congruent A B A'.1 B'.1)
    (hBC :
      Geo.Congruent B C B'.1 C'.1)
    (hAC :
      Geo.Congruent A C A'.1 C'.1) :
    Geo.AngleCongruent
      B A C
      B'.1 A'.1 C'.1 :=
  hilbert4D_ambient_sss_angleA_in_plane_corrected
    (Geo := Geo)
    sigma
    A B C
    A' B' C'
    hABC hA'B'C'
    hAB hBC hAC

end Geometry

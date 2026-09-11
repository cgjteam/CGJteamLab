import CGJteamLab.SalasE4PlaneIncidence
import CGJteamLab.SalasE4Compatibility
import CGJteamLab.Coxeter.E4AmbientTriangleSAS

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Ambient E4 SAS on the Salas foundation

Public incidence foundation:

    SalasIncidence + E4Dimension

Additional geometric assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence

No ambient Euclidean axiom is required for this SAS layer.
The historical E4 incidence interfaces are installed only as local
compatibility instances.
-/

@[instance_reducible]
local instance salasE4Primitive_ambientSAS
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_ambientSAS
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_ambientSAS
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_ambientSAS
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


/--
The two remaining angle conclusions of ambient E4 SAS, now exposed on
the Salas incidence foundation.
-/
theorem salas_e4_ambient_sas_remaining_angles
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (A B C A' B' C' : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hA'B'C' :
      Not (PrimCollinear Geo A' B' C'))
    (hAB :
      Geo.Congruent A B A' B')
    (hAC :
      Geo.Congruent A C A' C')
    (hAngleA :
      Geo.AngleCongruent B A C B' A' C') :
    Geo.AngleCongruent A B C A' B' C' /\
    Geo.AngleCongruent A C B A' C' B' :=
  hilbert4D_ambient_sas_remaining_angles_corrected
    (Geo := Geo)
    A B C A' B' C'
    hABC hA'B'C'
    hAB hAC hAngleA


/--
Ambient E4 SAS in third-side-and-angle form on the Salas foundation.

The source triangle is ambient.  The target triangle is carried by the
explicit ambient plane `sigma`.
-/
theorem salas_e4_ambient_sas_third_side_and_angle
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
    (hAC :
      Geo.Congruent A C A'.1 C'.1)
    (hAngleA :
      Geo.AngleCongruent
        B A C
        B'.1 A'.1 C'.1) :
    Geo.Congruent B C B'.1 C'.1 /\
    Geo.AngleCongruent
      A C B
      A'.1 C'.1 B'.1 :=
  hilbert4D_ambient_sas_third_side_and_angle_corrected
    (Geo := Geo)
    sigma
    A B C
    A' B' C'
    hABC hA'B'C'
    hAB hAC hAngleA

end Geometry

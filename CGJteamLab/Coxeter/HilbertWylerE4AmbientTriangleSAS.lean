import CGJteamLab.HilbertWylerE4PublicInstances
import CGJteamLab.Coxeter.E4AmbientTriangleSAS

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Ambient E4 SAS on the Hilbert-Wyler foundation

Public incidence foundation:

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension.

Additional geometric assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence.

No ambient Euclidean axiom is required for this SAS layer.
Historical E4 incidence interfaces are supplied by the public
Hilbert-Wyler compatibility instances.
-/

/--
The two remaining angle conclusions of ambient E4 SAS on the
Hilbert-Wyler incidence foundation.
-/
theorem hilbertWyler_e4_ambient_sas_remaining_angles
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
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
Ambient E4 SAS in third-side-and-angle form on the Hilbert-Wyler
foundation.

The source triangle is ambient. The target triangle is carried by the
explicit ambient plane `sigma`.
-/
theorem hilbertWyler_e4_ambient_sas_third_side_and_angle
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
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

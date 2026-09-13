import CGJteamLab.Coxeter.HilbertWylerE4AmbientTriangleSAS
import CGJteamLab.Coxeter.E4AmbientTriangleSSS

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Ambient E4 SSS on the Hilbert-Wyler foundation

Public incidence foundation:

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension.

Additional geometric assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence.

No ambient Euclidean axiom is required for this SSS layer.
Historical E4 incidence interfaces are supplied by the public
Hilbert-Wyler compatibility instances.
-/

/--
Ambient E4 SSS, angle-at-the-first-vertex form, on the Hilbert-Wyler
incidence foundation.

The source triangle `ABC` is ambient. The target triangle `A'B'C'`
lies in the explicit ambient plane `sigma`.
-/
theorem hilbertWyler_e4_ambient_sss_angleA_in_plane
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

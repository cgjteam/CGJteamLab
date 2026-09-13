import CGJteamLab.HilbertWylerE4PublicInstances
import CGJteamLab.Coxeter.E4NormalUniqueness

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert-Wyler E4 facade for normal uniqueness

This module exposes the existing corrected E4 normal-uniqueness theorems
on the foundation

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension
    + Hilbert Groups II-III.

No normal-uniqueness proof is repeated here. Group IV is not needed.
-/

/--
On the Hilbert-Wyler E4 foundation, a normal line to a fixed hyperplane
at a fixed foot is unique.
-/
theorem hilbertWyler_e4_normal_same_foot_unique
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
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
On the Hilbert-Wyler E4 foundation, the perpendicular foot of a fixed
point on a fixed hyperplane is unique.
-/
theorem hilbertWyler_e4_hyperplane_perpendicular_foot_unique
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
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

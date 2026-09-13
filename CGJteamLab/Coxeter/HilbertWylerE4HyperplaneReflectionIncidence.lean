import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionEquiv
import CGJteamLab.Coxeter.E4HyperplaneReflectionIncidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection incidence on the Hilbert-Wyler foundation

The canonical reflection is supplied by the Hilbert-Wyler E4 facade.
All incidence compatibility interfaces are derived by
`HilbertWylerE4PublicInstances`.
-/

/--
The canonical Hilbert-Wyler E4 hyperplane reflection preserves ambient
collinearity.
-/
theorem hilbertWylerE4HyperplaneReflect_preserves_collinear
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (A B C : Geo.Point)
    (hABC : PrimCollinear Geo A B C) :
    PrimCollinear
      Geo
      (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma A)
      (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma B)
      (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma C) := by

  unfold hilbertWylerE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_collinear
      (Geo := Geo)
      Sigma A B C hABC


/--
The canonical Hilbert-Wyler E4 hyperplane reflection also preserves
ambient noncollinearity.
-/
theorem hilbertWylerE4HyperplaneReflect_preserves_noncollinear
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    Not
      (PrimCollinear
        Geo
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma A)
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma B)
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma C)) := by

  unfold hilbertWylerE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_noncollinear
      (Geo := Geo)
      Sigma A B C hABC

end Geometry

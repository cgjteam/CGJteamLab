import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionHyperplaneTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionOrderTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 reflection order transport on the Hilbert-Wyler foundation
-/

/--
The Hilbert-Wyler E4 hyperplane reflection preserves strict betweenness.
-/
theorem hilbertWylerE4HyperplaneReflect_preserves_between
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
    (hABC : Geo.Between A B C) :
    Geo.Between
      (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma A)
      (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma B)
      (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma C) := by

  unfold hilbertWylerE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_between
      (Geo := Geo)
      Sigma A B C hABC


/--
The Hilbert-Wyler E4 hyperplane reflection preserves midpoint
configurations.
-/
theorem hilbertWylerE4HyperplaneReflect_preserves_midpoint
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (M A B : Geo.Point)
    (hMid : HilbertIsMidpoint Geo M A B) :
    HilbertIsMidpoint
      Geo
      (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma M)
      (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma A)
      (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma B) := by

  unfold hilbertWylerE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_midpoint
      (Geo := Geo)
      Sigma M A B hMid

end Geometry

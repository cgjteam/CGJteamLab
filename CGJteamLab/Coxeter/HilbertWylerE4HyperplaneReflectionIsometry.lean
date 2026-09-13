import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionOrderTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionIsometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection isometry on the Hilbert-Wyler foundation
-/

/--
Every point of the reflecting E4 hyperplane is equidistant from a point
and its Hilbert-Wyler reflected image.
-/
theorem hilbertWylerE4HyperplaneReflect_hyperplane_point_equidistant
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P R : Geo.Point)
    (hRSigma : E4OnHyperplane Geo R Sigma) :
    Geo.Congruent
      R P
      R (hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma P) := by

  unfold hilbertWylerE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_hyperplane_point_equidistant
      (Geo := Geo)
      Sigma P R hRSigma


/--
The Hilbert-Wyler E4 hyperplane reflection preserves segment congruence
globally.
-/
theorem hilbertWylerE4HyperplaneReflect_preserves_congruence
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P R : Geo.Point) :
    Geo.Congruent
      P R
      (hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma P)
      (hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma R) := by

  unfold hilbertWylerE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_congruence
      (Geo := Geo)
      Sigma P R


/--
The Hilbert-Wyler reflection equivalence is an isometry in the synthetic
sense: it preserves the primitive segment-congruence relation.
-/
theorem hilbertWylerE4HyperplaneReflectionEquiv_preserves_congruence
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P R : Geo.Point) :
    Geo.Congruent
      P R
      (hilbertWylerE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma P)
      (hilbertWylerE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma R) := by

  change
    Geo.Congruent
      P R
      (hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma P)
      (hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma R)

  exact
    hilbertWylerE4HyperplaneReflect_preserves_congruence
      (Geo := Geo)
      Sigma P R

end Geometry

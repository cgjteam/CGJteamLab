import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionIncidence
import CGJteamLab.Coxeter.E4HyperplaneReflectionLineTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane line transport on the Hilbert-Wyler foundation
-/

/--
Exact setwise transport of a line by the Hilbert-Wyler E4 hyperplane
reflection.
-/
def HilbertWylerE4HyperplaneReflectionMapsLine
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : Geo.Line) : Prop :=
  HyperplaneReflectionMapsLine4_corrected
    Geo Sigma source target


/--
Two reflected images of distinct source points determine the exact image
line.
-/
theorem hilbertWylerE4HyperplaneReflectionMapsLine_of_two_points
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : Geo.Line)
    (A B : Geo.Point)
    (hAB : Ne A B)
    (hAs : H.OnLine A source)
    (hBs : H.OnLine B source)
    (hA't :
      H.OnLine
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma A)
        target)
    (hB't :
      H.OnLine
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma B)
        target) :
    HilbertWylerE4HyperplaneReflectionMapsLine
      Geo Sigma source target := by

  unfold HilbertWylerE4HyperplaneReflectionMapsLine
  unfold hilbertWylerE4HyperplaneReflect at hA't hB't

  exact
    hyperplaneReflectionMapsLine4_corrected_of_two_points
      (Geo := Geo)
      Sigma source target
      A B
      hAB hAs hBs
      hA't hB't


/--
Every line has an exact reflected image line.
-/
theorem hilbertWylerE4HyperplaneReflectionMapsLine_exists
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line) :
    exists target : Geo.Line,
      HilbertWylerE4HyperplaneReflectionMapsLine
        Geo Sigma source target := by

  unfold HilbertWylerE4HyperplaneReflectionMapsLine

  exact
    hyperplaneReflectionMapsLine4_corrected_exists
      (Geo := Geo)
      Sigma source


/--
The exact reflected image line is unique.
-/
theorem hilbertWylerE4HyperplaneReflectionMapsLine_unique
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target1 target2 : Geo.Line)
    (hMap1 :
      HilbertWylerE4HyperplaneReflectionMapsLine
        Geo Sigma source target1)
    (hMap2 :
      HilbertWylerE4HyperplaneReflectionMapsLine
        Geo Sigma source target2) :
    target1 = target2 := by

  unfold HilbertWylerE4HyperplaneReflectionMapsLine at hMap1 hMap2

  exact
    hyperplaneReflectionMapsLine4_corrected_unique
      (Geo := Geo)
      Sigma source target1 target2
      hMap1 hMap2


/--
Canonical reflected image of a line.
-/
noncomputable def hilbertWylerE4HyperplaneReflectionLineCarrier
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line) :
    Geo.Line :=
  hyperplaneReflectionLineCarrier4_corrected
    (Geo := Geo)
    Sigma source


/--
Specification of the canonical reflected line.
-/
theorem hilbertWylerE4HyperplaneReflectionLineCarrier_spec
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line) :
    HilbertWylerE4HyperplaneReflectionMapsLine
      Geo Sigma source
      (hilbertWylerE4HyperplaneReflectionLineCarrier
        (Geo := Geo) Sigma source) := by

  unfold HilbertWylerE4HyperplaneReflectionMapsLine
  unfold hilbertWylerE4HyperplaneReflectionLineCarrier

  exact
    hyperplaneReflectionLineCarrier4_corrected_spec
      (Geo := Geo)
      Sigma source


/--
Pointwise membership characterization of the canonical reflected line.
-/
theorem hilbertWylerE4HyperplaneReflectionLineCarrier_iff
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line)
    (P : Geo.Point) :
    H.OnLine P source <->
      H.OnLine
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma P)
        (hilbertWylerE4HyperplaneReflectionLineCarrier
          (Geo := Geo) Sigma source) :=
  hilbertWylerE4HyperplaneReflectionLineCarrier_spec
    (Geo := Geo)
    Sigma source P


/--
Any exact target is the canonical reflected line.
-/
theorem hilbertWylerE4HyperplaneReflectionLineCarrier_eq
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : Geo.Line)
    (hMap :
      HilbertWylerE4HyperplaneReflectionMapsLine
        Geo Sigma source target) :
    hilbertWylerE4HyperplaneReflectionLineCarrier
        (Geo := Geo) Sigma source =
      target := by

  exact
    hilbertWylerE4HyperplaneReflectionMapsLine_unique
      (Geo := Geo)
      Sigma source
      (hilbertWylerE4HyperplaneReflectionLineCarrier
        (Geo := Geo) Sigma source)
      target
      (hilbertWylerE4HyperplaneReflectionLineCarrier_spec
        (Geo := Geo)
        Sigma source)
      hMap


/--
Exact line transport reverses under the same reflection.
-/
theorem hilbertWylerE4HyperplaneReflectionMapsLine_symm
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : Geo.Line)
    (hMap :
      HilbertWylerE4HyperplaneReflectionMapsLine
        Geo Sigma source target) :
    HilbertWylerE4HyperplaneReflectionMapsLine
      Geo Sigma target source := by

  unfold HilbertWylerE4HyperplaneReflectionMapsLine at hMap |-

  exact
    hyperplaneReflectionMapsLine4_corrected_symm
      (Geo := Geo)
      Sigma source target hMap


/--
Canonical line transport is involutive.
-/
theorem hilbertWylerE4HyperplaneReflectionLineCarrier_involutive
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : Geo.Line) :
    hilbertWylerE4HyperplaneReflectionLineCarrier
        (Geo := Geo)
        Sigma
        (hilbertWylerE4HyperplaneReflectionLineCarrier
          (Geo := Geo) Sigma source) =
      source := by

  unfold hilbertWylerE4HyperplaneReflectionLineCarrier

  exact
    hyperplaneReflectionLineCarrier4_corrected_involutive
      (Geo := Geo)
      Sigma source

end Geometry

import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionLineTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionPlaneTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane plane transport on the Hilbert-Wyler foundation
-/

/--
Exact setwise transport of an ambient 2-plane by the Hilbert-Wyler E4
hyperplane reflection.
-/
def HilbertWylerE4HyperplaneReflectionMapsPlane
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : S.Plane) : Prop :=
  HyperplaneReflectionMapsPlane4_corrected
    Geo Sigma source target


/--
Three noncollinear source points and their reflected images determine the
exact image plane.
-/
theorem hilbertWylerE4HyperplaneReflectionMapsPlane_of_three_points
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : S.Plane)
    (A B C : Geo.Point)
    (hAs : S.OnPlane A source)
    (hBs : S.OnPlane B source)
    (hCs : S.OnPlane C source)
    (hABC : Not (PrimCollinear Geo A B C))
    (hA't :
      S.OnPlane
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma A)
        target)
    (hB't :
      S.OnPlane
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma B)
        target)
    (hC't :
      S.OnPlane
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma C)
        target) :
    HilbertWylerE4HyperplaneReflectionMapsPlane
      Geo Sigma source target := by

  unfold HilbertWylerE4HyperplaneReflectionMapsPlane
  unfold hilbertWylerE4HyperplaneReflect at hA't hB't hC't

  exact
    hyperplaneReflectionMapsPlane4_corrected_of_three_points
      (Geo := Geo)
      Sigma
      source target
      A B C
      hAs hBs hCs
      hABC
      hA't hB't hC't


/--
Every ambient 2-plane has an exact reflected image plane.
-/
theorem hilbertWylerE4HyperplaneReflectionMapsPlane_exists
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : S.Plane) :
    exists target : S.Plane,
      HilbertWylerE4HyperplaneReflectionMapsPlane
        Geo Sigma source target := by

  unfold HilbertWylerE4HyperplaneReflectionMapsPlane

  exact
    hyperplaneReflectionMapsPlane4_corrected_exists
      (Geo := Geo)
      Sigma source


/--
The exact reflected image plane is unique.
-/
theorem hilbertWylerE4HyperplaneReflectionMapsPlane_unique
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target1 target2 : S.Plane)
    (hMap1 :
      HilbertWylerE4HyperplaneReflectionMapsPlane
        Geo Sigma source target1)
    (hMap2 :
      HilbertWylerE4HyperplaneReflectionMapsPlane
        Geo Sigma source target2) :
    target1 = target2 := by

  unfold HilbertWylerE4HyperplaneReflectionMapsPlane at hMap1 hMap2

  exact
    hyperplaneReflectionMapsPlane4_corrected_unique
      (Geo := Geo)
      Sigma
      source target1 target2
      hMap1 hMap2


/--
Canonical reflected image of an ambient 2-plane.
-/
noncomputable def hilbertWylerE4HyperplaneReflectionPlaneCarrier
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : S.Plane) :
    S.Plane :=
  hyperplaneReflectionPlaneCarrier4_corrected
    (Geo := Geo)
    Sigma source


/--
Specification of the canonical reflected plane.
-/
theorem hilbertWylerE4HyperplaneReflectionPlaneCarrier_spec
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : S.Plane) :
    HilbertWylerE4HyperplaneReflectionMapsPlane
      Geo Sigma source
      (hilbertWylerE4HyperplaneReflectionPlaneCarrier
        (Geo := Geo) Sigma source) := by

  unfold HilbertWylerE4HyperplaneReflectionMapsPlane
  unfold hilbertWylerE4HyperplaneReflectionPlaneCarrier

  exact
    hyperplaneReflectionPlaneCarrier4_corrected_spec
      (Geo := Geo)
      Sigma source


/--
Pointwise membership characterization of the canonical reflected plane.
-/
theorem hilbertWylerE4HyperplaneReflectionPlaneCarrier_iff
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : S.Plane)
    (P : Geo.Point) :
    S.OnPlane P source <->
      S.OnPlane
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma P)
        (hilbertWylerE4HyperplaneReflectionPlaneCarrier
          (Geo := Geo) Sigma source) := by

  exact
    hilbertWylerE4HyperplaneReflectionPlaneCarrier_spec
      (Geo := Geo)
      Sigma source P


/--
Any exact target is the canonical reflected image plane.
-/
theorem hilbertWylerE4HyperplaneReflectionPlaneCarrier_eq
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : S.Plane)
    (hMap :
      HilbertWylerE4HyperplaneReflectionMapsPlane
        Geo Sigma source target) :
    hilbertWylerE4HyperplaneReflectionPlaneCarrier
        (Geo := Geo) Sigma source =
      target := by

  exact
    hilbertWylerE4HyperplaneReflectionMapsPlane_unique
      (Geo := Geo)
      Sigma
      source
      (hilbertWylerE4HyperplaneReflectionPlaneCarrier
        (Geo := Geo) Sigma source)
      target
      (hilbertWylerE4HyperplaneReflectionPlaneCarrier_spec
        (Geo := Geo)
        Sigma source)
      hMap


/--
Exact plane transport reverses under the same involutive reflection.
-/
theorem hilbertWylerE4HyperplaneReflectionMapsPlane_symm
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : S.Plane)
    (hMap :
      HilbertWylerE4HyperplaneReflectionMapsPlane
        Geo Sigma source target) :
    HilbertWylerE4HyperplaneReflectionMapsPlane
      Geo Sigma target source := by

  unfold HilbertWylerE4HyperplaneReflectionMapsPlane at hMap |-

  exact
    hyperplaneReflectionMapsPlane4_corrected_symm
      (Geo := Geo)
      Sigma source target hMap


/--
Canonical plane transport is involutive.
-/
theorem hilbertWylerE4HyperplaneReflectionPlaneCarrier_involutive
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : S.Plane) :
    hilbertWylerE4HyperplaneReflectionPlaneCarrier
        (Geo := Geo)
        Sigma
        (hilbertWylerE4HyperplaneReflectionPlaneCarrier
          (Geo := Geo) Sigma source) =
      source := by

  unfold hilbertWylerE4HyperplaneReflectionPlaneCarrier

  exact
    hyperplaneReflectionPlaneCarrier4_corrected_involutive
      (Geo := Geo)
      Sigma source

end Geometry

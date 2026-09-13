import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionPlaneTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionHyperplaneTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane transport on the Hilbert-Wyler foundation
-/

/--
Containment of an ambient 2-plane in a derived E4 hyperplane.
-/
def HilbertWylerE4PlaneInHyperplane
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    (pi : S.Plane)
    (Sigma : E4Hyperplane Geo) : Prop :=
  HilbertPlaneInHyperplane4 Geo pi Sigma


/--
Exact setwise transport of a derived E4 hyperplane by reflection.
-/
def HilbertWylerE4HyperplaneReflectionMapsHyperplane
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma source target : E4Hyperplane Geo) : Prop :=
  HyperplaneReflectionMapsHyperplane4_corrected
    Geo Sigma source target


/--
Canonical reflected hyperplane determined from a common 2-plane.
-/
noncomputable def hilbertWylerE4HyperplaneReflectionCarrier
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : HilbertWylerE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : HilbertWylerE4PlaneInHyperplane Geo Delta Tau) :
    E4Hyperplane Geo := by

  unfold HilbertWylerE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau


/--
The canonical carrier gives exact reflected hyperplane transport.
-/
theorem hilbertWylerE4HyperplaneReflectionCarrier_maps
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : HilbertWylerE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : HilbertWylerE4PlaneInHyperplane Geo Delta Tau) :
    HilbertWylerE4HyperplaneReflectionMapsHyperplane
      Geo Sigma Tau
      (hilbertWylerE4HyperplaneReflectionCarrier
        (Geo := Geo)
        Sigma Tau Delta
        hDeltaSigma hDeltaTau) := by

  unfold HilbertWylerE4HyperplaneReflectionMapsHyperplane
  unfold hilbertWylerE4HyperplaneReflectionCarrier
  unfold HilbertWylerE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact
    hyperplaneReflectionCarrier4_corrected_maps
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau


/--
Pointwise membership characterization of the canonical reflected
hyperplane.
-/
theorem hilbertWylerE4HyperplaneReflectionCarrier_iff
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : HilbertWylerE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : HilbertWylerE4PlaneInHyperplane Geo Delta Tau)
    (P : Geo.Point) :
    E4OnHyperplane Geo P Tau <->
      E4OnHyperplane
        Geo
        (hilbertWylerE4HyperplaneReflect (Geo := Geo) Sigma P)
        (hilbertWylerE4HyperplaneReflectionCarrier
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau) := by

  have hMap :=
    hilbertWylerE4HyperplaneReflectionCarrier_maps
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau

  unfold HilbertWylerE4HyperplaneReflectionMapsHyperplane at hMap
  unfold hilbertWylerE4HyperplaneReflect
  unfold hilbertWylerE4HyperplaneReflectionCarrier
  unfold HilbertWylerE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact hMap P


/--
Exact hyperplane transport reverses under the same involutive reflection.
-/
theorem hilbertWylerE4HyperplaneReflectionMapsHyperplane_symm
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma source target : E4Hyperplane Geo)
    (hMap :
      HilbertWylerE4HyperplaneReflectionMapsHyperplane
        Geo Sigma source target) :
    HilbertWylerE4HyperplaneReflectionMapsHyperplane
      Geo Sigma target source := by

  unfold HilbertWylerE4HyperplaneReflectionMapsHyperplane at hMap |-

  exact
    hyperplaneReflectionMapsHyperplane4_corrected_symm
      (Geo := Geo)
      Sigma source target hMap


/--
The canonical reflected hyperplane still contains the common plane.
-/
theorem hilbertWylerE4HyperplaneReflectionCarrier_contains_common_plane
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : HilbertWylerE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : HilbertWylerE4PlaneInHyperplane Geo Delta Tau) :
    HilbertWylerE4PlaneInHyperplane
      Geo Delta
      (hilbertWylerE4HyperplaneReflectionCarrier
        (Geo := Geo)
        Sigma Tau Delta
        hDeltaSigma hDeltaTau) := by

  unfold HilbertWylerE4PlaneInHyperplane
  unfold hilbertWylerE4HyperplaneReflectionCarrier
  unfold HilbertWylerE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact
    hyperplaneReflectionCarrier4_corrected_contains_common_plane
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau


/--
Applying the canonical reflected-hyperplane construction twice returns
the original hyperplane.
-/
theorem hilbertWylerE4HyperplaneReflectionCarrier_involutive
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : HilbertWylerE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : HilbertWylerE4PlaneInHyperplane Geo Delta Tau) :
    hilbertWylerE4HyperplaneReflectionCarrier
        (Geo := Geo)
        Sigma
        (hilbertWylerE4HyperplaneReflectionCarrier
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau)
        Delta
        hDeltaSigma
        (hilbertWylerE4HyperplaneReflectionCarrier_contains_common_plane
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau) =
      Tau := by

  unfold hilbertWylerE4HyperplaneReflectionCarrier
  unfold HilbertWylerE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact
    hyperplaneReflectionCarrier4_corrected_involutive
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau

end Geometry

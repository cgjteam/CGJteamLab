import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionPlaneTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionHyperplaneTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane transport on the Salas foundation

Public incidence foundation:

    SalasIncidence + E4Dimension

Additional geometric assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean

The historical E4 classes are installed only as local compatibility
instances.  Public statements use derived `E4Hyperplane`.
-/

@[instance_reducible]
local instance salasE4Primitive_hyperplaneTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_hyperplaneTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_hyperplaneTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_hyperplaneTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_hyperplaneTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_hyperplaneTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_hyperplaneTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_hyperplaneTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo] :
    Hilbert4DNormalFromExternalPointExistence_corrected Geo :=
  hilbert4D_XI11_implies_normalFromExternalPointExistence_corrected
    (Geo := Geo)


/--
A Salas-facing name for containment of an ambient 2-plane in a derived
E4 hyperplane.
-/
def SalasE4PlaneInHyperplane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    (pi : S.Plane)
    (Sigma : E4Hyperplane Geo) : Prop :=
  HilbertPlaneInHyperplane4 Geo pi Sigma


/--
Exact setwise transport of a derived E4 hyperplane by the Salas-based
reflection.
-/
def SalasE4HyperplaneReflectionMapsHyperplane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
noncomputable def salasE4HyperplaneReflectionCarrier
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : SalasE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : SalasE4PlaneInHyperplane Geo Delta Tau) :
    E4Hyperplane Geo := by

  unfold SalasE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau


/--
The canonical carrier gives exact reflected hyperplane transport.
-/
theorem salasE4HyperplaneReflectionCarrier_maps
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : SalasE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : SalasE4PlaneInHyperplane Geo Delta Tau) :
    SalasE4HyperplaneReflectionMapsHyperplane
      Geo Sigma Tau
      (salasE4HyperplaneReflectionCarrier
        (Geo := Geo)
        Sigma Tau Delta
        hDeltaSigma hDeltaTau) := by

  unfold SalasE4HyperplaneReflectionMapsHyperplane
  unfold salasE4HyperplaneReflectionCarrier
  unfold SalasE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact
    hyperplaneReflectionCarrier4_corrected_maps
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau


/--
Pointwise membership characterization of the canonical reflected
hyperplane.
-/
theorem salasE4HyperplaneReflectionCarrier_iff
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : SalasE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : SalasE4PlaneInHyperplane Geo Delta Tau)
    (P : Geo.Point) :
    E4OnHyperplane Geo P Tau <->
      E4OnHyperplane
        Geo
        (salasE4HyperplaneReflect (Geo := Geo) Sigma P)
        (salasE4HyperplaneReflectionCarrier
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau) := by

  have hMap :=
    salasE4HyperplaneReflectionCarrier_maps
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau

  unfold SalasE4HyperplaneReflectionMapsHyperplane at hMap
  unfold salasE4HyperplaneReflect
  unfold salasE4HyperplaneReflectionCarrier
  unfold SalasE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact hMap P


/--
Exact hyperplane transport reverses under the same involutive reflection.
-/
theorem salasE4HyperplaneReflectionMapsHyperplane_symm
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma source target : E4Hyperplane Geo)
    (hMap :
      SalasE4HyperplaneReflectionMapsHyperplane
        Geo Sigma source target) :
    SalasE4HyperplaneReflectionMapsHyperplane
      Geo Sigma target source := by

  unfold SalasE4HyperplaneReflectionMapsHyperplane at hMap |-

  exact
    hyperplaneReflectionMapsHyperplane4_corrected_symm
      (Geo := Geo)
      Sigma source target hMap


/--
The canonical reflected hyperplane still contains the common plane.
-/
theorem salasE4HyperplaneReflectionCarrier_contains_common_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : SalasE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : SalasE4PlaneInHyperplane Geo Delta Tau) :
    SalasE4PlaneInHyperplane
      Geo Delta
      (salasE4HyperplaneReflectionCarrier
        (Geo := Geo)
        Sigma Tau Delta
        hDeltaSigma hDeltaTau) := by

  unfold SalasE4PlaneInHyperplane
  unfold salasE4HyperplaneReflectionCarrier
  unfold SalasE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact
    hyperplaneReflectionCarrier4_corrected_contains_common_plane
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau


/--
Applying the canonical reflected-hyperplane construction twice returns
the original hyperplane.
-/
theorem salasE4HyperplaneReflectionCarrier_involutive
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hDeltaSigma : SalasE4PlaneInHyperplane Geo Delta Sigma)
    (hDeltaTau : SalasE4PlaneInHyperplane Geo Delta Tau) :
    salasE4HyperplaneReflectionCarrier
        (Geo := Geo)
        Sigma
        (salasE4HyperplaneReflectionCarrier
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau)
        Delta
        hDeltaSigma
        (salasE4HyperplaneReflectionCarrier_contains_common_plane
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau) =
      Tau := by

  unfold salasE4HyperplaneReflectionCarrier
  unfold SalasE4PlaneInHyperplane at hDeltaSigma hDeltaTau

  exact
    hyperplaneReflectionCarrier4_corrected_involutive
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau

end Geometry

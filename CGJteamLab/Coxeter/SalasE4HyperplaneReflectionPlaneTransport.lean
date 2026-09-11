import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionLineTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionPlaneTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane plane transport on the Salas foundation

Public incidence foundation:

    SalasIncidence + E4Dimension

Additional geometric assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean

The historical E4 interfaces are installed only as local compatibility
instances.  Public statements use `E4Hyperplane` and the original ambient
plane type supplied by `HilbertSpacePrimitive`.
-/

@[instance_reducible]
local instance salasE4Primitive_planeTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_planeTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_planeTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_planeTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_planeTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_planeTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_planeTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_planeTransport
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
Exact setwise transport of an ambient 2-plane by the Salas-based E4
hyperplane reflection.
-/
def SalasE4HyperplaneReflectionMapsPlane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
theorem salasE4HyperplaneReflectionMapsPlane_of_three_points
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
        (salasE4HyperplaneReflect (Geo := Geo) Sigma A)
        target)
    (hB't :
      S.OnPlane
        (salasE4HyperplaneReflect (Geo := Geo) Sigma B)
        target)
    (hC't :
      S.OnPlane
        (salasE4HyperplaneReflect (Geo := Geo) Sigma C)
        target) :
    SalasE4HyperplaneReflectionMapsPlane
      Geo Sigma source target := by

  unfold SalasE4HyperplaneReflectionMapsPlane
  unfold salasE4HyperplaneReflect at hA't hB't hC't

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
theorem salasE4HyperplaneReflectionMapsPlane_exists
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : S.Plane) :
    exists target : S.Plane,
      SalasE4HyperplaneReflectionMapsPlane
        Geo Sigma source target := by

  unfold SalasE4HyperplaneReflectionMapsPlane

  exact
    hyperplaneReflectionMapsPlane4_corrected_exists
      (Geo := Geo)
      Sigma source


/--
The exact reflected image plane is unique.
-/
theorem salasE4HyperplaneReflectionMapsPlane_unique
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target1 target2 : S.Plane)
    (hMap1 :
      SalasE4HyperplaneReflectionMapsPlane
        Geo Sigma source target1)
    (hMap2 :
      SalasE4HyperplaneReflectionMapsPlane
        Geo Sigma source target2) :
    target1 = target2 := by

  unfold SalasE4HyperplaneReflectionMapsPlane at hMap1 hMap2

  exact
    hyperplaneReflectionMapsPlane4_corrected_unique
      (Geo := Geo)
      Sigma
      source target1 target2
      hMap1 hMap2


/--
Canonical reflected image of an ambient 2-plane.
-/
noncomputable def salasE4HyperplaneReflectionPlaneCarrier
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
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
theorem salasE4HyperplaneReflectionPlaneCarrier_spec
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : S.Plane) :
    SalasE4HyperplaneReflectionMapsPlane
      Geo Sigma source
      (salasE4HyperplaneReflectionPlaneCarrier
        (Geo := Geo) Sigma source) := by

  unfold SalasE4HyperplaneReflectionMapsPlane
  unfold salasE4HyperplaneReflectionPlaneCarrier

  exact
    hyperplaneReflectionPlaneCarrier4_corrected_spec
      (Geo := Geo)
      Sigma source


/--
Pointwise membership characterization of the canonical reflected plane.
-/
theorem salasE4HyperplaneReflectionPlaneCarrier_iff
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : S.Plane)
    (P : Geo.Point) :
    S.OnPlane P source <->
      S.OnPlane
        (salasE4HyperplaneReflect (Geo := Geo) Sigma P)
        (salasE4HyperplaneReflectionPlaneCarrier
          (Geo := Geo) Sigma source) := by

  exact
    salasE4HyperplaneReflectionPlaneCarrier_spec
      (Geo := Geo)
      Sigma source P


/--
Any exact target is the canonical reflected image plane.
-/
theorem salasE4HyperplaneReflectionPlaneCarrier_eq
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : S.Plane)
    (hMap :
      SalasE4HyperplaneReflectionMapsPlane
        Geo Sigma source target) :
    salasE4HyperplaneReflectionPlaneCarrier
        (Geo := Geo) Sigma source =
      target := by

  apply
    salasE4HyperplaneReflectionMapsPlane_unique
      (Geo := Geo)
      Sigma
      source
      (salasE4HyperplaneReflectionPlaneCarrier
        (Geo := Geo) Sigma source)
      target

  · exact
      salasE4HyperplaneReflectionPlaneCarrier_spec
        (Geo := Geo)
        Sigma source

  · exact hMap


/--
Exact plane transport reverses under the same involutive reflection.
-/
theorem salasE4HyperplaneReflectionMapsPlane_symm
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source target : S.Plane)
    (hMap :
      SalasE4HyperplaneReflectionMapsPlane
        Geo Sigma source target) :
    SalasE4HyperplaneReflectionMapsPlane
      Geo Sigma target source := by

  unfold SalasE4HyperplaneReflectionMapsPlane at hMap |-

  exact
    hyperplaneReflectionMapsPlane4_corrected_symm
      (Geo := Geo)
      Sigma source target hMap


/--
Canonical plane transport is involutive.
-/
theorem salasE4HyperplaneReflectionPlaneCarrier_involutive
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (source : S.Plane) :
    salasE4HyperplaneReflectionPlaneCarrier
        (Geo := Geo)
        Sigma
        (salasE4HyperplaneReflectionPlaneCarrier
          (Geo := Geo) Sigma source) =
      source := by

  unfold salasE4HyperplaneReflectionPlaneCarrier

  exact
    hyperplaneReflectionPlaneCarrier4_corrected_involutive
      (Geo := Geo)
      Sigma source

end Geometry

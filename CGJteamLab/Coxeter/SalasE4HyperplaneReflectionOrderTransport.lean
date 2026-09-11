import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionHyperplaneTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionOrderTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 reflection order transport on the Salas foundation

Public incidence foundation:

    SalasIncidence + E4Dimension

Additional geometric assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean

The Euclidean assumption is used here through the derived XI.11 normal
existence interface.  No historical E4 incidence class is a public
assumption of the results below.
-/

@[instance_reducible]
local instance salasE4Primitive_orderTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_orderTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_orderTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_orderTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_orderTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_orderTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_orderTransport
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_orderTransport
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
The Salas-based E4 hyperplane reflection preserves strict betweenness.
-/
theorem salasE4HyperplaneReflect_preserves_between
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    Geo.Between
      (salasE4HyperplaneReflect (Geo := Geo) Sigma A)
      (salasE4HyperplaneReflect (Geo := Geo) Sigma B)
      (salasE4HyperplaneReflect (Geo := Geo) Sigma C) := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_between
      (Geo := Geo)
      Sigma A B C hABC


/--
The Salas-based E4 hyperplane reflection preserves midpoint
configurations.
-/
theorem salasE4HyperplaneReflect_preserves_midpoint
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (M A B : Geo.Point)
    (hMid : HilbertIsMidpoint Geo M A B) :
    HilbertIsMidpoint
      Geo
      (salasE4HyperplaneReflect (Geo := Geo) Sigma M)
      (salasE4HyperplaneReflect (Geo := Geo) Sigma A)
      (salasE4HyperplaneReflect (Geo := Geo) Sigma B) := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_midpoint
      (Geo := Geo)
      Sigma M A B hMid

end Geometry

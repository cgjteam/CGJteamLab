import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionOrderTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionIsometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection isometry on the Salas foundation

Public incidence foundation:

    SalasIncidence + E4Dimension

Additional geometric assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean

All historical E4 incidence and normal-existence interfaces are derived
locally.  The public theorems below state the metric properties directly
for derived `E4Hyperplane`.
-/

@[instance_reducible]
local instance salasE4Primitive_isometry
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_isometry
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_isometry
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_isometry
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_isometry
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_isometry
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_isometry
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_isometry
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
Every point of the reflecting E4 hyperplane is equidistant from a point
and its Salas-based reflected image.
-/
theorem salasE4HyperplaneReflect_hyperplane_point_equidistant
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P R : Geo.Point)
    (hRSigma : E4OnHyperplane Geo R Sigma) :
    Geo.Congruent
      R P
      R (salasE4HyperplaneReflect
        (Geo := Geo) Sigma P) := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_hyperplane_point_equidistant
      (Geo := Geo)
      Sigma P R hRSigma


/--
The Salas-based E4 hyperplane reflection preserves segment congruence
globally.
-/
theorem salasE4HyperplaneReflect_preserves_congruence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P R : Geo.Point) :
    Geo.Congruent
      P R
      (salasE4HyperplaneReflect
        (Geo := Geo) Sigma P)
      (salasE4HyperplaneReflect
        (Geo := Geo) Sigma R) := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_congruence
      (Geo := Geo)
      Sigma P R


/--
The Salas-based reflection equivalence is an isometry in the synthetic
sense: it preserves the primitive segment-congruence relation.
-/
theorem salasE4HyperplaneReflectionEquiv_preserves_congruence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P R : Geo.Point) :
    Geo.Congruent
      P R
      (salasE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma P)
      (salasE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma R) := by

  change
    Geo.Congruent
      P R
      (salasE4HyperplaneReflect
        (Geo := Geo) Sigma P)
      (salasE4HyperplaneReflect
        (Geo := Geo) Sigma R)

  exact
    salasE4HyperplaneReflect_preserves_congruence
      (Geo := Geo)
      Sigma P R

end Geometry

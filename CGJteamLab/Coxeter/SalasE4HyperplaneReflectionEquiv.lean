import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionCore
import CGJteamLab.Coxeter.E4HyperplaneReflectionEquiv

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection equivalence on the Salas foundation

This module exposes the production hyperplane-reflection equivalence with
public assumptions

    SalasIncidence
    E4Dimension
    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean.

The historical E4 incidence and XI.11 interfaces are reconstructed only
as local compatibility instances.
-/

@[instance_reducible]
local instance salasE4Primitive_reflectionEquiv
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_reflectionEquiv
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_reflectionEquiv
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_reflectionEquiv
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_reflectionEquiv
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_reflectionEquiv
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_reflectionEquiv
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_reflectionEquiv
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
A point is fixed by the canonical Salas-based hyperplane reflection
exactly when it lies on the reflecting hyperplane.
-/
theorem salasE4HyperplaneReflect_fixed_iff
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    salasE4HyperplaneReflect
        (Geo := Geo) Sigma P = P <->
      E4OnHyperplane Geo P Sigma := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      Sigma P


/--
The canonical Salas-based reflection in an E4 hyperplane, packaged as an
equivalence of the ambient point type.
-/
noncomputable def salasE4HyperplaneReflectionEquiv
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo) :
    Equiv Geo.Point Geo.Point where

  toFun :=
    salasE4HyperplaneReflect
      (Geo := Geo) Sigma

  invFun :=
    salasE4HyperplaneReflect
      (Geo := Geo) Sigma

  left_inv := by
    intro P
    exact
      salasE4HyperplaneReflect_involutive
        (Geo := Geo)
        Sigma P

  right_inv := by
    intro P
    exact
      salasE4HyperplaneReflect_involutive
        (Geo := Geo)
        Sigma P


/--
The Salas-based equivalence realizes the corrected relational reflection.
-/
theorem salasE4HyperplaneReflectionEquiv_spec
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    IsHyperplaneReflection4_corrected
      Geo Sigma P
      (salasE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma P) := by

  change
    IsHyperplaneReflection4_corrected
      Geo Sigma P
      (salasE4HyperplaneReflect
        (Geo := Geo) Sigma P)

  exact
    salasE4HyperplaneReflect_spec
      (Geo := Geo)
      Sigma P


/--
The Salas-based reflection equivalence is pointwise involutive.
-/
theorem salasE4HyperplaneReflectionEquiv_apply_apply
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    salasE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma
        (salasE4HyperplaneReflectionEquiv
          (Geo := Geo) Sigma P) =
      P := by

  change
    salasE4HyperplaneReflect
        (Geo := Geo) Sigma
        (salasE4HyperplaneReflect
          (Geo := Geo) Sigma P) =
      P

  exact
    salasE4HyperplaneReflect_involutive
      (Geo := Geo)
      Sigma P


/--
The fixed points of the Salas-based equivalence are exactly the points
of the reflecting hyperplane.
-/
theorem salasE4HyperplaneReflectionEquiv_fixed_iff
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    salasE4HyperplaneReflectionEquiv
        (Geo := Geo) Sigma P = P <->
      E4OnHyperplane Geo P Sigma := by

  change
    salasE4HyperplaneReflect
        (Geo := Geo) Sigma P = P <->
      E4OnHyperplane Geo P Sigma

  exact
    salasE4HyperplaneReflect_fixed_iff
      (Geo := Geo)
      Sigma P

end Geometry

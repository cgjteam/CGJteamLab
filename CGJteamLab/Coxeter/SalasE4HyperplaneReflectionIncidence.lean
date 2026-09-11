import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionEquiv
import CGJteamLab.Coxeter.E4HyperplaneReflectionIncidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection incidence on the Salas foundation

This module exposes the production incidence-preservation layer with public
assumptions

    SalasIncidence
    E4Dimension
    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean.

The historical E4 incidence and normal-existence classes are reconstructed
locally as derived compatibility instances.
-/

@[instance_reducible]
local instance salasE4Primitive_reflectionIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_reflectionIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_reflectionIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_reflectionIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_reflectionIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_reflectionIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_reflectionIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_reflectionIncidence
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
The canonical Salas-based E4 hyperplane reflection preserves ambient
collinearity.
-/
theorem salasE4HyperplaneReflect_preserves_collinear
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (A B C : Geo.Point)
    (hABC : PrimCollinear Geo A B C) :
    PrimCollinear
      Geo
      (salasE4HyperplaneReflect (Geo := Geo) Sigma A)
      (salasE4HyperplaneReflect (Geo := Geo) Sigma B)
      (salasE4HyperplaneReflect (Geo := Geo) Sigma C) := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_collinear
      (Geo := Geo)
      Sigma A B C hABC


/--
The canonical Salas-based E4 hyperplane reflection also preserves ambient
noncollinearity.
-/
theorem salasE4HyperplaneReflect_preserves_noncollinear
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    Not
      (PrimCollinear
        Geo
        (salasE4HyperplaneReflect (Geo := Geo) Sigma A)
        (salasE4HyperplaneReflect (Geo := Geo) Sigma B)
        (salasE4HyperplaneReflect (Geo := Geo) Sigma C)) := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_preserves_noncollinear
      (Geo := Geo)
      Sigma A B C hABC

end Geometry

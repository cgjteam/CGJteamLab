import CGJteamLab.SalasE4PlaneIncidence
import CGJteamLab.SalasE4Compatibility
import CGJteamLab.SalasE4Local3DCompatibility
import CGJteamLab.Coxeter.E4Euclidean

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Local Hilbert layers in E4 on the Salas incidence foundation

This module isolates the architecture used throughout the E4 development.

Incidence is supplied by

    SalasIncidence + E4Dimension.

The ambient Hilbert groups II, III and IV remain genuine independent
geometric assumptions:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean.

From these assumptions every derived E4 hyperplane inherits the old
three-dimensional Hilbert interfaces needed by Book XI and by the
Coxeter development.

No old E4 incidence class occurs as a public hypothesis of the theorems
below.
-/

@[instance_reducible]
local instance salasE4Primitive_hilbertLayers
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_hilbertLayers
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_hilbertLayers
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_hilbertLayers
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_hilbertLayers
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_hilbertLayers
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


/--
Every derived E4 hyperplane inherits the full three-dimensional Hilbert
Group II order structure from ambient E4 order.
-/
theorem salas_e4_hyperplane_hilbertSpaceOrder
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    (Sigma : E4Hyperplane Geo) :
    HilbertSpaceOrder
      (HyperplaneGeo4 Geo Sigma) := by
  infer_instance


/--
Every derived E4 hyperplane inherits the full three-dimensional Hilbert
Group III congruence structure from ambient E4 congruence.
-/
theorem salas_e4_hyperplane_hilbertSpaceCongruence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : E4Hyperplane Geo) :
    HilbertSpaceCongruence
      (HyperplaneGeo4 Geo Sigma) := by
  infer_instance


/--
Every derived E4 hyperplane inherits the full three-dimensional Hilbert
Group IV Euclidean structure from ambient E4 Group IV.
-/
theorem salas_e4_hyperplane_hilbertSpaceEuclidean
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo) :
    HilbertSpaceEuclidean
      (HyperplaneGeo4 Geo Sigma) := by
  infer_instance

end Geometry

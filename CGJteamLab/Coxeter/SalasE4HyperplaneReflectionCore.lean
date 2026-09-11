import CGJteamLab.E4HyperplaneXI11
import CGJteamLab.SalasE4PlaneIncidence
import CGJteamLab.SalasE4Compatibility
import CGJteamLab.SalasE4Local3DCompatibility
import CGJteamLab.SalasE4PlaneHyperplane
import CGJteamLab.Coxeter.E4HyperplaneReflectionCore

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane reflection core on the Salas foundation

This module exposes the production hyperplane-reflection core with the
incidence foundation

    SalasIncidence + E4Dimension.

The only additional geometric assumptions are the ambient Hilbert
Groups II-IV:

    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence
    Hilbert4DAmbientEuclidean.

All historical E4 incidence and normal-existence interfaces are installed
locally as derived compatibility instances.
-/

@[instance_reducible]
local instance salasE4Primitive_reflectionCore
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_reflectionCore
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_reflectionCore
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_reflectionCore
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_reflectionCore
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_reflectionCore
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_reflectionCore
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_reflectionCore
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
On the Salas E4 foundation, every point outside a derived hyperplane has
a perpendicular foot on that hyperplane.
-/
theorem salas_e4_hyperplane_perpendicular_foot_exists
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point)
    (hPSigma : Not (E4OnHyperplane Geo P Sigma)) :
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
        Geo Sigma F P :=
  hyperplane_perpendicular_foot_exists4_corrected
    (Geo := Geo)
    Sigma P hPSigma


/--
The perpendicular foot is unique.
-/
theorem salas_e4_hyperplane_perpendicular_foot_exists_unique
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point)
    (hPSigma : Not (E4OnHyperplane Geo P Sigma)) :
    exists F : Geo.Point,
      PerpendicularToHyperplaneThrough4_corrected
          Geo Sigma F P /\
      forall G : Geo.Point,
        PerpendicularToHyperplaneThrough4_corrected
            Geo Sigma G P ->
        G = F :=
  hyperplane_perpendicular_foot_exists_unique4_corrected
    (Geo := Geo)
    Sigma P hPSigma


/--
Every point has a reflected point in a derived E4 hyperplane.
-/
theorem salas_e4_hyperplane_reflection_exists
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    exists P' : Geo.Point,
      IsHyperplaneReflection4_corrected
        Geo Sigma P P' :=
  hyperplane_reflection_exists4_corrected
    (Geo := Geo)
    Sigma P


/--
Canonical hyperplane reflection on the Salas E4 foundation.
-/
noncomputable def salasE4HyperplaneReflect
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    Geo.Point :=
  hyperplaneReflect4_corrected
    Geo Sigma P


/--
Specification of the canonical Salas-based hyperplane reflection.
-/
theorem salasE4HyperplaneReflect_spec
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
      (salasE4HyperplaneReflect
        (Geo := Geo) Sigma P) := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_spec
      (Geo := Geo)
      Sigma P


/--
The canonical Salas-based E4 hyperplane reflection is involutive.
-/
theorem salasE4HyperplaneReflect_involutive
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
        (Geo := Geo) Sigma
        (salasE4HyperplaneReflect
          (Geo := Geo) Sigma P) =
      P := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_corrected_involutive
      (Geo := Geo)
      Sigma P

end Geometry

import CGJteamLab.Coxeter.SalasE4NormalSection
import CGJteamLab.Coxeter.E4NormalParallel

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 normal parallelism on the Salas foundation

This module exposes the dimension-corrected normal-parallelism layer
with Salas incidence as the public foundation.

Pure incidence results require only:

    SalasIncidence + E4Dimension.

The final XI.6-style parallelism theorem requires:

    SalasIncidence
    E4Dimension
    Hilbert4DAmbientOrder
    Hilbert4DAmbientCongruence.

No ambient Group IV assumption is needed for this theorem.
-/

@[instance_reducible]
local instance salasE4Primitive_normalParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_normalParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_normalParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_normalParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_normalParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_normalParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_normalParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


/--
Inside a derived E4 hyperplane every ambient 2-plane misses at least one
point of the hyperplane.
-/
theorem salas_e4_hyperplane_point_off_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    (Sigma : E4Hyperplane Geo)
    (rho : S.Plane) :
    exists D : Geo.Point,
      E4OnHyperplane Geo D Sigma /\
      Not (S.OnPlane D rho) := by

  exact
    hilbert4D_hyperplane_point_off_plane_corrected
      (Geo := Geo)
      Sigma rho


/--
Two normals to one derived E4 hyperplane at distinct feet lie in one
derived E4 hyperplane.
-/
theorem salas_e4_distinct_foot_normals_common_hyperplane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    (Sigma : E4Hyperplane Geo)
    (l m : Geo.Line)
    (F G : Geo.Point)
    (hFG : Ne F G)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma G) :
    exists Lambda : E4Hyperplane Geo,
      HilbertLineInHyperplane4 Geo l Lambda /\
      HilbertLineInHyperplane4 Geo m Lambda := by

  exact
    hilbert4D_distinct_foot_normals_common_hyperplane_corrected
      (Geo := Geo)
      Sigma
      l m
      F G
      hFG
      hLNormal
      hMNormal


/--
Dimension-safe ambient line parallelism in E4: the two lines lie in one
ambient 2-plane and are disjoint.
-/
def SalasE4LinesParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    (l m : Geo.Line) : Prop :=
  Hilbert4DLinesParallel_corrected Geo l m


/--
Two normals to the same derived E4 hyperplane at distinct feet are
parallel in the dimension-safe ambient E4 sense.

This is the Salas-facing form of the localized Euclid XI.6 argument.
-/
theorem salas_e4_normals_to_same_hyperplane_parallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : E4Hyperplane Geo)
    (l m : Geo.Line)
    (F G : Geo.Point)
    (hFG : Ne F G)
    (hLNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo l Sigma F)
    (hMNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo m Sigma G) :
    SalasE4LinesParallel Geo l m := by

  unfold SalasE4LinesParallel

  exact
    hilbert4D_normals_to_same_hyperplane_parallel_corrected
      (Geo := Geo)
      Sigma
      l m
      F G
      hFG
      hLNormal
      hMNormal

end Geometry

import CGJteamLab.Coxeter.SalasE4NormalParallel
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionCore
import CGJteamLab.Coxeter.E4ReflectionPlaneInvariance

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Reflection-invariant planes on the Salas E4 foundation

If an ambient 2-plane `N` contains one normal `r` to a reflecting
hyperplane `Sigma`, then reflection in `Sigma` preserves `N`.

There are two layers.

1. Relational invariance needs only

       SalasIncidence + E4Dimension
       + Hilbert4DAmbientOrder
       + Hilbert4DAmbientCongruence.

2. The canonical reflection function additionally uses the derived
   XI.11 normal-existence interface, hence our current construction
   requires ambient Group IV as well.

All historical E4 incidence interfaces are local derived compatibility
instances.
-/

@[instance_reducible]
local instance salasE4Primitive_planeInvariance
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_planeInvariance
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_planeInvariance
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_planeInvariance
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_planeInvariance
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_planeInvariance
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_planeInvariance
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_planeInvariance
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
Relational plane invariance.

If `N` contains a `Sigma`-normal through `O`, then every reflected image
of a point of `N` again lies in `N`.
-/
theorem salas_e4_reflection_relation_preserves_plane_of_normal
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    (Sigma : E4Hyperplane Geo)
    (N : S.Plane)
    (O : Geo.Point)
    (r : Geo.Line)
    (hrN :
      HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (P P' : Geo.Point)
    (hPN :
      S.OnPlane P N)
    (hRefl :
      IsHyperplaneReflection4_corrected
        Geo Sigma P P') :
    S.OnPlane P' N := by

  exact
    hilbert4D_reflection_relation_preserves_plane_of_normal_smith
      (Geo := Geo)
      Sigma N O r
      hrN hRNormal
      P P'
      hPN
      hRefl


/--
Functional plane invariance for the canonical Salas-based hyperplane
reflection.
-/
theorem salasE4HyperplaneReflect_preserves_plane_of_normal
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma : E4Hyperplane Geo)
    (N : S.Plane)
    (O : Geo.Point)
    (r : Geo.Line)
    (hrN :
      HilbertLineInPlane Geo r N)
    (hRNormal :
      HilbertLinePerpendicularHyperplaneAt4_corrected
        Geo r Sigma O)
    (P : Geo.Point)
    (hPN :
      S.OnPlane P N) :
    S.OnPlane
      (salasE4HyperplaneReflect
        (Geo := Geo) Sigma P)
      N := by

  unfold salasE4HyperplaneReflect

  exact
    hyperplaneReflect4_preserves_plane_of_normal_smith
      (Geo := Geo)
      Sigma N O r
      hrN hRNormal
      P hPN

end Geometry

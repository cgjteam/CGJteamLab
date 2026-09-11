import CGJteamLab.SalasE4PlaneHyperplane
import CGJteamLab.Coxeter.SalasE4HyperplaneReflectionEquiv
import CGJteamLab.Coxeter.E4NormalParallel
import CGJteamLab.Coxeter.E4HyperplaneIntersection

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane intersections on the Salas foundation

The incidence results in this file require only

    SalasIncidence + E4Dimension.

Order, congruence and Euclidean geometry enter only in the final
reflection fixed-point corollary.
-/

@[instance_reducible]
local instance salasE4Primitive_hyperplaneIntersection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_hyperplaneIntersection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasE4DimensionFree_hyperplaneIntersection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasE4HyperplaneCore_hyperplaneIntersection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


local instance salasE4AmbientIncidence_hyperplaneIntersection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DAmbientIncidence Geo :=
  hilbert4DAmbientIncidence_of_dimensionFree
    (Geo := Geo)


local instance salasE4Local3D_hyperplaneIntersection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneLocal3DIncidence Geo :=
  salas_e4_implies_oldHyperplaneLocal3DIncidence
    (Geo := Geo)


local instance salasE4PlaneHyperplane_hyperplaneIntersection
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo :=
  salas_e4_implies_oldPlaneHyperplaneIncidence
    (Geo := Geo)


local instance salasE4NormalExistence_hyperplaneIntersection
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
Two derived E4 hyperplanes containing two distinct common points contain
a common ambient 2-plane through those points.
-/
theorem salas_e4_two_hyperplanes_common_plane_through_two_points
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    (Sigma Lambda : E4Hyperplane Geo)
    (F G : Geo.Point)
    (hFG : Ne F G)
    (hFSigma : E4OnHyperplane Geo F Sigma)
    (hGSigma : E4OnHyperplane Geo G Sigma)
    (hFLambda : E4OnHyperplane Geo F Lambda)
    (hGLambda : E4OnHyperplane Geo G Lambda) :
    exists rho : S.Plane,
      S.OnPlane F rho /\
      S.OnPlane G rho /\
      HilbertPlaneInHyperplane4 Geo rho Sigma /\
      HilbertPlaneInHyperplane4 Geo rho Lambda := by

  exact
    hilbert4D_two_hyperplanes_common_plane_through_two_points_corrected
      (Geo := Geo)
      Sigma Lambda
      F G
      hFG
      hFSigma hGSigma
      hFLambda hGLambda


/--
Two derived E4 hyperplanes meet exactly in the ambient plane `Delta`.
-/
def SalasE4HyperplanesMeetInPlane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane) : Prop :=
  HyperplanesMeetInPlane4_corrected
    Geo Sigma Tau Delta


/--
Two distinct derived E4 hyperplanes containing the same three
noncollinear points have an exact common intersection plane.
-/
theorem salas_e4_distinct_hyperplanes_exact_common_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (hSigmaTau : Ne Sigma Tau)
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hASigma : E4OnHyperplane Geo A Sigma)
    (hBSigma : E4OnHyperplane Geo B Sigma)
    (hCSigma : E4OnHyperplane Geo C Sigma)
    (hATau : E4OnHyperplane Geo A Tau)
    (hBTau : E4OnHyperplane Geo B Tau)
    (hCTau : E4OnHyperplane Geo C Tau) :
    exists Delta : S.Plane,
      S.OnPlane A Delta /\
      S.OnPlane B Delta /\
      S.OnPlane C Delta /\
      SalasE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta := by

  rcases
      hilbert4D_distinct_hyperplanes_exact_common_plane_corrected
        (Geo := Geo)
        Sigma Tau
        hSigmaTau
        A B C
        hABC
        hASigma hBSigma hCSigma
        hATau hBTau hCTau with
    ⟨Delta, hA, hB, hC, hMeet⟩

  exact
    ⟨Delta, hA, hB, hC, by
      unfold SalasE4HyperplanesMeetInPlane
      exact hMeet⟩


/--
Membership in an exact common plane is equivalent to membership in both
derived E4 hyperplanes.
-/
theorem salas_e4_hyperplanesMeetInPlane_iff
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      SalasE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (X : Geo.Point) :
    S.OnPlane X Delta <->
      E4OnHyperplane Geo X Sigma /\
      E4OnHyperplane Geo X Tau := by

  unfold SalasE4HyperplanesMeetInPlane at hMeet

  exact
    hyperplanesMeetInPlane4_corrected_iff
      (Geo := Geo)
      Sigma Tau Delta
      hMeet X


/--
Every point of the exact common plane is fixed by both Salas-based
hyperplane reflections.
-/
theorem salas_e4_hyperplanesMeetInPlane_common_point_fixed
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      SalasE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (X : Geo.Point)
    (hXDelta : S.OnPlane X Delta) :
    salasE4HyperplaneReflect
        (Geo := Geo) Sigma X = X /\
    salasE4HyperplaneReflect
        (Geo := Geo) Tau X = X := by

  have hBoth :=
    (salas_e4_hyperplanesMeetInPlane_iff
      (Geo := Geo)
      Sigma Tau Delta
      hMeet X).mp hXDelta

  constructor

  · exact
      (salasE4HyperplaneReflect_fixed_iff
        (Geo := Geo)
        Sigma X).2 hBoth.1

  · exact
      (salasE4HyperplaneReflect_fixed_iff
        (Geo := Geo)
        Tau X).2 hBoth.2

end Geometry

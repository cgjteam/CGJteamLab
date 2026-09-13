import CGJteamLab.HilbertWylerE4PublicInstances
import CGJteamLab.Coxeter.HilbertWylerE4HyperplaneReflectionEquiv
import CGJteamLab.Coxeter.E4NormalParallel
import CGJteamLab.Coxeter.E4HyperplaneIntersection

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# E4 hyperplane intersections on the Hilbert-Wyler foundation

The incidence results in this file require only

    HilbertIncidence
    + HilbertPlaneIncidence
    + HilbertSpacePrimitive
    + HilbertWylerAxioms
    + E4Dimension.

Order, congruence and Euclidean geometry enter only in the final
reflection fixed-point corollary.

Historical corrected-E4 incidence interfaces are supplied by
`HilbertWylerE4PublicInstances`.

No new axiom is introduced here.
-/

/--
Two derived E4 hyperplanes containing two distinct common points contain
a common ambient 2-plane through those points.
-/
theorem hilbertWyler_e4_two_hyperplanes_common_plane_through_two_points
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
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
def HilbertWylerE4HyperplanesMeetInPlane
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane) : Prop :=
  HyperplanesMeetInPlane4_corrected
    Geo Sigma Tau Delta


/--
Two distinct derived E4 hyperplanes containing the same three
noncollinear points have an exact common intersection plane.
-/
theorem hilbertWyler_e4_distinct_hyperplanes_exact_common_plane
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
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
      HilbertWylerE4HyperplanesMeetInPlane
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
      unfold HilbertWylerE4HyperplanesMeetInPlane
      exact hMeet⟩


/--
Membership in an exact common plane is equivalent to membership in both
derived E4 hyperplanes.
-/
theorem hilbertWyler_e4_hyperplanesMeetInPlane_iff
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      HilbertWylerE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (X : Geo.Point) :
    S.OnPlane X Delta <->
      E4OnHyperplane Geo X Sigma /\
      E4OnHyperplane Geo X Tau := by

  unfold HilbertWylerE4HyperplanesMeetInPlane at hMeet

  exact
    hyperplanesMeetInPlane4_corrected_iff
      (Geo := Geo)
      Sigma Tau Delta
      hMeet X


/--
Every point of the exact common plane is fixed by both Hilbert-Wyler
hyperplane reflections.
-/
theorem hilbertWyler_e4_hyperplanesMeetInPlane_common_point_fixed
    [H : HilbertIncidence Geo]
    [_HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    [E4Dimension Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    (Sigma Tau : E4Hyperplane Geo)
    (Delta : S.Plane)
    (hMeet :
      HilbertWylerE4HyperplanesMeetInPlane
        Geo Sigma Tau Delta)
    (X : Geo.Point)
    (hXDelta : S.OnPlane X Delta) :
    hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Sigma X = X /\
    hilbertWylerE4HyperplaneReflect
        (Geo := Geo) Tau X = X := by

  have hBoth :=
    (hilbertWyler_e4_hyperplanesMeetInPlane_iff
      (Geo := Geo)
      Sigma Tau Delta
      hMeet X).mp hXDelta

  constructor

  · exact
      (hilbertWylerE4HyperplaneReflect_fixed_iff
        (Geo := Geo)
        Sigma X).2 hBoth.1

  · exact
      (hilbertWylerE4HyperplaneReflect_fixed_iff
        (Geo := Geo)
        Tau X).2 hBoth.2

end Geometry

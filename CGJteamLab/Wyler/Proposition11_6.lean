import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.6.

If two lines are perpendicular to the same plane at distinct points,
then they are parallel in space.

The spatial parallel predicate has two components:

  1. the two lines are coplanar;
  2. the two lines are disjoint.

The Wyler layer supplies these as separate reusable geometric facts.
XI.6 is their composition.
-/
theorem euclid_proposition_11_6
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l m : Geo.Line)
    (B D : Geo.Point)
    (hBD : Ne B D)
    (hLperp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi B)
    (hMperp :
      HilbertLinePerpendicularPlaneAt
        Geo m pi D) :
    HilbertSpaceLinesParallel Geo l m := by

  /-
  First component of spatial parallelism:
  the two normals to pi lie in a common plane sigma.
  -/
  cases
      hilbert_XI6_normals_to_same_plane_coplanar_wyler
        (Geo := Geo)
        pi l m B D
        hBD
        hLperp
        hMperp with
  | intro sigma hSigmaData =>
      have hlsigma :
          HilbertLineInPlane Geo l sigma :=
        hSigmaData.1

      have hmsigma :
          HilbertLineInPlane Geo m sigma :=
        hSigmaData.2

      /-
      Second component:
      inside their common plane, the two distinct-foot normals
      cannot meet.
      -/
      have hDisjoint :
          HilbertLinesDisjoint Geo l m :=
        hilbert_XI6_coplanar_normals_disjoint_wyler
          (Geo := Geo)
          pi sigma
          l m
          B D
          hBD
          hlsigma
          hmsigma
          hLperp
          hMperp

      /-
      Spatial parallelism is exactly coplanarity plus disjointness.
      -/
      exact
        ⟨sigma,
         hlsigma,
         hmsigma,
         hDisjoint⟩

end Geometry

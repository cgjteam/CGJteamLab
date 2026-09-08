import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.14.

Planes to which the same straight line is perpendicular are parallel.

The proof separates the flat and metric structure.

Flat certificate:
  pi != rho  ->  Join(carrier(pi), carrier(rho)) = E^3.

Metric/separation argument:
  - equal feet would force pi = rho by uniqueness of the plane
    perpendicular to a fixed line at a fixed point;
  - hence the feet A,B are distinct;
  - a hypothetical common point K of pi and rho produces an auxiliary
    plane sigma containing the common normal l and K;
  - inside PlaneGeo(sigma), the triangle ABK has two right angles;
  - Euclid I.17 makes this impossible.

Thus pi and rho have empty meet, i.e. they are parallel in the sense of
XI.Def.8.
-/
theorem euclid_proposition_11_14
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (A B : Geo.Point)
    (hPlanesNe : Ne pi rho)
    (hPerpPi :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hPerpRho :
      HilbertLinePerpendicularPlaneAt Geo l rho B) :
    HilbertSpacePlanesParallel Geo pi rho := by

  /-
  Flat rank certificate: two distinct ambient planes generate E^3.
  It records the global position of the two plane carriers.
  -/
  have _hJoinRank3 :
      HilbertJoin3D Geo
          (HilbertPlaneCarrier3D Geo pi)
          (HilbertPlaneCarrier3D Geo rho) =
        (Set.univ : Set Geo.Point) :=
    hilbertJoin3D_two_distinct_planes_eq_univ
      (Geo := Geo)
      pi rho hPlanesNe

  /-
  The feet of the common normal must be distinct.

  If A = B, the plane perpendicular to l at that point is unique,
  contradicting pi != rho.
  -/
  have hAB : Ne A B := by
    intro hABeq
    subst B

    have hPlanesEq : pi = rho :=
      hilbert_XI14_plane_perpendicular_to_line_at_unique_wyler
        (Geo := Geo)
        pi rho l A
        hPerpPi
        hPerpRho

    exact hPlanesNe hPlanesEq

  /-
  Plane parallelism is the absence of a common point.
  -/
  change
    Not
      (exists K : Geo.Point,
        S.OnPlane K pi /\
        S.OnPlane K rho)

  intro hCommon

  cases hCommon with
  | intro K hKData =>
      have hKpi : S.OnPlane K pi :=
        hKData.1

      have hKrho : S.OnPlane K rho :=
        hKData.2

      /-
      A hypothetical common point K produces the exact planar
      contradiction configuration: a nondegenerate triangle ABK in an
      auxiliary plane sigma with right angles at both A and B.
      -/
      cases
          hilbert_XI14_triangle_has_two_right_angles_wyler
            (Geo := Geo)
            pi rho l A B K
            hAB
            hPerpPi
            hPerpRho
            hKpi
            hKrho with
      | intro sigma hSigmaData =>
          cases hSigmaData with
          | intro Ap hApData =>
              cases hApData with
              | intro Bp hBpData =>
                  cases hBpData with
                  | intro Kp hTriangleData =>

                      have hNon :
                          Not
                            (PrimCollinear
                              (PlaneGeo Geo sigma)
                              Ap Bp Kp) :=
                        hTriangleData.1

                      have hRightBAK :
                          HilbertRightAngle
                            (PlaneGeo Geo sigma)
                            Bp Ap Kp :=
                        hTriangleData.2.1

                      have hRightABK :
                          HilbertRightAngle
                            (PlaneGeo Geo sigma)
                            Ap Bp Kp :=
                        hTriangleData.2.2

                      /-
                      Euclid I.17 forbids two right angles in one
                      nondegenerate triangle.
                      -/
                      exact
                        hilbert_XI14_two_right_angles_impossible_wyler
                          (PlaneGeo Geo sigma)
                          Ap Bp Kp
                          hNon
                          hRightBAK
                          hRightABK

end Geometry

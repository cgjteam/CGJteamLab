import CGJteamLab.Wyler.Proposition11_8
import CGJteamLab.Wyler.Proposition11_11

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.12.

Given a point A in a plane pi, construct a line through A perpendicular
to pi.

The proof keeps Euclid's dependency route visible:

  XI.11
    ->
  construct one normal l to pi from an external point B
    ->
  if A lies on l, foot uniqueness finishes
    ->
  otherwise form the generated slice

      Join(carrier(l), {A}) = carrier(sigma)

  and inside it construct m through A parallel to l, with

      Join(carrier(l), carrier(m)) = carrier(sigma).

  XI.8 transfers perpendicularity from l to m, and foot uniqueness
  identifies the new foot with A.
-/
theorem euclid_proposition_11_12
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi) :
    exists l : Geo.Line,
      HilbertLinePerpendicularPlaneAt Geo l pi A := by

  /-
  Step 1.  Choose an external point B.
  -/
  cases
      hilbert_point_off_plane
        (Geo := Geo)
        pi with
  | intro B hBpi =>

      /-
      The external point raises the plane to rank three.
      This is the flat certificate behind XI.11.
      -/
      have hRank3 :
          HilbertJoin3D Geo
              (HilbertPlaneCarrier3D Geo pi)
              ({B} : Set Geo.Point) =
            (Set.univ : Set Geo.Point) :=
        hilbertJoin3D_plane_external_point_eq_univ
          (Geo := Geo)
          pi B hBpi

      /-
      Step 2.  XI.11 constructs one normal l through B.
      -/
      cases
          euclid_proposition_11_11
            (Geo := Geo)
            pi B hBpi with
      | intro l hLData =>
          cases hLData with
          | intro F hFData =>
              have hBl : H.OnLine B l :=
                hFData.1

              have hPerp :
                  HilbertLinePerpendicularPlaneAt
                    Geo l pi F :=
                hFData.2

              /-
              Step 3.  Either A already lies on l...
              -/
              by_cases hAl : H.OnLine A l

              next =>
                have hAF : A = F :=
                  hilbertLinePerpendicularPlaneAt_foot_unique_wyler
                    (Geo := Geo)
                    pi l F A
                    hPerp
                    hAl
                    hApi

                subst F

                exact
                  Exists.intro l hPerp

              /-
              ...or l and A generate a plane slice sigma.
              -/
              next =>
                cases
                    hilbert_XI12_generated_slice_parallel_native
                      (Geo := Geo)
                      l A hAl with
                | intro sigma hSlice =>
                    cases hSlice with
                    | intro m hMData =>

                        have hJoinLA :
                            HilbertJoin3D Geo
                                (HilbertLineCarrier3D Geo l)
                                ({A} : Set Geo.Point) =
                              HilbertPlaneCarrier3D Geo sigma :=
                          hMData.1

                        have hAm : H.OnLine A m :=
                          hMData.2.1

                        have hParallel :
                            HilbertSpaceLinesParallel Geo l m :=
                          hMData.2.2.1

                        have hJoinLM :
                            HilbertJoin3D Geo
                                (HilbertLineCarrier3D Geo l)
                                (HilbertLineCarrier3D Geo m) =
                              HilbertPlaneCarrier3D Geo sigma :=
                          hMData.2.2.2

                        /-
                        The two exact join identities are the flat normal
                        form of the nontrivial XI.12 branch:

                          sigma = Join(l,{A}) = Join(l,m).
                        -/
                        have _hSameGeneratedSlice :
                            HilbertJoin3D Geo
                                (HilbertLineCarrier3D Geo l)
                                ({A} : Set Geo.Point) =
                              HilbertJoin3D Geo
                                (HilbertLineCarrier3D Geo l)
                                (HilbertLineCarrier3D Geo m) :=
                          hJoinLA.trans hJoinLM.symm

                        /-
                        Step 4.  XI.8 transfers perpendicularity from l
                        to the parallel line m.
                        -/
                        cases
                            euclid_proposition_11_8
                              (Geo := Geo)
                              l m pi F
                              hParallel hPerp with
                        | intro D hPerpM =>

                            /-
                            Step 5.  Since A lies on m and in pi, the
                            perpendicular foot D must be A.
                            -/
                            have hAD : A = D :=
                              hilbertLinePerpendicularPlaneAt_foot_unique_wyler
                                (Geo := Geo)
                                pi m D A
                                hPerpM
                                hAm
                                hApi

                            subst D

                            exact
                              Exists.intro m hPerpM

end Geometry

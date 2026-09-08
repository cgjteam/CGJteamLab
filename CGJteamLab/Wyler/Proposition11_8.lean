import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.8.

If two lines are parallel and one of them is perpendicular to a plane,
then the other is also perpendicular to that plane.

The proof exposes the three layers of the Wyler architecture:

  1. build the spatial auxiliary configuration at the second line;
  2. use the Euclidean/Group-IV bridge to obtain the first required
     perpendicular direction in the reference plane;
  3. apply the XI.4 metric core to two distinct plane directions.

This is precisely the point where pure flat incidence is not sufficient.
-/
theorem euclid_proposition_11_8
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (l m : Geo.Line)
    (pi : S.Plane)
    (B : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo l pi B) :
    exists D : Geo.Point,
      HilbertLinePerpendicularPlaneAt Geo m pi D := by

  /-
  Step 1.  Construct the XI.8 auxiliary configuration.

  The point D lies on m and in pi.  The lines d,e lie in pi through D.
  The construction also provides e perpendicular to d and e perpendicular
  to m.
  -/
  cases
      hilbert_XI8_auxiliary_line_perpendicular_to_parallel_wyler
        (Geo := Geo)
        pi l m B
        hParallel hPerp with
  | intro D hD =>
      cases hD with
      | intro d hd =>
          cases hd with
          | intro e hData =>

              have hDm : H.OnLine D m :=
                hData.1

              have hDpi : S.OnPlane D pi :=
                hData.2.1

              have hBd : H.OnLine B d :=
                hData.2.2.1

              have hDd : H.OnLine D d :=
                hData.2.2.2.1

              have hdpi :
                  HilbertLineInPlane Geo d pi :=
                hData.2.2.2.2.1

              have hDe : H.OnLine D e :=
                hData.2.2.2.2.2.1

              have hepi :
                  HilbertLineInPlane Geo e pi :=
                hData.2.2.2.2.2.2.1

              have hPerpED :
                  HilbertLinesPerpendicularAt Geo e d D :=
                hData.2.2.2.2.2.2.2.1

              have hPerpEm :
                  HilbertLinesPerpendicularAt Geo e m D :=
                hData.2.2.2.2.2.2.2.2

              /-
              Step 2.  The Euclidean bridge along the fixed transversal
              d = BD transfers the original normality of l to the
              parallel line m.
              -/
              have hPerpMd :
                  HilbertLinesPerpendicularAt Geo m d D :=
                hilbert_XI8_parallel_line_perpendicular_to_given_BD_wyler
                  (Geo := Geo)
                  pi
                  l m d
                  B D
                  hParallel
                  hPerp
                  hDm
                  hDpi
                  hBd
                  hDd
                  hdpi

              /-
              Normalize the second direction to m perpendicular e.
              -/
              have hPerpMe :
                  HilbertLinesPerpendicularAt Geo m e D :=
                hilbertLinesPerpendicularAt_symm_wyler
                  (Geo := Geo)
                  e m D
                  hPerpEm

              /-
              The two reference-plane directions d,e are distinct.
              -/
              have hed : Ne e d :=
                hilbert_linesPerpendicularAt_ne
                  (Geo := Geo)
                  e d D
                  hPerpED

              have hde : Ne d e :=
                hed.symm

              /-
              Package the two generating directions and their common point
              as objects of PlaneGeo(pi).
              -/
              let dp : PlaneLine Geo pi :=
                ⟨d, hdpi⟩

              let ep : PlaneLine Geo pi :=
                ⟨e, hepi⟩

              let Dp : PlanePoint Geo pi :=
                ⟨D, hDpi⟩

              have hdep : Ne dp ep := by
                intro hEq
                apply hde
                exact congrArg Subtype.val hEq

              have hPerpMdp :
                  HilbertLinesPerpendicularAt
                    Geo m dp.1 Dp.1 := by
                simpa [dp, Dp] using hPerpMd

              have hPerpMep :
                  HilbertLinesPerpendicularAt
                    Geo m ep.1 Dp.1 := by
                simpa [ep, Dp] using hPerpMe

              /-
              Step 3.  Normalize the incidence/nondegeneracy data required
              by the XI.4 metric core.
              -/
              have hmd : Ne m dp.1 :=
                hilbert_linesPerpendicularAt_ne
                  (Geo := Geo)
                  m dp.1 Dp.1
                  hPerpMdp

              have hme : Ne m ep.1 :=
                hilbert_linesPerpendicularAt_ne
                  (Geo := Geo)
                  m ep.1 Dp.1
                  hPerpMep

              have hDm' : H.OnLine Dp.1 m :=
                hPerpMdp.1

              have hDd' : H.OnLine Dp.1 dp.1 :=
                hPerpMdp.2.1

              have hDe' : H.OnLine Dp.1 ep.1 :=
                hPerpMep.2.1

              have hFinal :
                  HilbertLinePerpendicularPlaneAt
                    Geo m pi D := by
                have h :=
                  hilbert_XI4_line_perpendicular_plane_core
                    (Geo := Geo)
                    pi dp ep m Dp
                    hdep
                    hmd hme
                    hDm' hDd' hDe'
                    hPerpMdp hPerpMep
                simpa [Dp] using h

              exact
                Exists.intro D hFinal

end Geometry

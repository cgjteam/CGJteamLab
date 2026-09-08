import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.5.

If a line `l` is perpendicular at the common point `O` to three lines
`m`, `n`, `p`, and `m` and `n` are distinct, then `m`, `n`, `p` are
coplanar.

Wyler decomposition:

  m,n generate a plane pi,
  l perp m,n  ->  l perp pi.

If p is not contained in pi, then l,p generate a second plane sigma.
The meet pi inter sigma is a line q through O.  Since q lies in pi,

  l perp q.

Now p and q are two lines of sigma through O, both perpendicular to l.
If p != q, they force

  l perp sigma,

but l itself lies in sigma.  Contradiction.  Hence p = q, so p lies in
pi together with m and n.
-/
theorem euclid_proposition_11_5
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (l m n p : Geo.Line)
    (O : Geo.Point)
    (hmn : Ne m n)
    (hPerpM :
      HilbertLinesPerpendicularAt Geo l m O)
    (hPerpN :
      HilbertLinesPerpendicularAt Geo l n O)
    (hPerpP :
      HilbertLinesPerpendicularAt Geo l p O) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo m pi /\
      HilbertLineInPlane Geo n pi /\
      HilbertLineInPlane Geo p pi := by

  have hOl : H.OnLine O l :=
    hPerpM.1

  have hOm : H.OnLine O m :=
    hPerpM.2.1

  have hOn : H.OnLine O n :=
    hPerpN.2.1

  have hOp : H.OnLine O p :=
    hPerpP.2.1

  /-
  Step 1.  The distinct intersecting lines m,n generate pi.
  -/
  cases
      hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
        (Geo := Geo)
        m n O
        hmn hOm hOn with
  | intro pi hPiData =>
      have hmpi :
          HilbertLineInPlane Geo m pi :=
        hPiData.1

      have hnpi :
          HilbertLineInPlane Geo n pi :=
        hPiData.2.1

      have _hJoinPi :
          HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo m)
              (HilbertLineCarrier3D Geo n) =
            HilbertPlaneCarrier3D Geo pi :=
        hPiData.2.2

      have hOpi : S.OnPlane O pi :=
        hmpi O hOm

      let mp : PlaneLine Geo pi :=
        ⟨m, hmpi⟩

      let np : PlaneLine Geo pi :=
        ⟨n, hnpi⟩

      let Op : PlanePoint Geo pi :=
        ⟨O, hOpi⟩

      have hmnp : Ne mp np := by
        intro h
        apply hmn
        exact congrArg Subtype.val h

      have hPerpMp :
          HilbertLinesPerpendicularAt
            Geo l mp.1 Op.1 := by
        simpa [mp, Op] using hPerpM

      have hPerpNp :
          HilbertLinesPerpendicularAt
            Geo l np.1 Op.1 := by
        simpa [np, Op] using hPerpN

      /-
      Step 2.  The two generating perpendicular directions give

          l perp pi.
      -/
      have hlm : Ne l mp.1 :=
        hilbert_linesPerpendicularAt_ne
          (Geo := Geo)
          l mp.1 Op.1
          hPerpMp

      have hln : Ne l np.1 :=
        hilbert_linesPerpendicularAt_ne
          (Geo := Geo)
          l np.1 Op.1
          hPerpNp

      have hOl' : H.OnLine Op.1 l :=
        hPerpMp.1

      have hOm' : H.OnLine Op.1 mp.1 :=
        hPerpMp.2.1

      have hOn' : H.OnLine Op.1 np.1 :=
        hPerpNp.2.1

      have hlPerpPi :
          HilbertLinePerpendicularPlaneAt
            Geo l pi O := by
        have h :=
          hilbert_XI4_line_perpendicular_plane_core
            (Geo := Geo)
            pi mp np l Op
            hmnp
            hlm hln
            hOl' hOm' hOn'
            hPerpMp hPerpNp
        simpa [Op] using h

      /-
      Step 3.  Either p is already in pi, or construct sigma = join(l,p).
      -/
      by_cases hppi :
          HilbertLineInPlane Geo p pi

      next =>
        exact
          Exists.intro pi
            (And.intro hmpi
              (And.intro hnpi hppi))

      next =>
        have hlp : Ne l p :=
          hilbert_linesPerpendicularAt_ne
            (Geo := Geo)
            l p O
            hPerpP

        cases
            hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
              (Geo := Geo)
              l p O
              hlp hOl hOp with
        | intro sigma hSigmaData =>
            have hlsigma :
                HilbertLineInPlane Geo l sigma :=
              hSigmaData.1

            have hpsigma :
                HilbertLineInPlane Geo p sigma :=
              hSigmaData.2.1

            have _hJoinSigma :
                HilbertJoin3D Geo
                    (HilbertLineCarrier3D Geo l)
                    (HilbertLineCarrier3D Geo p) =
                  HilbertPlaneCarrier3D Geo sigma :=
              hSigmaData.2.2

            have hOsigma : S.OnPlane O sigma :=
              hlsigma O hOl

            have hPiSigma : Ne pi sigma := by
              intro hEq
              apply hppi
              rw [hEq]
              exact hpsigma

            /-
            Step 4.  The meet of pi and sigma is a line q through O.
            -/
            cases
                hilbertPlaneCarrier3D_inter_eq_lineCarrier
                  (Geo := Geo)
                  pi sigma
                  hPiSigma
                  O hOpi hOsigma with
            | intro q hQData =>
                have hOq : H.OnLine O q :=
                  hQData.1

                have hqpi :
                    HilbertLineInPlane Geo q pi :=
                  hQData.2.1

                have hqsigma :
                    HilbertLineInPlane Geo q sigma :=
                  hQData.2.2.1

                have _hMeet :
                    Set.inter
                        (HilbertPlaneCarrier3D Geo pi)
                        (HilbertPlaneCarrier3D Geo sigma) =
                      HilbertLineCarrier3D Geo q :=
                  hQData.2.2.2

                /-
                Since q lies in pi and passes through O,

                    l perp q.
                -/
                have hPerpQ :
                    HilbertLinesPerpendicularAt Geo l q O :=
                  HilbertLinePerpendicularPlaneAt.perpendicular_to_line
                    (Geo := Geo)
                    hlPerpPi
                    hqpi
                    hOq

                /-
                Step 5.  If p != q, then p and q are two distinct
                perpendicular directions in sigma, hence l perp sigma.
                But l is itself contained in sigma.
                -/
                have hpq : p = q := by
                  by_contra hpq

                  let pp : PlaneLine Geo sigma :=
                    ⟨p, hpsigma⟩

                  let qp : PlaneLine Geo sigma :=
                    ⟨q, hqsigma⟩

                  let Os : PlanePoint Geo sigma :=
                    ⟨O, hOsigma⟩

                  have hppqp : Ne pp qp := by
                    intro h
                    apply hpq
                    exact congrArg Subtype.val h

                  have hPerpPp :
                      HilbertLinesPerpendicularAt
                        Geo l pp.1 Os.1 := by
                    simpa [pp, Os] using hPerpP

                  have hPerpQp :
                      HilbertLinesPerpendicularAt
                        Geo l qp.1 Os.1 := by
                    simpa [qp, Os] using hPerpQ

                  have hlp' : Ne l pp.1 :=
                    hilbert_linesPerpendicularAt_ne
                      (Geo := Geo)
                      l pp.1 Os.1
                      hPerpPp

                  have hlq' : Ne l qp.1 :=
                    hilbert_linesPerpendicularAt_ne
                      (Geo := Geo)
                      l qp.1 Os.1
                      hPerpQp

                  have hOlSigma : H.OnLine Os.1 l :=
                    hPerpPp.1

                  have hOpSigma : H.OnLine Os.1 pp.1 :=
                    hPerpPp.2.1

                  have hOqSigma : H.OnLine Os.1 qp.1 :=
                    hPerpQp.2.1

                  have hlPerpSigma :
                      HilbertLinePerpendicularPlaneAt
                        Geo l sigma O := by
                    have h :=
                      hilbert_XI4_line_perpendicular_plane_core
                        (Geo := Geo)
                        sigma pp qp l Os
                        hppqp
                        hlp' hlq'
                        hOlSigma hOpSigma hOqSigma
                        hPerpPp hPerpQp
                    simpa [Os] using h

                  exact
                    (hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
                      (Geo := Geo)
                      l sigma O hlPerpSigma)
                      hlsigma

                have hppi' :
                    HilbertLineInPlane Geo p pi := by
                  rw [hpq]
                  exact hqpi

                exact
                  Exists.intro pi
                    (And.intro hmpi
                      (And.intro hnpi hppi'))

end Geometry

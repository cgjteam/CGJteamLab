import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.13.

A perpendicular to a plane at a prescribed point is unique as an
unoriented line carrier.

The proof exposes the complete join-meet-metric contradiction:

  assume l != m
      |
      v
  sigma = Join(l,m)
      |
      v
  q = Meet(pi,sigma)
      |
      v
  l perp q, m perp q
      |
      v
  q perp l, q perp m
      |
      v
  XI.4 metric core: q perp sigma
      |
      v
  q subset sigma
      |
      v
  contradiction.

No call is made to the packaged XI.13 contradiction theorem.
-/
theorem euclid_proposition_11_13
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
    (A : Geo.Point)
    (hLperp :
      HilbertLinePerpendicularPlaneAt Geo l pi A)
    (hMperp :
      HilbertLinePerpendicularPlaneAt Geo m pi A) :
    l = m := by

  by_contra hlm

  have hLInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hLperp

  have hMInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hMperp

  have hAl : H.OnLine A l :=
    hLInc.1

  have hAm : H.OnLine A m :=
    hMInc.1

  have hApi : S.OnPlane A pi :=
    hLInc.2

  /-
  The two distinct intersecting lines generate sigma.
  -/
  cases
      hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
        (Geo := Geo)
        l m A
        hlm hAl hAm with
  | intro sigma hSigmaData =>

      have hlsigma :
          HilbertLineInPlane Geo l sigma :=
        hSigmaData.1

      have hmsigma :
          HilbertLineInPlane Geo m sigma :=
        hSigmaData.2.1

      have hJoinSigma :
          HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo l)
              (HilbertLineCarrier3D Geo m) =
            HilbertPlaneCarrier3D Geo sigma :=
        hSigmaData.2.2

      have hAsigma : S.OnPlane A sigma :=
        hlsigma A hAl

      /-
      sigma and pi are distinct.

      Otherwise l would be contained in pi, impossible for a line
      perpendicular to pi.
      -/
      have hPiSigma : Ne pi sigma := by
        intro hEq

        have hlpi :
            HilbertLineInPlane Geo l pi := by
          intro X hXl
          have hXsigma : S.OnPlane X sigma :=
            hlsigma X hXl
          rw [<- hEq] at hXsigma
          exact hXsigma

        exact
          (hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
            (Geo := Geo)
            l pi A hLperp)
            hlpi

      /-
      The meet of pi and sigma is a line q through A.
      -/
      cases
          hilbertPlaneCarrier3D_inter_eq_lineCarrier
            (Geo := Geo)
            pi sigma
            hPiSigma
            A hApi hAsigma with
      | intro q hQData =>

          have hAq : H.OnLine A q :=
            hQData.1

          have hqpi :
              HilbertLineInPlane Geo q pi :=
            hQData.2.1

          have hqsigma :
              HilbertLineInPlane Geo q sigma :=
            hQData.2.2.1

          have hMeet :
              Set.inter
                  (HilbertPlaneCarrier3D Geo pi)
                  (HilbertPlaneCarrier3D Geo sigma) =
                HilbertLineCarrier3D Geo q :=
            hQData.2.2.2

          /-
          Since q lies in pi through A, both candidate normals are
          perpendicular to q.
          -/
          have hLperpQ :
              HilbertLinesPerpendicularAt Geo l q A :=
            HilbertLinePerpendicularPlaneAt.perpendicular_to_line
              (Geo := Geo)
              hLperp
              hqpi
              hAq

          have hMperpQ :
              HilbertLinesPerpendicularAt Geo m q A :=
            HilbertLinePerpendicularPlaneAt.perpendicular_to_line
              (Geo := Geo)
              hMperp
              hqpi
              hAq

          /-
          Reverse both perpendicularities.  Now q is perpendicular to
          the two generators l,m of sigma.
          -/
          have hQperpL :
              HilbertLinesPerpendicularAt Geo q l A :=
            hilbertLinesPerpendicularAt_symm_wyler
              (Geo := Geo)
              l q A
              hLperpQ

          have hQperpM :
              HilbertLinesPerpendicularAt Geo q m A :=
            hilbertLinesPerpendicularAt_symm_wyler
              (Geo := Geo)
              m q A
              hMperpQ

          let lp : PlaneLine Geo sigma :=
            ⟨l, hlsigma⟩

          let mp : PlaneLine Geo sigma :=
            ⟨m, hmsigma⟩

          let Ap : PlanePoint Geo sigma :=
            ⟨A, hAsigma⟩

          have hlpmp : Ne lp mp := by
            intro hEq
            apply hlm
            exact congrArg Subtype.val hEq

          have hQperpLp :
              HilbertLinesPerpendicularAt
                Geo q lp.1 Ap.1 := by
            simpa [lp, Ap] using hQperpL

          have hQperpMp :
              HilbertLinesPerpendicularAt
                Geo q mp.1 Ap.1 := by
            simpa [mp, Ap] using hQperpM

          have hql : Ne q lp.1 :=
            hilbert_linesPerpendicularAt_ne
              (Geo := Geo)
              q lp.1 Ap.1
              hQperpLp

          have hqm : Ne q mp.1 :=
            hilbert_linesPerpendicularAt_ne
              (Geo := Geo)
              q mp.1 Ap.1
              hQperpMp

          have hAq' : H.OnLine Ap.1 q :=
            hQperpLp.1

          have hAl' : H.OnLine Ap.1 lp.1 :=
            hQperpLp.2.1

          have hAm' : H.OnLine Ap.1 mp.1 :=
            hQperpMp.2.1

          /-
          XI.4 on sigma:
              q perp l and q perp m
          imply
              q perp sigma.
          -/
          have hQperpSigma :
              HilbertLinePerpendicularPlaneAt
                Geo q sigma A := by
            have h :=
              hilbert_XI4_line_perpendicular_plane_core
                (Geo := Geo)
                sigma lp mp q Ap
                hlpmp
                hql hqm
                hAq' hAl' hAm'
                hQperpLp hQperpMp

            simpa [Ap] using h

          /-
          Contradiction: q is itself contained in sigma.
          -/
          exact
            (hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
              (Geo := Geo)
              q sigma A hQperpSigma)
              hqsigma

end Geometry

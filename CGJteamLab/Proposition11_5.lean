import CGJteamLab.Proposition11_4

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
A line perpendicular to a plane at a point cannot itself lie in that plane.

Indeed, if it lay in the plane, the definition of line-plane
perpendicularity would make the line perpendicular to itself.
-/
theorem hilbert_linePerpendicularPlaneAt_not_in_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l : Geo.Line)
    (pi : S.Plane)
    (O : Geo.Point)
    (hPerp :
      HilbertLinePerpendicularPlaneAt Geo l pi O) :
    Not (HilbertLineInPlane Geo l pi) := by

  intro hlpi

  have hSelf :
      HilbertLinesPerpendicularAt Geo l l O :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerp
      hlpi
      hPerp.1

  exact
    (hilbert_linesPerpendicularAt_ne
      Geo l l O hSelf) rfl


/--
Euclid XI.5.

If a line `l` is perpendicular at the common point `O` to three
lines `m`, `n`, `p`, and `m` and `n` are distinct, then the three
lines `m`, `n`, `p` lie in one plane.

The proof uses XI.4 twice.

The distinct intersecting lines `m,n` determine a plane `pi`.
By XI.4, `l` is perpendicular to `pi`.

If `p` were not in `pi`, then `l,p` would determine another plane
`sigma`. The planes `pi,sigma` meet in a line `q` through `O`.
Since `q` lies in `pi`, the line `l` is perpendicular to `q`.

Now `p,q` both lie in `sigma` and both are perpendicular to `l`.
If `p != q`, XI.4 applied inside `sigma` would imply that `l` is
perpendicular to `sigma`. But `l` itself lies in `sigma`, impossible.
Therefore `p = q`, hence `p` lies in `pi`.
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

  ----------------------------------------------------------------------
  -- m and n determine the reference plane pi.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_through_two_intersecting_lines
        (Geo := Geo)
        m n hmn
        O hOm hOn
    with
    ⟨pi, hmpi, hnpi, _hUniquePi⟩

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

  have hlPerpPi :
      HilbertLinePerpendicularPlaneAt
        Geo l pi O := by
    have h :=
      euclid_proposition_11_4
        (Geo := Geo)
        pi mp np l Op
        hmnp
        hPerpMp
        hPerpNp
    simpa [Op] using h

  ----------------------------------------------------------------------
  -- Either p is already in pi, or derive a contradiction.
  ----------------------------------------------------------------------

  by_cases hppi : HilbertLineInPlane Geo p pi

  · exact
      ⟨pi, hmpi, hnpi, hppi⟩

  ·
    --------------------------------------------------------------------
    -- l and p determine a second plane sigma.
    --------------------------------------------------------------------

    have hlp : Ne l p :=
      hilbert_linesPerpendicularAt_ne
        Geo l p O hPerpP

    rcases
        hilbert_plane_through_two_intersecting_lines
          (Geo := Geo)
          l p hlp
          O hOl hOp
      with
      ⟨sigma, hlsigma, hpsigma, _hUniqueSigma⟩

    have hOsigma : S.OnPlane O sigma :=
      hlsigma O hOl

    have hPiSigma : Ne pi sigma := by
      intro hEq
      apply hppi
      rw [hEq]
      exact hpsigma

    --------------------------------------------------------------------
    -- The two planes meet in q through O.
    --------------------------------------------------------------------

    rcases
        hilbert_plane_intersection_line
          (Geo := Geo)
          pi sigma hPiSigma
          O hOpi hOsigma
      with
      ⟨q, hOq, hqpi, hqsigma, _hCommon⟩

    have hPerpQ :
        HilbertLinesPerpendicularAt Geo l q O :=
      HilbertLinePerpendicularPlaneAt.perpendicular_to_line
        (Geo := Geo)
        hlPerpPi
        hqpi
        hOq

    --------------------------------------------------------------------
    -- If p and q were distinct, XI.4 in sigma would make l
    -- perpendicular to sigma.
    --------------------------------------------------------------------

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

      have hlPerpSigma :
          HilbertLinePerpendicularPlaneAt
            Geo l sigma O := by
        have h :=
          euclid_proposition_11_4
            (Geo := Geo)
            sigma pp qp l Os
            hppqp
            hPerpPp
            hPerpQp
        simpa [Os] using h

      exact
        (hilbert_linePerpendicularPlaneAt_not_in_plane
          (Geo := Geo)
          l sigma O hlPerpSigma)
          hlsigma

    have hppi' :
        HilbertLineInPlane Geo p pi := by
      rw [hpq]
      exact hqpi

    exact
      ⟨pi, hmpi, hnpi, hppi'⟩

end Geometry

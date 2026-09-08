import CGJteamLab.Wyler.HilbertWylerParallel
import CGJteamLab.Proposition12
import CGJteamLab.Proposition31

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert-Wyler Euclidean 3D transport

Book-XI-independent extraction of the reusable Euclidean transport
machinery first developed for XI.8, XI.11, and XI.12.

No numbered Book XI proposition is imported.
-/
theorem hilbertLinePerpendicularPlaneAt_foot_unique_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (l : Geo.Line)
    (C A : Geo.Point)
    (hPerp :
      HilbertLinePerpendicularPlaneAt Geo l pi C)
    (hAl : H.OnLine A l)
    (hApi : S.OnPlane A pi) :
    A = C := by

  have hInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hCl : H.OnLine C l :=
    hInc.1

  have hCpi : S.OnPlane C pi :=
    hInc.2

  by_contra hAC

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A C hAC
      l hAl hCl
      pi hApi hCpi

  have hSelfPerp :
      HilbertLinesPerpendicularAt Geo l l C :=
    hPerp.2.2 l hlpi hCl

  have hll : Ne l l :=
    hilbert_linesPerpendicularAt_ne
      (Geo := Geo)
      l l C hSelfPerp

  exact hll rfl


/--
Inside an ambient plane sigma, through a point A not on a line l,
Euclid I.31 constructs a line m through A parallel to l.  The planar
parallelism is then packaged as ambient spatial parallelism.
-/

theorem hilbert_XI12_parallel_through_point_in_plane_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (l : Geo.Line)
    (A : Geo.Point)
    (hlsigma : HilbertLineInPlane Geo l sigma)
    (hAsigma : S.OnPlane A sigma)
    (hAl : Not (H.OnLine A l)) :
    exists m : Geo.Line,
      H.OnLine A m /\
      HilbertSpaceLinesParallel Geo l m := by

  rcases
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo) l
    with
    ⟨B, C, hBC, hBl, hCl⟩

  have hBsigma : S.OnPlane B sigma :=
    hlsigma B hBl

  have hCsigma : S.OnPlane C sigma :=
    hlsigma C hCl

  let Bsigma : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Csigma : PlanePoint Geo sigma :=
    ⟨C, hCsigma⟩

  let Asigma : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let lsigma : PlaneLine Geo sigma :=
    ⟨l, hlsigma⟩

  have hBCsigma : Ne Bsigma Csigma := by
    intro h
    apply hBC
    exact congrArg Subtype.val h

  have hBCA :
      Not
        (PrimCollinear
          (PlaneGeo Geo sigma)
          Bsigma Csigma Asigma) := by
    intro hColPlane

    have hColAmbient :
        PrimCollinear Geo B C A :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        sigma
        Bsigma Csigma Asigma
        hColPlane

    have hAonL : H.OnLine A l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hBC
        hBl
        hCl
        hColAmbient

    exact hAl hAonL

  rcases
      hilbert_parallel_through_point_exists
        (PlaneGeo Geo sigma)
        Bsigma Csigma Asigma
        hBCsigma
        hBCA
    with
    ⟨Qsigma, hAQ, hParallelPlane⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma)
        Asigma Qsigma hAQ
    with
    ⟨msigma, hAm, hQm⟩

  have hDisjointAmbient :
      HilbertLinesDisjoint Geo l msigma.1 := by
    rintro ⟨X, hXl, hXm⟩

    have hXsigma : S.OnPlane X sigma :=
      hlsigma X hXl

    let Xsigma : PlanePoint Geo sigma :=
      ⟨X, hXsigma⟩

    have hXBC :
        Xsigma ∈
          (PlaneGeo Geo sigma).PointLine
            Bsigma Csigma := by
      apply
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo sigma)
          Bsigma Csigma Xsigma
          lsigma
          hParallelPlane.1
          hBl
          hCl).mpr
      exact hXl

    have hXAQ :
        Xsigma ∈
          (PlaneGeo Geo sigma).PointLine
            Asigma Qsigma := by
      apply
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo sigma)
          Asigma Qsigma Xsigma
          msigma
          hParallelPlane.2.1
          hAm
          hQm).mpr
      exact hXm

    exact
      Set.disjoint_left.mp
        hParallelPlane.2.2
        hXBC
        hXAQ

  refine
    ⟨msigma.1,
     hAm,
     ?_⟩

  exact
    ⟨sigma,
     hlsigma,
     msigma.2,
     hDisjointAmbient⟩


/--
Euclid, Book XI, Proposition XI.12.

To set up a straight line at right angles to a given plane
from a given point in it.

Given a plane pi and a point A on pi, there exists a line
perpendicular to pi at A.

Classical dependency route:
XI.11 -> I.31 -> XI.8.
-/

theorem hilbert_XI8_parallel_meets_perpendicular_plane_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (l m : Geo.Line)
    (B : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo l pi B) :
    exists D : Geo.Point,
      H.OnLine D m /\
      S.OnPlane D pi := by

  rcases hParallel with
    ⟨sigma, hlsigma, hmsigma, hlmDisjoint⟩

  have hBInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hBl : H.OnLine B l := hBInc.1
  have hBpi : S.OnPlane B pi := hBInc.2

  have hBsigma : S.OnPlane B sigma :=
    hlsigma B hBl

  have hSigmaPi : Ne sigma pi := by
    intro hEq
    apply
      (hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
        (Geo := Geo) l pi B hPerp)
    intro X hXl
    have hXsigma : S.OnPlane X sigma :=
      hlsigma X hXl
    simpa [hEq] using hXsigma

  rcases
      hilbert_plane_intersection_line
        (Geo := Geo)
        pi sigma hSigmaPi.symm
        B hBpi hBsigma with
    ⟨q, hBq, hqpi, hqsigma, _hIntersection⟩

  have hBm : Not (H.OnLine B m) := by
    intro hBm
    exact hlmDisjoint ⟨B, hBl, hBm⟩

  have hMeet : HilbertLinesMeet Geo m q := by
    by_contra hmq

    have hqmDisjoint :
        HilbertLinesDisjoint Geo q m := by
      rintro ⟨X, hXq, hXm⟩
      exact hmq ⟨X, hXm, hXq⟩

    have hlq : l = q :=
      HSE.parallel_unique_in_plane
        sigma
        m hmsigma
        B hBsigma hBm
        l q
        hlsigma hqsigma
        hBl hlmDisjoint
        hBq hqmDisjoint

    have hlpi : HilbertLineInPlane Geo l pi := by
      intro X hXl
      have hXq : H.OnLine X q := by
        rw [← hlq]
        exact hXl
      exact hqpi X hXq

    exact
      (hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
        (Geo := Geo) l pi B hPerp) hlpi

  rcases hMeet with ⟨D, hDm, hDq⟩

  exact
    ⟨D,
     hDm,
     hqpi D hDq⟩

/--
Euclid XI.8, first use of XI.4 after the metric construction.

Let `sigma` be the plane containing the parallel lines `l,m`.
The auxiliary line `e = DE` is perpendicular to:

* `d = DB`, by construction;
* `a = DA`, because angle EDA has been proved right.

The lines `d,a` are distinct and both lie in `sigma`, so XI.4 gives
`e` perpendicular to `sigma`. Since `m` lies in `sigma`, it follows
that `e` is perpendicular to `m` at `D`.

This is Euclid's step:
  ED perpendicular to DB and DA
  => ED perpendicular to plane BDA
  => ED perpendicular to CD.
-/

theorem hilbert_XI8_auxiliary_line_perpendicular_to_parallel_wyler
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
    (l m : Geo.Line)
    (B : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo l pi B) :
    exists D : Geo.Point,
      exists d e : Geo.Line,
        H.OnLine D m /\
        S.OnPlane D pi /\
        H.OnLine B d /\
        H.OnLine D d /\
        HilbertLineInPlane Geo d pi /\
        H.OnLine D e /\
        HilbertLineInPlane Geo e pi /\
        HilbertLinesPerpendicularAt Geo e d D /\
        HilbertLinesPerpendicularAt Geo e m D := by
  rcases
      hilbert_XI8_parallel_meets_perpendicular_plane_wyler
        (Geo := Geo)
        pi l m B
        hParallel hPerp
    with
    ⟨D, hDm, hDpi⟩

  rcases hParallel with
    ⟨sigma, hlsigma, hmsigma, hlmDisjoint⟩

  have hBInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hBl : H.OnLine B l :=
    hBInc.1

  have hBpi : S.OnPlane B pi :=
    hBInc.2

  have hBsigma : S.OnPlane B sigma :=
    hlsigma B hBl

  have hDsigma : S.OnPlane D sigma :=
    hmsigma D hDm

  have hBD : Ne B D := by
    intro hBD
    subst D
    exact
      hlmDisjoint
        ⟨B, hBl, hDm⟩

  rcases
      hilbert_XI6_second_SSS_right_angle_wyler
        (Geo := Geo)
        pi l B D
        hDpi
        hBD
        hPerp
    with
    ⟨A, d, e, E,
     hAB, hAl,
     hBd, hDd, hdpi,
     hDe, hEe, hED,
     hepi, hPerpED,
     _hDEAB, _hADEB,
     hRightEDA⟩

  have hAsigma : S.OnPlane A sigma :=
    hlsigma A hAl

  have hlNotPi :
      Not (HilbertLineInPlane Geo l pi) :=
    hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
      (Geo := Geo)
      l pi B hPerp

  have hApi : Not (S.OnPlane A pi) := by
    intro hApi
    have hlpi : HilbertLineInPlane Geo l pi :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        A B hAB
        l hAl hBl
        pi hApi hBpi
    exact hlNotPi hlpi

  have hAD : Ne A D := by
    intro hEq
    subst A
    exact hApi hDpi

  have hDA : Ne D A :=
    hAD.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        D A hDA
    with
    ⟨a, hDa, hAa⟩

  have hDE : Ne D E :=
    hED.symm

  have hNonEDA :
      Not (PrimCollinear Geo E D A) := by
    intro hEDA

    have hDEA :
        PrimCollinear Geo D E A :=
      PrimCollinearSwap
        Geo E D A hEDA

    have hAe : H.OnLine A e :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hDE
        hDe
        hEe
        hDEA

    exact hApi (hepi A hAe)

  have hPerpEA :
      HilbertLinesPerpendicularAt
        Geo e a D :=
    ⟨hDe, hDa,
     E, A,
     hED, hAD,
     hEe, hAa,
     hNonEDA,
     hRightEDA⟩

  have hdsigma :
      HilbertLineInPlane Geo d sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      B D hBD
      d hBd hDd
      sigma hBsigma hDsigma

  have hasigma :
      HilbertLineInPlane Geo a sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      D A hDA
      a hDa hAa
      sigma hDsigma hAsigma

  have hda : Ne d a := by
    intro hEq
    subst a
    exact hApi (hdpi A hAa)

  let dp : PlaneLine Geo sigma :=
    ⟨d, hdsigma⟩

  let ap : PlaneLine Geo sigma :=
    ⟨a, hasigma⟩

  let Dp : PlanePoint Geo sigma :=
    ⟨D, hDsigma⟩

  have hdap : Ne dp ap := by
    intro h
    apply hda
    exact congrArg Subtype.val h

  have hEperpSigma :
      HilbertLinePerpendicularPlaneAt
        Geo e sigma D :=
    hilbertLinePerpendicularPlaneAt_of_two_plane_lines_parallel_wyler
      (Geo := Geo)
      sigma
      dp ap
      e
      Dp
      hdap
      hPerpED
      hPerpEA

  have hPerpEM :
      HilbertLinesPerpendicularAt
        Geo e m D :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hEperpSigma
      hmsigma
      hDm

  exact
    ⟨D, d, e,
     hDm,
     hDpi,
     hBd,
     hDd,
     hdpi,
     hDe,
     hepi,
     hPerpED,
     hPerpEM⟩

/--
Neutral planar helper extracted from the final planar part of XI.6.

If two lines `l,m` lie in one ambient plane `sigma` and are
perpendicular at distinct points `B,D` to the same transversal `d`,
then `l,m` are disjoint.

The proof is carried out inside `PlaneGeo Geo sigma` and is an
application of Euclid I.27 to equal right alternate angles.
-/

theorem hilbert_XI8_coplanar_perpendiculars_to_same_line_disjoint_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (l m d : Geo.Line)
    (B D : Geo.Point)
    (hBD : Ne B D)
    (hlsigma : HilbertLineInPlane Geo l sigma)
    (hmsigma : HilbertLineInPlane Geo m sigma)
    (hdsigma : HilbertLineInPlane Geo d sigma)
    (hPerpLd :
      HilbertLinesPerpendicularAt Geo l d B)
    (hPerpMd :
      HilbertLinesPerpendicularAt Geo m d D) :
    HilbertLinesDisjoint Geo l m := by

  have hBl : H.OnLine B l :=
    hPerpLd.1

  have hBd : H.OnLine B d :=
    hPerpLd.2.1

  have hDm : H.OnLine D m :=
    hPerpMd.1

  have hDd : H.OnLine D d :=
    hPerpMd.2.1

  have hBsigma : S.OnPlane B sigma :=
    hlsigma B hBl

  have hDsigma : S.OnPlane D sigma :=
    hmsigma D hDm

  let Bp : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Dp : PlanePoint Geo sigma :=
    ⟨D, hDsigma⟩

  let lp : PlaneLine Geo sigma :=
    ⟨l, hlsigma⟩

  let mp : PlaneLine Geo sigma :=
    ⟨m, hmsigma⟩

  let dp : PlaneLine Geo sigma :=
    ⟨d, hdsigma⟩

  have hBDp : Ne Bp Dp := by
    intro h
    apply hBD
    exact congrArg Subtype.val h

  have hPerpLpDp :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma) lp dp Bp :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      sigma lp dp Bp).mpr
      hPerpLd

  have hPerpMpDp :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma) mp dp Dp :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      sigma mp dp Dp).mpr
      hPerpMd

  ----------------------------------------------------------------------
  -- Choose one nonfoot point A on l and one nonfoot point C on m.
  ----------------------------------------------------------------------

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        l B
    with
    ⟨A, hAB, hAl⟩

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        m D
    with
    ⟨C, hCD, hCm⟩

  have hAsigma : S.OnPlane A sigma :=
    hlsigma A hAl

  have hCsigma : S.OnPlane C sigma :=
    hmsigma C hCm

  let Ap : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let Cp : PlanePoint Geo sigma :=
    ⟨C, hCsigma⟩

  have hABp : Ne Ap Bp := by
    intro h
    apply hAB
    exact congrArg Subtype.val h

  have hCDp : Ne Cp Dp := by
    intro h
    apply hCD
    exact congrArg Subtype.val h

  have hNormA :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo sigma)
      lp dp
      Bp Ap Dp
      (hilbert_linesPerpendicularAt_ne
        (PlaneGeo Geo sigma)
        lp dp Bp hPerpLpDp)
      hPerpLpDp
      hABp
      hBDp.symm
      hAl
      hDd

  have hNormC :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo sigma)
      mp dp
      Dp Cp Bp
      (hilbert_linesPerpendicularAt_ne
        (PlaneGeo Geo sigma)
        mp dp Dp hPerpMpDp)
      hPerpMpDp
      hCDp
      hBDp
      hCm
      hBd

  have hAoff :
      Not (PlaneOnLine Geo Ap dp) := by
    intro hAd
    exact
      hNormA.1
        ⟨dp, hAd, hBd, hDd⟩

  have hCoff :
      Not (PlaneOnLine Geo Cp dp) := by
    intro hCd
    exact
      hNormC.1
        ⟨dp, hCd, hDd, hBd⟩

  ----------------------------------------------------------------------
  -- Choose X on l on the opposite side of d from C.
  ----------------------------------------------------------------------

  obtain
      ⟨Xp, hXB, hXlp, hXoff, hOppXC, hRightXBD⟩ :
      exists Xp : PlanePoint Geo sigma,
        Ne Xp Bp /\
        PlaneOnLine Geo Xp lp /\
        Not (PlaneOnLine Geo Xp dp) /\
        HilbertOppositeSide
          (PlaneGeo Geo sigma) Xp Cp dp /\
        HilbertRightAngle
          (PlaneGeo Geo sigma) Xp Bp Dp := by

    by_cases hSame :
        HilbertSameSide
          (PlaneGeo Geo sigma) Ap Cp dp

    · rcases
          HilbertOrder.between_extension
            (Geo := PlaneGeo Geo sigma)
            Ap Bp hABp
        with
        ⟨Xp, hABX⟩

      have hABXData :=
        HilbertOrder.between_incidence
          (Geo := PlaneGeo Geo sigma)
          Ap Bp Xp hABX

      have hXB : Ne Xp Bp :=
        hABXData.2.1.symm

      have hABXcol :
          PrimCollinear
            (PlaneGeo Geo sigma) Ap Bp Xp :=
        hABXData.2.2.2.1

      have hXlp :
          PlaneOnLine Geo Xp lp :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := PlaneGeo Geo sigma)
          hABp
          hAl
          hBl
          hABXcol

      have hXoff :
          Not (PlaneOnLine Geo Xp dp) := by
        intro hXd

        have hEq : lp = dp :=
          HilbertPlaneIncidence.line_unique
            (Geo := PlaneGeo Geo sigma)
            Bp Xp hXB.symm
            lp dp
            hBl hXlp
            hBd hXd

        have hAd :
            PlaneOnLine Geo Ap dp := by
          rw [← hEq]
          exact hAl

        exact hAoff hAd

      have hOppAX :
          HilbertOppositeSide
            (PlaneGeo Geo sigma) Ap Xp dp :=
        ⟨hAoff,
         hXoff,
         ⟨Bp, hABX, hBd⟩⟩

      have hOppXA :
          HilbertOppositeSide
            (PlaneGeo Geo sigma) Xp Ap dp :=
        hilbert_oppositeSide_symm
          (PlaneGeo Geo sigma)
          Ap Xp dp hOppAX

      have hOppXC :
          HilbertOppositeSide
            (PlaneGeo Geo sigma) Xp Cp dp :=
        hilbert_oppositeSide_transport_right
          (PlaneGeo Geo sigma)
          Xp Ap Cp dp
          hOppXA
          hSame

      have hNormX :=
        hilbert_XI4_linesPerpendicularAt_right_angle_of_points
          (PlaneGeo Geo sigma)
          lp dp
          Bp Xp Dp
          (hilbert_linesPerpendicularAt_ne
            (PlaneGeo Geo sigma)
            lp dp Bp hPerpLpDp)
          hPerpLpDp
          hXB
          hBDp.symm
          hXlp
          hDd

      exact
        ⟨Xp,
         hXB,
         (show PlaneOnLine Geo Xp lp from hXlp),
         (show Not (PlaneOnLine Geo Xp dp) from hXoff),
         hOppXC,
         hNormX.2⟩

    · have hOppAC :
          HilbertOppositeSide
            (PlaneGeo Geo sigma) Ap Cp dp :=
        hilbert_oppositeSide_of_not_sameSide
          (PlaneGeo Geo sigma)
          Ap Cp dp
          hAoff hCoff hSame

      exact
        ⟨Ap,
         hABp,
         (show PlaneOnLine Geo Ap lp from hAl),
         (show Not (PlaneOnLine Geo Ap dp) from hAoff),
         hOppAC,
         hNormA.2⟩

  ----------------------------------------------------------------------
  -- The selected right angles are congruent.
  ----------------------------------------------------------------------

  have hNonXBDPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Xp Bp Dp) := by
    intro h
    exact
      hXoff
        (hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := PlaneGeo Geo sigma)
          hBDp
          hBd
          hDd
          (PrimCollinearCycle
            (PlaneGeo Geo sigma)
            Xp Bp Dp h))

  have hNonCDBPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) Cp Dp Bp) :=
    hNormC.1

  have hNonXBDAmbient :
      Not (PrimCollinear Geo Xp.1 B D) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      sigma Xp Bp Dp hNonXBDPlane

  have hNonCDBAmbient :
      Not (PrimCollinear Geo C D B) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      sigma Cp Dp Bp hNonCDBPlane

  have hRightXBDAmbient :
      HilbertRightAngle Geo Xp.1 B D :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      sigma Xp Bp Dp).mp
      hRightXBD

  have hRightCDBAmbient :
      HilbertRightAngle Geo C D B :=
    (planeGeo_rightAngle_iff_ambient
      (Geo := Geo)
      sigma Cp Dp Bp).mp
      hNormC.2

  have hRightAnglesAmbient :
      Geo.AngleCongruent
        Xp.1 B D
        C D B :=
    hilbert_XI6_space_right_angles_congruent_in_plane_wyler
      (Geo := Geo)
      sigma
      Xp.1 B D
      Cp Dp Bp
      hNonXBDAmbient
      hNonCDBAmbient
      hRightXBDAmbient
      hRightCDBAmbient

  have hRightAnglesPlane :
      (PlaneGeo Geo sigma).AngleCongruent
        Xp Bp Dp
        Cp Dp Bp :=
    (planeGeo_angleCongruent_iff_ambient
      (Geo := Geo)
      sigma
      Xp Bp Dp
      Cp Dp Bp).mpr
      hRightAnglesAmbient

  have hReversed :
      (PlaneGeo Geo sigma).AngleCongruent
        Dp Bp Xp
        Bp Dp Cp :=
    AngleCongruentReverse
      (PlaneGeo Geo sigma)
      Xp Bp Dp
      Cp Dp Bp
      hRightAnglesPlane

  ----------------------------------------------------------------------
  -- Put a point M between B,D and normalize the transversal rays.
  ----------------------------------------------------------------------

  rcases
      hilbert_between_exists
        (PlaneGeo Geo sigma)
        Bp Dp hBDp
    with
    ⟨Mp, hBMD⟩

  have hDMB :
      (PlaneGeo Geo sigma).Between
        Dp Mp Bp :=
    (HilbertOrder.between_incidence
      (Geo := PlaneGeo Geo sigma)
      Bp Mp Dp hBMD).2.2.2.2

  have hRayBMD :
      HilbertSameRay
        (PlaneGeo Geo sigma) Bp Mp Dp :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      Bp Mp Dp hBMD

  have hRayDMB :
      HilbertSameRay
        (PlaneGeo Geo sigma) Dp Mp Bp :=
    hilbert_sameRay_of_between
      (PlaneGeo Geo sigma)
      Dp Mp Bp hDMB

  have hLeft :
      (PlaneGeo Geo sigma).Angle Mp Bp Xp =
      (PlaneGeo Geo sigma).Angle Dp Bp Xp :=
    hilbert_angle_eq_of_sameRay_first
      (PlaneGeo Geo sigma)
      Bp Mp Dp Xp hRayBMD

  have hRight :
      (PlaneGeo Geo sigma).Angle Mp Dp Cp =
      (PlaneGeo Geo sigma).Angle Bp Dp Cp :=
    hilbert_angle_eq_of_sameRay_first
      (PlaneGeo Geo sigma)
      Dp Mp Bp Cp hRayDMB

  have hAlternate :
      (PlaneGeo Geo sigma).AngleCongruent
        Mp Bp Xp
        Mp Dp Cp := by
    unfold Geometry.Geo.AngleCongruent
      at hReversed ⊢
    rw [hLeft, hRight]
    exact hReversed

  ----------------------------------------------------------------------
  -- Euclid I.27 in PlaneGeo(sigma).
  ----------------------------------------------------------------------

  have hParallel :
      (PlaneGeo Geo sigma).Parallel
        Bp Xp Dp Cp :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      (PlaneGeo Geo sigma)
      Bp Xp Dp Mp Cp
      dp
      hBMD
      hBd
      hDd
      hOppXC
      hAlternate

  ----------------------------------------------------------------------
  -- Convert point-pair parallelism to ambient carrier disjointness.
  ----------------------------------------------------------------------

  intro hMeet

  rcases hMeet with
    ⟨P, hPl, hPm⟩

  have hPsigma : S.OnPlane P sigma :=
    hlsigma P hPl

  let Pp : PlanePoint Geo sigma :=
    ⟨P, hPsigma⟩

  have hPBX :
      Pp ∈ (PlaneGeo Geo sigma).PointLine Bp Xp :=
    (hilbert_mem_pointLine_iff_onLine
      (PlaneGeo Geo sigma)
      Bp Xp Pp lp
      hParallel.1
      hBl hXlp).mpr
      hPl

  have hPDC :
      Pp ∈ (PlaneGeo Geo sigma).PointLine Dp Cp :=
    (hilbert_mem_pointLine_iff_onLine
      (PlaneGeo Geo sigma)
      Dp Cp Pp mp
      hParallel.2.1
      hDm hCm).mpr
      hPm

  exact
    Set.disjoint_left.mp
      hParallel.2.2
      hPBX
      hPDC

/--
Euclid XI.8, Group-IV step for an already fixed transversal `d = BD`.

Assume `D` is the intersection point of the parallel line `m` with the
reference plane `pi`, and `d` is the already chosen line through `B,D`
lying in `pi`.

Since `l` is perpendicular to `pi`, it is perpendicular to `d` at `B`.
Inside the common plane `sigma` of `l,m`, construct through `D` a line
`p` perpendicular to `d`. By the neutral I.27 helper, `p` is disjoint
from `l`. Group IV then identifies `p` with the unique parallel `m`
through `D`. Hence `m` is perpendicular to `d` at `D`.
-/

theorem hilbert_XI8_parallel_line_perpendicular_to_given_BD_wyler
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
    (l m d : Geo.Line)
    (B D : Geo.Point)
    (hParallel : HilbertSpaceLinesParallel Geo l m)
    (hPerp : HilbertLinePerpendicularPlaneAt Geo l pi B)
    (hDm : H.OnLine D m)
    (hDpi : S.OnPlane D pi)
    (hBd : H.OnLine B d)
    (hDd : H.OnLine D d)
    (hdpi : HilbertLineInPlane Geo d pi) :
    HilbertLinesPerpendicularAt Geo m d D := by

  rcases hParallel with
    ⟨sigma, hlsigma, hmsigma, hlmDisjoint⟩

  have hBInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hBl : H.OnLine B l :=
    hBInc.1

  have hBsigma : S.OnPlane B sigma :=
    hlsigma B hBl

  have hDsigma : S.OnPlane D sigma :=
    hmsigma D hDm

  have hBD : Ne B D := by
    intro hBD
    subst D
    exact
      hlmDisjoint
        ⟨B, hBl, hDm⟩

  have hdsigma :
      HilbertLineInPlane Geo d sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      B D hBD
      d hBd hDd
      sigma hBsigma hDsigma

  let Bp : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Dp : PlanePoint Geo sigma :=
    ⟨D, hDsigma⟩

  let dp : PlaneLine Geo sigma :=
    ⟨d, hdsigma⟩

  have hBDp : Ne Bp Dp := by
    intro h
    apply hBD
    exact congrArg Subtype.val h

  have hPerpLd :
      HilbertLinesPerpendicularAt Geo l d B :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerp
      hdpi
      hBd

  ----------------------------------------------------------------------
  -- Construct p through D in sigma, perpendicular to d.
  ----------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        (Geo := PlaneGeo Geo sigma)
        Bp Dp hBDp
    with
    ⟨Xp, hBDX⟩

  rcases
      hilbert_right_angle_exists_nondegenerate
        (PlaneGeo Geo sigma)
        Bp Dp Xp hBDX
    with
    ⟨Yp, hNonBDY, hRightBDY⟩

  have hDYp : Ne Dp Yp := by
    intro h
    subst Yp
    apply hNonBDY
    exact
      ⟨dp, hBd, hDd, hDd⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma)
        Dp Yp hDYp
    with
    ⟨pp, hDpp, hYpp⟩

  have hPerpDpPp :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo sigma) dp pp Dp :=
    ⟨hDd, hDpp,
     Bp, Yp,
     hBDp, hDYp.symm,
     hBd, hYpp,
     hNonBDY,
     hRightBDY⟩

  have hPerpAmbientDP :
      HilbertLinesPerpendicularAt
        Geo d pp.1 D :=
    (planeGeo_linesPerpendicularAt_iff_ambient
      (Geo := Geo)
      sigma dp pp Dp).mp
      hPerpDpPp

  have hPerpPd :
      HilbertLinesPerpendicularAt
        Geo pp.1 d D :=
    hilbertLinesPerpendicularAt_symm_wyler
      (Geo := Geo)
      d pp.1 D
      hPerpAmbientDP

  ----------------------------------------------------------------------
  -- I.27: p and l are disjoint.
  ----------------------------------------------------------------------

  have hlpDisjoint :
      HilbertLinesDisjoint Geo l pp.1 :=
    hilbert_XI8_coplanar_perpendiculars_to_same_line_disjoint_wyler
      (Geo := Geo)
      sigma
      l pp.1 d
      B D
      hBD
      hlsigma
      pp.2
      hdsigma
      hPerpLd
      hPerpPd

  have hDl : Not (H.OnLine D l) := by
    intro hDl
    exact
      hlmDisjoint
        ⟨D, hDl, hDm⟩

  have hmlDisjoint :
      HilbertLinesDisjoint Geo m l := by
    rintro ⟨P, hPm, hPl⟩
    exact
      hlmDisjoint
        ⟨P, hPl, hPm⟩

  have hplDisjoint :
      HilbertLinesDisjoint Geo pp.1 l := by
    rintro ⟨P, hPp, hPl⟩
    exact
      hlpDisjoint
        ⟨P, hPl, hPp⟩

  ----------------------------------------------------------------------
  -- Group IV: m is the constructed perpendicular p.
  ----------------------------------------------------------------------

  have hmp : m = pp.1 :=
    HSE.parallel_unique_in_plane
      sigma
      l hlsigma
      D hDsigma hDl
      m pp.1
      hmsigma pp.2
      hDm hmlDisjoint
      hDpp hplDisjoint

  rw [hmp]
  exact hPerpPd

/--
Euclid XI.8.

If two spatial lines are parallel, and the first is perpendicular to a
plane, then the second is also perpendicular to that plane.

The proof follows Euclid's synthetic route.

1. Group IV shows that the second parallel meets the reference plane.
2. The XI.6 auxiliary construction produces `d = BD` and an auxiliary
   line `e = DE` in the reference plane, with `e` perpendicular to `d`.
3. The metric part of XI.6, followed by XI.4 in the common plane of the
   parallel lines, gives `e` perpendicular to `m`.
4. The planar I.27 argument plus Group IV gives `m` perpendicular to
   `d` at `D` -- the formal replacement for Euclid's use of I.29.
5. Since `d,e` are distinct intersecting lines of the reference plane
   and `m` is perpendicular to both at `D`, XI.4 gives
   `m` perpendicular to the reference plane.
-/

theorem euclid_proposition_11_8_wyler
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

  ----------------------------------------------------------------------
  -- Use the XI.8 metric configuration with one fixed D,d,e.
  ----------------------------------------------------------------------

  rcases
      hilbert_XI8_auxiliary_line_perpendicular_to_parallel_wyler
        (Geo := Geo)
        pi l m B
        hParallel hPerp
    with
    ⟨D, d, e,
     hDm,
     hDpi,
     hBd,
     hDd,
     hdpi,
     hDe,
     hepi,
     hPerpED,
     hPerpEm⟩

  ----------------------------------------------------------------------
  -- I.29 / Group IV for the same fixed transversal d = BD.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- Normalize e perpendicular m to m perpendicular e.
  ----------------------------------------------------------------------

  have hPerpMe :
      HilbertLinesPerpendicularAt Geo m e D :=
    hilbertLinesPerpendicularAt_symm_wyler
      (Geo := Geo)
      e m D
      hPerpEm

  ----------------------------------------------------------------------
  -- d and e are distinct because e is perpendicular to d.
  ----------------------------------------------------------------------

  have hed : Ne e d :=
    hilbert_linesPerpendicularAt_ne
      (Geo := Geo)
      e d D
      hPerpED

  have hde : Ne d e :=
    hed.symm

  let dp : PlaneLine Geo pi :=
    ⟨d, hdpi⟩

  let ep : PlaneLine Geo pi :=
    ⟨e, hepi⟩

  let Dp : PlanePoint Geo pi :=
    ⟨D, hDpi⟩

  have hdep : Ne dp ep := by
    intro h
    apply hde
    exact congrArg Subtype.val h

  ----------------------------------------------------------------------
  -- Final Euclid XI.4 in the reference plane pi.
  ----------------------------------------------------------------------

  have hMperpPi :
      HilbertLinePerpendicularPlaneAt Geo m pi D :=
    hilbertLinePerpendicularPlaneAt_of_two_plane_lines_parallel_wyler
      (Geo := Geo)
      pi
      dp ep
      m
      Dp
      hdep
      hPerpMd
      hPerpMe

  exact
    ⟨D, hMperpPi⟩

theorem euclid_proposition_11_11_wyler
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
    (hApi : Not (S.OnPlane A pi)) :
    exists l F,
      H.OnLine A l /\
      HilbertLinePerpendicularPlaneAt Geo l pi F := by

  ----------------------------------------------------------------------
  -- Choose a nondegenerate line bc in the given plane pi.
  ----------------------------------------------------------------------

  rcases
      hilbert_three_noncollinear_on_plane
        (Geo := Geo) pi
    with
    ⟨B, C, T,
     hBpi, hCpi, _hTpi,
     hBCT⟩

  have hBC : Ne B C :=
    hilbert_noncollinear_ne_first
      Geo B C T hBCT

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        B C hBC
    with
    ⟨bc, hBbc, hCbc⟩

  have hbcpi :
      HilbertLineInPlane Geo bc pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      B C hBC
      bc hBbc hCbc
      pi hBpi hCpi

  have hAbc :
      Not (H.OnLine A bc) := by
    intro h
    exact hApi (hbcpi A h)

  ----------------------------------------------------------------------
  -- The line bc together with A determines the auxiliary plane sigma.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_through_line_and_external_point
        (Geo := Geo)
        bc A hAbc
    with
    ⟨sigma, hbcsigma, hAsigma, _hSigmaUnique⟩

  have hBsigma : S.OnPlane B sigma :=
    hbcsigma B hBbc

  have hCsigma : S.OnPlane C sigma :=
    hbcsigma C hCbc

  let Bsigma : PlanePoint Geo sigma :=
    ⟨B, hBsigma⟩

  let Csigma : PlanePoint Geo sigma :=
    ⟨C, hCsigma⟩

  let Asigma : PlanePoint Geo sigma :=
    ⟨A, hAsigma⟩

  let bcsigma : PlaneLine Geo sigma :=
    ⟨bc, hbcsigma⟩

  have hBCsigma : Ne Bsigma Csigma := by
    intro h
    apply hBC
    exact congrArg Subtype.val h

  ----------------------------------------------------------------------
  -- First Euclid I.12 in PlaneGeo(sigma):
  -- draw AD perpendicular to BC.
  ----------------------------------------------------------------------

  rcases
      hilbert_perpendicular_from_point_exists
        (PlaneGeo Geo sigma)
        Bsigma Csigma Asigma
        bcsigma
        hBCsigma
        hBbc
        hCbc
        hAbc
    with
    ⟨Dsigma, Rsigma,
     hDbc,
     hRbc,
     hRightRDAPlane⟩

  have hRightRDA :
      HilbertRightAngle Geo Rsigma.1 Dsigma.1 A := by
    apply
      (planeGeo_rightAngle_iff_ambient
        (Geo := Geo)
        sigma Rsigma Dsigma Asigma).mp
    exact hRightRDAPlane

  have hDpi : S.OnPlane Dsigma.1 pi :=
    hbcpi Dsigma.1 hDbc

  have hAD : Ne A Dsigma.1 := by
    intro h
    apply hApi
    rw [h]
    exact hDpi

  have hDA : Ne Dsigma.1 A :=
    hAD.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        Dsigma.1 A hDA
    with
    ⟨ad, hDad, hAad⟩

  have hadsigma :
      HilbertLineInPlane Geo ad sigma :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      Dsigma.1 A hDA
      ad hDad hAad
      sigma Dsigma.2 hAsigma

  ----------------------------------------------------------------------
  -- Package the first I.12 right angle as bc perpendicular ad at D.
  ----------------------------------------------------------------------

  rcases hRightRDA with
    ⟨X, hRDX, hAngleRDA_ADX⟩

  have hRDXData :=
    HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      Rsigma.1 Dsigma.1 X hRDX

  have hRD : Ne Rsigma.1 Dsigma.1 :=
    hRDXData.1

  have hRightRDA' :
      HilbertRightAngle Geo Rsigma.1 Dsigma.1 A :=
    ⟨X, hRDX, hAngleRDA_ADX⟩

  have hRDA :
      Not (PrimCollinear Geo Rsigma.1 Dsigma.1 A) := by
    intro hCol

    have hAonBC :
        H.OnLine A bc :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hRD
        hRbc
        hDbc
        hCol

    exact hApi (hbcpi A hAonBC)

  have hPerpBCAD :
      HilbertLinesPerpendicularAt Geo bc ad Dsigma.1 := by
    exact
      ⟨hDbc,
       hDad,
       Rsigma.1, A,
       hRD,
       hAD,
       hRbc,
       hAad,
       hRDA,
       hRightRDA'⟩

  ----------------------------------------------------------------------
  -- Euclid's case split.
  ----------------------------------------------------------------------

  by_cases hADpi :
      HilbertLinePerpendicularPlaneAt Geo ad pi Dsigma.1

  · exact
      ⟨ad, Dsigma.1, hAad, hADpi⟩

  · --------------------------------------------------------------------
    -- Nontrivial branch:
    -- construct DE in pi perpendicular to BC at D.
    --------------------------------------------------------------------

    let Bpi : PlanePoint Geo pi :=
      ⟨B, hBpi⟩

    let Cpi : PlanePoint Geo pi :=
      ⟨C, hCpi⟩

    let Dpi : PlanePoint Geo pi :=
      ⟨Dsigma.1, hDpi⟩

    let bcpi : PlaneLine Geo pi :=
      ⟨bc, hbcpi⟩

    rcases
        planeGeo_opposite_points_on_line_congruent_to
          (Geo := Geo)
          pi
          bcpi
          Dpi Bpi Cpi
          hDbc
      with
      ⟨Lpi, Mpi,
       hLbc,
       hMbc,
       hLDM,
       _hDLref,
       _hDMref⟩

    rcases
        hilbert_right_angle_exists_nondegenerate
          (PlaneGeo Geo pi)
          Lpi Dpi Mpi
          hLDM
      with
      ⟨Epi,
       hLDE_noncol,
       hRightLDE⟩

    have hDEL_noncol :
        Not
          (PrimCollinear
            (PlaneGeo Geo pi)
            Dpi Epi Lpi) := by
      intro h
      exact
        hLDE_noncol
          (PrimCollinearCycle
            (PlaneGeo Geo pi)
            Epi Lpi Dpi
            (PrimCollinearCycle
              (PlaneGeo Geo pi)
              Dpi Epi Lpi h))

    have hDEpi : Ne Dpi Epi :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        Dpi Epi Lpi
        hDEL_noncol

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := PlaneGeo Geo pi)
          Dpi Epi hDEpi
      with
      ⟨depi, hDde, hEde⟩

    have hLD : Ne Lpi Dpi :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        Lpi Dpi Epi
        hLDE_noncol

    have hED : Ne Epi Dpi :=
      hDEpi.symm

    have hPerpBCDEPlane :
        HilbertLinesPerpendicularAt
          (PlaneGeo Geo pi)
          bcpi depi Dpi := by
      exact
        ⟨hDbc,
         hDde,
         Lpi, Epi,
         hLD,
         hED,
         hLbc,
         hEde,
         hLDE_noncol,
         hRightLDE⟩

    have hPerpBCDE :
        HilbertLinesPerpendicularAt
          Geo bc depi.1 Dsigma.1 :=
      (planeGeo_linesPerpendicularAt_iff_ambient
        (Geo := Geo)
        pi bcpi depi Dpi).mp
        hPerpBCDEPlane

    have hADDE : Ne ad depi.1 := by
      intro hEq

      have hAde :
          H.OnLine A depi.1 := by
        rw [← hEq]
        exact hAad

      exact hApi (depi.2 A hAde)

    --------------------------------------------------------------------
    -- The intersecting lines ad,de determine the auxiliary plane tau.
    --------------------------------------------------------------------

    rcases
        hilbert_plane_through_two_intersecting_lines
          (Geo := Geo)
          ad depi.1
          hADDE
          Dsigma.1
          hDad
          hDde
      with
      ⟨tau,
       hadtau,
       hdetau,
       _hTauUnique⟩

    have hAtau : S.OnPlane A tau :=
      hadtau A hAad

    have hAde :
        Not (H.OnLine A depi.1) := by
      intro h
      exact hApi (depi.2 A h)

    --------------------------------------------------------------------
    -- Second Euclid I.12 in PlaneGeo(tau):
    -- draw AF perpendicular to DE.
    --------------------------------------------------------------------

    rcases
        hilbert_other_point_on_line
          (Geo := Geo)
          depi.1 Dsigma.1
      with
      ⟨E, hEDambient, hEdeAmbient⟩

    have hDEambient : Ne Dsigma.1 E :=
      hEDambient.symm

    have hEtau : S.OnPlane E tau :=
      hdetau E hEdeAmbient

    let Dtau : PlanePoint Geo tau :=
      ⟨Dsigma.1, hdetau Dsigma.1 hDde⟩

    let Etau : PlanePoint Geo tau :=
      ⟨E, hEtau⟩

    let Atau : PlanePoint Geo tau :=
      ⟨A, hAtau⟩

    let detau : PlaneLine Geo tau :=
      ⟨depi.1, hdetau⟩

    have hDEtau : Ne Dtau Etau := by
      intro h
      apply hDEambient
      exact congrArg Subtype.val h

    rcases
        hilbert_perpendicular_from_point_exists
          (PlaneGeo Geo tau)
          Dtau Etau Atau
          detau
          hDEtau
          hDde
          hEdeAmbient
          hAde
      with
      ⟨Ftau, Qtau,
       hFde,
       hQde,
       hRightQFAPlane⟩

    have hRightQFA :
        HilbertRightAngle Geo Qtau.1 Ftau.1 A := by
      apply
        (planeGeo_rightAngle_iff_ambient
          (Geo := Geo)
          tau Qtau Ftau Atau).mp
      exact hRightQFAPlane

    have hFpi : S.OnPlane Ftau.1 pi :=
      depi.2 Ftau.1 hFde

    have hAF : Ne A Ftau.1 := by
      intro h
      apply hApi
      rw [h]
      exact hFpi

    have hFA : Ne Ftau.1 A :=
      hAF.symm

    rcases hRightQFA with
      ⟨Y, hQFY, hAngleQFA_AFY⟩

    have hQFYData :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        Qtau.1 Ftau.1 Y hQFY

    have hQF : Ne Qtau.1 Ftau.1 :=
      hQFYData.1

    have hRightQFA' :
        HilbertRightAngle Geo Qtau.1 Ftau.1 A :=
      ⟨Y, hQFY, hAngleQFA_AFY⟩

    have hQFA :
        Not (PrimCollinear Geo Qtau.1 Ftau.1 A) := by
      intro hCol

      have hAonDE :
          H.OnLine A depi.1 :=
        hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo)
          hQF
          hQde
          hFde
          hCol

      exact hAde hAonDE

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          Ftau.1 A hFA
      with
      ⟨af, hFaf, hAaf⟩

    have haftau :
        HilbertLineInPlane Geo af tau :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        Ftau.1 A hFA
        af hFaf hAaf
        tau Ftau.2 hAtau

    have hPerpDEAF :
        HilbertLinesPerpendicularAt Geo depi.1 af Ftau.1 := by
      exact
        ⟨hFde,
         hFaf,
         Qtau.1, A,
         hQF,
         hAF,
         hQde,
         hAaf,
         hQFA,
         hRightQFA'⟩

    --------------------------------------------------------------------
    -- Hidden formal fact: F is not on bc.
    --------------------------------------------------------------------

    have hBCDE :
        Ne bc depi.1 :=
      hilbert_linesPerpendicularAt_ne
        (Geo := Geo)
        bc depi.1 Dsigma.1
        hPerpBCDE

    have hFnotBC :
        Not (H.OnLine Ftau.1 bc) := by

      intro hFbc

      have hFD : Ftau.1 = Dsigma.1 := by
        by_contra hFDne

        have hDF : Ne Dsigma.1 Ftau.1 := by
          intro h
          exact hFDne h.symm

        have hBCeqDE : bc = depi.1 :=
          HilbertPlaneIncidence.line_unique
            (Geo := Geo)
            Dsigma.1 Ftau.1 hDF
            bc depi.1
            hDbc hFbc
            hDde hFde

        exact hBCDE hBCeqDE

      have hDaf :
          H.OnLine Dsigma.1 af := by
        rw [← hFD]
        exact hFaf

      have hADeqAF : ad = af :=
        HilbertPlaneIncidence.line_unique
          (Geo := Geo)
          Dsigma.1 A hDA
          ad af
          hDad hAad
          hDaf hAaf

      have hPerpADBC :
          HilbertLinesPerpendicularAt Geo ad bc Dsigma.1 :=
        hilbertLinesPerpendicularAt_symm_wyler
          (Geo := Geo)
          bc ad Dsigma.1
          hPerpBCAD

      have hPerpDEAD :
          HilbertLinesPerpendicularAt Geo depi.1 ad Dsigma.1 := by
        rw [hADeqAF]
        rw [← hFD]
        exact hPerpDEAF

      have hPerpADDE :
          HilbertLinesPerpendicularAt Geo ad depi.1 Dsigma.1 :=
        hilbertLinesPerpendicularAt_symm_wyler
          (Geo := Geo)
          depi.1 ad Dsigma.1
          hPerpDEAD

      let depPi : PlaneLine Geo pi :=
        ⟨depi.1, depi.2⟩

      have hBCDEpi : Ne bcpi depPi := by
        intro h
        apply hBCDE
        exact congrArg Subtype.val h

      have hADpi' :
          HilbertLinePerpendicularPlaneAt
            Geo ad pi Dsigma.1 :=
        hilbertLinePerpendicularPlaneAt_of_two_plane_lines_parallel_wyler
          (Geo := Geo)
          (pi := pi)
          (m := bcpi)
          (n := depPi)
          (l := ad)
          (O := Dpi)
          hBCDEpi
          hPerpADBC
          hPerpADDE

      exact hADpi hADpi'

    --------------------------------------------------------------------
    -- Euclid I.31 in PlaneGeo(pi):
    -- through F draw GH parallel to BC.
    --------------------------------------------------------------------

    let Fpi : PlanePoint Geo pi :=
      ⟨Ftau.1, hFpi⟩

    have hFnotBCPlane :
        Not ((PlaneGeo Geo pi).OnLine Fpi bcpi) := by
      exact hFnotBC

    have hBCF :
        Not
          (PrimCollinear
            (PlaneGeo Geo pi)
            Bpi Cpi Fpi) :=
      hilbert_not_collinear_of_off_line
        (PlaneGeo Geo pi)
        Bpi Cpi Fpi
        bcpi
        (by
          intro h
          apply hBC
          exact congrArg Subtype.val h)
        hBbc
        hCbc
        hFnotBCPlane

    rcases
        euclid_proposition_31
          (Geo := PlaneGeo Geo pi)
          Bpi Cpi Fpi
          (by
            intro h
            apply hBC
            exact congrArg Subtype.val h)
          hBCF
      with
      ⟨Gpi, hFG, hParallelPlane⟩

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := PlaneGeo Geo pi)
          Fpi Gpi hFG
      with
      ⟨ghpi, hFgh, hGgh⟩

    have hDisjointPlane :
        HilbertLinesDisjoint
          (PlaneGeo Geo pi)
          bcpi ghpi := by

      rintro ⟨Ppi, hPbc, hPgh⟩

      have hPBC :
          Ppi ∈
            (PlaneGeo Geo pi).PointLine Bpi Cpi :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Bpi Cpi Ppi
          bcpi
          hParallelPlane.1
          hBbc hCbc).mpr
          hPbc

      have hPFG :
          Ppi ∈
            (PlaneGeo Geo pi).PointLine Fpi Gpi :=
        (hilbert_mem_pointLine_iff_onLine
          (PlaneGeo Geo pi)
          Fpi Gpi Ppi
          ghpi
          hParallelPlane.2.1
          hFgh hGgh).mpr
          hPgh

      exact
        Set.disjoint_left.mp
          hParallelPlane.2.2
          hPBC
          hPFG

    have hDisjointAmbient :
        HilbertLinesDisjoint Geo bc ghpi.1 :=
      (planeGeo_linesDisjoint_iff_ambient
        (Geo := Geo)
        pi bcpi ghpi).mp
        hDisjointPlane

    have hSpaceParallel :
        HilbertSpaceLinesParallel Geo bc ghpi.1 :=
      ⟨pi,
       hbcpi,
       ghpi.2,
       hDisjointAmbient⟩

    --------------------------------------------------------------------
    -- XI.4 in tau:
    -- bc is perpendicular to both ad and de at D.
    --------------------------------------------------------------------

    let adtau : PlaneLine Geo tau :=
      ⟨ad, hadtau⟩

    let depTau : PlaneLine Geo tau :=
      ⟨depi.1, hdetau⟩

    let Dtau' : PlanePoint Geo tau :=
      ⟨Dsigma.1, hdetau Dsigma.1 hDde⟩

    have hADDEtau : Ne adtau depTau := by
      intro h
      apply hADDE
      exact congrArg Subtype.val h

    have hBCtau :
        HilbertLinePerpendicularPlaneAt
          Geo bc tau Dsigma.1 :=
      hilbertLinePerpendicularPlaneAt_of_two_plane_lines_parallel_wyler
        (Geo := Geo)
        (pi := tau)
        (m := adtau)
        (n := depTau)
        (l := bc)
        (O := Dtau')
        hADDEtau
        hPerpBCAD
        hPerpBCDE

    --------------------------------------------------------------------
    -- XI.8 transfers perpendicularity to the parallel line gh.
    --------------------------------------------------------------------

    rcases
        euclid_proposition_11_8_wyler
          (Geo := Geo)
          bc ghpi.1
          tau
          Dsigma.1
          hSpaceParallel
          hBCtau
      with
      ⟨K, hGHtauK⟩

    --------------------------------------------------------------------
    -- Normalize the XI.8 foot K to the already constructed point F.
    --------------------------------------------------------------------

    have hKInc :=
      hGHtauK.incidence

    have hKgh :
        H.OnLine K ghpi.1 :=
      hKInc.1

    have hKtau :
        S.OnPlane K tau :=
      hKInc.2

    have hKF : K = Ftau.1 := by
      by_contra hKFne

      have hghtau :
          HilbertLineInPlane Geo ghpi.1 tau :=
        HilbertSpaceIncidence.line_in_plane
          (Geo := Geo)
          K Ftau.1 hKFne
          ghpi.1 hKgh hFgh
          tau hKtau Ftau.2

      have hSelfPerp :
          HilbertLinesPerpendicularAt
            Geo ghpi.1 ghpi.1 K :=
        HilbertLinePerpendicularPlaneAt.perpendicular_to_line
          (Geo := Geo)
          hGHtauK
          hghtau
          hKgh

      have hSelfNe :
          Ne ghpi.1 ghpi.1 :=
        hilbert_linesPerpendicularAt_ne
          (Geo := Geo)
          ghpi.1 ghpi.1 K
          hSelfPerp

      exact hSelfNe rfl

    subst K

    have hGHtauF :
        HilbertLinePerpendicularPlaneAt
          Geo ghpi.1 tau Ftau.1 :=
      hGHtauK

    --------------------------------------------------------------------
    -- XI.Def.3 gives gh perpendicular af, hence af perpendicular gh.
    --------------------------------------------------------------------

    have hPerpGHAF :
        HilbertLinesPerpendicularAt
          Geo ghpi.1 af Ftau.1 :=
      HilbertLinePerpendicularPlaneAt.perpendicular_to_line
        (Geo := Geo)
        hGHtauF
        haftau
        hFaf

    have hPerpAFGH :
        HilbertLinesPerpendicularAt
          Geo af ghpi.1 Ftau.1 :=
      hilbertLinesPerpendicularAt_symm_wyler
        (Geo := Geo)
        ghpi.1 af Ftau.1
        hPerpGHAF

    have hPerpAFDE :
        HilbertLinesPerpendicularAt
          Geo af depi.1 Ftau.1 :=
      hilbertLinesPerpendicularAt_symm_wyler
        (Geo := Geo)
        depi.1 af Ftau.1
        hPerpDEAF

    --------------------------------------------------------------------
    -- de and gh are distinct lines of pi.
    --------------------------------------------------------------------

    have hDEGH :
        Ne depi.1 ghpi.1 := by
      intro hEq

      have hDgh :
          H.OnLine Dsigma.1 ghpi.1 := by
        rw [← hEq]
        exact hDde

      exact
        hDisjointAmbient
          ⟨Dsigma.1, hDbc, hDgh⟩

    let depPiFinal : PlaneLine Geo pi :=
      ⟨depi.1, depi.2⟩

    let ghpFinal : PlaneLine Geo pi :=
      ⟨ghpi.1, ghpi.2⟩

    have hDEGHpi :
        Ne depPiFinal ghpFinal := by
      intro h
      apply hDEGH
      exact congrArg Subtype.val h

    --------------------------------------------------------------------
    -- Final XI.4 in pi.
    --------------------------------------------------------------------

    have hAFpi :
        HilbertLinePerpendicularPlaneAt
          Geo af pi Ftau.1 :=
      hilbertLinePerpendicularPlaneAt_of_two_plane_lines_parallel_wyler
        (Geo := Geo)
        (pi := pi)
        (m := depPiFinal)
        (n := ghpFinal)
        (l := af)
        (O := Fpi)
        hDEGHpi
        hPerpAFDE
        hPerpAFGH

    exact
      ⟨af, Ftau.1, hAaf, hAFpi⟩

end Geometry

import CGJteamLab.Hilbert3DInterface
import CGJteamLab.Proposition11_4
import CGJteamLab.Proposition11_5
import CGJteamLab.Proposition11_6

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.8, first hidden incidence step.

If `l` and `m` are parallel spatial lines and `l` is perpendicular to
`pi` at `B`, then the second parallel line `m` meets `pi`.

This formalizes Euclid's unproved opening construction
"let the parallel lines meet the plane at B, D".

The proof is the first direct use of spatial Hilbert Group IV.
-/
theorem hilbert_XI8_parallel_meets_perpendicular_plane
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
      (hilbert_linePerpendicularPlaneAt_not_in_plane
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
      (hilbert_linePerpendicularPlaneAt_not_in_plane
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
theorem hilbert_XI8_auxiliary_line_perpendicular_to_parallel
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
      hilbert_XI8_parallel_meets_perpendicular_plane
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
      hilbert_XI6_second_SSS_right_angle
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
    hilbert_linePerpendicularPlaneAt_not_in_plane
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
    euclid_proposition_11_4
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
theorem hilbert_XI8_coplanar_perpendiculars_to_same_line_disjoint
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
    hilbert_XI6_space_right_angles_congruent_in_plane
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
theorem hilbert_XI8_parallel_line_perpendicular_to_given_BD
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
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      d pp.1 D
      hPerpAmbientDP

  ----------------------------------------------------------------------
  -- I.27: p and l are disjoint.
  ----------------------------------------------------------------------

  have hlpDisjoint :
      HilbertLinesDisjoint Geo l pp.1 :=
    hilbert_XI8_coplanar_perpendiculars_to_same_line_disjoint
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

  ----------------------------------------------------------------------
  -- Use the XI.8 metric configuration with one fixed D,d,e.
  ----------------------------------------------------------------------

  rcases
      hilbert_XI8_auxiliary_line_perpendicular_to_parallel
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
    hilbert_XI8_parallel_line_perpendicular_to_given_BD
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
    hilbert_space_linesPerpendicularAt_symm
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
    euclid_proposition_11_4
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

end Geometry

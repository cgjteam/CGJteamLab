import CGJteamLab.Hilbert3DPlanePerpendicular
import CGJteamLab.Proposition11_6
import CGJteamLab.Proposition11_13
import CGJteamLab.Proposition11_15

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Euclid XI.19 -- direct Hilbert 3D route

If two planes which cut one another are both perpendicular to a third
plane, then their common section is perpendicular to the third plane.

This is the direct Hilbert 3D reconstruction.  It does not use any
Wyler XI.19 theorem.

The proof has two layers.

Layer 1: show that the two traces

    r = rho cap pi,
    s = sigma cap pi

meet.  Otherwise r || s.  At points R on r and Q on s, XI.Def.4 gives
normals g subset rho and h subset sigma to pi.  XI.6 gives g || h.
Then XI.15 makes rho || sigma, contradicting their common point K.

Layer 2: at the triple point D, XI.Def.4 gives one normal to pi inside
rho and one inside sigma.  XI.13 identifies them.  Since rho and sigma
have an exact common section t through D, line uniqueness identifies
that common normal with t.

The only Euclidean/global step is Layer 1 through XI.15.
-/

/--
Inside a fixed ambient plane rho, erect at D a line perpendicular to a
given line s through D.
-/
theorem hilbert_XI19_perpendicular_line_through_point_in_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho : S.Plane)
    (s : Geo.Line)
    (D : Geo.Point)
    (hsrho : HilbertLineInPlane Geo s rho)
    (hDs : H.OnLine D s) :
    exists g : Geo.Line,
      HilbertLineInPlane Geo g rho /\
      HilbertLinesPerpendicularAt Geo g s D := by

  have hDrho : S.OnPlane D rho :=
    hsrho D hDs

  rcases
      hilbert_other_point_on_line
        (Geo := Geo) s D with
    ⟨A, hAD, hAs⟩

  have hArho : S.OnPlane A rho :=
    hsrho A hAs

  let sp : PlaneLine Geo rho :=
    ⟨s, hsrho⟩

  let Dp : PlanePoint Geo rho :=
    ⟨D, hDrho⟩

  let Ap : PlanePoint Geo rho :=
    ⟨A, hArho⟩

  have hADp : Ne Ap Dp := by
    intro hEq
    apply hAD
    exact congrArg Subtype.val hEq

  rcases
      HilbertOrder.between_extension
        (Geo := PlaneGeo Geo rho)
        Ap Dp hADp with
    ⟨Bp, hADB⟩

  rcases
      hilbert_right_angle_exists_nondegenerate
        (PlaneGeo Geo rho)
        Ap Dp Bp hADB with
    ⟨Yp, hNonADY, hRightADY⟩

  have hDYp : Ne Dp Yp := by
    intro hEq
    subst Yp
    apply hNonADY
    exact
      ⟨sp,
       hAs,
       hDs,
       hDs⟩

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo rho)
        Dp Yp hDYp with
    ⟨gp, hDg, hYg⟩

  have hPerpSGPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo rho)
        sp gp Dp := by
    exact
      ⟨hDs,
       hDg,
       Ap, Yp,
       hADp,
       hDYp.symm,
       hAs,
       hYg,
       hNonADY,
       hRightADY⟩

  have hPerpSG :
      HilbertLinesPerpendicularAt Geo s gp.1 D := by
    apply
      (planeGeo_linesPerpendicularAt_iff_ambient
        (Geo := Geo)
        rho sp gp Dp).mp
    exact hPerpSGPlane

  have hPerpGS :
      HilbertLinesPerpendicularAt Geo gp.1 s D :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      s gp.1 D
      hPerpSG

  exact
    ⟨gp.1,
     gp.2,
     hPerpGS⟩


/--
XI.Def.4 as a normal-extraction rule.

At every point D of the common section s, a plane rho perpendicular to pi
along s contains a line through D perpendicular to pi.
-/
theorem hilbert_XI19_planesPerpendicularAlong_normal_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho pi : S.Plane)
    (s : Geo.Line)
    (D : Geo.Point)
    (hPerp :
      HilbertSpacePlanesPerpendicularAlong
        Geo rho pi s)
    (hDs : H.OnLine D s) :
    exists g : Geo.Line,
      HilbertLineInPlane Geo g rho /\
      HilbertLinePerpendicularPlaneAt Geo g pi D := by

  have hsrho :
      HilbertLineInPlane Geo s rho :=
    hilbertSpacePlanesPerpendicularAlong_section_in_left
      (Geo := Geo)
      hPerp

  rcases
      hilbert_XI19_perpendicular_line_through_point_in_plane
        (Geo := Geo)
        rho s D
        hsrho hDs with
    ⟨g, hgrho, hPerpGS⟩

  have hGperpPi :
      HilbertLinePerpendicularPlaneAt Geo g pi D :=
    hilbertSpacePlanesPerpendicularAlong_line_perpendicular_plane
      (Geo := Geo)
      hPerp
      hgrho
      hPerpGS

  exact
    ⟨g,
     hgrho,
     hGperpPi⟩


/--
Neutral common-point core of XI.19.

If rho and sigma are distinct, meet at D, D also lies in pi, and both
planes are perpendicular to pi, then their exact common section is
perpendicular to pi at D.
-/
theorem euclid_proposition_11_19_common_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho sigma pi : S.Plane)
    (D : Geo.Point)
    (hRhoSigma : Ne rho sigma)
    (hDrho : S.OnPlane D rho)
    (hDsigma : S.OnPlane D sigma)
    (hDpi : S.OnPlane D pi)
    (hRhoPerp :
      HilbertSpacePlanesPerpendicular Geo rho pi)
    (hSigmaPerp :
      HilbertSpacePlanesPerpendicular Geo sigma pi) :
    exists t : Geo.Line,
      H.OnLine D t /\
      HilbertLineInPlane Geo t rho /\
      HilbertLineInPlane Geo t sigma /\
      (forall X : Geo.Point,
        (S.OnPlane X rho /\ S.OnPlane X sigma) <->
          H.OnLine X t) /\
      HilbertLinePerpendicularPlaneAt Geo t pi D := by

  rcases
      hilbertSpacePlanesPerpendicular_exists_section
        (Geo := Geo)
        hRhoPerp with
    ⟨r, hRhoAlong⟩

  rcases
      hilbertSpacePlanesPerpendicular_exists_section
        (Geo := Geo)
        hSigmaPerp with
    ⟨s, hSigmaAlong⟩

  have hDr : H.OnLine D r :=
    (hilbertSpacePlanesPerpendicularAlong_section_exact
      (Geo := Geo)
      hRhoAlong
      D).mp
      ⟨hDrho, hDpi⟩

  have hDs : H.OnLine D s :=
    (hilbertSpacePlanesPerpendicularAlong_section_exact
      (Geo := Geo)
      hSigmaAlong
      D).mp
      ⟨hDsigma, hDpi⟩

  rcases
      hilbert_XI19_planesPerpendicularAlong_normal_exists
        (Geo := Geo)
        rho pi r D
        hRhoAlong hDr with
    ⟨g, hgrho, hGperpPi⟩

  rcases
      hilbert_XI19_planesPerpendicularAlong_normal_exists
        (Geo := Geo)
        sigma pi s D
        hSigmaAlong hDs with
    ⟨h, hhsigma, hHperpPi⟩

  have hgh : g = h :=
    euclid_proposition_11_13
      (Geo := Geo)
      pi g h D
      hGperpPi
      hHperpPi

  have hgsigma :
      HilbertLineInPlane Geo g sigma := by
    rw [hgh]
    exact hhsigma

  rcases
      hilbert_plane_intersection_line
        (Geo := Geo)
        rho sigma hRhoSigma
        D hDrho hDsigma with
    ⟨t, hDt, htrho, htsigma, hMeet⟩

  have hDg : H.OnLine D g :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hGperpPi).1

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        g D with
    ⟨P, hPD, hPg⟩

  have hPrho : S.OnPlane P rho :=
    hgrho P hPg

  have hPsigma : S.OnPlane P sigma :=
    hgsigma P hPg

  have hPt : H.OnLine P t :=
    (hMeet P).mp
      ⟨hPrho, hPsigma⟩

  have hDP : Ne D P :=
    hPD.symm

  have hgt : g = t :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      D P hDP
      g t
      hDg hPg
      hDt hPt

  have hTperpPi :
      HilbertLinePerpendicularPlaneAt Geo t pi D := by
    rw [← hgt]
    exact hGperpPi

  exact
    ⟨t,
     hDt,
     htrho,
     htsigma,
     hMeet,
     hTperpPi⟩


/--
Euclid XI.19, direct Hilbert 3D reconstruction.

rho and sigma are distinct planes with a common point K.  If both are
perpendicular to pi, their exact common section is perpendicular to pi.
-/
theorem euclid_proposition_11_19
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (rho sigma pi : S.Plane)
    (K : Geo.Point)
    (hRhoSigma : Ne rho sigma)
    (hKrho : S.OnPlane K rho)
    (hKsigma : S.OnPlane K sigma)
    (hRhoPerp :
      HilbertSpacePlanesPerpendicular Geo rho pi)
    (hSigmaPerp :
      HilbertSpacePlanesPerpendicular Geo sigma pi) :
    exists D : Geo.Point,
    exists t : Geo.Line,
      S.OnPlane D pi /\
      H.OnLine D t /\
      HilbertLineInPlane Geo t rho /\
      HilbertLineInPlane Geo t sigma /\
      (forall X : Geo.Point,
        (S.OnPlane X rho /\ S.OnPlane X sigma) <->
          H.OnLine X t) /\
      HilbertLinePerpendicularPlaneAt Geo t pi D := by

  rcases
      hilbertSpacePlanesPerpendicular_exists_section
        (Geo := Geo)
        hRhoPerp with
    ⟨r, hRhoAlong⟩

  rcases
      hilbertSpacePlanesPerpendicular_exists_section
        (Geo := Geo)
        hSigmaPerp with
    ⟨s, hSigmaAlong⟩

  have hrrho :
      HilbertLineInPlane Geo r rho :=
    hilbertSpacePlanesPerpendicularAlong_section_in_left
      (Geo := Geo)
      hRhoAlong

  have hrpi :
      HilbertLineInPlane Geo r pi :=
    hilbertSpacePlanesPerpendicularAlong_section_in_right
      (Geo := Geo)
      hRhoAlong

  have hssigma :
      HilbertLineInPlane Geo s sigma :=
    hilbertSpacePlanesPerpendicularAlong_section_in_left
      (Geo := Geo)
      hSigmaAlong

  have hspi :
      HilbertLineInPlane Geo s pi :=
    hilbertSpacePlanesPerpendicularAlong_section_in_right
      (Geo := Geo)
      hSigmaAlong

  have hRSMeet :
      HilbertLinesMeet Geo r s := by

    by_contra hNoMeet

    have hRSDisjoint :
        HilbertLinesDisjoint Geo r s := by
      rintro ⟨X, hXr, hXs⟩
      exact hNoMeet
        ⟨X, hXr, hXs⟩

    have hParallelRS :
        HilbertSpaceLinesParallel Geo r s :=
      ⟨pi,
       hrpi,
       hspi,
       hRSDisjoint⟩

    rcases
        HilbertSpaceIncidence.two_points_on_each_line
          (Geo := Geo) r with
      ⟨R, R', hRR', hRr, _hR'r⟩

    rcases
        HilbertSpaceIncidence.two_points_on_each_line
          (Geo := Geo) s with
      ⟨Q, Q', hQQ', hQs, _hQ's⟩

    have hRrho : S.OnPlane R rho :=
      hrrho R hRr

    have hRpi : S.OnPlane R pi :=
      hrpi R hRr

    have hQsigma : S.OnPlane Q sigma :=
      hssigma Q hQs

    have hQpi : S.OnPlane Q pi :=
      hspi Q hQs

    have hRQ : Ne R Q := by
      intro hRQ
      subst Q
      exact
        hRSDisjoint
          ⟨R, hRr, hQs⟩

    rcases
        hilbert_XI19_planesPerpendicularAlong_normal_exists
          (Geo := Geo)
          rho pi r R
          hRhoAlong hRr with
      ⟨g, hgrho, hGperpPi⟩

    rcases
        hilbert_XI19_planesPerpendicularAlong_normal_exists
          (Geo := Geo)
          sigma pi s Q
          hSigmaAlong hQs with
      ⟨h, hhsigma, hHperpPi⟩

    have hRg : H.OnLine R g :=
      (HilbertLinePerpendicularPlaneAt.incidence
        (Geo := Geo)
        hGperpPi).1

    have hQh : H.OnLine Q h :=
      (HilbertLinePerpendicularPlaneAt.incidence
        (Geo := Geo)
        hHperpPi).1

    have hParallelGH :
        HilbertSpaceLinesParallel Geo g h :=
      euclid_proposition_11_6
        (Geo := Geo)
        pi g h R Q
        hRQ
        hGperpPi
        hHperpPi

    have hGperpR :
        HilbertLinesPerpendicularAt Geo g r R :=
      HilbertLinePerpendicularPlaneAt.perpendicular_to_line
        (Geo := Geo)
        hGperpPi
        hrpi
        hRr

    have hHperpS :
        HilbertLinesPerpendicularAt Geo h s Q :=
      HilbertLinePerpendicularPlaneAt.perpendicular_to_line
        (Geo := Geo)
        hHperpPi
        hspi
        hQs

    have hgr : Ne g r :=
      hilbert_linesPerpendicularAt_ne
        (Geo := Geo)
        g r R hGperpR

    have hrs : Ne r g :=
      hgr.symm

    have hhs : Ne h s :=
      hilbert_linesPerpendicularAt_ne
        (Geo := Geo)
        h s Q hHperpS

    have hsh : Ne s h :=
      hhs.symm

    let rp : PlaneLine Geo rho :=
      ⟨r, hrrho⟩

    let gp : PlaneLine Geo rho :=
      ⟨g, hgrho⟩

    let sp : PlaneLine Geo sigma :=
      ⟨s, hssigma⟩

    let hp : PlaneLine Geo sigma :=
      ⟨h, hhsigma⟩

    let Rp : PlanePoint Geo rho :=
      ⟨R, hRrho⟩

    have hrpgp : Ne rp gp := by
      intro hEq
      apply hrs
      exact congrArg Subtype.val hEq

    have hNoCommonPlane :
        Not (exists omega : S.Plane,
          HilbertLineInPlane Geo r omega /\
          HilbertLineInPlane Geo g omega /\
          HilbertLineInPlane Geo s omega /\
          HilbertLineInPlane Geo h omega) := by

      rintro ⟨omega,
        hromega,
        hgomega,
        hsomega,
        hhomega⟩

      rcases
          hilbert_plane_through_two_intersecting_lines
            (Geo := Geo)
            r g hrs
            R hRr hRg with
        ⟨tauR, hrtauR, hgtauR, hUniqueR⟩

      have hRhoTauR : rho = tauR :=
        hUniqueR rho hrrho hgrho

      have hOmegaTauR : omega = tauR :=
        hUniqueR omega hromega hgomega

      have hRhoOmega : rho = omega :=
        hRhoTauR.trans hOmegaTauR.symm

      rcases
          hilbert_plane_through_two_intersecting_lines
            (Geo := Geo)
            s h hsh
            Q hQs hQh with
        ⟨tauS, hstauS, hhtauS, hUniqueS⟩

      have hSigmaTauS : sigma = tauS :=
        hUniqueS sigma hssigma hhsigma

      have hOmegaTauS : omega = tauS :=
        hUniqueS omega hsomega hhomega

      have hSigmaOmega : sigma = omega :=
        hSigmaTauS.trans hOmegaTauS.symm

      exact
        hRhoSigma
          (hRhoOmega.trans hSigmaOmega.symm)

    have hRhoSigmaParallel :
        HilbertSpacePlanesParallel Geo rho sigma :=
      euclid_proposition_11_15
        (Geo := Geo)
        rho sigma
        rp gp
        sp hp
        Rp
        hRr
        hRg
        hrpgp
        hParallelRS
        hParallelGH
        hNoCommonPlane

    exact
      hRhoSigmaParallel
        ⟨K, hKrho, hKsigma⟩

  rcases hRSMeet with
    ⟨D, hDr, hDs⟩

  have hDrho : S.OnPlane D rho :=
    hrrho D hDr

  have hDsigma : S.OnPlane D sigma :=
    hssigma D hDs

  have hDpi : S.OnPlane D pi :=
    hrpi D hDr

  rcases
      euclid_proposition_11_19_common_point
        (Geo := Geo)
        rho sigma pi D
        hRhoSigma
        hDrho
        hDsigma
        hDpi
        hRhoPerp
        hSigmaPerp with
    ⟨t,
     hDt,
     htrho,
     htsigma,
     hMeet,
     hTperpPi⟩

  exact
    ⟨D,
     t,
     hDpi,
     hDt,
     htrho,
     htsigma,
     hMeet,
     hTperpPi⟩

end Geometry

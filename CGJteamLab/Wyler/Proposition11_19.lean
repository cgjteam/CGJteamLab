import CGJteamLab.Wyler.Proposition11_19_common_point_wyler
import CGJteamLab.Wyler.Proposition11_6
import CGJteamLab.Wyler.Proposition11_15

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Euclid XI.19 in Wyler form

If two planes which cut one another are both perpendicular to a third
plane, then their common section is perpendicular to the third plane.

After the Wyler refactor the proof separates into two layers.

## Layer 1: incidence/existence of the triple point

Let

  r = rho cap pi,
  s = sigma cap pi.

Assume r and s do not meet.

Because both lie in pi, they are spatially parallel.

At arbitrary points R on r and S on s, XI.Def.4 supplies normals

  g subset rho,    g perp pi at R,
  h subset sigma,  h perp pi at S.

Since R != S, XI.6 gives g || h.

Thus rho contains the intersecting pair r,g while sigma contains the
intersecting pair s,h, with

  r || s,
  g || h.

Euclid XI.15 then gives rho || sigma, contradicting the hypothesis that
rho and sigma cut one another.

Hence r and s meet at some D.  Therefore

  D in rho cap sigma cap pi.

## Layer 2: neutral XI.19 core

The previously proved theorem
`euclid_proposition_11_19_common_point_wyler`
uses XI.Def.4 and XI.13 to identify the common section rho cap sigma
with the unique normal to pi at D.

The Euclidean assumption occurs only in Layer 1 through XI.15.
-/

/--
Euclid XI.19, production Wyler form.

`rho` and `sigma` are distinct planes with a common point `K`, so they
cut one another.  If both are perpendicular to `pi`, their exact common
section is perpendicular to `pi`.

The result returns the section line and its perpendicular foot.
-/
theorem euclid_proposition_11_19_wyler
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

  ----------------------------------------------------------------------
  -- Recover the exact sections
  --
  --   r = rho cap pi,
  --   s = sigma cap pi.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- Main incidence claim: r and s meet.
  ----------------------------------------------------------------------

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

    --------------------------------------------------------------------
    -- Choose R on r and S on s.
    --------------------------------------------------------------------

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

    --------------------------------------------------------------------
    -- XI.Def.4 supplies one normal to pi in each perpendicular plane.
    --------------------------------------------------------------------

    rcases
        hilbertSpacePlanesPerpendicularAlong_normal_exists_wyler
          (Geo := Geo)
          rho pi r R
          hRhoAlong hRr with
      ⟨g, hgrho, hGperpPi⟩

    rcases
        hilbertSpacePlanesPerpendicularAlong_normal_exists_wyler
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

    --------------------------------------------------------------------
    -- XI.6: the two distinct-foot normals to pi are parallel.
    --------------------------------------------------------------------

    have hParallelGH :
        HilbertSpaceLinesParallel Geo g h :=
      euclid_proposition_11_6
        (Geo := Geo)
        pi g h R Q
        hRQ
        hGperpPi
        hHperpPi

    --------------------------------------------------------------------
    -- r and g are distinct intersecting lines in rho.
    -- s and h are distinct intersecting lines in sigma.
    --------------------------------------------------------------------

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

    --------------------------------------------------------------------
    -- The four lines r,g,s,h cannot all lie in one plane.
    --
    -- Otherwise r,g determine both rho and that plane, while s,h
    -- determine both sigma and that same plane. Hence rho = sigma.
    --------------------------------------------------------------------

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

    --------------------------------------------------------------------
    -- XI.15: the two carrier planes would be parallel.
    --------------------------------------------------------------------

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

    --------------------------------------------------------------------
    -- But rho and sigma have the common point K.
    --------------------------------------------------------------------

    exact
      hRhoSigmaParallel
        ⟨K, hKrho, hKsigma⟩

  ----------------------------------------------------------------------
  -- Therefore the two traces meet at D.
  ----------------------------------------------------------------------

  rcases hRSMeet with
    ⟨D, hDr, hDs⟩

  have hDrho : S.OnPlane D rho :=
    hrrho D hDr

  have hDsigma : S.OnPlane D sigma :=
    hssigma D hDs

  have hDpi : S.OnPlane D pi :=
    hrpi D hDr

  ----------------------------------------------------------------------
  -- Apply the neutral common-point core.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_11_19_common_point_wyler
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

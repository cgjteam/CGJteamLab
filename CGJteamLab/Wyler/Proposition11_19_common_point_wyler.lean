import CGJteamLab.Wyler.HilbertWylerPlaneNormal
import CGJteamLab.Wyler.Proposition11_13

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Euclid XI.19: common-point core in Wyler form

This module isolates the metric-incidence core of Euclid XI.19.

Classical statement:

  if two intersecting planes are perpendicular to a third plane,
  then their intersection is perpendicular to that third plane.

The classical diagram chooses a point D which belongs simultaneously to
the two given planes and to the reference plane.  Here that incidence is
made explicit.

Once D is available, the proof is neutral:

1. XI.Def.4 in rho produces a line g in rho perpendicular to pi at D;
2. XI.Def.4 in sigma produces a line h in sigma perpendicular to pi at D;
3. XI.13 gives g = h;
4. the common normal therefore lies in rho and sigma;
5. the exact meet rho cap sigma is a line t through D;
6. line uniqueness identifies the common normal with t.

No `HilbertSpaceEuclidean` assumption is used.
-/

/--
Euclid XI.19, common-point core.

Assume `rho` and `sigma` are distinct planes meeting at a point `D`,
and both are perpendicular to `pi`.  If `D` also lies in `pi`, then the
exact section line `t = rho cap sigma` is perpendicular to `pi` at `D`.

The theorem returns the section line together with its full incidence
certificate.
-/
theorem euclid_proposition_11_19_common_point_wyler
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

  ----------------------------------------------------------------------
  -- Recover the two XI.Def.4 section certificates with pi.
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

  ----------------------------------------------------------------------
  -- Since D lies in rho and pi, it lies on their exact section r.
  -- Likewise D lies on s = sigma cap pi.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- XI.Def.4: erect within each perpendicular plane a normal to pi
  -- at the common point D.
  ----------------------------------------------------------------------

  rcases
      hilbertSpacePlanesPerpendicularAlong_normal_exists_wyler
        (Geo := Geo)
        rho pi r D
        hRhoAlong hDr with
    ⟨g, hgrho, hGperpPi⟩

  rcases
      hilbertSpacePlanesPerpendicularAlong_normal_exists_wyler
        (Geo := Geo)
        sigma pi s D
        hSigmaAlong hDs with
    ⟨h, hhsigma, hHperpPi⟩

  ----------------------------------------------------------------------
  -- XI.13: the normal to pi at D is unique.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- XI.3 / Wyler meet: rho and sigma have an exact section t through D.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_intersection_line
        (Geo := Geo)
        rho sigma hRhoSigma
        D hDrho hDsigma with
    ⟨t, hDt, htrho, htsigma, hMeet⟩

  ----------------------------------------------------------------------
  -- The common normal g lies in both rho and sigma, hence every point
  -- of g lies on the exact meet line t.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- g and t contain the two distinct points D,P, so they are equal.
  ----------------------------------------------------------------------

  have hgt : g = t :=
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      D P hDP
      g t
      hDg hPg
      hDt hPt

  ----------------------------------------------------------------------
  -- Transport the normality certificate from g to the meet line t.
  ----------------------------------------------------------------------

  have hTperpPi :
      HilbertLinePerpendicularPlaneAt Geo t pi D := by
    rw [<- hgt]
    exact hGperpPi

  exact
    ⟨t,
     hDt,
     htrho,
     htsigma,
     hMeet,
     hTperpPi⟩

end Geometry

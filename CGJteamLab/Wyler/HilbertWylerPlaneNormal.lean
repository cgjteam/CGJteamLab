import CGJteamLab.Wyler.HilbertWylerPlanePerpendicular

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Normal extraction from a perpendicular-plane certificate

This is a lower helper for Euclid XI.19.

If `s` is a line contained in an ambient plane `rho` and `D` lies on
`s`, then one can erect inside `rho` a line through `D` perpendicular
to `s`.

Combined with Euclid XI.Def.4, represented by
`HilbertSpacePlanesPerpendicularAlong`, this says:

  if rho is perpendicular to pi along s,
  then at every point D of s there is a line in rho
  perpendicular to pi at D.

This is exactly the construction of DE and DF used in Euclid XI.19.
-/

/--
Inside a fixed ambient plane `rho`, erect at `D` a line perpendicular
to a given line `s` through `D`.

The construction is carried out entirely in `PlaneGeo Geo rho`.
-/
theorem hilbert_perpendicular_line_through_point_in_plane_wyler
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

  ----------------------------------------------------------------------
  -- Choose A != D on s.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- Extend A-D inside PlaneGeo(rho), obtaining A-D-B.
  ----------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        (Geo := PlaneGeo Geo rho)
        Ap Dp hADp with
    ⟨Bp, hADB⟩

  ----------------------------------------------------------------------
  -- Erect a nondegenerate right angle A-D-Y.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- Let g = DY in PlaneGeo(rho).
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo rho)
        Dp Yp hDYp with
    ⟨gp, hDg, hYg⟩

  ----------------------------------------------------------------------
  -- First package s perpendicular g at D in the induced plane.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- Transport to the ambient geometry and reverse the order.
  ----------------------------------------------------------------------

  have hPerpSG :
      HilbertLinesPerpendicularAt Geo s gp.1 D := by
    apply
      (planeGeo_linesPerpendicularAt_iff_ambient
        (Geo := Geo)
        rho sp gp Dp).mp
    exact hPerpSGPlane

  have hPerpGS :
      HilbertLinesPerpendicularAt Geo gp.1 s D :=
    hilbertLinesPerpendicularAt_symm_wyler
      (Geo := Geo)
      s gp.1 D
      hPerpSG

  exact
    ⟨gp.1,
     gp.2,
     hPerpGS⟩


/--
XI.Def.4 as a normal-extraction rule.

At every point `D` of the common section `s`, a plane `rho`
perpendicular to `pi` along `s` contains a line through `D`
perpendicular to `pi`.
-/
theorem hilbertSpacePlanesPerpendicularAlong_normal_exists_wyler
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
      hilbert_perpendicular_line_through_point_in_plane_wyler
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

end Geometry

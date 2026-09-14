import CGJteamLab.Hilbert3DPlanePerpendicular
import CGJteamLab.Proposition11_12

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Euclid XI.18 -- direct Hilbert 3D route

If a straight line is perpendicular to a plane, then every plane through
that straight line is perpendicular to the given plane.

This file is the direct Hilbert 3D reconstruction.  It does not import the
Wyler Book XI route.

The conclusion uses the common Hilbert 3D rendering of Euclid XI.Def.4:

    HilbertSpacePlanesPerpendicular Geo rho pi.

Architecture:

1. the normal foot O belongs to both rho and pi;
2. rho and pi are distinct;
3. their exact common section s is obtained from spatial incidence;
4. l is perpendicular to s because l is perpendicular to pi;
5. every line g in rho perpendicular to s is either l itself or parallel
   to l;
6. in the parallel case XI.8 transports perpendicularity from l to g;
7. uniqueness of the perpendicular foot identifies the XI.8 foot with the
   given point on s.

Thus the proof is synthetic and genuinely Hilbertian.  No Wyler module is
used.
-/

/--
Same-foot case needed in XI.18.

Inside one ambient plane, two lines perpendicular to the same line at the
same point coincide.
-/
theorem hilbert_XI18_coplanar_perpendiculars_same_foot_equal
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho : S.Plane)
    (s l g : Geo.Line)
    (O : Geo.Point)
    (hsrho : HilbertLineInPlane Geo s rho)
    (hlrho : HilbertLineInPlane Geo l rho)
    (hgrho : HilbertLineInPlane Geo g rho)
    (hPerpL :
      HilbertLinesPerpendicularAt Geo l s O)
    (hPerpG :
      HilbertLinesPerpendicularAt Geo g s O) :
    l = g := by

  have hOl : H.OnLine O l :=
    hPerpL.1

  have hOs : H.OnLine O s :=
    hPerpL.2.1

  have hOg : H.OnLine O g :=
    hPerpG.1

  have hOrho : S.OnPlane O rho :=
    hsrho O hOs

  rcases
      hilbert_other_point_on_line
        (Geo := Geo) s O with
    ⟨T, hTO, hTs⟩

  rcases
      hilbert_other_point_on_line
        (Geo := Geo) l O with
    ⟨L, hLO, hLl⟩

  rcases
      hilbert_other_point_on_line
        (Geo := Geo) g O with
    ⟨G, hGO, hGg⟩

  have hTrho : S.OnPlane T rho :=
    hsrho T hTs

  have hLrho : S.OnPlane L rho :=
    hlrho L hLl

  have hGrho : S.OnPlane G rho :=
    hgrho G hGg

  let sp : PlaneLine Geo rho :=
    ⟨s, hsrho⟩

  let lp : PlaneLine Geo rho :=
    ⟨l, hlrho⟩

  let gp : PlaneLine Geo rho :=
    ⟨g, hgrho⟩

  let Op : PlanePoint Geo rho :=
    ⟨O, hOrho⟩

  let Tp : PlanePoint Geo rho :=
    ⟨T, hTrho⟩

  let Lp : PlanePoint Geo rho :=
    ⟨L, hLrho⟩

  let Gp : PlanePoint Geo rho :=
    ⟨G, hGrho⟩

  have hTOp : Ne Tp Op := by
    intro h
    apply hTO
    exact congrArg Subtype.val h

  have hLOp : Ne Lp Op := by
    intro h
    apply hLO
    exact congrArg Subtype.val h

  have hGOp : Ne Gp Op := by
    intro h
    apply hGO
    exact congrArg Subtype.val h

  have hPerpSL :
      HilbertLinesPerpendicularAt Geo s l O :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      l s O hPerpL

  have hPerpSG :
      HilbertLinesPerpendicularAt Geo s g O :=
    hilbert_space_linesPerpendicularAt_symm
      (Geo := Geo)
      g s O hPerpG

  have hPerpSLPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo rho) sp lp Op := by
    apply
      (planeGeo_linesPerpendicularAt_iff_ambient
        (Geo := Geo)
        rho sp lp Op).mpr
    simpa [sp, lp, Op] using hPerpSL

  have hPerpSGPlane :
      HilbertLinesPerpendicularAt
        (PlaneGeo Geo rho) sp gp Op := by
    apply
      (planeGeo_linesPerpendicularAt_iff_ambient
        (Geo := Geo)
        rho sp gp Op).mpr
    simpa [sp, gp, Op] using hPerpSG

  have hsplp : Ne sp lp :=
    hilbert_linesPerpendicularAt_ne
      (PlaneGeo Geo rho)
      sp lp Op
      hPerpSLPlane

  have hspgp : Ne sp gp :=
    hilbert_linesPerpendicularAt_ne
      (PlaneGeo Geo rho)
      sp gp Op
      hPerpSGPlane

  have hTOL :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo rho)
      sp lp
      Op Tp Lp
      hsplp
      hPerpSLPlane
      hTOp
      hLOp
      hTs
      hLl

  have hTOG :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo rho)
      sp gp
      Op Tp Gp
      hspgp
      hPerpSGPlane
      hTOp
      hGOp
      hTs
      hGg

  have hLOG :
      PrimCollinear
        (PlaneGeo Geo rho)
        Lp Op Gp :=
    hilbert_XI4_two_right_angles_same_first_arm_collinear
      (PlaneGeo Geo rho)
      Tp Op Lp Gp
      sp
      hTOp
      hTs
      hOs
      hTOL.1
      hTOG.1
      hTOL.2
      hTOG.2

  have hLOGAmbient :
      PrimCollinear Geo L O G :=
    planeGeo_primCollinear_to_ambient
      (Geo := Geo)
      rho
      Lp Op Gp
      hLOG

  have hOGLAmbient :
      PrimCollinear Geo O G L :=
    PrimCollinearCycle
      Geo
      L O G
      hLOGAmbient

  have hOL : Ne O L :=
    hLO.symm

  have hOG : Ne O G :=
    hGO.symm

  have hLg : H.OnLine L g :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hOG
      hOg
      hGg
      hOGLAmbient

  exact
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      O L hOL
      l g
      hOl hLl
      hOg hLg


/--
Inside one ambient plane, two lines perpendicular to the same line are
either equal or parallel.

The distinct-foot branch is the neutral coplanar theorem already proved in
the direct Hilbert proof of XI.8.  No spatial Euclidean axiom is needed here.
-/
theorem hilbert_XI18_coplanar_perpendiculars_eq_or_parallel
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (rho : S.Plane)
    (s l g : Geo.Line)
    (O F : Geo.Point)
    (hsrho : HilbertLineInPlane Geo s rho)
    (hlrho : HilbertLineInPlane Geo l rho)
    (hgrho : HilbertLineInPlane Geo g rho)
    (hPerpL :
      HilbertLinesPerpendicularAt Geo l s O)
    (hPerpG :
      HilbertLinesPerpendicularAt Geo g s F) :
    l = g \/ HilbertSpaceLinesParallel Geo l g := by

  by_cases hOF : O = F
  case pos =>
    subst F
    left
    exact
      hilbert_XI18_coplanar_perpendiculars_same_foot_equal
        (Geo := Geo)
        rho
        s l g
        O
        hsrho
        hlrho
        hgrho
        hPerpL
        hPerpG

  case neg =>
    right

    have hDisjoint :
        HilbertLinesDisjoint Geo l g :=
      hilbert_XI8_coplanar_perpendiculars_to_same_line_disjoint
        (Geo := Geo)
        rho
        l g s
        O F
        hOF
        hlrho
        hgrho
        hsrho
        hPerpL
        hPerpG

    exact
      ⟨rho,
       hlrho,
       hgrho,
       hDisjoint⟩


/--
Euclid XI.18, direct Hilbert 3D reconstruction.

If `l` is perpendicular to `pi` at `O` and the plane `rho` contains `l`,
then `rho` is perpendicular to `pi` in the sense of Euclid XI.Def.4.
-/
theorem euclid_proposition_11_18
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (O : Geo.Point)
    (hPerp :
      HilbertLinePerpendicularPlaneAt Geo l pi O)
    (hlrho :
      HilbertLineInPlane Geo l rho) :
    HilbertSpacePlanesPerpendicular Geo rho pi := by

  have hInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hOl : H.OnLine O l :=
    hInc.1

  have hOpi : S.OnPlane O pi :=
    hInc.2

  have hOrho : S.OnPlane O rho :=
    hlrho O hOl

  have hRhoPi : Ne rho pi := by
    intro hEq

    have hlpi : HilbertLineInPlane Geo l pi := by
      intro X hXl

      have hXrho : S.OnPlane X rho :=
        hlrho X hXl

      rw [hEq] at hXrho
      exact hXrho

    exact
      (hilbert_linePerpendicularPlaneAt_not_in_plane
        (Geo := Geo)
        l pi O hPerp)
        hlpi

  rcases
      hilbert_plane_intersection_line
        (Geo := Geo)
        rho pi hRhoPi
        O hOrho hOpi
    with
    ⟨s, hOs, hsrho, hspi, hSection⟩

  refine
    ⟨hRhoPi,
     s,
     ?_⟩

  refine
    ⟨hsrho,
     hspi,
     hSection,
     ?_⟩

  have hPerpLS :
      HilbertLinesPerpendicularAt Geo l s O :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerp
      hspi
      hOs

  intro g F hgrho hPerpGS

  have hEqOrParallel :
      l = g \/
      HilbertSpaceLinesParallel Geo l g :=
    hilbert_XI18_coplanar_perpendiculars_eq_or_parallel
      (Geo := Geo)
      rho
      s l g
      O F
      hsrho
      hlrho
      hgrho
      hPerpLS
      hPerpGS

  cases hEqOrParallel with
  | inl hlg =>
      subst g

      have hFl : H.OnLine F l :=
        hPerpGS.1

      have hFs : H.OnLine F s :=
        hPerpGS.2.1

      have hFpi : S.OnPlane F pi :=
        hspi F hFs

      have hFO : F = O :=
        hilbert_XI12_perpendicular_foot_unique
          (Geo := Geo)
          pi l O F
          hPerp
          hFl
          hFpi

      subst F
      exact hPerp

  | inr hParallel =>
      rcases
          euclid_proposition_11_8
            (Geo := Geo)
            l g pi O
            hParallel
            hPerp
        with
        ⟨D, hPerpG⟩

      have hFg : H.OnLine F g :=
        hPerpGS.1

      have hFs : H.OnLine F s :=
        hPerpGS.2.1

      have hFpi : S.OnPlane F pi :=
        hspi F hFs

      have hFD : F = D :=
        hilbert_XI12_perpendicular_foot_unique
          (Geo := Geo)
          pi g D F
          hPerpG
          hFg
          hFpi

      simpa [hFD] using hPerpG

end Geometry

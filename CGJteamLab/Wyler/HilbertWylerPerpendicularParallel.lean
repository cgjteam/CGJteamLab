import CGJteamLab.Wyler.HilbertWylerMetric
import CGJteamLab.Wyler.HilbertWylerPlanes
import CGJteamLab.Wyler.HilbertWylerPlanePerpendicular

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Coplanar perpendiculars to the same line

Neutral helper layer for the Wyler proof of Euclid XI.18.

The goal of this file is deliberately small:

  if two lines contained in one ambient plane are perpendicular to the
  same line contained in that plane, then they are equal or parallel.

No Euclidean parallel axiom is used.  The two geometric branches are:

* same foot: uniqueness of the perpendicular direction;
* distinct feet: a hypothetical intersection would create a
  nondegenerate triangle with two right angles, contradicting I.17.

This is the exact bridge needed before applying the already developed
XI.8 transport theorem in Proposition XI.18.
-/

/--
Two coplanar lines perpendicular to the same line at the same foot are
equal.

The proof is carried out inside `PlaneGeo rho`.  We choose one nonvertex
point on each of the three carriers.  The two right angles with common
first arm are transported to those points, and the neutral uniqueness
lemma from the XI.4 metric core makes the two second arms collinear.
Line uniqueness then identifies the two perpendicular carriers.
-/
theorem hilbert_coplanar_perpendiculars_same_foot_equal_wyler
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

  ----------------------------------------------------------------------
  -- Choose one nonvertex point on each carrier.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- Normalize both perpendicularities so that s is the first carrier.
  ----------------------------------------------------------------------

  have hPerpSL :
      HilbertLinesPerpendicularAt Geo s l O :=
    hilbertLinesPerpendicularAt_symm_wyler
      (Geo := Geo)
      l s O hPerpL

  have hPerpSG :
      HilbertLinesPerpendicularAt Geo s g O :=
    hilbertLinesPerpendicularAt_symm_wyler
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

  ----------------------------------------------------------------------
  -- Realize the two perpendicularities as right angles T-O-L, T-O-G.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- L lies on g; hence l and g share the distinct points O,L.
  ----------------------------------------------------------------------

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
Distinct-foot case.

Let `l` and `g` lie in `rho`, and let both be perpendicular to `s`,
at distinct feet `O` and `F`.  Then `l` and `g` are disjoint.

If they met at `K`, the triangle `O F K` in `PlaneGeo rho` would have
right angles at both `O` and `F`.  Euclid I.17, through the neutral
XI.14 helper, rules this out.
-/
theorem hilbert_coplanar_perpendiculars_distinct_feet_disjoint_wyler
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
    (O F : Geo.Point)
    (hsrho : HilbertLineInPlane Geo s rho)
    (hlrho : HilbertLineInPlane Geo l rho)
    (hgrho : HilbertLineInPlane Geo g rho)
    (hOF : Ne O F)
    (hPerpL :
      HilbertLinesPerpendicularAt Geo l s O)
    (hPerpG :
      HilbertLinesPerpendicularAt Geo g s F) :
    HilbertLinesDisjoint Geo l g := by

  intro hMeet

  rcases hMeet with
    ⟨K, hKl, hKg⟩

  have hOl : H.OnLine O l :=
    hPerpL.1

  have hOs : H.OnLine O s :=
    hPerpL.2.1

  have hFg : H.OnLine F g :=
    hPerpG.1

  have hFs : H.OnLine F s :=
    hPerpG.2.1

  have hOrho : S.OnPlane O rho :=
    hsrho O hOs

  have hFrho : S.OnPlane F rho :=
    hsrho F hFs

  have hKrho : S.OnPlane K rho :=
    hlrho K hKl

  ----------------------------------------------------------------------
  -- The hypothetical meeting point is different from both feet.
  ----------------------------------------------------------------------

  have hKO : Ne K O := by
    intro hEq
    subst K

    have hgs : g = s :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        O F hOF
        g s
        hKg hFg
        hOs hFs

    have hgsNe : Ne g s :=
      hilbert_linesPerpendicularAt_ne
        Geo g s F hPerpG

    exact hgsNe hgs

  have hKF : Ne K F := by
    intro hEq
    subst K

    have hls : l = s :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        O F hOF
        l s
        hOl hKl
        hOs hFs

    have hlsNe : Ne l s :=
      hilbert_linesPerpendicularAt_ne
        Geo l s O hPerpL

    exact hlsNe hls

  ----------------------------------------------------------------------
  -- Move the whole configuration into PlaneGeo rho.
  ----------------------------------------------------------------------

  let sp : PlaneLine Geo rho :=
    ⟨s, hsrho⟩

  let lp : PlaneLine Geo rho :=
    ⟨l, hlrho⟩

  let gp : PlaneLine Geo rho :=
    ⟨g, hgrho⟩

  let Op : PlanePoint Geo rho :=
    ⟨O, hOrho⟩

  let Fp : PlanePoint Geo rho :=
    ⟨F, hFrho⟩

  let Kp : PlanePoint Geo rho :=
    ⟨K, hKrho⟩

  have hOFp : Ne Op Fp := by
    intro h
    apply hOF
    exact congrArg Subtype.val h

  have hKOp : Ne Kp Op := by
    intro h
    apply hKO
    exact congrArg Subtype.val h

  have hKFp : Ne Kp Fp := by
    intro h
    apply hKF
    exact congrArg Subtype.val h

  have hOKp : Ne Op Kp :=
    hKOp.symm

  have hFKp : Ne Fp Kp :=
    hKFp.symm

  ----------------------------------------------------------------------
  -- Triangle O-F-K is nondegenerate.
  ----------------------------------------------------------------------

  have hNon :
      Not
        (PrimCollinear
          (PlaneGeo Geo rho)
          Op Fp Kp) := by
    intro hCol

    have hColAmbient :
        PrimCollinear Geo O F K :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        rho
        Op Fp Kp
        hCol

    have hKs : H.OnLine K s :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hOF
        hOs
        hFs
        hColAmbient

    have hOK : Ne O K :=
      hKO.symm

    have hls : l = s :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        O K hOK
        l s
        hOl hKl
        hOs hKs

    have hlsNe : Ne l s :=
      hilbert_linesPerpendicularAt_ne
        Geo l s O hPerpL

    exact hlsNe hls

  ----------------------------------------------------------------------
  -- Both right angles are written with the common section s first:
  --
  --   F-O-K is right,
  --   O-F-K is right.
  ----------------------------------------------------------------------

  have hPerpSL :
      HilbertLinesPerpendicularAt Geo s l O :=
    hilbertLinesPerpendicularAt_symm_wyler
      (Geo := Geo)
      l s O hPerpL

  have hPerpSG :
      HilbertLinesPerpendicularAt Geo s g F :=
    hilbertLinesPerpendicularAt_symm_wyler
      (Geo := Geo)
      g s F hPerpG

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
        (PlaneGeo Geo rho) sp gp Fp := by
    apply
      (planeGeo_linesPerpendicularAt_iff_ambient
        (Geo := Geo)
        rho sp gp Fp).mpr
    simpa [sp, gp, Fp] using hPerpSG

  have hsplp : Ne sp lp :=
    hilbert_linesPerpendicularAt_ne
      (PlaneGeo Geo rho)
      sp lp Op
      hPerpSLPlane

  have hspgp : Ne sp gp :=
    hilbert_linesPerpendicularAt_ne
      (PlaneGeo Geo rho)
      sp gp Fp
      hPerpSGPlane

  have hFOK :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo rho)
      sp lp
      Op Fp Kp
      hsplp
      hPerpSLPlane
      hOFp.symm
      hKOp
      hFs
      hKl

  have hOFK :=
    hilbert_XI4_linesPerpendicularAt_right_angle_of_points
      (PlaneGeo Geo rho)
      sp gp
      Fp Op Kp
      hspgp
      hPerpSGPlane
      hOFp
      hKFp
      hOs
      hKg

  exact
    hilbert_XI14_two_right_angles_impossible_wyler
      (PlaneGeo Geo rho)
      Op Fp Kp
      hNon
      hFOK.2
      hOFK.2


/--
Main neutral bridge.

Inside one ambient plane, two lines perpendicular to the same line are
either the same line or parallel in the spatial sense.

No `HilbertSpaceEuclidean` assumption occurs here.
-/
theorem hilbert_coplanar_perpendiculars_to_same_line_eq_or_parallel_wyler
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
    (O F : Geo.Point)
    (hsrho : HilbertLineInPlane Geo s rho)
    (hlrho : HilbertLineInPlane Geo l rho)
    (hgrho : HilbertLineInPlane Geo g rho)
    (hPerpL :
      HilbertLinesPerpendicularAt Geo l s O)
    (hPerpG :
      HilbertLinesPerpendicularAt Geo g s F) :
    l = g \/
    HilbertSpaceLinesParallel Geo l g := by

  by_cases hOF : O = F

  · left
    subst F
    exact
      hilbert_coplanar_perpendiculars_same_foot_equal_wyler
        (Geo := Geo)
        rho s l g O
        hsrho hlrho hgrho
        hPerpL hPerpG

  · by_cases hlg : l = g

    · exact Or.inl hlg

    · right

      have hDisjoint :
          HilbertLinesDisjoint Geo l g :=
        hilbert_coplanar_perpendiculars_distinct_feet_disjoint_wyler
          (Geo := Geo)
          rho s l g O F
          hsrho hlrho hgrho
          hOF
          hPerpL hPerpG

      exact
        ⟨rho,
         hlrho,
         hgrho,
         hDisjoint⟩

end Geometry

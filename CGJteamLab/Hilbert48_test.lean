import CGJteamLab.HilbertBookZero
import CGJteamLab.HilbertScissors
import CGJteamLab.Proposition07

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Equal altitude over a given base line
------------------------------------------------------------------------



def HilbertEqualAltitudeToLine
    [HilbertIncidence Geo]
    (A D : Geo.Point)
    (base : Geo.Line) : Prop :=
  ∃ F G X Y : Geo.Point,
    HilbertIncidence.OnLine F base ∧
    HilbertIncidence.OnLine X base ∧
    F ≠ X ∧
    HilbertIncidence.OnLine G base ∧
    HilbertIncidence.OnLine Y base ∧
    G ≠ Y ∧
    HilbertRightAngle Geo X F A ∧
    HilbertRightAngle Geo Y G D ∧
    Geo.Congruent A F D G


/--
Area-theoretic core of Hilbert Theorem 48.

Equicomplementable triangles on the same base have equal altitudes.
-/
axiom hilbert48_test_equal_altitude
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hBC : B ≠ C)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hEqual :
      HilbertScissorsEquicomplementable
        Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo D B C)) :
    HilbertEqualAltitudeToLine Geo A D base

/-
Two perpendiculars to the same line at distinct feet are parallel.

This is the nondegenerate geometric core of the final step of
Hilbert Theorem 48.
-/
/-
axiom hilbert48_test_perpendiculars_parallel_distinct_feet
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D F G X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hGbase : HilbertIncidence.OnLine G base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hGY : G ≠ Y)
    (hFG : F ≠ G)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo Y G D) :
    Geo.Parallel A F D G
-/
/--
Convert point-pair parallelism into explicit carrier lines.

The second carrier is the already fixed line `base`.
-/
theorem hilbert48_test_parallel_to_carriers
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A D F G : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hGbase : HilbertIncidence.OnLine G base)
    (hParallel : Geo.Parallel A D F G) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  rcases
      HilbertPlaneIncidence.line_through
        A D hParallel.1
    with
    ⟨top, hAtop, hDtop⟩

  refine ⟨top, hAtop, hDtop, ?_⟩

  rintro ⟨P, hPtop, hPbase⟩

  have hPAD :
      P ∈ Geo.PointLine A D :=
    (hilbert_mem_pointLine_iff_onLine
      Geo A D P top
      hParallel.1
      hAtop hDtop).mpr hPtop

  have hPFG :
      P ∈ Geo.PointLine F G :=
    (hilbert_mem_pointLine_iff_onLine
      Geo F G P base
      hParallel.2.1
      hFbase hGbase).mpr hPbase

  exact
    Set.disjoint_left.mp
      hParallel.2.2
      hPAD
      hPFG


/--
I.33 step used in the geometric end of Hilbert Theorem 48.

If AF and DG are equal and parallel, and A,D lie on the same side
of the carrier line FG, then AD is parallel to FG.
-/
theorem hilbert48_test_i33_join_parallel
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D F G : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hGbase : HilbertIncidence.OnLine G base)
    (hSame : HilbertSameSide Geo A D base)
    (hParallel : Geo.Parallel A F D G)
    (hCongruent : Geo.Congruent A F D G) :
    Geo.Parallel A D F G := by

  have hData :
      OnePairParallelCongruent Geo A D G F :=
    {
      parallel := hParallel
      congruent := hCongruent
      oriented := ⟨base, hFbase, hGbase, hSame⟩
    }

  have hParallelogram :
      IsParallelogram Geo A D G F :=
    OnePairParallelCongruentCriterion
      Geo A D G F hData

  have hAD_GF :
      Geo.Parallel A D G F :=
    hParallelogram.1

  exact
    ParallelSwapSecondLine
      Geo A D G F hAD_GF



/--
If A and D are collinear with the common foot F and lie on the
same side of the base line through F, then they lie on the same
ray from F.
-/
theorem hilbert48_test_same_foot_collinear_same_ray
     [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A D F : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hSame : HilbertSameSide Geo A D base)
    (hAFD : Collinear Geo A F D) :
    HilbertSameRay Geo F A D := by

  exact
    sameRay_of_collinear_sameSide
      (Geo := Geo)
      (O := F)
      (B := A)
      (X := D)
      (base := base)
      hFbase
      hSame.1
      hSame.2.1
      hSame
      hAFD

/--
A right angle is unchanged when its base point is replaced by
another point on the same ray from the vertex.
-/
theorem hilbert48_test_right_angle_same_base_ray
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (D F X Y : Geo.Point)
    (hRayXY : HilbertSameRay Geo F X Y)
    (hRight : HilbertRightAngle Geo Y F D) :
    HilbertRightAngle Geo X F D := by

  rcases hRight with
    ⟨E, hYFE, hAngle⟩

  have hFE : F ≠ E :=
    (HilbertOrder.between_incidence
      Y F E hYFE).2.1

  have hRayYX :
      HilbertSameRay Geo F Y X :=
    hilbert_sameRay_symm
      Geo F X Y hRayXY

  have hRayEE :
      HilbertSameRay Geo F E E :=
    hilbert_sameRay_refl
      Geo F E hFE.symm

  have hXFE :
      Geo.Between X F E :=
    hilbert_between_transport_sameRays
      Geo
      Y F E
      X E
      hYFE
      hRayYX
      hRayEE

  have hLeft :
      Geo.Angle Y F D =
        Geo.Angle X F D :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      F Y X D
      hRayYX

  refine ⟨E, hXFE, ?_⟩

  unfold Geometry.Geo.AngleCongruent at hAngle ⊢
  rw [← hLeft]
  exact hAngle

/--
Two nonzero rays from F along the same line are either the same ray
or their representatives lie on opposite sides of F.
-/
theorem hilbert48_test_base_ray_cases
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (F X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hFX : F ≠ X)
    (hFY : F ≠ Y) :
    HilbertSameRay Geo F X Y ∨
    Geo.Between X F Y := by

  by_cases hXY : X = Y

  · subst Y
    left
    exact
      hilbert_sameRay_refl
        Geo F X hFX.symm

  · have hXFYcol :
        Collinear Geo X F Y :=
      ⟨base, hXbase, hFbase, hYbase⟩

    rcases
        hilbert_between_trichotomy
          Geo
          X F Y
          hFX.symm
          hFY
          hXY
          hXFYcol with
      hXFY | hFXY | hXYF

    · exact Or.inr hXFY

    · exact
        Or.inl
          (hilbert_sameRay_of_between
            Geo F X Y hFXY)

    · have hFY_X :
          Geo.Between F Y X :=
        (HilbertOrder.between_incidence
          X Y F hXYF).2.2.2.2

      have hRayYX :
          HilbertSameRay Geo F Y X :=
        hilbert_sameRay_of_between
          Geo F Y X hFY_X

      exact
        Or.inl
          (hilbert_sameRay_symm
            Geo F Y X hRayYX)

/--
If X-F-Y and YFD is a right angle, then XFD is also a right angle.

This is the local supplementary-angle consequence of Hilbert Theorem 14.
-/
theorem hilbert48_test_right_angle_opposite_base
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (D F X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hDoff : ¬ HilbertIncidence.OnLine D base)
    (hXFY : Geo.Between X F Y)
    (hRight : HilbertRightAngle Geo Y F D) :
    HilbertRightAngle Geo X F D := by

  rcases hRight with
    ⟨E, hYFE, hAngle⟩

  have hYFEData :=
    HilbertOrder.between_incidence
      Y F E hYFE

  have hYF : Y ≠ F :=
    hYFEData.1

  have hFE : F ≠ E :=
    hYFEData.2.1

  have hYFEcol :
      Collinear Geo Y F E :=
    hYFEData.2.2.2.1

  have hEbase :
      HilbertIncidence.OnLine E base :=
    hilbert_collinear_on_line
      Geo
      Y F E
      base
      hYF
      hYbase
      hFbase
      hYFEcol

  have hYFX :
      Geo.Between Y F X :=
    (HilbertOrder.between_incidence
      X F Y hXFY).2.2.2.2

  have hEFY :
      Geo.Between E F Y :=
    hYFEData.2.2.2.2

  have hYFD :
      ¬ Collinear Geo Y F D :=
    hilbert_not_collinear_of_off_line
      Geo
      Y F D
      base
      hYF
      hYbase
      hFbase
      hDoff

  have hEFD :
      ¬ Collinear Geo E F D :=
    hilbert_not_collinear_of_off_line
      Geo
      E F D
      base
      hFE.symm
      hEbase
      hFbase
      hDoff

  have hStart :
      Geo.AngleCongruent Y F D E F D :=
    (Geo.angle_congruent_reverse_second
      Y F D D F E).mp hAngle

  have hSupp :
      Geo.AngleCongruent D F X D F Y :=
    hilbert_adjacent_angles_congruent
      Geo
      Y F D X
      E F D Y
      hYFX
      hEFY
      hYFD
      hEFD
      hStart

  have hTarget :
      Geo.AngleCongruent X F D D F Y :=
    (Geo.angle_congruent_reverse_first
      D F X D F Y).mp hSupp

  exact
    ⟨Y, hXFY, hTarget⟩

theorem hilbert48_test_right_angle_base_normalize
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (D F X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hFX : F ≠ X)
    (hFY : F ≠ Y)
    (hDoff : ¬ HilbertIncidence.OnLine D base)
    (hRight : HilbertRightAngle Geo Y F D) :
    HilbertRightAngle Geo X F D := by

  rcases
      hilbert48_test_base_ray_cases
        Geo F X Y base
        hFbase hXbase hYbase
        hFX hFY with
    hRay | hBetween

  · exact
      hilbert48_test_right_angle_same_base_ray
        Geo D F X Y
        hRay hRight

  · exact
      hilbert48_test_right_angle_opposite_base
        Geo D F X Y base
        hFbase hYbase hDoff
        hBetween hRight

/--
If the two normalized angles at the common foot are congruent,
then their perpendicular rays coincide on the prescribed side.
-/
theorem hilbert48_test_same_foot_same_ray_of_angle_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hAngle :
      Geo.AngleCongruent X F A X F D) :
    HilbertSameRay Geo F A D := by

  rcases
      hilbert_angle_unique_common_ray
        Geo
        X F A D
        base
        hFX.symm
        hXbase
        hFbase
        hSame.1
        hSame
        hAngle with
    ⟨Z, hZA, hZD⟩

  exact
    hilbert_sameRay_of_common
      Geo
      F Z A D
      hZA
      hZD

/--
For two rays from the same foot into the same half-plane,
their angles with the fixed base ray satisfy angle trichotomy.
-/
theorem hilbert48_test_same_foot_angle_cases
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base) :
    Geo.AngleCongruent X F A X F D ∨
    HilbertAngleLess Geo X F A X F D ∨
    HilbertAngleLess Geo X F D X F A := by

  have hXFA :
      ¬ PrimCollinear Geo X F A :=
    hilbert_not_collinear_of_off_line
      Geo
      X F A
      base
      hFX.symm
      hXbase
      hFbase
      hSame.1

  have hXFD :
      ¬ PrimCollinear Geo X F D :=
    hilbert_not_collinear_of_off_line
      Geo
      X F D
      base
      hFX.symm
      hXbase
      hFbase
      hSame.2.1

  exact
    angle_trichotomy
      Geo
      X F A
      X F D
      hXFA
      hXFD

/--
If angle XFA is strictly smaller than angle XFD, with A and D
on the same side of the base XF, then ray FA meets the open
segment XD.
-/
theorem hilbert48_test_angle_less_ray_inside
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hLess :
      HilbertAngleLess Geo X F A X F D) :
    HilbertRayMeetsSegment Geo F A X D := by

  rcases hLess with
    ⟨hXFA, hXFD, J, hInsideJ, hAngle⟩

  rcases hInsideJ with
    ⟨H, hXHD, hRayFJH⟩

  have hDHX :
      Geo.Between D H X :=
    (HilbertOrder.between_incidence
      X H D hXHD).2.2.2.2

  have hDXF :
      ¬ PrimCollinear Geo D X F := by
    intro h
    exact hXFD
      (PrimCollinearCycle Geo D X F h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        D H F X
        hDHX
        hDXF with
    ⟨lineFX, hFlineFX, hXlineFX, hDHSame_lineFX⟩

  have hLineEq :
      lineFX = base :=
    HilbertPlaneIncidence.line_unique
      F X hFX
      lineFX base
      hFlineFX hXlineFX
      hFbase hXbase

  have hDHSame :
      HilbertSameSide Geo D H base := by
    rw [← hLineEq]
    exact hDHSame_lineFX

  have hAHSame :
      HilbertSameSide Geo A H base :=
    hilbert_sameSide_trans
      Geo
      A D H
      base
      hSame
      hDHSame

  have hXFJ :
      ¬ PrimCollinear Geo X F J :=
    (hilbert_interior_angle_less
      Geo
      F J X D
      hXFD
      ⟨H, hXHD, hRayFJH⟩).1

  have hFJ :
    F ≠ J :=
  hRayFJH.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        F J hFJ with
    ⟨lineFJ, hFlineFJ, hJlineFJ⟩

  have hXoffFJ :
      ¬ HilbertIncidence.OnLine X lineFJ := by
    intro hXline
    exact hXFJ
      ⟨lineFJ, hXline, hFlineFJ, hJlineFJ⟩

  have hRayFJJ :
      HilbertSameRay Geo F J J :=
    hilbert_sameRay_refl
      Geo F J hFJ.symm

  have hJHSame :
      HilbertSameSide Geo J H base :=
    hilbert_sameRay_points_sameSide
      Geo
      F J
      J H
      X
      lineFJ base
      hFlineFJ
      hJlineFJ
      hFbase
      hXbase
      hXoffFJ
      hRayFJJ
      hRayFJH

  have hHJSame :
      HilbertSameSide Geo H J base :=
    hilbert_sameSide_symm
      Geo J H base hJHSame

  have hAJSame :
      HilbertSameSide Geo A J base :=
    hilbert_sameSide_trans
      Geo
      A H J
      base
      hAHSame
      hHJSame

  rcases
      hilbert_angle_unique_common_ray
        Geo
        X F A J
        base
        hFX.symm
        hXbase
        hFbase
        hAJSame.1
        hAJSame
        hAngle with
    ⟨Z, hRayZA, hRayZJ⟩

  have hRayAJ :
      HilbertSameRay Geo F A J :=
    hilbert_sameRay_of_common
      Geo F Z A J
      hRayZA hRayZJ

  have hRayJA :
      HilbertSameRay Geo F J A :=
    hilbert_sameRay_symm
      Geo F A J hRayAJ

  have hRayFAH :
      HilbertSameRay Geo F A H :=
    hilbert_sameRay_of_common
      Geo
      F J A H
      hRayJA
      hRayFJH

  exact
    ⟨H, hXHD, hRayFAH⟩


/--
A right angle may be expressed using any chosen point on the
opposite base ray.
-/
theorem hilbert48_test_right_angle_chosen_supplement
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (D F X Y : Geo.Point)
    (hXFY : Geo.Between X F Y)
    (hXFD : ¬ PrimCollinear Geo X F D)
    (hRight : HilbertRightAngle Geo X F D) :
    Geo.AngleCongruent X F D D F Y := by

  rcases hRight with
    ⟨E, hXFE, hRightE⟩

  have hRefl :
      Geo.AngleCongruent X F D X F D :=
    Geo.angle_congruent_reflexive
      X F D

  have hSupp :
      Geo.AngleCongruent D F E D F Y :=
    hilbert_adjacent_angles_congruent
      Geo
      X F D E
      X F D Y
      hXFE
      hXFY
      hXFD
      hXFD
      hRefl

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X F D
      D F E
      D F Y
      hRightE
      hSupp

/--
If ray FA meets the open segment XD and X-F-Y, then ray FD
meets the open segment AY, provided A and D lie on the same
side of the base XY.
-/
theorem hilbert48_test_inside_flip
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A D F X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hSame : HilbertSameSide Geo A D base)
    (hXFY : Geo.Between X F Y)
    (hInside :
      HilbertRayMeetsSegment Geo F A X D) :
    HilbertRayMeetsSegment Geo F D A Y := by

  rcases hInside with
    ⟨H, hXHD, hRayFAH⟩

  have hFA : F ≠ A := by
    intro h
    subst A
    exact hSame.1 hFbase

  have hXFYData :=
    HilbertOrder.between_incidence
      X F Y hXFY

  have hFY : F ≠ Y :=
    hXFYData.2.1

  have hXY : X ≠ Y :=
    hXFYData.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        F A hFA with
    ⟨lineFA, hFlineFA, hAlineFA⟩

  have hHlineFA :
      HilbertIncidence.OnLine H lineFA :=
    hilbert_collinear_on_line
      Geo
      F A H
      lineFA
      hFA
      hFlineFA
      hAlineFA
      hRayFAH.2.2.1

  have hXYD :
      ¬ Collinear Geo X Y D :=
    hilbert_not_collinear_of_off_line
      Geo
      X Y D
      base
      hXY
      hXbase
      hYbase
      hSame.2.1

  have hYDsame :
      HilbertSameSide Geo Y D lineFA :=
    hilbert_third_side_endpoints_sameSide
      Geo
      X Y D
      F H
      lineFA
      hXYD
      hXFY
      hXHD
      hFlineFA
      hHlineFA

  have hDYsame :
      HilbertSameSide Geo D Y lineFA :=
    hilbert_sameSide_symm
      Geo Y D lineFA hYDsame

  have hFYD :
      ¬ Collinear Geo F Y D :=
    hilbert_not_collinear_of_off_line
      Geo
      F Y D
      base
      hFY
      hFbase
      hYbase
      hSame.2.1

  have hDFY :
      ¬ Collinear Geo D F Y := by
    intro h
    exact hFYD
      (PrimCollinearCycle Geo D F Y h)

  rcases
      hilbert_sameSide_rays_order
        Geo
        F D A Y
        lineFA
        hFA
        hFlineFA
        hAlineFA
        hDYsame.1
        hDYsame.2.1
        hDYsame
        hDFY with
    hFD | hFYmeet

  · rcases hFD with
      ⟨K, hYKA, hRayFDK⟩

    have hAKY :
        Geo.Between A K Y :=
      (HilbertOrder.between_incidence
        Y K A hYKA).2.2.2.2

    exact
      ⟨K, hAKY, hRayFDK⟩

  · rcases hFYmeet with
      ⟨K, hDKA, hRayFYK⟩

    have hKbase :
        HilbertIncidence.OnLine K base :=
      hilbert_collinear_on_line
        Geo
        F Y K
        base
        hFY
        hFbase
        hYbase
        hRayFYK.2.2.1

    have hOppDA :
        HilbertOppositeSide Geo D A base :=
      ⟨hSame.2.1,
       hSame.1,
       ⟨K, hDKA, hKbase⟩⟩

    have hSameDA :
        HilbertSameSide Geo D A base :=
      hilbert_sameSide_symm
        Geo A D base hSame

    exact
      False.elim
        ((hilbert_oppositeSide_not_sameSide
            Geo D A base hOppDA)
          hSameDA)

/--
A strict inequality between two right angles with the same first
base ray is impossible when their second rays lie in the same
half-plane.
-/
theorem hilbert48_test_right_angle_less_impossible
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo X F D)
    (hLess :
      HilbertAngleLess Geo X F A X F D) :
    False := by

  have hXFA :
      ¬ PrimCollinear Geo X F A :=
    hLess.1

  have hXFD :
      ¬ PrimCollinear Geo X F D :=
    hLess.2.1

  rcases
      HilbertOrder.between_extension
        X F hFX.symm with
    ⟨Y, hXFY⟩

  have hXFYData :=
    HilbertOrder.between_incidence
      X F Y hXFY

  have hFY : F ≠ Y :=
    hXFYData.2.1

  have hYbase :
    HilbertIncidence.OnLine Y base :=
  hilbert_collinear_on_line
    Geo
    X F Y
    base
    hXFYData.1
    hXbase
    hFbase
    hXFYData.2.2.2.1

  have hInsideA :
      HilbertRayMeetsSegment Geo F A X D :=
    hilbert48_test_angle_less_ray_inside
      Geo
      A D F X
      base
      hFbase
      hXbase
      hFX
      hSame
      hLess

  have hInsideD :
      HilbertRayMeetsSegment Geo F D A Y :=
    hilbert48_test_inside_flip
      Geo
      A D F X Y
      base
      hFbase
      hXbase
      hYbase
      hSame
      hXFY
      hInsideA

  have hAFY :
      ¬ PrimCollinear Geo A F Y := by
    have hFYA :
        ¬ PrimCollinear Geo F Y A :=
      hilbert_not_collinear_of_off_line
        Geo
        F Y A
        base
        hFY
        hFbase
        hYbase
        hSame.1

    intro h
    exact hFYA
      (PrimCollinearCycle Geo A F Y h)

  have hDFY :
      ¬ PrimCollinear Geo D F Y := by
    have hFYD :
        ¬ PrimCollinear Geo F Y D :=
      hilbert_not_collinear_of_off_line
        Geo
        F Y D
        base
        hFY
        hFbase
        hYbase
        hSame.2.1

    intro h
    exact hFYD
      (PrimCollinearCycle Geo D F Y h)

  have hXFA_AFY :
      Geo.AngleCongruent X F A A F Y :=
    hilbert48_test_right_angle_chosen_supplement
      Geo
      A F X Y
      hXFY
      hXFA
      hRightA

  have hXFD_DFY :
      Geo.AngleCongruent X F D D F Y :=
    hilbert48_test_right_angle_chosen_supplement
      Geo
      D F X Y
      hXFY
      hXFD
      hRightD

  have hXFA_DFY :
      HilbertAngleLess Geo X F A D F Y :=
    hilbert_angleLess_transport_right
      Geo
      X F A
      X F D
      D F Y
      hLess
      hDFY
      hXFD_DFY

  have hAFY_XFA :
      Geo.AngleCongruent A F Y X F A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X F A
      A F Y
      hXFA_AFY

  have hAFY_DFY :
      HilbertAngleLess Geo A F Y D F Y :=
    hilbert_angleLess_transport_left
      Geo
      X F A
      A F Y
      D F Y
      hXFA_DFY
      hAFY
      hAFY_XFA

  rcases hInsideD with
    ⟨K, hAKY, hRayFDK⟩

  have hYKA :
      Geo.Between Y K A :=
    (HilbertOrder.between_incidence
      A K Y hAKY).2.2.2.2

  have hInsideDrev :
      HilbertRayMeetsSegment Geo F D Y A :=
    ⟨K, hYKA, hRayFDK⟩

  have hYFA :
      ¬ PrimCollinear Geo Y F A := by
    intro h
    exact hAFY
      (PrimCollinearSymm Geo Y F A h)

  have hYFD_YFA :
      HilbertAngleLess Geo Y F D Y F A :=
    hilbert_interior_angle_less
      Geo
      F D Y A
      hYFA
      hInsideDrev

  have hYFDrefl :
      Geo.AngleCongruent Y F D Y F D :=
    Geo.angle_congruent_reflexive
      Y F D

  have hDFY_YFD :
      Geo.AngleCongruent D F Y Y F D :=
    (Geo.angle_congruent_reverse_first
      Y F D
      Y F D).mp hYFDrefl

  have hDFY_YFA :
      HilbertAngleLess Geo D F Y Y F A :=
    hilbert_angleLess_transport_left
      Geo
      Y F D
      D F Y
      Y F A
      hYFD_YFA
      hDFY
      hDFY_YFD

  have hYFArefl :
      Geo.AngleCongruent Y F A Y F A :=
    Geo.angle_congruent_reflexive
      Y F A

  have hYFA_AFY :
      Geo.AngleCongruent Y F A A F Y :=
    (Geo.angle_congruent_reverse_second
      Y F A
      Y F A).mp hYFArefl

  have hDFY_AFY :
      HilbertAngleLess Geo D F Y A F Y :=
    hilbert_angleLess_transport_right
      Geo
      D F Y
      Y F A
      A F Y
      hDFY_YFA
      hAFY
      hYFA_AFY

  have hCycle :
      HilbertAngleLess Geo A F Y A F Y :=
    hilbert_angleLess_trans
      Geo
      A F Y
      D F Y
      A F Y
      hAFY_DFY
      hDFY_AFY

  exact
    (hilbert_angleLess_irrefl
      Geo A F Y)
      hCycle


/--
Two right angles erected from the same base ray into the same
half-plane are congruent.
-/
theorem hilbert48_test_same_base_right_angles_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo X F D) :
    Geo.AngleCongruent X F A X F D := by

  rcases
      hilbert48_test_same_foot_angle_cases
        Geo
        A D F X
        base
        hFbase
        hXbase
        hFX
        hSame with
    hCong | hLessAD | hLessDA

  · exact hCong

  · exact
      False.elim
        (hilbert48_test_right_angle_less_impossible
          Geo
          A D F X
          base
          hFbase
          hXbase
          hFX
          hSame
          hRightA
          hRightD
          hLessAD)

  · have hSameDA :
        HilbertSameSide Geo D A base :=
      hilbert_sameSide_symm
        Geo A D base hSame

    exact
      False.elim
        (hilbert48_test_right_angle_less_impossible
          Geo
          D A F X
          base
          hFbase
          hXbase
          hFX
          hSameDA
          hRightD
          hRightA
          hLessDA)

/--
Two perpendicular rays erected at the same point of a line,
on the same side of that line, determine the same ray.
-/
theorem hilbert48_test_same_foot_perpendicular_same_ray
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D F X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hFY : F ≠ Y)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo Y F D) :
    HilbertSameRay Geo F A D := by

  have hRightDX :
      HilbertRightAngle Geo X F D :=
    hilbert48_test_right_angle_base_normalize
      Geo
      D F X Y
      base
      hFbase
      hXbase
      hYbase
      hFX
      hFY
      hSame.2.1
      hRightD

  have hAngle :
      Geo.AngleCongruent X F A X F D :=
    hilbert48_test_same_base_right_angles_congruent
      Geo
      A D F X
      base
      hFbase
      hXbase
      hFX
      hSame
      hRightA
      hRightDX

  exact
    hilbert48_test_same_foot_same_ray_of_angle_congruent
      Geo
      A D F X
      base
      hFbase
      hXbase
      hFX
      hSame
      hAngle


/--
All right angles are congruent.

This is Hilbert Theorem 21 in the form needed for the
perpendicular-parallel argument.
-/
theorem hilbert48_test_all_right_angles_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F G X E : Geo.Point)
    (base1 base2 : Geo.Line)
    (hFbase1 : HilbertIncidence.OnLine F base1)
    (hXbase1 : HilbertIncidence.OnLine X base1)
    (hAoff : ¬ HilbertIncidence.OnLine A base1)
    (hGbase2 : HilbertIncidence.OnLine G base2)
    (hEbase2 : HilbertIncidence.OnLine E base2)
    (hDoff : ¬ HilbertIncidence.OnLine D base2)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo E G D) :
    Geo.AngleCongruent X F A E G D := by

  rcases hRightA with
    ⟨Y, hXFY, hRightAeq⟩

  rcases hRightD with
    ⟨T, hEGT, hRightDeq⟩

  have hXF : X ≠ F :=
    (HilbertOrder.between_incidence
      X F Y hXFY).1

  have hEG : E ≠ G :=
    (HilbertOrder.between_incidence
      E G T hEGT).1

  have hGE : G ≠ E :=
    hEG.symm

  have hXFA :
      ¬ PrimCollinear Geo X F A :=
    hilbert_not_collinear_of_off_line
      Geo
      X F A
      base1
      hXF
      hXbase1
      hFbase1
      hAoff

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        X F A
        E G D
        hXFA
        hEG
        base2
        hEbase2
        hGbase2
        hDoff with
    ⟨K, hKDSame, hCopy, _⟩

  have hEGK :
      ¬ PrimCollinear Geo E G K :=
    hilbert_not_collinear_of_off_line
      Geo
      E G K
      base2
      hEG
      hEbase2
      hGbase2
      hKDSame.1

  have hSupp :
      Geo.AngleCongruent A F Y K G T :=
    hilbert_adjacent_angles_congruent
      Geo
      X F A Y
      E G K T
      hXFY
      hEGT
      hXFA
      hEGK
      hCopy

  have hEGK_XFA :
      Geo.AngleCongruent E G K X F A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X F A
      E G K
      hCopy

  have hEGK_AFY :
      Geo.AngleCongruent E G K A F Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E G K
      X F A
      A F Y
      hEGK_XFA
      hRightAeq

  have hEGK_KGT :
      Geo.AngleCongruent E G K K G T :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E G K
      A F Y
      K G T
      hEGK_AFY
      hSupp

  have hRightK :
      HilbertRightAngle Geo E G K :=
    ⟨T, hEGT, hEGK_KGT⟩

  have hRightD' :
      HilbertRightAngle Geo E G D :=
    ⟨T, hEGT, hRightDeq⟩

  have hKGD :
      Geo.AngleCongruent E G K E G D :=
    hilbert48_test_same_base_right_angles_congruent
      Geo
      K D G E
      base2
      hGbase2
      hEbase2
      hGE
      hKDSame
      hRightK
      hRightD'

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X F A
      E G K
      E G D
      hCopy
      hKGD


theorem hilbert48_test_same_foot_equal_perpendiculars_eq
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D F G X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hGbase : HilbertIncidence.OnLine G base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hGY : G ≠ Y)
    (hFG : F = G)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo Y G D)
    (hAlt : Geo.Congruent A F D G) :
    A = D := by

  subst G

  have hFA : F ≠ A := by
    intro hFA
    subst A
    exact hSame.1 hFbase

  have hRayAD :
      HilbertSameRay Geo F A D :=
    hilbert48_test_same_foot_perpendicular_same_ray
      Geo
      A D F X Y
      base
      hFbase
      hXbase
      hFX
      hYbase
      hGY
      hSame
      hRightA
      hRightD

  have hFA_FD :
      Geo.Congruent F A F D :=
    CongruentReverseBoth
      Geo
      A F D F
      hAlt

  have hFD_FA :
      Geo.Congruent F D F A :=
    hilbert_congruent_symmetry
      Geo
      F A F D
      hFA_FD

  have hRayAA :
    HilbertSameRay Geo F A A :=
  hilbert_sameRay_refl
    Geo F A hFA.symm

  exact
    hilbert_segment_construction_unique
      Geo
      F A
      F A
      A D
      hRayAA
      hRayAD
      (hilbert_congruent_reflexive Geo F A)
      hFD_FA


theorem hilbert48_test_equal_perpendiculars_parallel_same_foot
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D F G X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hGbase : HilbertIncidence.OnLine G base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hGY : G ≠ Y)
    (hFG : F = G)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo Y G D)
    (hAlt : Geo.Congruent A F D G) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  have hAD : A = D :=
    hilbert48_test_same_foot_equal_perpendiculars_eq
      Geo
      A D F G X Y
      base
      hFbase
      hXbase
      hFX
      hGbase
      hYbase
      hGY
      hFG
      hSame
      hRightA
      hRightD
      hAlt

  subst D

  have hAoff :
      ¬ HilbertIncidence.OnLine A base :=
    hSame.1

  have hFXA :
      ¬ Collinear Geo F X A :=
    hilbert_not_collinear_of_off_line
      Geo
      F X A
      base
      hFX
      hFbase
      hXbase
      hAoff

  rcases
      hilbert_parallel_through_point_exists
        Geo
        F X A
        hFX
        hFXA
    with
    ⟨Q, hAQ, hFX_AQ⟩

  have hAQ_FX :
      Geo.Parallel A Q F X :=
    ParallelSymmetry
      Geo
      F X A Q
      hFX_AQ

  rcases
      hilbert48_test_parallel_to_carriers
        Geo
        A Q F X
        base
        hFbase
        hXbase
        hAQ_FX
    with
    ⟨top, hAtop, hQtop, hDisjoint⟩

  exact
    ⟨top, hAtop, hAtop, hDisjoint⟩

/-
axiom hilbert48_test_equal_perpendiculars_parallel_same_foot
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D F G X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hGbase : HilbertIncidence.OnLine G base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hGY : G ≠ Y)
    (hFG : F = G)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo Y G D)
    (hAlt : Geo.Congruent A F D G) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base
-/


/--
Reversing the perpendicular ray preserves a right angle.
-/
theorem hilbert48_test_right_angle_opposite_perp
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A A' F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hAoff : ¬ HilbertIncidence.OnLine A base)
    (hAFA' : Geo.Between A F A')
    (hRight : HilbertRightAngle Geo X F A) :
    HilbertRightAngle Geo X F A' := by

  rcases hRight with
    ⟨Y, hXFY, hRightEq⟩

  have hXFYData :=
    HilbertOrder.between_incidence
      X F Y hXFY

  have hFX : F ≠ X :=
    hXFYData.1.symm

  have hFY : F ≠ Y :=
    hXFYData.2.1

  have hYbase :
      HilbertIncidence.OnLine Y base :=
    hilbert_collinear_on_line
      Geo
      X F Y
      base
      hXFYData.1
      hXbase
      hFbase
      hXFYData.2.2.2.1

  have hFXA :
      ¬ PrimCollinear Geo F X A :=
    hilbert_not_collinear_of_off_line
      Geo
      F X A
      base
      hFX
      hFbase
      hXbase
      hAoff

  have hAFX :
      ¬ PrimCollinear Geo A F X := by
    intro h
    exact hFXA
      (PrimCollinearCycle Geo A F X h)

  have hFYA :
      ¬ PrimCollinear Geo F Y A :=
    hilbert_not_collinear_of_off_line
      Geo
      F Y A
      base
      hFY
      hFbase
      hYbase
      hAoff

  have hAFY :
      ¬ PrimCollinear Geo A F Y := by
    intro h
    exact hFYA
      (PrimCollinearCycle Geo A F Y h)

  have hAFX_AFY :
      Geo.AngleCongruent A F X A F Y :=
    (Geo.angle_congruent_reverse_first
      X F A
      A F Y).mp hRightEq

  have hSupp :
      Geo.AngleCongruent X F A' Y F A' :=
    hilbert_adjacent_angles_congruent
      Geo
      A F X A'
      A F Y A'
      hAFA'
      hAFA'
      hAFX
      hAFY
      hAFX_AFY

  have hTarget :
      Geo.AngleCongruent X F A' A' F Y :=
    (Geo.angle_congruent_reverse_second
      X F A'
      Y F A').mp hSupp

  exact
    ⟨Y, hXFY, hTarget⟩

/--
Two perpendiculars erected at distinct points of the same line,
with their endpoints on the same side of that line, are parallel.
-/
theorem hilbert48_test_perpendiculars_parallel_distinct_feet_same_side
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F G X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hGbase : HilbertIncidence.OnLine G base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hGY : G ≠ Y)
    (hFG : F ≠ G)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo Y G D) :
    Geo.Parallel A F D G := by

  have hAoff :
      ¬ HilbertIncidence.OnLine A base :=
    hSame.1

  have hDoff :
      ¬ HilbertIncidence.OnLine D base :=
    hSame.2.1

  have hAF : A ≠ F := by
    intro h
    subst A
    exact hAoff hFbase

  ----------------------------------------------------------------------
  -- Normalize both right angles to the common transversal FG.
  ----------------------------------------------------------------------

  have hRightAFG :
      HilbertRightAngle Geo G F A :=
    hilbert48_test_right_angle_base_normalize
      Geo
      A F G X
      base
      hFbase
      hGbase
      hXbase
      hFG
      hFX
      hAoff
      hRightA

  have hRightDGF :
      HilbertRightAngle Geo F G D :=
    hilbert48_test_right_angle_base_normalize
      Geo
      D G F Y
      base
      hGbase
      hFbase
      hYbase
      hFG.symm
      hGY
      hDoff
      hRightD

  ----------------------------------------------------------------------
  -- Extend AF through F.  The new point A' lies on the opposite
  -- side of the base from A, hence from D.
  ----------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        A F hAF with
    ⟨A', hAFA'⟩

  have hAFA'Data :=
    HilbertOrder.between_incidence
      A F A' hAFA'

  have hFA' : F ≠ A' :=
    hAFA'Data.2.1

  have hAFA'col :
      PrimCollinear Geo A F A' :=
    hAFA'Data.2.2.2.1

  have hA'off :
      ¬ HilbertIncidence.OnLine A' base := by
    intro hA'base

    have hAon :
        HilbertIncidence.OnLine A base :=
      hilbert_collinear_on_line
        Geo
        F A' A
        base
        hFA'
        hFbase
        hA'base
        (PrimCollinearCycle
          Geo
          A F A'
          hAFA'col)

    exact hAoff hAon

  have hOppAA' :
      HilbertOppositeSide Geo A A' base :=
    ⟨hAoff,
     hA'off,
     ⟨F, hAFA', hFbase⟩⟩

  have hOppA'A :
      HilbertOppositeSide Geo A' A base :=
    hilbert_oppositeSide_symm
      Geo A A' base hOppAA'

  have hOppA'D :
      HilbertOppositeSide Geo A' D base :=
    hilbert_oppositeSide_transport_right
      Geo
      A' A D
      base
      hOppA'A
      hSame

  ----------------------------------------------------------------------
  -- The opposite perpendicular ray at F is still perpendicular.
  ----------------------------------------------------------------------

  have hRightA' :
      HilbertRightAngle Geo G F A' :=
    hilbert48_test_right_angle_opposite_perp
      Geo
      A A' F G
      base
      hFbase
      hGbase
      hAoff
      hAFA'
      hRightAFG

  ----------------------------------------------------------------------
  -- Hilbert 21: the two right angles are congruent.
  ----------------------------------------------------------------------

  have hRightAngles :
      Geo.AngleCongruent G F A' F G D :=
    hilbert48_test_all_right_angles_congruent
      Geo
      A' D F G G F
      base base
      hFbase
      hGbase
      hA'off
      hGbase
      hFbase
      hDoff
      hRightA'
      hRightDGF

  ----------------------------------------------------------------------
  -- Choose an interior point M of FG, so that the angles are written
  -- in the exact transversal orientation required by I.27.
  ----------------------------------------------------------------------

  rcases
      hilbert_between_exists
        Geo F G hFG with
    ⟨M, hFMG⟩

  have hGMF :
      Geo.Between G M F :=
    (HilbertOrder.between_incidence
      F M G hFMG).2.2.2.2

  have hRayFMG :
      HilbertSameRay Geo F M G :=
    hilbert_sameRay_of_between
      Geo F M G hFMG

  have hRayGMF :
      HilbertSameRay Geo G M F :=
    hilbert_sameRay_of_between
      Geo G M F hGMF

  have hAtF :
      Geo.Angle M F A' =
        Geo.Angle G F A' :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      F M G A'
      hRayFMG

  have hAtG :
      Geo.Angle M G D =
        Geo.Angle F G D :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      G M F D
      hRayGMF

  have hAlternate :
      Geo.AngleCongruent M F A' M G D := by
    unfold Geometry.Geo.AngleCongruent at hRightAngles ⊢
    rw [hAtF, hAtG]
    exact hRightAngles

  ----------------------------------------------------------------------
  -- I.27: equal alternate angles imply parallel lines.
  ----------------------------------------------------------------------

  have hParallelFA'_GD :
      Geo.Parallel F A' G D :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo
      F A' G M D
      base
      hFMG
      hFbase
      hGbase
      hOppA'D
      hAlternate

  have hParallelA'F_GD :
      Geo.Parallel A' F G D :=
    ParallelSwapFirstLine
      Geo F A' G D
      hParallelFA'_GD

  ----------------------------------------------------------------------
  -- A, F and A' determine the same carrier line.
  ----------------------------------------------------------------------

  have hAA'F :
      Collinear Geo A A' F :=
    PrimCollinearRotate
      Geo
      A F A'
      hAFA'col

  have hParallelAF_GD :
      Geo.Parallel A F G D :=
    ParallelCollinearLeft
      Geo
      A' F A G D
      hAF
      hParallelA'F_GD
      hAA'F

  exact
    ParallelSwapSecondLine
      Geo
      A F G D
      hParallelAF_GD
/--
Geometric end of Hilbert Theorem 48 in the case of distinct
perpendicular feet.

The two altitude segments are parallel because both are perpendicular
to the base.  Since they are also congruent, I.33 gives AD parallel FG.
Finally the point-pair parallelism is converted to explicit carrier
lines.
-/
theorem hilbert48_test_equal_perpendiculars_parallel_distinct_feet
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D F G X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hGbase : HilbertIncidence.OnLine G base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hGY : G ≠ Y)
    (hFG : F ≠ G)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo Y G D)
    (hAlt : Geo.Congruent A F D G) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  have hAF_DG :
      Geo.Parallel A F D G :=
    hilbert48_test_perpendiculars_parallel_distinct_feet_same_side
      Geo
      A D F G X Y
      base
      hFbase
      hXbase
      hFX
      hGbase
      hYbase
      hGY
      hFG
      hSame
      hRightA
      hRightD

  have hAD_FG :
      Geo.Parallel A D F G :=
    hilbert48_test_i33_join_parallel
      Geo
      A D F G
      base
      hFbase
      hGbase
      hSame
      hAF_DG
      hAlt

  exact
    hilbert48_test_parallel_to_carriers
      Geo
      A D F G
      base
      hFbase
      hGbase
      hAD_FG

/--
Elementary geometric core of the final step of Hilbert Theorem 48.

If A and D lie on the same side of a line, and the perpendiculars
from A and D to that line are congruent, then A and D lie on one
line disjoint from the given line.
-/
/-axiom hilbert48_test_equal_perpendiculars_parallel
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D F G X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hGbase : HilbertIncidence.OnLine G base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hGY : G ≠ Y)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo Y G D)
    (hAlt : Geo.Congruent A F D G) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base
-/
theorem hilbert48_test_equal_perpendiculars_parallel
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D F G X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hGbase : HilbertIncidence.OnLine G base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hGY : G ≠ Y)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo Y G D)
    (hAlt : Geo.Congruent A F D G) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  by_cases hFG : F = G

  · exact
      hilbert48_test_equal_perpendiculars_parallel_same_foot
        Geo
        A D F G X Y
        base
        hFbase
        hXbase
        hFX
        hGbase
        hYbase
        hGY
        hFG
        hSame
        hRightA
        hRightD
        hAlt

  · exact
      hilbert48_test_equal_perpendiculars_parallel_distinct_feet
        Geo
        A D F G X Y
        base
        hFbase
        hXbase
        hFX
        hGbase
        hYbase
        hGY
        hFG
        hSame
        hRightA
        hRightD
        hAlt


theorem hilbert48_test_equal_altitude_parallel
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D : Geo.Point)
    (base : Geo.Line)
    (hSame : HilbertSameSide Geo A D base)
    (hAlt : HilbertEqualAltitudeToLine Geo A D base) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  rcases hAlt with
    ⟨F, G, X, Y,
      hFbase, hXbase, hFX,
      hGbase, hYbase, hGY,
      hRightA, hRightD, hAFDG⟩

  exact
    hilbert48_test_equal_perpendiculars_parallel
      Geo
      A D F G X Y
      base
      hFbase
      hXbase
      hFX
      hGbase
      hYbase
      hGY
      hSame
      hRightA
      hRightD
      hAFDG


------------------------------------------------------------------------
-- Hilbert Theorem 48
--
-- Converse of Theorem 46.
--
-- Hilbert:
--   equicomplementable triangles with the same base
--   have the same altitude.
--
-- In the I.39 configuration, where the two third vertices lie on
-- the same side of the common base, equality of altitude is expressed
-- geometrically by the existence of one line through both vertices
-- disjoint from the base line.
------------------------------------------------------------------------
theorem hilbert_theorem_48_test
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hBC : B ≠ C)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hSame : HilbertSameSide Geo A D base)
    (hEqual :
      HilbertScissorsEquicomplementable
        Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo D B C)) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  have hAlt :
      HilbertEqualAltitudeToLine Geo A D base :=
    hilbert48_test_equal_altitude
      Geo
      A B C D
      base
      hBC
      hBbase
      hCbase
      hEqual

  exact
    hilbert48_test_equal_altitude_parallel
      Geo
      A D
      base
      hSame
      hAlt


end Geometry

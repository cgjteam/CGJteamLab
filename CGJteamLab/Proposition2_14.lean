import CGJteamLab.Proposition2_13
import CGJteamLab.Proposition45
import CGJteamLab.Proposition46
import CGJteamLab.Proposition47
import CGJteamLab.Proposition2_5
import CGJteamLab.HilbertRectangle
import CGJteamLab.HilbertSquareTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid II.14.

A rectangle with two congruent adjacent sides is a square.

This is the immediate branch in Euclid II.14:

  if BE = ED,

then the rectangle BCDE is already a square.

No content argument is used here.  The result is purely geometric.
-/
theorem proposition2_14_rectangle_equal_sides_square
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hRect : IsRectangle Geo A B C D)
    (hAB_BC : Geo.Congruent A B B C) :
    IsSquare Geo A B C D := by

  --------------------------------------------------------------------
  -- Rectangle data.
  --------------------------------------------------------------------

  have hPar :
      IsParallelogram Geo A B C D :=
    hRect.1

  have hRightABC :
      HilbertRightAngle Geo A B C :=
    hRect.2

  --------------------------------------------------------------------
  -- Opposite sides of the parallelogram are congruent.
  --
  --   AB ~= CD
  --   BC ~= DA
  --------------------------------------------------------------------

  have hSides :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hPar

  have hAB_CD :
      Geo.Congruent A B C D :=
    hSides.1

  have hBC_DA :
      Geo.Congruent B C D A :=
    hSides.2

  --------------------------------------------------------------------
  -- Since AB ~= BC, all four sides are congruent.
  --------------------------------------------------------------------

  have hBC_AB :
      Geo.Congruent B C A B :=
    hilbert_congruent_symmetry
      Geo A B B C hAB_BC

  have hBC_CD :
      Geo.Congruent B C C D :=
    hilbert_congruent_transitivity
      Geo
      B C
      A B
      C D
      hBC_AB
      hAB_CD

  have hCD_AB :
      Geo.Congruent C D A B :=
    hilbert_congruent_symmetry
      Geo A B C D hAB_CD

  have hCD_BC :
      Geo.Congruent C D B C :=
    hilbert_congruent_transitivity
      Geo
      C D
      A B
      B C
      hCD_AB
      hAB_BC

  have hCD_DA :
      Geo.Congruent C D D A :=
    hilbert_congruent_transitivity
      Geo
      C D
      B C
      D A
      hCD_BC
      hBC_DA

  --------------------------------------------------------------------
  -- Rotate the parallelogram and propagate the right angle around
  -- its four vertices.
  --------------------------------------------------------------------

  have hParBCDA :
      IsParallelogram Geo B C D A :=
    And.intro
      hPar.2
      (ParallelSymmetry
        Geo A B C D hPar.1)

  have hRightBCD :
      HilbertRightAngle Geo B C D :=
    parallelogram_adjacent_right_angle
      Geo
      B C D A
      hParBCDA
      hRightABC

  have hParCDAB :
      IsParallelogram Geo C D A B :=
    And.intro
      hParBCDA.2
      (ParallelSymmetry
        Geo B C D A hParBCDA.1)

  have hRightCDA :
      HilbertRightAngle Geo C D A :=
    parallelogram_adjacent_right_angle
      Geo
      C D A B
      hParCDAB
      hRightBCD

  have hParDABC :
      IsParallelogram Geo D A B C :=
    And.intro
      hParCDAB.2
      (ParallelSymmetry
        Geo C D A B hParCDAB.1)

  have hRightDAB :
      HilbertRightAngle Geo D A B :=
    parallelogram_adjacent_right_angle
      Geo
      D A B C
      hParDABC
      hRightCDA

  --------------------------------------------------------------------
  -- Euclid Definition I.22, in the project representation IsSquare.
  --------------------------------------------------------------------

  exact
    And.intro
      hPar
      (And.intro
        hAB_BC
        (And.intro
          hBC_CD
          (And.intro
            hCD_DA
            (And.intro
              hRightDAB
              (And.intro
                hRightABC
                (And.intro
                  hRightBCD
                  hRightCDA))))))


/--
Euclid II.14.

Order package for the unequal-side branch.

Assume ED is shorter than BE. We extend BE beyond E and lay off

  EF ~= ED.

Then we construct a point G and prove that G is the midpoint of BF,
with the strict order

  B -- G -- E -- F.

The auxiliary point P comes from the definition ED < BE. Thus

  B -- P -- E
  BP ~= ED ~= EF.

Taking G as the midpoint of PE gives

  BP + PG ~= FE + EG,

hence BG ~= GF. Therefore G is also the midpoint of BF.

This package supplies exactly the order needed later for Euclid II.5:
after reversing the line,

  F -- E -- G -- B.
-/
theorem proposition2_14_unequal_side_order
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B E D : Geo.Point)
    (hShort : HilbertSegmentLess Geo E D B E) :
    exists F G : Geo.Point,
      Geo.Between B G E /\
      Geo.Between G E F /\
      Geo.Between B E F /\
      HilbertIsMidpoint Geo G B F /\
      Geo.Congruent E F E D := by

  rcases hShort with
    ⟨P, hBPE, hED_BP⟩

  have hBPEdata :=
    HilbertOrder.between_incidence
      B P E hBPE

  have hPE : Ne P E :=
    hBPEdata.2.1

  have hBE : Ne B E :=
    hBPEdata.2.2.1

  rcases
      HilbertOrder.between_extension
        B E hBE with
    ⟨R, hBER⟩

  have hER : Ne E R :=
    (HilbertOrder.between_incidence
      B E R hBER).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        E D
        E R
        hER with
    ⟨F, hRayERF, hEF_ED⟩

  have hRayEBB :
      HilbertSameRay Geo E B B :=
    hilbert_sameRay_refl
      Geo E B hBE

  have hBEF :
      Geo.Between B E F :=
    hilbert_between_transport_sameRays
      Geo
      B E R
      B F
      hBER
      hRayEBB
      hRayERF

  have hBP_ED :
      Geo.Congruent B P E D :=
    hilbert_congruent_symmetry
      Geo E D B P hED_BP

  have hED_EF :
      Geo.Congruent E D E F :=
    hilbert_congruent_symmetry
      Geo E F E D hEF_ED

  have hBP_EF :
      Geo.Congruent B P E F :=
    hilbert_congruent_transitivity
      Geo
      B P
      E D
      E F
      hBP_ED
      hED_EF

  rcases
      HilbertMidpointExists
        Geo P E hPE with
    ⟨G, hMidPE⟩

  have hPGE :
      Geo.Between P G E :=
    hMidPE.1

  have hPG_GE :
      Geo.Congruent P G G E :=
    hMidPE.2

  have hEGP :
      Geo.Between E G P :=
    (HilbertOrder.between_incidence
      P G E hPGE).2.2.2.2

  have hEPB :
      Geo.Between E P B :=
    (HilbertOrder.between_incidence
      B P E hBPE).2.2.2.2

  have hOrderLeft :=
    hilbert_between_inner_trans
      Geo
      E G P B
      hEGP
      hEPB

  have hGPB :
      Geo.Between G P B :=
    hOrderLeft.1

  have hEGB :
      Geo.Between E G B :=
    hOrderLeft.2

  have hBPG :
      Geo.Between B P G :=
    (HilbertOrder.between_incidence
      G P B hGPB).2.2.2.2

  have hBGE :
      Geo.Between B G E :=
    (HilbertOrder.between_incidence
      E G B hEGB).2.2.2.2

  have hOrderRight :=
    hilbert_between_inner_trans
      Geo
      B G E F
      hBGE
      hBEF

  have hGEF :
      Geo.Between G E F :=
    hOrderRight.1

  have hBGF :
      Geo.Between B G F :=
    hOrderRight.2

  have hFEG :
      Geo.Between F E G :=
    (HilbertOrder.between_incidence
      G E F hGEF).2.2.2.2

  have hBP_FE :
      Geo.Congruent B P F E :=
    CongruentSwapSecond
      Geo B P E F hBP_EF

  have hPG_EG :
      Geo.Congruent P G E G :=
    CongruentSwapSecond
      Geo P G G E hPG_GE

  have hBG_FG :
      Geo.Congruent B G F G :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      B P G
      F E G
      hBPG
      hFEG
      hBP_FE
      hPG_EG

  have hBG_GF :
      Geo.Congruent B G G F :=
    CongruentSwapSecond
      Geo B G F G hBG_FG

  have hMidBF :
      HilbertIsMidpoint Geo G B F :=
    ⟨hBGF, hBG_GF⟩

  exact
    ⟨F, G,
      hBGE,
      hGEF,
      hBEF,
      hMidBF,
      hEF_ED⟩


/--
Euclid II.14.

If

  G -- E -- F,

then E is strictly inside the circle with center G and radius GF:

  GE < GF.

This is the exact "inside" datum needed later for the circle
intersection step producing H.
-/
theorem proposition2_14_inside_circle
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G E F : Geo.Point)
    (hGEF : Geo.Between G E F) :
    HilbertSegmentLess Geo G E G F /\
    Ne G F /\
    Ne G E /\
    Ne E F := by

  have hData :=
    HilbertOrder.between_incidence
      G E F hGEF

  have hGE : Ne G E :=
    hData.1

  have hEF : Ne E F :=
    hData.2.1

  have hGF : Ne G F :=
    hData.2.2.1

  have hInside :
      HilbertSegmentLess Geo G E G F := by
    exact
      ⟨E,
       hGEF,
       hilbert_congruent_reflexive Geo G E⟩

  exact
    ⟨hInside,
     hGF,
     hGE,
     hEF⟩


/--
Euclid II.14.

Right-angle package after the point H has been obtained.

For a rectangle BCDE, assume

  B -- G -- E -- F
  D -- E -- H.

Then triangle GEH is right at E.

The proof uses only:
* propagation of the rectangle right angle,
* same-ray transport,
* the opposite extension of a right angle,
* vertical angles.

No circle-continuity argument is used here.
-/
theorem proposition2_14_right_triangle_after_H
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E G F H : Geo.Point)
    (hRect : IsRectangle Geo B C D E)
    (hBGE : Geo.Between B G E)
    (hGEF : Geo.Between G E F)
    (hDEH : Geo.Between D E H) :
    HilbertRightAngle Geo G E H := by

  --------------------------------------------------------------------
  -- Propagate the rectangle right angle from C to D and then to E.
  --------------------------------------------------------------------

  have hPar :
      IsParallelogram Geo B C D E :=
    hRect.1

  have hRightBCD :
      HilbertRightAngle Geo B C D :=
    hRect.2

  have hParCDEB :
      IsParallelogram Geo C D E B :=
    And.intro
      hPar.2
      (ParallelSymmetry
        Geo B C D E hPar.1)

  have hRightCDE :
      HilbertRightAngle Geo C D E :=
    parallelogram_adjacent_right_angle
      Geo
      C D E B
      hParCDEB
      hRightBCD

  have hParDEBC :
      IsParallelogram Geo D E B C :=
    And.intro
      hParCDEB.2
      (ParallelSymmetry
        Geo C D E B hParCDEB.1)

  have hRightDEB :
      HilbertRightAngle Geo D E B :=
    parallelogram_adjacent_right_angle
      Geo
      D E B C
      hParDEBC
      hRightCDE

  --------------------------------------------------------------------
  -- DEB is a genuine angle because DE is parallel to BC.
  --------------------------------------------------------------------

  have hDEB :
      Not (Collinear Geo D E B) :=
    parallel_first_not_collinear
      Geo D E B C hParDEBC.1

  --------------------------------------------------------------------
  -- Since B-G-E, B and G determine the same ray from E.
  --------------------------------------------------------------------

  have hEGB :
      Geo.Between E G B :=
    (HilbertOrder.between_incidence
      B G E hBGE).2.2.2.2

  have hRayEGB :
      HilbertSameRay Geo E G B :=
    hilbert_sameRay_of_between
      Geo E G B hEGB

  have hRayEBG :
      HilbertSameRay Geo E B G :=
    hilbert_sameRay_symm
      Geo E G B hRayEGB

  --------------------------------------------------------------------
  -- D-E-H is the opposite extension of ray ED.
  -- Therefore the right angle DEB is congruent to BEH.
  --------------------------------------------------------------------

  have hDEB_BEH :
      Geo.AngleCongruent D E B B E H :=
    hilbert_right_angle_opposite_extension
      Geo
      D E B H
      hDEB
      hRightDEB
      hDEH

  --------------------------------------------------------------------
  -- Replace B by G on the same ray from E.
  --------------------------------------------------------------------

  have hAngleDEB_DEG :
      Geo.Angle D E B =
      Geo.Angle D E G :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      E D B G
      hRayEBG

  have hAngleBEH_GEH :
      Geo.Angle B E H =
      Geo.Angle G E H :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      E B G H
      hRayEBG

  have hDEG_GEH :
      Geo.AngleCongruent D E G G E H := by
    unfold Geometry.Geo.AngleCongruent
      at hDEB_BEH ⊢
    rw [← hAngleDEB_DEG]
    rw [← hAngleBEH_GEH]
    exact hDEB_BEH

  --------------------------------------------------------------------
  -- DEG is nondegenerate.
  --------------------------------------------------------------------

  have hEG : Ne E G :=
    ((HilbertOrder.between_incidence
      B G E hBGE).2.1).symm

  have hEGBcol :
      Collinear Geo E G B :=
    hRayEGB.2.2.1

  have hDEG :
      Not (Collinear Geo D E G) := by
    intro hCol
    have hDEB' :
        Collinear Geo D E B :=
      hilbert_primCollinear_trans
        Geo
        D E G B
        hEG
        hCol
        hEGBcol
    exact hDEB hDEB'

  --------------------------------------------------------------------
  -- Vertical angles:
  --
  --   DEG ~= HEF.
  --------------------------------------------------------------------

  have hDEG_HEF :
      Geo.AngleCongruent D E G H E F :=
    VerticalAngles
      Geo
      D E G H F
      hDEH
      hGEF
      hDEG

  --------------------------------------------------------------------
  -- Hence
  --
  --   GEH ~= DEG ~= HEF.
  --
  -- Together with G-E-F this is exactly the project definition of
  -- a right angle GEH.
  --------------------------------------------------------------------

  have hGEH_DEG :
      Geo.AngleCongruent G E H D E G :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      D E G
      G E H
      hDEG_GEH

  have hGEH_HEF :
      Geo.AngleCongruent G E H H E F :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      G E H
      D E G
      H E F
      hGEH_DEG
      hDEG_HEF

  exact
    ⟨F,
     hGEF,
     hGEH_HEF⟩


/--
Euclid II.14.

Mirror-center construction.

From

  G -- E -- F

construct K on ray EF such that

  EK ~= GE.

Then

  G -- E -- K

and E is the midpoint of GK.

This is the synthetic reflection of the circle center G through E.
It will be used to reduce the required line-circle intersection to
the available circle-circle continuity principle.
-/
theorem proposition2_14_mirror_center
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G E F : Geo.Point)
    (hGEF : Geo.Between G E F) :
    exists K : Geo.Point,
      Geo.Between G E K /\
      HilbertIsMidpoint Geo E G K /\
      Geo.Congruent E K G E := by

  have hData :=
    HilbertOrder.between_incidence
      G E F hGEF

  have hGE : Ne G E :=
    hData.1

  have hEF : Ne E F :=
    hData.2.1

  --------------------------------------------------------------------
  -- Lay off GE on ray EF.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        G E
        E F
        hEF with
    ⟨K, hRayEFK, hEK_GE⟩

  --------------------------------------------------------------------
  -- Keep G fixed on its own ray from E and move F to K.
  -- Since G-E-F, same-ray transport gives G-E-K.
  --------------------------------------------------------------------

  have hRayEGG :
      HilbertSameRay Geo E G G :=
    hilbert_sameRay_refl
      Geo E G hGE

  have hGEK :
      Geo.Between G E K :=
    hilbert_between_transport_sameRays
      Geo
      G E F
      G K
      hGEF
      hRayEGG
      hRayEFK

  --------------------------------------------------------------------
  -- Convert EK ~= GE to GE ~= EK.
  --------------------------------------------------------------------

  have hGE_EK :
      Geo.Congruent G E E K :=
    hilbert_congruent_symmetry
      Geo
      E K
      G E
      hEK_GE

  have hMidE :
      HilbertIsMidpoint Geo E G K :=
    ⟨hGEK, hGE_EK⟩

  exact
    ⟨K,
     hGEK,
     hMidE,
     hEK_GE⟩


/--
Euclid II.14.

The rectangle side DE lies on the perpendicular-bisector axis of GK.

Assume:
* BCDE is a rectangle,
* B -- G -- E,
* E is the midpoint of GK.

Then D is equidistant from G and K:

  DG ~= DK.

Geometrically, triangles EDG and EDK are congruent by SAS:
* ED is common,
* EG ~= EK,
* angle DEG ~= angle DEK because DE is perpendicular to GK.
-/
theorem proposition2_14_rectangle_axis_equidistant
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E G K : Geo.Point)
    (hRect : IsRectangle Geo B C D E)
    (hBGE : Geo.Between B G E)
    (hMidE : HilbertIsMidpoint Geo E G K) :
    Geo.Congruent D G D K := by

  --------------------------------------------------------------------
  -- Rectangle right angle at E.
  --------------------------------------------------------------------

  have hPar :
      IsParallelogram Geo B C D E :=
    hRect.1

  have hRightBCD :
      HilbertRightAngle Geo B C D :=
    hRect.2

  have hParCDEB :
      IsParallelogram Geo C D E B :=
    And.intro
      hPar.2
      (ParallelSymmetry
        Geo B C D E hPar.1)

  have hRightCDE :
      HilbertRightAngle Geo C D E :=
    parallelogram_adjacent_right_angle
      Geo
      C D E B
      hParCDEB
      hRightBCD

  have hParDEBC :
      IsParallelogram Geo D E B C :=
    And.intro
      hParCDEB.2
      (ParallelSymmetry
        Geo C D E B hParCDEB.1)

  have hRightDEB :
      HilbertRightAngle Geo D E B :=
    parallelogram_adjacent_right_angle
      Geo
      D E B C
      hParDEBC
      hRightCDE

  have hDEB :
      Not (Collinear Geo D E B) :=
    parallel_first_not_collinear
      Geo D E B C hParDEBC.1

  --------------------------------------------------------------------
  -- B and G determine the same ray from E.
  --------------------------------------------------------------------

  have hEGB :
      Geo.Between E G B :=
    (HilbertOrder.between_incidence
      B G E hBGE).2.2.2.2

  have hRayEGB :
      HilbertSameRay Geo E G B :=
    hilbert_sameRay_of_between
      Geo E G B hEGB

  have hRayEBG :
      HilbertSameRay Geo E B G :=
    hilbert_sameRay_symm
      Geo E G B hRayEGB

  have hEGBcol :
      Collinear Geo E G B :=
    hRayEGB.2.2.1

  have hEG : Ne E G :=
    hRayEGB.1.symm

  --------------------------------------------------------------------
  -- DEG is nondegenerate.
  --------------------------------------------------------------------

  have hDEG :
      Not (Collinear Geo D E G) := by
    intro hCol

    have hDEB' :
        Collinear Geo D E B :=
      hilbert_primCollinear_trans
        Geo
        D E G B
        hEG
        hCol
        hEGBcol

    exact hDEB hDEB'

  --------------------------------------------------------------------
  -- Transport the right angle DEB from ray EB to ray EG.
  --------------------------------------------------------------------

  rcases hRightDEB with
    ⟨X, hDEX, hDEB_BEX⟩

  have hAngleDEB_DEG :
      Geo.Angle D E B =
      Geo.Angle D E G :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      E D B G
      hRayEBG

  have hAngleBEX_GEX :
      Geo.Angle B E X =
      Geo.Angle G E X :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      E B G X
      hRayEBG

  have hDEG_GEX :
      Geo.AngleCongruent D E G G E X := by
    unfold Geometry.Geo.AngleCongruent
      at hDEB_BEX ⊢
    rw [← hAngleDEB_DEG]
    rw [← hAngleBEX_GEX]
    exact hDEB_BEX

  --------------------------------------------------------------------
  -- E is the midpoint of GK, hence G-E-K and GE ~= EK.
  --------------------------------------------------------------------

  have hGEK :
      Geo.Between G E K :=
    hMidE.1

  have hGE_EK :
      Geo.Congruent G E E K :=
    hMidE.2

  have hEG_EK :
      Geo.Congruent E G E K :=
    CongruentReverseFirst
      Geo
      G E
      E K
      hGE_EK

  have hGEKdata :=
    HilbertOrder.between_incidence
      G E K hGEK

  have hEK : Ne E K :=
    hGEKdata.2.1

  --------------------------------------------------------------------
  -- X-E-D and G-E-K form two crossing straight lines.
  -- Therefore angle GEX is congruent to angle KED.
  --------------------------------------------------------------------

  have hXED :
      Geo.Between X E D :=
    (HilbertOrder.between_incidence
      D E X hDEX).2.2.2.2

  have hDEXcol :
      Collinear Geo D E X :=
    (HilbertOrder.between_incidence
      D E X hDEX).2.2.2.1

  have hEX : Ne E X :=
    (HilbertOrder.between_incidence
      D E X hDEX).2.1

  have hGEX :
      Not (Collinear Geo G E X) := by
    intro hCol

    have hEXG :
        Collinear Geo E X G :=
      PrimCollinearCycle
        Geo G E X hCol

    have hDEG' :
        Collinear Geo D E G :=
      hilbert_primCollinear_trans
        Geo
        D E X G
        hEX
        hDEXcol
        hEXG

    exact hDEG hDEG'

  have hGEX_KED :
      Geo.AngleCongruent G E X K E D :=
    VerticalAngles
      Geo
      G E X K D
      hGEK
      hXED
      hGEX

  have hGEX_DEK :
      Geo.AngleCongruent G E X D E K :=
    (Geo.angle_congruent_reverse_second
      G E X
      K E D).mp
      hGEX_KED

  have hDEG_DEK :
      Geo.AngleCongruent D E G D E K :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      D E G
      G E X
      D E K
      hDEG_GEX
      hGEX_DEK

  --------------------------------------------------------------------
  -- EDK is also a genuine triangle.
  --------------------------------------------------------------------

  have hGEKcol :
      Collinear Geo G E K :=
    hGEKdata.2.2.2.1

  have hEKG :
      Collinear Geo E K G :=
    PrimCollinearCycle
      Geo G E K hGEKcol

  have hDEK :
      Not (Collinear Geo D E K) := by
    intro hCol

    have hDEG' :
        Collinear Geo D E G :=
      hilbert_primCollinear_trans
        Geo
        D E K G
        hEK
        hCol
        hEKG

    exact hDEG hDEG'

  have hEDG :
      Not (Collinear Geo E D G) := by
    intro hCol
    exact
      hDEG
        (PrimCollinearSwap
          Geo E D G hCol)

  have hEDK :
      Not (Collinear Geo E D K) := by
    intro hCol
    exact
      hDEK
        (PrimCollinearSwap
          Geo E D K hCol)

  --------------------------------------------------------------------
  -- SAS on triangles EDG and EDK.
  --------------------------------------------------------------------

  have hED_ED :
      Geo.Congruent E D E D :=
    hilbert_congruent_reflexive
      Geo E D

  have hSAS :=
    SAS
      Geo
      E D G
      E D K
      hEDG
      hEDK
      hED_ED
      hDEG_DEK
      hEG_EK

  exact hSAS.sideBC


/--
Euclid II.14.

Perpendicular-bisector direction.

If E is the midpoint of GK and X is equidistant from G and K,
then EX is perpendicular to GK.  In the project language:

  angle GEX is a right angle.

The proof is SSS on triangles EGX and EKX:
* EG ~= EK,
* GX ~= KX,
* EX ~= EX.

The equal angles at E are adjacent because G -- E -- K.
-/
theorem proposition2_14_equidistant_right_angle
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G E K X : Geo.Point)
    (hMidE : HilbertIsMidpoint Geo E G K)
    (hEGX : Not (Collinear Geo E G X))
    (hXG_XK : Geo.Congruent X G X K) :
    HilbertRightAngle Geo G E X := by

  --------------------------------------------------------------------
  -- Midpoint data.
  --------------------------------------------------------------------

  have hGEK :
      Geo.Between G E K :=
    hMidE.1

  have hGE_EK :
      Geo.Congruent G E E K :=
    hMidE.2

  have hEG_EK :
      Geo.Congruent E G E K :=
    CongruentReverseFirst
      Geo
      G E
      E K
      hGE_EK

  --------------------------------------------------------------------
  -- Reorient the equidistance hypothesis for the SSS side GX ~= KX.
  --------------------------------------------------------------------

  have hGX_KX :
      Geo.Congruent G X K X :=
    CongruentReverseBoth
      Geo
      X G
      X K
      hXG_XK

  have hEX_EX :
      Geo.Congruent E X E X :=
    hilbert_congruent_reflexive
      Geo E X

  --------------------------------------------------------------------
  -- SSS for triangles EGX and EKX.
  --------------------------------------------------------------------

  have hSSS :=
    HilbertSSS
      Geo
      E G X
      E K X
      hEGX
      hEG_EK
      hGX_KX
      hEX_EX

  have hGEX_KEX :
      Geo.AngleCongruent G E X K E X :=
    hSSS.2.angleA

  --------------------------------------------------------------------
  -- The project definition of a right angle GEX asks for
  --
  --   G -- E -- K
  --   angle GEX ~= angle XEK.
  --
  -- Reverse the endpoints of the second angle.
  --------------------------------------------------------------------

  have hGEX_XEK :
      Geo.AngleCongruent G E X X E K :=
    (Geo.angle_congruent_reverse_second
      G E X
      K E X).mp
      hGEX_KEX

  exact
    Exists.intro
      K
      (And.intro
        hGEK
        hGEX_XEK)


/--
Euclid II.14.

Same-half-plane uniqueness of an angle ray.

Let G,E lie on a reference line. Suppose D and H lie on the same
side of that line and

  angle GED ~= angle GEH.

Hilbert III.4 says that the copied angle on a prescribed side of the
ray EG has a unique resulting ray. Hence ED and EH are the same ray,
and therefore D,E,H are collinear.

This is the local uniqueness statement needed for the
perpendicular-bisector argument.
-/
theorem proposition2_14_same_side_angle_collinear
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G E D H : Geo.Point)
    (base : Geo.Line)
    (hGE : Ne G E)
    (hGbase : HilbertIncidence.OnLine G base)
    (hEbase : HilbertIncidence.OnLine E base)
    (hDoff : Not (HilbertIncidence.OnLine D base))
    (hSameDH : HilbertSameSide Geo D H base)
    (hAngle :
      Geo.AngleCongruent G E D G E H) :
    Collinear Geo D E H := by

  rcases
      hilbert_angle_unique_common_ray
        Geo
        G E D H
        base
        hGE
        hGbase
        hEbase
        hDoff
        hSameDH
        hAngle with
    ⟨X, hRayXD, hRayXH⟩

  have hEX : Ne E X :=
    hRayXD.1.symm

  have hEXD :
      Collinear Geo E X D :=
    hRayXD.2.2.1

  have hEXH :
      Collinear Geo E X H :=
    hRayXH.2.2.1

  have hDEX :
      Collinear Geo D E X := by
    exact
      PrimCollinearRotate
        Geo
        D X E
        (PrimCollinearSymm
          Geo E X D hEXD)

  exact
    hilbert_primCollinear_trans
      Geo
      D E X H
      hEX
      hDEX
      hEXH


/--
Euclid II.14.

Reduce the opposite-half-plane case to the same-half-plane case.

Assume D and H lie on opposite sides of a reference line through E.
Extend DE beyond E to D'.

Then either:
* D,E,H are already collinear, or
* D' and H lie on the same side of the reference line.

In the noncollinear case this is exactly the third-side consequence
of Pasch: the reference line meets DD' at E and DH at the crossing
point supplied by OppositeSide, so it cannot also meet D'H.
-/
theorem proposition2_14_opposite_side_reduction
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (E D H : Geo.Point)
    (base : Geo.Line)
    (hEbase : HilbertIncidence.OnLine E base)
    (hOppDH : HilbertOppositeSide Geo D H base) :
    Collinear Geo D E H \/
    Exists (fun D' : Geo.Point =>
      Geo.Between D E D' /\
      HilbertSameSide Geo D' H base) := by

  have hDE : Ne D E := by
    intro h
    subst D
    exact hOppDH.1 hEbase

  let D' :=
    (HilbertOrder.between_extension
      (Geo := Geo)
      D E hDE).choose

  have hDED' :
      Geo.Between D E D' :=
    (HilbertOrder.between_extension
      (Geo := Geo)
      D E hDE).choose_spec

  have hDED'col :
      Collinear Geo D E D' :=
    (HilbertOrder.between_incidence
      D E D' hDED').2.2.2.1

  have hDD' : Ne D D' :=
    (HilbertOrder.between_incidence
      D E D' hDED').2.2.1

  by_cases hCol :
      Collinear Geo D D' H

  case pos =>
    have hEDD' :
        Collinear Geo E D D' :=
      PrimCollinearSwap
        Geo D E D' hDED'col

    have hEDH :
        Collinear Geo E D H :=
      hilbert_primCollinear_trans
        Geo
        E D D' H
        hDD'
        hEDD'
        hCol

    exact
      Or.inl
        (PrimCollinearSwap
          Geo E D H hEDH)

  case neg =>
    let Y := hOppDH.2.2.choose

    have hDYH :
        Geo.Between D Y H :=
      hOppDH.2.2.choose_spec.1

    have hYbase :
        HilbertIncidence.OnLine Y base :=
      hOppDH.2.2.choose_spec.2

    have hSameD'H :
        HilbertSameSide Geo D' H base :=
      hilbert_third_side_endpoints_sameSide
        Geo
        D D' H
        E Y
        base
        hCol
        hDED'
        hDYH
        hEbase
        hYbase

    exact
      Or.inr
        (Exists.intro
          D'
          (And.intro
            hDED'
            hSameD'H))


/--
Euclid II.14.

Two right-angle rays through the same foot are collinear.

Let G,E lie on a reference line. If D and H are off that line and
both GED and GEH are right angles, then D,E,H are collinear.

The proof splits directly from the project definitions:
* if segment DH does not meet the base, D and H are on the same side,
  so Hilbert III.4 uniqueness applies through test08;
* if segment DH meets the base, D and H are on opposite sides.
  Test09 extends DE through E to D' on H's side, after which test08
  applies to D' and H.

Hilbert Theorem 21 supplies congruence of the two right angles.
-/
theorem proposition2_14_right_angle_axis_collinear
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G E D H : Geo.Point)
    (base : Geo.Line)
    (hGE : Ne G E)
    (hGbase : HilbertIncidence.OnLine G base)
    (hEbase : HilbertIncidence.OnLine E base)
    (hDoff : Not (HilbertIncidence.OnLine D base))
    (hHoff : Not (HilbertIncidence.OnLine H base))
    (hRightD : HilbertRightAngle Geo G E D)
    (hRightH : HilbertRightAngle Geo G E H) :
    Collinear Geo D E H := by

  have hGED :
      Not (Collinear Geo G E D) :=
    hilbert_not_collinear_of_off_line
      Geo
      G E D
      base
      hGE
      hGbase
      hEbase
      hDoff

  have hGEH :
      Not (Collinear Geo G E H) :=
    hilbert_not_collinear_of_off_line
      Geo
      G E H
      base
      hGE
      hGbase
      hEbase
      hHoff

  have hAngleDH :
      Geo.AngleCongruent G E D G E H :=
    hilbert_all_right_angles_congruent
      Geo
      G E D
      G E H
      hGED
      hGEH
      hRightD
      hRightH

  by_cases hMeet :
      HilbertSegmentMeetsLine Geo D H base

  case neg =>
    have hSameDH :
        HilbertSameSide Geo D H base :=
      And.intro
        hDoff
        (And.intro
          hHoff
          (Relation.ReflTransGen.single
            (And.intro
              hDoff
              (And.intro
                hHoff
                hMeet))))

    exact
      proposition2_14_same_side_angle_collinear
        Geo
        G E D H
        base
        hGE
        hGbase
        hEbase
        hDoff
        hSameDH
        hAngleDH

  case pos =>
    have hOppDH :
        HilbertOppositeSide Geo D H base :=
      And.intro
        hDoff
        (And.intro
          hHoff
          hMeet)

    rcases
        proposition2_14_opposite_side_reduction
          Geo
          E D H
          base
          hEbase
          hOppDH with
      hCol | hReduced

    case inl =>
      exact hCol

    case inr =>
      rcases hReduced with
        ⟨D', hDED', hSameD'H⟩

      have hD'off :
          Not (HilbertIncidence.OnLine D' base) :=
        hSameD'H.1

      have hGED' :
          Not (Collinear Geo G E D') :=
        hilbert_not_collinear_of_off_line
          Geo
          G E D'
          base
          hGE
          hGbase
          hEbase
          hD'off

      ------------------------------------------------------------------
      -- The extension D-E-D' preserves the right angle.
      --
      -- From the definition of hRightD choose C opposite G:
      --
      --   G-E-C
      --   angle GED ~= angle DEC.
      --
      -- Since D-E-D', vertical angles give
      --
      --   angle DEC ~= angle D'EG = angle GED'.
      ------------------------------------------------------------------

      rcases hRightD with
        ⟨C, hGEC, hGED_DEC⟩

      have hCEG :
          Geo.Between C E G :=
        (HilbertOrder.between_incidence
          G E C hGEC).2.2.2.2

      have hGECcol :
          Collinear Geo G E C :=
        (HilbertOrder.between_incidence
          G E C hGEC).2.2.2.1

      have hCbase :
          HilbertIncidence.OnLine C base :=
        hilbert_collinear_on_line
          Geo
          G E C
          base
          hGE
          hGbase
          hEbase
          hGECcol

      have hCE : Ne C E :=
        (HilbertOrder.between_incidence
          G E C hGEC).2.1.symm

      have hDEC :
          Not (Collinear Geo D E C) := by
        have hCED :
            Not (Collinear Geo C E D) :=
          hilbert_not_collinear_of_off_line
            Geo
            C E D
            base
            hCE
            hCbase
            hEbase
            hDoff

        intro h
        exact
          hCED
            (PrimCollinearSymm
              Geo D E C h)

      have hDEC_D'EG :
          Geo.AngleCongruent D E C D' E G :=
        VerticalAngles
          Geo
          D E C
          D' G
          hDED'
          hCEG
          hDEC

      have hGED_D'EG :
          Geo.AngleCongruent G E D D' E G :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          G E D
          D E C
          D' E G
          hGED_DEC
          hDEC_D'EG

      have hGED_GED' :
          Geo.AngleCongruent G E D G E D' :=
        (Geo.angle_congruent_reverse_second
          G E D
          D' E G).mp
          hGED_D'EG

      have hGED'_GED :
          Geo.AngleCongruent G E D' G E D :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          G E D
          G E D'
          hGED_GED'

      have hGED'_GEH :
          Geo.AngleCongruent G E D' G E H :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          G E D'
          G E D
          G E H
          hGED'_GED
          hAngleDH

      have hD'EH :
          Collinear Geo D' E H :=
        proposition2_14_same_side_angle_collinear
          Geo
          G E D' H
          base
          hGE
          hGbase
          hEbase
          hD'off
          hSameD'H
          hGED'_GEH

      ------------------------------------------------------------------
      -- D-E-D' and D'-E-H determine the same line.
      ------------------------------------------------------------------

      have hDED'col :
          Collinear Geo D E D' :=
        (HilbertOrder.between_incidence
          D E D' hDED').2.2.2.1

      have hED' : Ne E D' :=
        (HilbertOrder.between_incidence
          D E D' hDED').2.1

      have hED'H :
          Collinear Geo E D' H :=
        PrimCollinearSwap
          Geo D' E H hD'EH

      exact
        hilbert_primCollinear_trans
          Geo
          D E D' H
          hED'
          hDED'col
          hED'H


/--
Euclid II.14.

The distance between the two symmetric circle centers is smaller than
the sum of the two equal radii.

Assume:
* G-E-F,
* E is the midpoint of GK.

Then GE < GF. Since EK ~= GE, also EK < GF. Hence

  GK = GE + EK < GF + GF.

The right-hand sum is represented by a point P with G-F-P and
FP ~= GF. The conclusion is exactly

  HilbertSegmentSumGreater Geo G F G F G K.
-/
theorem proposition2_14_centers_less_two_radii
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G E F K : Geo.Point)
    (hGEF : Geo.Between G E F)
    (hMidE : HilbertIsMidpoint Geo E G K) :
    HilbertSegmentSumGreater Geo G F G F G K := by

  have hGEK :
      Geo.Between G E K :=
    hMidE.1

  have hGE_EK :
      Geo.Congruent G E E K :=
    hMidE.2

  have hEK_GE :
      Geo.Congruent E K G E :=
    hilbert_congruent_symmetry
      Geo
      G E
      E K
      hGE_EK

  have hGE_GF :
      HilbertSegmentLess Geo G E G F :=
    hilbert_segmentLess_of_between
      Geo
      G E F
      hGEF

  have hGF : Ne G F :=
    (HilbertOrder.between_incidence
      G E F hGEF).2.2.1

  --------------------------------------------------------------------
  -- Choose a carrier ray beyond F.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        (Geo := Geo)
        G F hGF with
    ⟨R, hGFR⟩

  have hFR : Ne F R :=
    (HilbertOrder.between_incidence
      G F R hGFR).2.1

  have hFG : Ne F G :=
    hGF.symm

  have hRayFGG :
      HilbertSameRay Geo F G G :=
    hilbert_sameRay_refl
      Geo F G hGF

  --------------------------------------------------------------------
  -- P represents GF + GF:
  --
  --   G -- F -- P
  --   FP ~= GF.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        G F
        F R
        hFR with
    ⟨P, hRayFRP, hFP_GF⟩

  have hGFP :
      Geo.Between G F P :=
    hilbert_between_transport_sameRays
      Geo
      G F R
      G P
      hGFR
      hRayFGG
      hRayFRP

  have hGF_FP :
      Geo.Congruent G F F P :=
    hilbert_congruent_symmetry
      Geo
      F P
      G F
      hFP_GF

  --------------------------------------------------------------------
  -- Q represents GF + EK:
  --
  --   G -- F -- Q
  --   FQ ~= EK.
  --
  -- It is an intermediate sum between GK and GP.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        E K
        F R
        hFR with
    ⟨Q, hRayFRQ, hFQ_EK⟩

  have hGFQ :
      Geo.Between G F Q :=
    hilbert_between_transport_sameRays
      Geo
      G F R
      G Q
      hGFR
      hRayFGG
      hRayFRQ

  have hEK_FQ :
      Geo.Congruent E K F Q :=
    hilbert_congruent_symmetry
      Geo
      F Q
      E K
      hFQ_EK

  --------------------------------------------------------------------
  -- First inequality:
  --
  --   GE < GF
  --   EK ~= FQ
  --
  -- therefore
  --
  --   GK < GQ.
  --------------------------------------------------------------------

  have hGK_GQ :
      HilbertSegmentLess Geo G K G Q :=
    bookZero_53_lessThanAdditive
      Geo
      G E
      G F
      K Q
      hGE_GF
      hGEK
      hGFQ
      hEK_FQ

  --------------------------------------------------------------------
  -- EK < GF, hence FQ < FP.
  --------------------------------------------------------------------

  have hEK_GF :
      HilbertSegmentLess Geo E K G F :=
    hilbert_segmentLess_congruent_left
      Geo
      G E
      E K
      G F
      hGE_GF
      hEK_GE

  have hFQ_GF :
      HilbertSegmentLess Geo F Q G F :=
    hilbert_segmentLess_congruent_left
      Geo
      E K
      F Q
      G F
      hEK_GF
      hFQ_EK

  have hFQ_FP :
      HilbertSegmentLess Geo F Q F P :=
    hilbert_segmentLess_congruent_right
      Geo
      F Q
      G F
      F P
      hFQ_GF
      hGF_FP

  --------------------------------------------------------------------
  -- Prepend the same segment FG to FQ < FP.
  --
  -- Reverse the two sums:
  --
  --   Q -- F -- G
  --   P -- F -- G.
  --------------------------------------------------------------------

  have hQFG :
      Geo.Between Q F G :=
    (HilbertOrder.between_incidence
      G F Q hGFQ).2.2.2.2

  have hPFG :
      Geo.Between P F G :=
    (HilbertOrder.between_incidence
      G F P hGFP).2.2.2.2

  have hQF_FQ :
      Geo.Congruent Q F F Q :=
    CongruentReverseFirst
      Geo
      F Q
      F Q
      (hilbert_congruent_reflexive Geo F Q)

  have hQF_FP :
      HilbertSegmentLess Geo Q F F P :=
    hilbert_segmentLess_congruent_left
      Geo
      F Q
      Q F
      F P
      hFQ_FP
      hQF_FQ

  have hFP_PF :
      Geo.Congruent F P P F :=
    CongruentReverseFirst
      Geo
      P F
      P F
      (hilbert_congruent_reflexive Geo P F)

  have hQF_PF :
      HilbertSegmentLess Geo Q F P F :=
    hilbert_segmentLess_congruent_right
      Geo
      Q F
      F P
      P F
      hQF_FP
      hFP_PF

  have hFG_FG :
      Geo.Congruent F G F G :=
    hilbert_congruent_reflexive
      Geo F G

  have hQG_PG :
      HilbertSegmentLess Geo Q G P G :=
    bookZero_53_lessThanAdditive
      Geo
      Q F
      P F
      G G
      hQF_PF
      hQFG
      hPFG
      hFG_FG

  --------------------------------------------------------------------
  -- Reorient QG < PG as GQ < GP.
  --------------------------------------------------------------------

  have hGQ_QG :
      Geo.Congruent G Q Q G :=
    CongruentReverseFirst
      Geo
      Q G
      Q G
      (hilbert_congruent_reflexive Geo Q G)

  have hGQ_PG :
      HilbertSegmentLess Geo G Q P G :=
    hilbert_segmentLess_congruent_left
      Geo
      Q G
      G Q
      P G
      hQG_PG
      hGQ_QG

  have hPG_GP :
      Geo.Congruent P G G P :=
    CongruentReverseFirst
      Geo
      G P
      G P
      (hilbert_congruent_reflexive Geo G P)

  have hGQ_GP :
      HilbertSegmentLess Geo G Q G P :=
    hilbert_segmentLess_congruent_right
      Geo
      G Q
      P G
      G P
      hGQ_PG
      hPG_GP

  --------------------------------------------------------------------
  -- Transitivity:
  --
  --   GK < GQ < GP.
  --------------------------------------------------------------------

  have hGK_GP :
      HilbertSegmentLess Geo G K G P :=
    bookZero_52_lessThanTransitive
      Geo
      G K
      G Q
      G P
      hGK_GQ
      hGQ_GP

  exact
    Exists.intro
      P
      (And.intro
        hGFP
        (And.intro
          hFP_GF
          hGK_GP))


/--
Euclid II.14.

Construct the outside witness required by circle-circle continuity.

Given two distinct centers G,K and a nonzero radius GF, construct Y
beyond K on line GK such that

  KY ~= GF.

Then Y lies on the circle centered at K with radius GF, while

  GF < GY,

so Y is outside the circle centered at G with radius GF.
-/
theorem proposition2_14_circle_outside_witness
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G K F : Geo.Point)
    (hGK : Ne G K)
    (_hGF : Ne G F) :
    exists Y : Geo.Point,
      Geo.Between G K Y /\
      Geo.Congruent K Y G F /\
      HilbertSegmentLess Geo G F G Y := by

  rcases
      HilbertOrder.between_extension
        (Geo := Geo)
        G K hGK with
    ⟨R, hGKR⟩

  have hKR : Ne K R :=
    (HilbertOrder.between_incidence
      G K R hGKR).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        G F
        K R
        hKR with
    ⟨Y, hRayKRY, hKY_GF⟩

  have hRayKGG :
      HilbertSameRay Geo K G G :=
    hilbert_sameRay_refl
      Geo K G hGK

  have hGKY :
      Geo.Between G K Y :=
    hilbert_between_transport_sameRays
      Geo
      G K R
      G Y
      hGKR
      hRayKGG
      hRayKRY

  have hYKG :
      Geo.Between Y K G :=
    (HilbertOrder.between_incidence
      G K Y hGKY).2.2.2.2

  have hYK_YG :
      HilbertSegmentLess Geo Y K Y G :=
    hilbert_segmentLess_of_between
      Geo
      Y K G
      hYKG

  have hYK_GF :
      Geo.Congruent Y K G F :=
    CongruentReverseFirst
      Geo
      K Y
      G F
      hKY_GF

  have hGF_YK :
      Geo.Congruent G F Y K :=
    hilbert_congruent_symmetry
      Geo
      Y K
      G F
      hYK_GF

  have hGF_YG :
      HilbertSegmentLess Geo G F Y G :=
    hilbert_segmentLess_congruent_left
      Geo
      Y K
      G F
      Y G
      hYK_YG
      hGF_YK

  have hYG_GY :
      Geo.Congruent Y G G Y :=
    CongruentReverseFirst
      Geo
      G Y
      G Y
      (hilbert_congruent_reflexive Geo G Y)

  have hGF_GY :
      HilbertSegmentLess Geo G F G Y :=
    hilbert_segmentLess_congruent_right
      Geo
      G F
      Y G
      G Y
      hGF_YG
      hYG_GY

  exact
    ⟨Y,
     hGKY,
     hKY_GF,
     hGF_GY⟩


/--
Local order helper for II.14.

If A-B-E and C-D-F, the terminal parts BE and DF are congruent,
and AE < CF, then AB < CD.

This is the strict-inequality cancellation fact needed below.
It is mathematically Book Zero material and should eventually be
promoted there rather than remain proposition-specific.
-/
theorem proposition2_14_less_cancel_right
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E C D F : Geo.Point)
    (hABE : Geo.Between A B E)
    (hCDF : Geo.Between C D F)
    (hBE_DF : Geo.Congruent B E D F)
    (hAE_CF : HilbertSegmentLess Geo A E C F) :
    HilbertSegmentLess Geo A B C D := by

  by_cases hAB_CD :
      HilbertSegmentLess Geo A B C D

  case pos =>
    exact hAB_CD

  case neg =>
    by_cases hCD_AB :
        HilbertSegmentLess Geo C D A B

    case pos =>
      have hDF_BE :
          Geo.Congruent D F B E :=
        hilbert_congruent_symmetry
          Geo B E D F hBE_DF

      have hCF_AE :
          HilbertSegmentLess Geo C F A E :=
        bookZero_53_lessThanAdditive
          Geo
          C D
          A B
          F E
          hCD_AB
          hCDF
          hABE
          hDF_BE

      exact
        False.elim
          ((bookZero_47_trichotomy2
              Geo A E C F hAE_CF)
            hCF_AE)

    case neg =>
      have hAB : Ne A B :=
        (HilbertOrder.between_incidence
          A B E hABE).1

      have hCD : Ne C D :=
        (HilbertOrder.between_incidence
          C D F hCDF).1

      have hAB_CD_cong :
          Geo.Congruent A B C D :=
        bookZero_31_trichotomy1
          Geo
          A B
          C D
          hAB_CD
          hCD_AB
          hAB
          hCD

      have hAE_CF_cong :
          Geo.Congruent A E C F :=
        bookZero_sumOfParts
          Geo
          A B E
          C D F
          hAB_CD_cong
          hBE_DF
          hABE
          hCDF

      have hCF_AE_cong :
          Geo.Congruent C F A E :=
        hilbert_congruent_symmetry
          Geo A E C F hAE_CF_cong

      have hAE_AE :
          HilbertSegmentLess Geo A E A E :=
        bookZero_30_lessThanCongruence
          Geo
          A E
          C F
          A E
          hAE_CF
          hCF_AE_cong

      exact
        False.elim
          ((bookZero_47_trichotomy2
              Geo A E A E hAE_AE)
            hAE_AE)

/--
Euclid II.14.

Construct the inside witness required by circle-circle continuity.

Assume GK is shorter than the sum GF + GF. Lay off GF from K on
the ray KG, obtaining X with

  KX ~= GF.

Then either X = G, or GX < GF. Thus X is on the circle centered at K
with radius GF and is inside (or at the center of) the circle centered
at G with radius GF.
-/
theorem proposition2_14_circle_inside_witness
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G K F : Geo.Point)
    (hGK : Ne G K)
    (_hGF : Ne G F)
    (hSum :
      HilbertSegmentSumGreater Geo G F G F G K) :
    Exists (fun X : Geo.Point =>
      Geo.Congruent K X G F /\
      (X = G \/
       HilbertSegmentLess Geo G X G F)) := by

  have hKG : Ne K G :=
    hGK.symm

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        G F
        K G
        hKG with
    ⟨X, hRayKGX, hKX_GF⟩

  rcases hSum with
    ⟨P, hGFP, hFP_GF, hGK_GP⟩

  rcases
      hilbert_sameRay_cases
        Geo K G X hRayKGX with
    hGX | hKGX | hKXG

  · exact
      Exists.intro
        X
        (And.intro
          hKX_GF
          (Or.inl hGX.symm))

  · have hXGK :
        Geo.Between X G K :=
      (HilbertOrder.between_incidence
        K G X hKGX).2.2.2.2

    have hXG_XK :
        HilbertSegmentLess Geo X G X K :=
      hilbert_segmentLess_of_between
        Geo X G K hXGK

    have hXG_GX :
        Geo.Congruent X G G X :=
      CongruentReverseFirst
        Geo
        G X
        G X
        (hilbert_congruent_reflexive Geo G X)

    have hGX_XG :
        Geo.Congruent G X X G :=
      CongruentReverseBoth
        Geo
        X G
        G X
        hXG_GX

    have hGX_XK :
        HilbertSegmentLess Geo G X X K :=
      hilbert_segmentLess_congruent_left
        Geo
        X G
        G X
        X K
        hXG_XK
        hGX_XG

    have hXK_GF :
        Geo.Congruent X K G F :=
      CongruentReverseFirst
        Geo
        K X
        G F
        hKX_GF

    have hGX_GF :
        HilbertSegmentLess Geo G X G F :=
      hilbert_segmentLess_congruent_right
        Geo
        G X
        X K
        G F
        hGX_XK
        hXK_GF

    exact
      Exists.intro
        X
        (And.intro
          hKX_GF
          (Or.inr hGX_GF))

  · have hGXK :
        Geo.Between G X K :=
      (HilbertOrder.between_incidence
        K X G hKXG).2.2.2.2

    have hPFG :
        Geo.Between P F G :=
      (HilbertOrder.between_incidence
        G F P hGFP).2.2.2.2

    have hXK_FG :
        Geo.Congruent X K F G :=
      CongruentReverseBoth
        Geo
        K X
        G F
        hKX_GF

    have hGP_PG :
        Geo.Congruent G P P G :=
      CongruentSwapSecond
        Geo
        G P
        G P
        (hilbert_congruent_reflexive Geo G P)

    have hGK_PG :
        HilbertSegmentLess Geo G K P G :=
      hilbert_segmentLess_congruent_right
        Geo
        G K
        G P
        P G
        hGK_GP
        hGP_PG

    have hGX_PF :
        HilbertSegmentLess Geo G X P F :=
      proposition2_14_less_cancel_right
        Geo
        G X K
        P F G
        hGXK
        hPFG
        hXK_FG
        hGK_PG

    have hPF_GF :
        Geo.Congruent P F G F :=
      CongruentReverseFirst
        Geo
        F P
        G F
        hFP_GF

    have hGX_GF :
        HilbertSegmentLess Geo G X G F :=
      hilbert_segmentLess_congruent_right
        Geo
        G X
        P F
        G F
        hGX_PF
        hPF_GF

    exact
      Exists.intro
        X
        (And.intro
          hKX_GF
          (Or.inr hGX_GF))


/--
Euclid II.14.

Construct the common point of the two equal circles used in the
semicircle step.

Assume:
* G-E-F,
* E is the midpoint of GK.

Then the two circles

  center G, radius GF
  center K, radius GF

have a common point H. The conclusion is expressed only by the two
radius congruences

  GH ~= GF
  KH ~= GF.

The proof uses:
* test11 for GK < GF + GF,
* test12 for the outside witness Y,
* test13 for the inside witness X,
* Hilbert circle-circle continuity.
-/
theorem proposition2_14_equal_circles_intersect
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G E F K : Geo.Point)
    (hGEF : Geo.Between G E F)
    (hMidE : HilbertIsMidpoint Geo E G K) :
    exists H : Geo.Point,
      Geo.Congruent G H G F /\
      Geo.Congruent K H G F := by

  have hGF : Ne G F :=
    (HilbertOrder.between_incidence
      G E F hGEF).2.2.1

  have hGK : Ne G K :=
    (HilbertOrder.between_incidence
      G E K hMidE.1).2.2.1

  have hSum :
      HilbertSegmentSumGreater Geo G F G F G K :=
    proposition2_14_centers_less_two_radii
      Geo
      G E F K
      hGEF
      hMidE

  rcases
      proposition2_14_circle_inside_witness
        Geo
        G K F
        hGK
        hGF
        hSum with
    ⟨X, hKX_GF, hXinside⟩

  rcases
      proposition2_14_circle_outside_witness
        Geo
        G K F
        hGK
        hGF with
    ⟨Y, _, hKY_GF, hYoutside⟩

  have hGF_KX :
      Geo.Congruent G F K X :=
    hilbert_congruent_symmetry
      Geo
      K X
      G F
      hKX_GF

  have hKX : Ne K X :=
    bookZero_nullSegment3
      Geo
      G F
      K X
      hGF
      hGF_KX

  have hXon2 :
      Geo.Congruent K X K X :=
    hilbert_congruent_reflexive
      Geo K X

  have hKY_KX :
      Geo.Congruent K Y K X :=
    hilbert_congruent_transitivity
      Geo
      K Y
      G F
      K X
      hKY_GF
      hGF_KX

  rcases
      hilbert_circle_circle_intersection
        Geo
        G F
        K X
        X Y
        hGF
        hKX
        hXon2
        hKY_KX
        hXinside
        hYoutside with
    ⟨H, hGH_GF, hKH_KX⟩

  have hKH_GF :
      Geo.Congruent K H G F :=
    hilbert_congruent_transitivity
      Geo
      K H
      K X
      G F
      hKH_KX
      hKX_GF

  exact
    ⟨H,
     hGH_GF,
     hKH_GF⟩


/--
Euclid II.14.

Assume the common circle point H is already known to lie off the
center line GE. Then H lies on the rectangle side line DE.

The argument is the perpendicular-bisector mechanism isolated in the
previous tests:

* test06: D is equidistant from G and K;
* test07: therefore ED is perpendicular to GK;
* circle data: H is equidistant from G and K;
* test07: therefore EH is perpendicular to GK;
* test10: the two perpendiculars through E are the same line.

The only fact deliberately not proved here is that H is off GE.
That one-dimensional circle fact is left for test16.
-/
theorem proposition2_14_circle_point_on_rectangle_axis
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E G F K H : Geo.Point)
    (base : Geo.Line)
    (hRect : IsRectangle Geo B C D E)
    (hBGE : Geo.Between B G E)
    (hMidE : HilbertIsMidpoint Geo E G K)
    (hGH_GF : Geo.Congruent G H G F)
    (hKH_GF : Geo.Congruent K H G F)
    (hGbase : HilbertIncidence.OnLine G base)
    (hEbase : HilbertIncidence.OnLine E base)
    (hHoff : Not (HilbertIncidence.OnLine H base)) :
    Collinear Geo D E H := by

  --------------------------------------------------------------------
  -- The base line is the line GE, and B also lies on it.
  --------------------------------------------------------------------

  have hGE : Ne G E :=
    (HilbertOrder.between_incidence
      B G E hBGE).2.1

  have hEG : Ne E G :=
    hGE.symm

  have hBGEcol :
      Collinear Geo B G E :=
    (HilbertOrder.between_incidence
      B G E hBGE).2.2.2.1

  have hGEB :
      Collinear Geo G E B :=
    PrimCollinearCycle
      Geo B G E hBGEcol

  have hBbase :
      HilbertIncidence.OnLine B base :=
    hilbert_collinear_on_line
      Geo
      G E B
      base
      hGE
      hGbase
      hEbase
      hGEB

  --------------------------------------------------------------------
  -- D is off the line GE because D,E,B are noncollinear vertices
  -- of the rectangle.
  --------------------------------------------------------------------

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo
      B C D E
      hRect.1

  have hDEB :
      Not (Collinear Geo D E B) :=
    hNC.2.2.2

  have hDoff :
      Not (HilbertIncidence.OnLine D base) := by
    intro hDbase
    exact
      hDEB
        (PrimCollinear.mk
          (Geo := Geo)
          hDbase
          hEbase
          hBbase)

  --------------------------------------------------------------------
  -- D is equidistant from the symmetric centers G,K.
  --------------------------------------------------------------------

  have hDG_DK :
      Geo.Congruent D G D K :=
    proposition2_14_rectangle_axis_equidistant
      Geo
      B C D E G K
      hRect
      hBGE
      hMidE

  have hEGD :
      Not (Collinear Geo E G D) :=
    hilbert_not_collinear_of_off_line
      Geo
      E G D
      base
      hEG
      hEbase
      hGbase
      hDoff

  have hRightD :
      HilbertRightAngle Geo G E D :=
    proposition2_14_equidistant_right_angle
      Geo
      G E K D
      hMidE
      hEGD
      hDG_DK

  --------------------------------------------------------------------
  -- H is also equidistant from G,K because it lies on both equal
  -- circles.
  --------------------------------------------------------------------

  have hHG_GF :
      Geo.Congruent H G G F :=
    CongruentReverseFirst
      Geo
      G H
      G F
      hGH_GF

  have hHK_GF :
      Geo.Congruent H K G F :=
    CongruentReverseFirst
      Geo
      K H
      G F
      hKH_GF

  have hGF_HK :
      Geo.Congruent G F H K :=
    hilbert_congruent_symmetry
      Geo
      H K
      G F
      hHK_GF

  have hHG_HK :
      Geo.Congruent H G H K :=
    hilbert_congruent_transitivity
      Geo
      H G
      G F
      H K
      hHG_GF
      hGF_HK

  have hEGH :
      Not (Collinear Geo E G H) :=
    hilbert_not_collinear_of_off_line
      Geo
      E G H
      base
      hEG
      hEbase
      hGbase
      hHoff

  have hRightH :
      HilbertRightAngle Geo G E H :=
    proposition2_14_equidistant_right_angle
      Geo
      G E K H
      hMidE
      hEGH
      hHG_HK

  --------------------------------------------------------------------
  -- Both ED and EH are perpendicular to the same line at E.
  --------------------------------------------------------------------

  exact
    proposition2_14_right_angle_axis_collinear
      Geo
      G E D H
      base
      hGE
      hGbase
      hEbase
      hDoff
      hHoff
      hRightD
      hRightH


/--
Euclid II.14.

A common point H of the two equal circles cannot lie on the line of
their centers in the II.14 configuration.

Assume:
* G-E-F,
* E is the midpoint of GK,
* GH ~= GF,
* KH ~= GF.

If H lay on line GK, the order trichotomy for G,K,H gives three cases.

* G-K-H: KH is a proper part of GH, contradicting GH ~= KH.
* K-G-H: GH is a proper part of KH, contradicting GH ~= KH.
* G-H-K: H is inside GK. Comparing H with the known midpoint E,
  every H != E order gives opposite strict inequalities between the
  two half-segments. Hence H = E. But then GE ~= GF, contradicting
  G-E-F.

Thus H is off the center line.
-/
theorem proposition2_14_circle_point_off_center_line
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (G E F K H : Geo.Point)
    (base : Geo.Line)
    (hGEF : Geo.Between G E F)
    (hMidE : HilbertIsMidpoint Geo E G K)
    (hGH_GF : Geo.Congruent G H G F)
    (hKH_GF : Geo.Congruent K H G F)
    (hGbase : HilbertIncidence.OnLine G base)
    (hEbase : HilbertIncidence.OnLine E base) :
    Not (HilbertIncidence.OnLine H base) := by

  have hGEK :
      Geo.Between G E K :=
    hMidE.1

  have hGE_EK :
      Geo.Congruent G E E K :=
    hMidE.2

  have hGE : Ne G E :=
    (HilbertOrder.between_incidence
      G E K hGEK).1

  have hGK : Ne G K :=
    (HilbertOrder.between_incidence
      G E K hGEK).2.2.1

  have hGF : Ne G F :=
    (HilbertOrder.between_incidence
      G E F hGEF).2.2.1

  have hGE_GF :
      HilbertSegmentLess Geo G E G F :=
    hilbert_segmentLess_of_between
      Geo
      G E F
      hGEF

  have hGF_KH :
      Geo.Congruent G F K H :=
    hilbert_congruent_symmetry
      Geo
      K H
      G F
      hKH_GF

  have hGH_KH :
      Geo.Congruent G H K H :=
    hilbert_congruent_transitivity
      Geo
      G H
      G F
      K H
      hGH_GF
      hGF_KH

  have hHG_HK :
      Geo.Congruent H G H K :=
    CongruentReverseBoth
      Geo
      G H
      K H
      hGH_KH

  have hGF_GH :
      Geo.Congruent G F G H :=
    hilbert_congruent_symmetry
      Geo
      G H
      G F
      hGH_GF

  have hGH : Ne G H :=
    bookZero_nullSegment3
      Geo
      G F
      G H
      hGF
      hGF_GH

  have hKH : Ne K H :=
    bookZero_nullSegment3
      Geo
      G F
      K H
      hGF
      hGF_KH

  have hGEKcol :
      Collinear Geo G E K :=
    (HilbertOrder.between_incidence
      G E K hGEK).2.2.2.1

  have hKbase :
      HilbertIncidence.OnLine K base :=
    hilbert_collinear_on_line
      Geo
      G E K
      base
      hGE
      hGbase
      hEbase
      hGEKcol

  intro hHbase

  have hGKHcol :
      Collinear Geo G K H :=
    PrimCollinear.mk
      (Geo := Geo)
      hGbase
      hKbase
      hHbase

  rcases
      hilbert_between_trichotomy
        Geo
        G K H
        hGK
        hKH
        hGH
        hGKHcol with
    hGKH | hKGH | hGHK

  --------------------------------------------------------------------
  -- Case 1: G-K-H.
  --------------------------------------------------------------------

  · have hHKG :
        Geo.Between H K G :=
      (HilbertOrder.between_incidence
        G K H hGKH).2.2.2.2

    have hHK_HG :
        HilbertSegmentLess Geo H K H G :=
      hilbert_segmentLess_of_between
        Geo
        H K G
        hHKG

    have hHK_HG_cong :
        Geo.Congruent H K H G :=
      hilbert_congruent_symmetry
        Geo
        H G
        H K
        hHG_HK

    exact
      (hilbert_segmentLess_not_congruent
        Geo
        H K
        H G
        hHK_HG)
        hHK_HG_cong

  --------------------------------------------------------------------
  -- Case 2: K-G-H.
  --------------------------------------------------------------------

  · have hHGK :
        Geo.Between H G K :=
      (HilbertOrder.between_incidence
        K G H hKGH).2.2.2.2

    have hHG_HK_less :
        HilbertSegmentLess Geo H G H K :=
      hilbert_segmentLess_of_between
        Geo
        H G K
        hHGK

    exact
      (hilbert_segmentLess_not_congruent
        Geo
        H G
        H K
        hHG_HK_less)
        hHG_HK

  --------------------------------------------------------------------
  -- Case 3: G-H-K.
  --------------------------------------------------------------------

  · by_cases hHE : H = E

    · subst H

      exact
        (hilbert_segmentLess_not_congruent
          Geo
          G E
          G F
          hGE_GF)
          hGH_GF

    · have hEH : Ne E H := by
        intro hEH
        exact hHE hEH.symm

      have hGEHcol :
          Collinear Geo G E H :=
        PrimCollinear.mk
          (Geo := Geo)
          hGbase
          hEbase
          hHbase

      rcases
          hilbert_between_trichotomy
            Geo
            G E H
            hGE
            hEH
            hGH
            hGEHcol with
        hGEH | hEGH | hGHE

      --------------------------------------------------------------
      -- Subcase 3a: G-E-H-K.
      --------------------------------------------------------------

      · have hEHK :
            Geo.Between E H K :=
          (hilbert_between_inner_trans
            Geo
            G E H K
            hGEH
            hGHK).1

        have hKHE :
            Geo.Between K H E :=
          (HilbertOrder.between_incidence
            E H K hEHK).2.2.2.2

        have hGE_GH :
            HilbertSegmentLess Geo G E G H :=
          hilbert_segmentLess_of_between
            Geo
            G E H
            hGEH

        have hEK_GE :
            Geo.Congruent E K G E :=
          hilbert_congruent_symmetry
            Geo
            G E
            E K
            hGE_EK

        have hEK_GH :
            HilbertSegmentLess Geo E K G H :=
          hilbert_segmentLess_congruent_left
            Geo
            G E
            E K
            G H
            hGE_GH
            hEK_GE

        have hEK_KH :
            HilbertSegmentLess Geo E K K H :=
          hilbert_segmentLess_congruent_right
            Geo
            E K
            G H
            K H
            hEK_GH
            hGH_KH

        have hKH_KE :
            HilbertSegmentLess Geo K H K E :=
          hilbert_segmentLess_of_between
            Geo
            K H E
            hKHE

        have hKE_EK :
            Geo.Congruent K E E K :=
          CongruentReverseFirst
            Geo
            E K
            E K
            (hilbert_congruent_reflexive Geo E K)

        have hKH_EK :
            HilbertSegmentLess Geo K H E K :=
          hilbert_segmentLess_congruent_right
            Geo
            K H
            K E
            E K
            hKH_KE
            hKE_EK

        exact
          (hilbert_segmentLess_asymm
            Geo
            E K
            K H
            hEK_KH)
            hKH_EK

      --------------------------------------------------------------
      -- Subcase 3b: E-G-H. Together with G-H-K this gives E-G-K,
      -- contradicting the known order G-E-K.
      --------------------------------------------------------------

      · have hEGK :
            Geo.Between E G K :=
          (hilbert_between_outer_trans
            Geo
            E G H K
            hEGH
            hGHK).2

        have hNotEGK :
            Not (Geo.Between E G K) :=
          (HilbertOrder.between_unique
            G E K
            hGEKcol
            hGEK).1

        exact hNotEGK hEGK

      --------------------------------------------------------------
      -- Subcase 3c: G-H-E-K.
      --------------------------------------------------------------

      · have hHEK :
            Geo.Between H E K :=
          (hilbert_between_inner_trans
            Geo
            G H E K
            hGHE
            hGEK).1

        have hKEH :
            Geo.Between K E H :=
          (HilbertOrder.between_incidence
            H E K hHEK).2.2.2.2

        have hGH_GE :
            HilbertSegmentLess Geo G H G E :=
          hilbert_segmentLess_of_between
            Geo
            G H E
            hGHE

        have hKH_GH :
            Geo.Congruent K H G H :=
          hilbert_congruent_symmetry
            Geo
            G H
            K H
            hGH_KH

        have hKH_GE :
            HilbertSegmentLess Geo K H G E :=
          hilbert_segmentLess_congruent_left
            Geo
            G H
            K H
            G E
            hGH_GE
            hKH_GH

        have hKH_EK :
            HilbertSegmentLess Geo K H E K :=
          hilbert_segmentLess_congruent_right
            Geo
            K H
            G E
            E K
            hKH_GE
            hGE_EK

        have hKE_KH :
            HilbertSegmentLess Geo K E K H :=
          hilbert_segmentLess_of_between
            Geo
            K E H
            hKEH

        have hKE_EK :
            Geo.Congruent K E E K :=
          CongruentReverseFirst
            Geo
            E K
            E K
            (hilbert_congruent_reflexive Geo E K)

        have hEK_KE :
            Geo.Congruent E K K E :=
          CongruentSwapSecond
            Geo
            E K
            E K
            (hilbert_congruent_reflexive Geo E K)

        have hEK_KH :
            HilbertSegmentLess Geo E K K H :=
          hilbert_segmentLess_congruent_left
            Geo
            K E
            E K
            K H
            hKE_KH
            hEK_KE

        exact
          (hilbert_segmentLess_asymm
            Geo
            K H
            E K
            hKH_EK)
            hEK_KH


/--
Euclid II.14.

Assemble the circle construction and the perpendicular-bisector
arguments.

Assume the non-square branch of the II.14 configuration:
* B-G-E,
* G-E-F,
* E is the midpoint of GK,
* BCDE is a rectangle.

Then there exists a point H such that
* GH ~= GF,
* KH ~= GF,
* D,E,H are collinear.

This is the first test in which the point produced by circle-circle
continuity is connected back to the rectangle geometry.
-/
theorem proposition2_14_circle_point_on_DE
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E G F K : Geo.Point)
    (hRect : IsRectangle Geo B C D E)
    (hBGE : Geo.Between B G E)
    (hGEF : Geo.Between G E F)
    (hMidE : HilbertIsMidpoint Geo E G K) :
    exists H : Geo.Point,
      Geo.Congruent G H G F /\
      Geo.Congruent K H G F /\
      Collinear Geo D E H := by

  have hGE : Ne G E :=
    (HilbertOrder.between_incidence
      B G E hBGE).2.1

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        G E hGE with
    ⟨base, hGbase, hEbase⟩

  rcases
      proposition2_14_equal_circles_intersect
        Geo
        G E F K
        hGEF
        hMidE with
    ⟨H, hGH_GF, hKH_GF⟩

  have hHoff :
      Not (HilbertIncidence.OnLine H base) :=
    proposition2_14_circle_point_off_center_line
      Geo
      G E F K H
      base
      hGEF
      hMidE
      hGH_GF
      hKH_GF
      hGbase
      hEbase

  have hDEH :
      Collinear Geo D E H :=
    proposition2_14_circle_point_on_rectangle_axis
      Geo
      B C D E G F K H
      base
      hRect
      hBGE
      hMidE
      hGH_GF
      hKH_GF
      hGbase
      hEbase
      hHoff

  exact
    ⟨H,
     hGH_GF,
     hKH_GF,
     hDEH⟩


/--
Euclid II.14.

Orient a copy of the segment EH on the extension of DE beyond E.

Given D != E and an arbitrary point H, construct H' such that

  D-E-H'
  EH' ~= EH.

This is a purely neutral one-dimensional construction:
extend DE beyond E, then lay off EH on the resulting ray.
-/
theorem proposition2_14_oriented_copy_on_extension
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (D E H : Geo.Point)
    (hDE : Ne D E) :
    exists H' : Geo.Point,
      Geo.Between D E H' /\
      Geo.Congruent E H' E H := by

  rcases
      HilbertOrder.between_extension
        (Geo := Geo)
        D E hDE with
    ⟨X, hDEX⟩

  have hEX : Ne E X :=
    (HilbertOrder.between_incidence
      (Geo := Geo)
      D E X hDEX).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        E H
        E X
        hEX with
    ⟨H', hRayEXH', hEH'_EH⟩

  have hRayEDD :
      HilbertSameRay Geo E D D :=
    hilbert_sameRay_refl
      Geo
      E D
      hDE

  have hDEH' :
      Geo.Between D E H' :=
    hilbert_between_transport_sameRays
      Geo
      D E X
      D H'
      hDEX
      hRayEDD
      hRayEXH'

  exact
    ⟨H',
     hDEH',
     hEH'_EH⟩


/--
Euclid II.14.

The oriented replacement H' from test18 remains on both equal circles.

Assume:
* BCDE is a rectangle,
* B-G-E and G-E-F,
* E is the midpoint of GK,
* H is a common point of the circles centered at G and K with radius GF,
* D,E,H are collinear,
* D-E-H' and EH' ~= EH.

Then

  GH' ~= GF
  KH' ~= GF.

The proof uses two SAS arguments at the right angle through E.
-/
theorem proposition2_14_oriented_point_stays_on_circles
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E G F K H H' : Geo.Point)
    (hRect : IsRectangle Geo B C D E)
    (hBGE : Geo.Between B G E)
    (hGEF : Geo.Between G E F)
    (hMidE : HilbertIsMidpoint Geo E G K)
    (hGH_GF : Geo.Congruent G H G F)
    (hKH_GF : Geo.Congruent K H G F)
    (_hDEH : Collinear Geo D E H)
    (hDEH' : Geo.Between D E H')
    (hEH'_EH : Geo.Congruent E H' E H) :
    Geo.Congruent G H' G F /\
    Geo.Congruent K H' G F := by

  --------------------------------------------------------------------
  -- The center line GE.
  --------------------------------------------------------------------

  have hGE : Ne G E :=
    (HilbertOrder.between_incidence
      B G E hBGE).2.1

  have hEG : Ne E G :=
    hGE.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        G E hGE with
    ⟨base, hGbase, hEbase⟩

  --------------------------------------------------------------------
  -- The original circle point H is off GE and hence GEH is right.
  --------------------------------------------------------------------

  have hHoff :
      Not (HilbertIncidence.OnLine H base) :=
    proposition2_14_circle_point_off_center_line
      Geo
      G E F K H
      base
      hGEF
      hMidE
      hGH_GF
      hKH_GF
      hGbase
      hEbase

  have hEGH :
      Not (Collinear Geo E G H) :=
    hilbert_not_collinear_of_off_line
      Geo
      E G H
      base
      hEG
      hEbase
      hGbase
      hHoff

  have hHG_GF :
      Geo.Congruent H G G F :=
    CongruentReverseFirst
      Geo
      G H
      G F
      hGH_GF

  have hHK_GF :
      Geo.Congruent H K G F :=
    CongruentReverseFirst
      Geo
      K H
      G F
      hKH_GF

  have hGF_HK :
      Geo.Congruent G F H K :=
    hilbert_congruent_symmetry
      Geo
      H K
      G F
      hHK_GF

  have hHG_HK :
      Geo.Congruent H G H K :=
    hilbert_congruent_transitivity
      Geo
      H G
      G F
      H K
      hHG_GF
      hGF_HK

  have hRightGEH :
      HilbertRightAngle Geo G E H :=
    proposition2_14_equidistant_right_angle
      Geo
      G E K H
      hMidE
      hEGH
      hHG_HK

  --------------------------------------------------------------------
  -- The oriented point H' gives the desired strict order D-E-H'.
  -- Therefore GEH' is right by test04.
  --------------------------------------------------------------------

  have hRightGEH' :
      HilbertRightAngle Geo G E H' :=
    proposition2_14_right_triangle_after_H
      Geo
      B C D E G F H'
      hRect
      hBGE
      hGEF
      hDEH'

  --------------------------------------------------------------------
  -- Noncollinearity of E,G,H'.
  --
  -- First D is off the center line GE. If E,G,H' were collinear,
  -- D-E-H' would force D onto GE as well.
  --------------------------------------------------------------------

  have hBGEcol :
      Collinear Geo B G E :=
    (HilbertOrder.between_incidence
      B G E hBGE).2.2.2.1

  have hGEB :
      Collinear Geo G E B :=
    PrimCollinearCycle
      Geo
      B G E
      hBGEcol

  have hBbase :
      HilbertIncidence.OnLine B base :=
    hilbert_collinear_on_line
      Geo
      G E B
      base
      hGE
      hGbase
      hEbase
      hGEB

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo
      B C D E
      hRect.1

  have hDEB :
      Not (Collinear Geo D E B) :=
    hNC.2.2.2

  have hDoff :
      Not (HilbertIncidence.OnLine D base) := by
    intro hDbase
    exact
      hDEB
        (PrimCollinear.mk
          (Geo := Geo)
          hDbase
          hEbase
          hBbase)

  have hDEH'col :
      PrimCollinear Geo D E H' :=
    (HilbertOrder.between_incidence
      D E H' hDEH').2.2.2.1

  have hEH' : Ne E H' :=
    (HilbertOrder.between_incidence
      D E H' hDEH').2.1

  have hEGH' :
      Not (Collinear Geo E G H') := by
    intro hEGH'col

    have hGEH'col :
        PrimCollinear Geo G E H' :=
      PrimCollinearSwap
        Geo
        E G H'
        hEGH'col

    have hEH'D :
        PrimCollinear Geo E H' D :=
      PrimCollinearCycle
        Geo
        D E H'
        hDEH'col

    have hGED :
        PrimCollinear Geo G E D :=
      hilbert_primCollinear_trans
        Geo
        G E H' D
        hEH'
        hGEH'col
        hEH'D

    exact
      hDoff
        (hilbert_collinear_on_line
          Geo
          G E D
          base
          hGE
          hGbase
          hEbase
          hGED)

  have hGEH_prim :
      Not (PrimCollinear Geo G E H) := by
    intro h
    exact
      hEGH
        (PrimCollinearSwap
          Geo
          G E H
          h)

  have hGEH'_prim :
      Not (PrimCollinear Geo G E H') := by
    intro h
    exact
      hEGH'
        (PrimCollinearSwap
          Geo
          G E H'
          h)

  --------------------------------------------------------------------
  -- First SAS:
  --
  --   triangle E-G-H'  ~=  triangle E-G-H
  --
  -- EG is common, EH' ~= EH, and both included angles are right.
  --------------------------------------------------------------------

  have hAngleH'_H :
      Geo.AngleCongruent G E H' G E H :=
    hilbert_all_right_angles_congruent
      Geo
      G E H'
      G E H
      hGEH'_prim
      hGEH_prim
      hRightGEH'
      hRightGEH

  have hEG_EG :
      Geo.Congruent E G E G :=
    hilbert_congruent_reflexive
      Geo
      E G

  have hTriangles1 :
      TriangleCongruenceResult
        Geo
        E G H'
        E G H :=
    SAS
      Geo
      E G H'
      E G H
      hEGH'
      hEGH
      hEG_EG
      hAngleH'_H
      hEH'_EH

  have hGH'_GH :
      Geo.Congruent G H' G H :=
    hTriangles1.sideBC

  have hGH'_GF :
      Geo.Congruent G H' G F :=
    hilbert_congruent_transitivity
      Geo
      G H'
      G H
      G F
      hGH'_GH
      hGH_GF

  --------------------------------------------------------------------
  -- Second SAS: H' lies on the perpendicular bisector of GK.
  --
  -- Compare E-G-H' and E-K-H'.
  --------------------------------------------------------------------

  have hGEK :
      Geo.Between G E K :=
    hMidE.1

  have hGE_EK :
      Geo.Congruent G E E K :=
    hMidE.2

  have hEG_EK :
      Geo.Congruent E G E K :=
    CongruentReverseFirst
      Geo
      G E
      E K
      hGE_EK

  have hGEH'_H'EK :
      Geo.AngleCongruent G E H' H' E K :=
    hilbert_right_angle_opposite_extension
      Geo
      G E H' K
      hGEH'_prim
      hRightGEH'
      hGEK

  have hGEH'_KEH' :
      Geo.AngleCongruent G E H' K E H' :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      G E H'
      H' E K).mp
      hGEH'_H'EK

  have hEKH' :
      Not (Collinear Geo E K H') := by
    intro hEKH'col

    have hGEKcol :
        PrimCollinear Geo G E K :=
      (HilbertOrder.between_incidence
        G E K hGEK).2.2.2.1

    have hEK : Ne E K :=
      (HilbertOrder.between_incidence
        G E K hGEK).2.1

    have hGEH'col :
        PrimCollinear Geo G E H' :=
      hilbert_primCollinear_trans
        Geo
        G E K H'
        hEK
        hGEKcol
        hEKH'col

    exact hGEH'_prim hGEH'col

  have hEH'_EH' :
      Geo.Congruent E H' E H' :=
    hilbert_congruent_reflexive
      Geo
      E H'

  have hTriangles2 :
      TriangleCongruenceResult
        Geo
        E G H'
        E K H' :=
    SAS
      Geo
      E G H'
      E K H'
      hEGH'
      hEKH'
      hEG_EK
      hGEH'_KEH'
      hEH'_EH'

  have hGH'_KH' :
      Geo.Congruent G H' K H' :=
    hTriangles2.sideBC

  have hKH'_GH' :
      Geo.Congruent K H' G H' :=
    hilbert_congruent_symmetry
      Geo
      G H'
      K H'
      hGH'_KH'

  have hKH'_GF :
      Geo.Congruent K H' G F :=
    hilbert_congruent_transitivity
      Geo
      K H'
      G H'
      G F
      hKH'_GH'
      hGH'_GF

  exact
    ⟨hGH'_GF,
     hKH'_GF⟩


/--
Euclid II.14.

Package the oriented circle point needed by the classical construction.

From the rectangle configuration, the extension G-E-F, and the midpoint
E of GK, construct H such that

  D-E-H,
  GH ~= GF,
  KH ~= GF.

This combines:
* test17: an arbitrary common point of the two equal circles lies on DE;
* test18: replace it by an equal segment on the extension of DE beyond E;
* test19: the oriented replacement remains on both circles.
-/
theorem proposition2_14_oriented_circle_point
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E G F K : Geo.Point)
    (hRect : IsRectangle Geo B C D E)
    (hBGE : Geo.Between B G E)
    (hGEF : Geo.Between G E F)
    (hMidE : HilbertIsMidpoint Geo E G K) :
    exists H : Geo.Point,
      Geo.Between D E H /\
      Geo.Congruent G H G F /\
      Geo.Congruent K H G F := by

  --------------------------------------------------------------------
  -- First obtain an arbitrary common circle point on the carrier DE.
  --------------------------------------------------------------------

  rcases
      proposition2_14_circle_point_on_DE
        Geo
        B C D E G F K
        hRect
        hBGE
        hGEF
        hMidE with
    ⟨H0, hGH0_GF, hKH0_GF, hDEH0⟩

  --------------------------------------------------------------------
  -- D and E are distinct because they are adjacent rectangle vertices.
  --------------------------------------------------------------------

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo
      B C D E
      hRect.1

  have hDEB :
      Not (Collinear Geo D E B) :=
    hNC.2.2.2

  have hDE : Ne D E :=
    hilbert_noncollinear_ne_first
      Geo
      D E B
      hDEB

  --------------------------------------------------------------------
  -- Copy EH0 onto the ray from E opposite D.
  --------------------------------------------------------------------

  rcases
      proposition2_14_oriented_copy_on_extension
        Geo
        D E H0
        hDE with
    ⟨H, hDEH, hEH_EH0⟩

  --------------------------------------------------------------------
  -- The copied point is still on both equal circles.
  --------------------------------------------------------------------

  have hCircles :
      Geo.Congruent G H G F /\
      Geo.Congruent K H G F :=
    proposition2_14_oriented_point_stays_on_circles
      Geo
      B C D E G F K H0 H
      hRect
      hBGE
      hGEF
      hMidE
      hGH0_GF
      hKH0_GF
      hDEH0
      hDEH
      hEH_EH0

  exact
    ⟨H,
     hDEH,
     hCircles.1,
     hCircles.2⟩


/--
Euclid II.14.

Repackage the unequal-side construction in exactly the orientation required
for Proposition II.5.

From ED < BE, test02 gives points F,G with

  B-G-E-F,
  G midpoint of BF,
  EF ~= ED.

For II.5 we use the reversed baseline

  F-E-G-B,

so the required inputs are

  F-E-G,
  G midpoint of FB.

This theorem records both the original II.14 orientation and the II.5
orientation.
-/
theorem proposition2_14_ii5_baseline
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B E D : Geo.Point)
    (hShort : HilbertSegmentLess Geo E D B E) :
    exists F G : Geo.Point,
      Geo.Between B G E /\
      Geo.Between G E F /\
      Geo.Between F E G /\
      HilbertIsMidpoint Geo G F B /\
      Geo.Congruent E F E D := by

  rcases
      proposition2_14_unequal_side_order
        Geo
        B E D
        hShort with
    ⟨F, G,
      hBGE,
      hGEF,
      _hBEF,
      hMidBF,
      hEF_ED⟩

  --------------------------------------------------------------------
  -- Reverse G-E-F to obtain the II.5 internal cut F-E-G.
  --------------------------------------------------------------------

  have hFEG :
      Geo.Between F E G :=
    (HilbertOrder.between_incidence
      G E F hGEF).2.2.2.2

  --------------------------------------------------------------------
  -- Reverse the midpoint orientation:
  --
  --   G midpoint of BF
  -- becomes
  --   G midpoint of FB.
  --------------------------------------------------------------------

  have hFGB :
      Geo.Between F G B :=
    (HilbertOrder.between_incidence
      B G F hMidBF.1).2.2.2.2

  have hBG_GF :
      Geo.Congruent B G G F :=
    hMidBF.2

  have hGB_FG :
      Geo.Congruent G B F G :=
    CongruentReverseBoth
      Geo
      B G
      G F
      hBG_GF

  have hFG_GB :
      Geo.Congruent F G G B :=
    hilbert_congruent_symmetry
      Geo
      G B
      F G
      hGB_FG

  have hMidFB :
      HilbertIsMidpoint Geo G F B :=
    ⟨hFGB, hFG_GB⟩

  exact
    ⟨F, G,
     hBGE,
     hGEF,
     hFEG,
     hMidFB,
     hEF_ED⟩


/--
Euclid II.14 -- local rectangle-cut helper, step 1.

Core cut constructor for an arbitrary rectangle.

Given

    D -------- E
    |          |
    |          |
    B --- M -- C

with B-M-C, construct L so that

    D --- L --- E
    |     |     |
    |     |     |
    B --- M --- C

and both pieces are parallelograms.

This is the generic version of the square-cut geometry used in I.47.
No betweenness D-L-E or diagonal intersection is proved yet.
-/
private theorem proposition2_14_rectangle_cut_core_aux
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C) :
    exists L : Geo.Point,
      Collinear Geo D L E /\
      IsParallelogram Geo L D B M /\
      IsParallelogram Geo C E L M := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hBM : Ne B M :=
    hBMCdata.1

  have hMC : Ne M C :=
    hBMCdata.2.1

  have hBC : Ne B C :=
    hBMCdata.2.2.1

  have hBMCcol :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  have hBCMcol :
      Collinear Geo B C M :=
    PrimCollinearRotate
      Geo B M C hBMCcol

  --------------------------------------------------------------------
  -- C,E,M are noncollinear.
  --------------------------------------------------------------------

  have hRectNC :=
    parallelogram_vertices_noncollinear
      Geo B C E D hRect.1

  have hBCE :
      Not (Collinear Geo B C E) :=
    hRectNC.2.1

  have hCEM :
      Not (Collinear Geo C E M) := by
    intro hCEMcol

    have hCME :
        Collinear Geo C M E :=
      PrimCollinearRotate
        Geo C E M hCEMcol

    have hBCEcol :
        Collinear Geo B C E :=
      hilbert_primCollinear_trans
        Geo
        B C M E
        hMC.symm
        hBCMcol
        hCME

    exact hBCE hBCEcol

  --------------------------------------------------------------------
  -- Complete C-E-M to the parallelogram C-E-L-M.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo C E M hCEM with
    ⟨L, hRightPar⟩

  --------------------------------------------------------------------
  -- First show that EL is parallel to BC.
  --
  -- Right cut: EL || MC.
  -- Since B,M,C are collinear, MC has the same carrier as BC.
  --------------------------------------------------------------------

  have hParMC_EL :
      Geo.Parallel M C E L :=
    ParallelSymmetry
      Geo
      E L M C
      hRightPar.2

  have hParBC_EL :
      Geo.Parallel B C E L :=
    ParallelCollinearLeft
      Geo
      M C B
      E L
      hBC
      hParMC_EL
      hBMCcol

  have hParEL_BC :
      Geo.Parallel E L B C :=
    ParallelSymmetry
      Geo B C E L hParBC_EL

  --------------------------------------------------------------------
  -- The upper side ED of the original rectangle is also parallel BC.
  --------------------------------------------------------------------

  have hParBC_ED :
      Geo.Parallel B C E D :=
    hRect.1.1

  have hParED_BC :
      Geo.Parallel E D B C :=
    ParallelSymmetry
      Geo B C E D hParBC_ED

  --------------------------------------------------------------------
  -- EL and ED pass through E and are both parallel to BC.
  -- Hilbert IV identifies their incidence carriers.
  --------------------------------------------------------------------

  have hEL : Ne E L :=
    hParEL_BC.1

  have hED : Ne E D :=
    hParED_BC.1

  rcases
      HilbertPlaneIncidence.line_through
        B C hBC with
    ⟨lineBC, hBbc, hCbc⟩

  rcases
      HilbertPlaneIncidence.line_through
        E D hED with
    ⟨lineED, hEed, hDed⟩

  rcases
      HilbertPlaneIncidence.line_through
        E L hEL with
    ⟨lineEL, hEel, hLel⟩

  have hLinesED_BC :
      HilbertLinesDisjoint Geo lineED lineBC := by
    rintro ⟨X, hXed, hXbc⟩

    have hXED :
        X ∈ Geo.PointLine E D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo E D X lineED
        hED hEed hDed).mpr hXed

    have hXBC :
        X ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X lineBC
        hBC hBbc hCbc).mpr hXbc

    exact
      Set.disjoint_left.mp
        hParED_BC.2.2
        hXED hXBC

  have hLinesEL_BC :
      HilbertLinesDisjoint Geo lineEL lineBC := by
    rintro ⟨X, hXel, hXbc⟩

    have hXEL :
        X ∈ Geo.PointLine E L :=
      (hilbert_mem_pointLine_iff_onLine
        Geo E L X lineEL
        hEL hEel hLel).mpr hXel

    have hXBC :
        X ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X lineBC
        hBC hBbc hCbc).mpr hXbc

    exact
      Set.disjoint_left.mp
        hParEL_BC.2.2
        hXEL hXBC

  have hEoffBC :
      Not (HilbertIncidence.OnLine E lineBC) := by
    intro hEbc
    exact
      hLinesED_BC
        ⟨E, hEed, hEbc⟩

  have hLineED_EL :
      lineED = lineEL :=
    HilbertEuclideanPlane.parallel_unique
      (Geo := Geo)
      lineBC
      E
      hEoffBC
      lineED
      lineEL
      hEed
      hLinesED_BC
      hEel
      hLinesEL_BC

  have hLed :
      HilbertIncidence.OnLine L lineED := by
    rw [hLineED_EL]
    exact hLel

  have hDLEcol :
      Collinear Geo D L E :=
    ⟨lineED, hDed, hLed, hEed⟩

  --------------------------------------------------------------------
  -- L is distinct from D.
  --
  -- Otherwise DB and DM would be two parallels through D to CE.
  -- Their carriers would coincide, putting D,B,M,C on one line,
  -- contradicting the rectangle.
  --------------------------------------------------------------------

  have hLD : Ne L D := by
    intro hLD_eq
    subst L

    have hParDB_CE :
        Geo.Parallel D B C E :=
      ParallelSymmetry
        Geo C E D B hRect.1.2

    have hParDM_CE :
        Geo.Parallel D M C E :=
      ParallelSymmetry
        Geo C E D M hRightPar.1

    have hCarrier :
        Geo.PointLine D B =
        Geo.PointLine D M := by
      by_contra hDistinct

      have hDB_DM :
          Geo.Parallel D B D M :=
        hilbert_parallel_transitive_distinct
          Geo
          D B
          D M
          C E
          hParDB_CE
          hParDM_CE
          hDistinct

      exact
        (intersection_test_not_parallel_of_common_point
          Geo
          D B
          D M
          D
          (intersection_test_left_mem Geo D B)
          (intersection_test_left_mem Geo D M))
          hDB_DM

    have hDB : Ne D B :=
      hParDB_CE.1

    rcases
        HilbertPlaneIncidence.line_through
          D B hDB with
      ⟨lineDB, hDdb, hBdb⟩

    have hM_DM :
        M ∈ Geo.PointLine D M :=
      intersection_test_right_mem
        Geo D M

    have hM_DB :
        M ∈ Geo.PointLine D B := by
      rw [hCarrier]
      exact hM_DM

    have hMdb :
        HilbertIncidence.OnLine M lineDB :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D B M lineDB
        hDB hDdb hBdb).mp hM_DB

    have hDBM :
        Collinear Geo D B M :=
      ⟨lineDB, hDdb, hBdb, hMdb⟩

    have hDBC :
        Collinear Geo D B C :=
      hilbert_primCollinear_trans
        Geo
        D B M C
        hBM
        hDBM
        hBMCcol

    exact hRectNC.1 hDBC

  --------------------------------------------------------------------
  -- First opposite pair of the left piece:
  --
  --     LD || BM.
  --------------------------------------------------------------------

  have hLEDcol :
      Collinear Geo L E D :=
    PrimCollinearCycle
      Geo D L E hDLEcol

  have hParLD_BC :
      Geo.Parallel L D B C :=
    ParallelCollinearLeft
      Geo
      E D L
      B C
      hLD
      hParED_BC
      hLEDcol

  have hParBC_LD :
      Geo.Parallel B C L D :=
    ParallelSymmetry
      Geo L D B C hParLD_BC

  have hParBM_LD :
      Geo.Parallel B M L D :=
    collinear_parallel_trans
      Geo
      B M C
      L D
      hBM
      hBMCcol
      hParBC_LD

  have hParLD_BM :
      Geo.Parallel L D B M :=
    ParallelSymmetry
      Geo B M L D hParBM_LD

  --------------------------------------------------------------------
  -- Second opposite pair:
  --
  --     DB || ML.
  --------------------------------------------------------------------

  have hParDB_CE :
      Geo.Parallel D B C E :=
    ParallelSymmetry
      Geo C E D B hRect.1.2

  have hParLM_CE :
      Geo.Parallel L M C E :=
    ParallelSymmetry
      Geo C E L M hRightPar.1

  have hDistinctDB_LM :
      Geo.PointLine D B ≠
      Geo.PointLine L M := by
    intro hCarrier

    have hDB : Ne D B :=
      hParDB_CE.1

    rcases
        HilbertPlaneIncidence.line_through
          D B hDB with
      ⟨lineDB, hDdb, hBdb⟩

    have hM_LM :
        M ∈ Geo.PointLine L M :=
      intersection_test_right_mem
        Geo L M

    have hM_DB :
        M ∈ Geo.PointLine D B := by
      rw [hCarrier]
      exact hM_LM

    have hMdb :
        HilbertIncidence.OnLine M lineDB :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D B M lineDB
        hDB hDdb hBdb).mp hM_DB

    have hDBM :
        Collinear Geo D B M :=
      ⟨lineDB, hDdb, hBdb, hMdb⟩

    have hDBC :
        Collinear Geo D B C :=
      hilbert_primCollinear_trans
        Geo
        D B M C
        hBM
        hDBM
        hBMCcol

    exact hRectNC.1 hDBC

  have hParDB_LM :
      Geo.Parallel D B L M :=
    hilbert_parallel_transitive_distinct
      Geo
      D B
      L M
      C E
      hParDB_CE
      hParLM_CE
      hDistinctDB_LM

  have hParDB_ML :
      Geo.Parallel D B M L :=
    ParallelSwapSecondLine
      Geo D B L M hParDB_LM

  have hLeftPar :
      IsParallelogram Geo L D B M :=
    ⟨hParLD_BM, hParDB_ML⟩

  exact
    ⟨L,
      hDLEcol,
      hLeftPar,
      hRightPar⟩


/--
Euclid II.14 -- local rectangle-cut helper, step 2.

Strengthen the generic rectangle cut from mere collinearity

    D, L, E

to the strict order

    D --- L --- E.

The proof is Hilbert Theorem 27.

From the original rectangle and the two cut parallelograms:

    BM ~= DL,
    BC ~= DE,
    MC ~= LE.

Since B-M-C, the corresponding point L lies strictly between D and E.
-/
private theorem proposition2_14_rectangle_cut_between
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C) :
    exists L : Geo.Point,
      Geo.Between D L E /\
      IsParallelogram Geo L D B M /\
      IsParallelogram Geo C E L M := by

  rcases
      proposition2_14_rectangle_cut_core_aux
        Geo
        B C D E M
        hRect
        hBMC with
    ⟨L, hDLEcol, hLeftPar, hRightPar⟩

  --------------------------------------------------------------------
  -- Distinctness of D,L,E.
  --------------------------------------------------------------------

  have hDL : Ne D L :=
    hLeftPar.1.1.symm

  have hLE : Ne L E :=
    hRightPar.2.1.symm

  have hDE : Ne D E :=
    hRect.1.1.2.1.symm

  --------------------------------------------------------------------
  -- BM ~= DL from L-D-B-M.
  --------------------------------------------------------------------

  have hLeftSides :
      OppositeSidesCongruent Geo L D B M :=
    ParallelogramOppositeSidesCongruent
      Geo L D B M hLeftPar

  have hLD_BM :
      Geo.Congruent L D B M :=
    hLeftSides.1

  have hBM_LD :
      Geo.Congruent B M L D :=
    hilbert_congruent_symmetry
      Geo L D B M hLD_BM

  have hBM_DL :
      Geo.Congruent B M D L :=
    CongruentSwapSecond
      Geo B M L D hBM_LD

  --------------------------------------------------------------------
  -- BC ~= DE from the original rectangle.
  --------------------------------------------------------------------

  have hWholeSides :
      OppositeSidesCongruent Geo B C E D :=
    ParallelogramOppositeSidesCongruent
      Geo B C E D hRect.1

  have hBC_ED :
      Geo.Congruent B C E D :=
    hWholeSides.1

  have hBC_DE :
      Geo.Congruent B C D E :=
    CongruentSwapSecond
      Geo B C E D hBC_ED

  --------------------------------------------------------------------
  -- MC ~= LE from C-E-L-M.
  --------------------------------------------------------------------

  have hRightSides :
      OppositeSidesCongruent Geo C E L M :=
    ParallelogramOppositeSidesCongruent
      Geo C E L M hRightPar

  have hEL_MC :
      Geo.Congruent E L M C :=
    hRightSides.2

  have hMC_EL :
      Geo.Congruent M C E L :=
    hilbert_congruent_symmetry
      Geo E L M C hEL_MC

  have hMC_LE :
      Geo.Congruent M C L E :=
    CongruentSwapSecond
      Geo M C E L hMC_EL

  --------------------------------------------------------------------
  -- Hilbert Theorem 27 transports B-M-C to D-L-E.
  --------------------------------------------------------------------

  have hDLE :
      Geo.Between D L E :=
    hilbert_theorem27_three_points
      Geo
      B M C
      D L E
      hBMC
      hDL
      hLE
      hDE
      hBM_DL
      hBC_DE
      hMC_LE

  exact
    ⟨L,
      hDLE,
      hLeftPar,
      hRightPar⟩


/--
Euclid II.14 -- local rectangle-cut helper, step 3.

Generic diagonal/cut intersection for a rectangle.

This is the I.47 Pasch argument with the square hypothesis weakened
to an arbitrary rectangle.  Only the parallelogram structure of the
rectangle is used to prove that triangle C-B-D is nondegenerate.
-/
private theorem proposition2_14_diagonal_cut_intersection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M L : Geo.Point)
    (hBMC : Geo.Between B M C)
    (hRect : IsRectangle Geo B C E D)
    (hLeftPar : IsParallelogram Geo L D B M) :
    exists N : Geo.Point,
      Geo.Between D N C /\
      Geo.Between M N L := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hBM : Ne B M :=
    hBMCdata.1

  have hMC : Ne M C :=
    hBMCdata.2.1

  have hBC : Ne B C :=
    hBMCdata.2.2.1

  have hBMCcol :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  have hCMB :
      Geo.Between C M B :=
    hBMCdata.2.2.2.2

  have hCMBcol :
      Collinear Geo C M B :=
    (HilbertOrder.between_incidence
      C M B hCMB).2.2.2.1

  --------------------------------------------------------------------
  -- DB || ML from the left cut parallelogram.
  --------------------------------------------------------------------

  have hDB_ML :
      Geo.Parallel D B M L :=
    hLeftPar.2

  have hDB : Ne D B :=
    hDB_ML.1

  have hML : Ne M L :=
    hDB_ML.2.1

  --------------------------------------------------------------------
  -- Choose actual incidence carriers DB and ML.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        D B hDB with
    ⟨lineDB, hDdb, hBdb⟩

  rcases
      HilbertPlaneIncidence.line_through
        M L hML with
    ⟨lineML, hMml, hLml⟩

  --------------------------------------------------------------------
  -- The two incidence lines are disjoint because DB || ML.
  --------------------------------------------------------------------

  have hLinesDB_ML :
      HilbertLinesDisjoint Geo lineDB lineML := by

    rintro ⟨X, hXdb, hXml⟩

    have hX_DB :
        X ∈ Geo.PointLine D B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D B X
        lineDB
        hDB
        hDdb
        hBdb).mpr hXdb

    have hX_ML :
        X ∈ Geo.PointLine M L :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        M L X
        lineML
        hML
        hMml
        hLml).mpr hXml

    exact
      Set.disjoint_left.mp
        hDB_ML.2.2
        hX_DB
        hX_ML

  --------------------------------------------------------------------
  -- B and D are off ML.
  --------------------------------------------------------------------

  have hBoff :
      Not (HilbertIncidence.OnLine B lineML) := by
    intro hBml
    exact
      hLinesDB_ML
        ⟨B, hBdb, hBml⟩

  have hDoff :
      Not (HilbertIncidence.OnLine D lineML) := by
    intro hDml
    exact
      hLinesDB_ML
        ⟨D, hDdb, hDml⟩

  --------------------------------------------------------------------
  -- C is also off ML.
  --------------------------------------------------------------------

  have hCoff :
      Not (HilbertIncidence.OnLine C lineML) := by
    intro hCml

    have hBml :
        HilbertIncidence.OnLine B lineML :=
      hilbert_collinear_on_line
        Geo
        C M B
        lineML
        hMC.symm
        hCml
        hMml
        hCMBcol

    exact hBoff hBml

  --------------------------------------------------------------------
  -- Triangle C-B-D is nondegenerate.
  --
  -- Here the I.47 proof used hSquare.1.  A rectangle already has the
  -- same parallelogram structure as its first component.
  --------------------------------------------------------------------

  have hRectNC :=
    parallelogram_vertices_noncollinear
      Geo B C E D hRect.1

  have hDBC :
      Not (Collinear Geo D B C) :=
    hRectNC.1

  have hCBD :
      Not (Collinear Geo C B D) := by
    intro h
    exact
      hDBC
        (PrimCollinearSymm
          Geo C B D h)

  --------------------------------------------------------------------
  -- ML enters triangle C-B-D through CB at M.
  --------------------------------------------------------------------

  have hMeetsCB :
      HilbertSegmentMeetsLine Geo C B lineML :=
    ⟨M, hCMB, hMml⟩

  --------------------------------------------------------------------
  -- ML cannot meet the open side BD because DB || ML.
  --------------------------------------------------------------------

  have hNotMeetsBD :
      Not (HilbertSegmentMeetsLine Geo B D lineML) := by

    rintro ⟨X, hBXD, hXml⟩

    have hXdb :
        HilbertIncidence.OnLine X lineDB :=
      hilbert_between_on_line
        Geo
        B X D
        lineDB
        hBdb
        hDdb
        hBXD

    exact
      hLinesDB_ML
        ⟨X, hXdb, hXml⟩

  --------------------------------------------------------------------
  -- Forced Pasch: ML meets CD internally.
  --------------------------------------------------------------------

  have hMeetsCD :
      HilbertSegmentMeetsLine Geo C D lineML :=
    hilbert_pasch_forced
      Geo
      C B D
      lineML
      hCBD
      hCoff
      hBoff
      hDoff
      hMeetsCB
      hNotMeetsBD

  rcases hMeetsCD with
    ⟨N, hCND, hNml⟩

  have hDNC :
      Geo.Between D N C :=
    (HilbertOrder.between_incidence
      C N D hCND).2.2.2.2

  have hLMN :
      Collinear Geo L M N :=
    ⟨lineML,
      hLml,
      hMml,
      hNml⟩

  --------------------------------------------------------------------
  -- DL || MC.
  --------------------------------------------------------------------

  have hDL_BM :
      Geo.Parallel D L B M :=
    ParallelSwapFirstLine
      Geo
      L D B M
      hLeftPar.1

  have hBM_DL :
      Geo.Parallel B M D L :=
    ParallelSymmetry
      Geo
      D L B M
      hDL_BM

  have hMB_DL :
      Geo.Parallel M B D L :=
    ParallelSwapFirstLine
      Geo
      B M D L
      hBM_DL

  have hMCBcol :
      Collinear Geo M C B :=
    PrimCollinearCycle
      Geo B M C hBMCcol

  have hMC_DL :
      Geo.Parallel M C D L :=
    collinear_parallel_trans
      Geo
      M C B
      D L
      hMC
      hMCBcol
      hMB_DL

  have hDL_MC :
      Geo.Parallel D L M C :=
    ParallelSymmetry
      Geo M C D L hMC_DL

  --------------------------------------------------------------------
  -- Parallel crossing order gives L-N-M, hence M-N-L.
  --------------------------------------------------------------------

  have hLNM :
      Geo.Between L N M :=
    hilbert_collinear_between_of_parallel
      Geo
      D L M C N
      hDL_MC
      hDNC
      hLMN

  have hMNL :
      Geo.Between M N L :=
    (HilbertOrder.between_incidence
      L N M hLNM).2.2.2.2

  exact
    ⟨N,
      hDNC,
      hMNL⟩


/--
Euclid II.14 -- exported local rectangle-cut helper.

Exported reusable cut constructor for an arbitrary rectangle.

From

    IsRectangle B C E D
    B-M-C

construct L and N satisfying exactly the geometric cut package used
by rectangle_split and the current Book II APIs:

    D-L-E,
    D-N-C,
    M-N-L,
    L-D-B-M parallelogram,
    C-E-L-M parallelogram.
-/
theorem proposition2_14_rectangle_cut_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C) :
    exists L N : Geo.Point,
      Geo.Between D L E /\
      Geo.Between D N C /\
      Geo.Between M N L /\
      IsParallelogram Geo L D B M /\
      IsParallelogram Geo C E L M := by

  rcases
      proposition2_14_rectangle_cut_between
        Geo
        B C D E M
        hRect
        hBMC with
    ⟨L, hDLE, hLeftPar, hRightPar⟩

  rcases
      proposition2_14_diagonal_cut_intersection
        Geo
        B C D E M L
        hBMC
        hRect
        hLeftPar with
    ⟨N, hDNC, hMNL⟩

  exact
    ⟨L, N,
      hDLE,
      hDNC,
      hMNL,
      hLeftPar,
      hRightPar⟩


/--
Euclid II.14.

Existential wrapper around the configured public API of Proposition II.5.

Assume

  F-E-G,
  G is the midpoint of FB.

Construct concrete representatives of

  Rect(EB,FE),
  Square(EG),
  Square(GB),

and prove the exact II.5 identity

  Rect(EB,FE) + Square(EG) = Square(GB).

All auxiliary rectangle cuts required by the old II.5 interface are
constructed internally using the later reusable rectangle-cut constructor
from Proposition II.11.
-/
theorem proposition2_14_ii5_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (F B E G : Geo.Point)
    (hMidG : HilbertIsMidpoint Geo G F B)
    (hFEG : Geo.Between F E G) :
    exists RP2 RP3 SEG0 SEG1 SGB0 SGB1 : Geo.Point,
      IsRectangleContainedBy Geo
        E B RP2 RP3 E B F E /\
      IsSquare Geo E G SEG0 SEG1 /\
      IsSquare Geo G B SGB0 SGB1 /\
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3 +
         hilbertParallelogramTerm Geo E G SEG0 SEG1)
        (hilbertParallelogramTerm Geo G B SGB0 SGB1) := by

  --------------------------------------------------------------------
  -- Baseline order and nondegeneracy.
  --------------------------------------------------------------------

  have hFGB :
      Geo.Between F G B :=
    hMidG.1

  have hFG : Ne F G :=
    (HilbertOrder.between_incidence
      F G B hFGB).1

  have hGB : Ne G B :=
    (HilbertOrder.between_incidence
      F G B hFGB).2.1

  have hFE : Ne F E :=
    (HilbertOrder.between_incidence
      F E G hFEG).1

  have hEG : Ne E G :=
    (HilbertOrder.between_incidence
      F E G hFEG).2.1

  have hOrder :=
    hilbert_between_inner_trans
      Geo
      F E G B
      hFEG
      hFGB

  have hEGB :
      Geo.Between E G B :=
    hOrder.1

  have hEB : Ne E B :=
    (HilbertOrder.between_incidence
      E G B hEGB).2.2.1

  --------------------------------------------------------------------
  -- test04 data:
  --
  -- outer rectangle Rect(FG,EG), cut at E with F-E-G.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        F G
        E G
        hFG with
    ⟨H4, E4, hFG_EG⟩

  rcases
      proposition2_14_rectangle_cut_exists
        Geo
        F G E4 H4 E
        hFG_EG.1
        hFEG with
    ⟨L4, X4,
      hE4L4H4,
      hE4X4G,
      hEX4L4,
      hLeftPar4,
      hRightPar4⟩

  --------------------------------------------------------------------
  -- Square(EG).
  --------------------------------------------------------------------

  rcases
      euclid_proposition_46
        Geo
        E G
        hEG with
    ⟨SEG0, SEG1, hSquareEG⟩

  --------------------------------------------------------------------
  -- Remaining rectangle representatives used in test04.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        F E
        E G
        hFE with
    ⟨T2, T3, hFE_EG⟩

  rcases
      rectangle_contained_by_exists
        Geo
        G B
        E G
        hGB with
    ⟨Z2, Z3, hGB_EG⟩

  --------------------------------------------------------------------
  -- test07 data:
  --
  -- outer rectangle Rect(EB,FE), cut at G with E-G-B.
  -- This rectangle is also the target unequal-parts rectangle.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        E B
        F E
        hEB with
    ⟨H7, E7, hEB_FE⟩

  rcases
      proposition2_14_rectangle_cut_exists
        Geo
        E B E7 H7 G
        hEB_FE.1
        hEGB with
    ⟨L7, X7,
      hE7L7H7,
      hE7X7B,
      hGX7L7,
      hLeftPar7,
      hRightPar7⟩

  rcases
      rectangle_contained_by_exists
        Geo
        E G
        F E
        hEG with
    ⟨Q2, Q3, hEG_FE⟩

  rcases
      rectangle_contained_by_exists
        Geo
        G B
        F E
        hGB with
    ⟨Y2, Y3, hGB_FE⟩

  --------------------------------------------------------------------
  -- test09 data:
  --
  -- outer rectangle Rect(FG,GB), again cut at E.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        F G
        G B
        hFG with
    ⟨H9, E9, hFG_GB⟩

  rcases
      proposition2_14_rectangle_cut_exists
        Geo
        F G E9 H9 E
        hFG_GB.1
        hFEG with
    ⟨L9, X9,
      hE9L9H9,
      hE9X9G,
      hEX9L9,
      hLeftPar9,
      hRightPar9⟩

  rcases
      rectangle_contained_by_exists
        Geo
        G B
        F G
        hGB with
    ⟨W2, W3, hGB_FG⟩

  --------------------------------------------------------------------
  -- Square(GB), the right side of II.5.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_46
        Geo
        G B
        hGB with
    ⟨SGB0, SGB1, hSquareGB⟩

  have hGB_GB :
      Geo.Congruent G B G B :=
    hilbert_congruent_reflexive
      Geo
      G B

  --------------------------------------------------------------------
  -- Apply public II.5 with
  --
  --   A := F
  --   B := B
  --   C := G
  --   D := E.
  --------------------------------------------------------------------

  have hII5 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E B H7 E7 +
         hilbertParallelogramTerm Geo E G SEG0 SEG1)
        (hilbertParallelogramTerm Geo G B SGB0 SGB1) :=
    euclid_proposition_2_5
      Geo
      F B G E
      hMidG
      hFEG

      -- test04 outer rectangle and cut
      E4 H4 L4 X4
      hFG_EG.1
      hFG_EG.2.2
      hE4L4H4
      hE4X4G
      hEX4L4
      hLeftPar4
      hRightPar4

      -- Square(EG)
      SEG0 SEG1
      hSquareEG

      -- Rect(FG,EG)
      F G H4 E4
      hFG_EG

      -- Rect(FE,EG)
      F E T2 T3
      hFE_EG

      -- Rect(GB,EG)
      G B Z2 Z3
      hGB_EG

      -- test07 outer rectangle and cut
      E7 H7 L7 X7
      hEB_FE.1
      hEB_FE.2.2
      hE7L7H7
      hE7X7B
      hGX7L7
      hLeftPar7
      hRightPar7

      -- Rect(EB,FE)
      E B H7 E7
      hEB_FE

      -- Rect(EG,FE)
      E G Q2 Q3
      hEG_FE

      -- Rect(GB,FE)
      G B Y2 Y3
      hGB_FE

      -- test09 outer rectangle and cut
      E9 H9 L9 X9
      hFG_GB.1
      hFG_GB.2.2
      hE9L9H9
      hE9X9G
      hEX9L9
      hLeftPar9
      hRightPar9

      -- Rect(GB,FG)
      G B W2 W3
      hGB_FG

      -- Square(GB)
      G B SGB0 SGB1
      hSquareGB
      hGB_GB

  exact
    ⟨H7, E7,
     SEG0, SEG1,
     SGB0, SGB1,
     hEB_FE,
     hSquareEG,
     hSquareGB,
     hII5⟩


/--
Euclid II.14.

Normalize the II.5 output from Square(GB) to Square(GF).

Since G is the midpoint of FB,

  GB ~= GF.

Hence the square on GB produced by II.5 is equicomplementable with
a square constructed on GF.  The resulting II.5 identity has exactly
the form needed later in II.14:

  Rect(EB,FE) + Square(EG) ~ec Square(GF).
-/
theorem proposition2_14_ii5_normalized_GF
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (F B E G : Geo.Point)
    (hMidG : HilbertIsMidpoint Geo G F B)
    (hFEG : Geo.Between F E G) :
    exists
      RP2 RP3
      SEG0 SEG1
      SGF0 SGF1 : Geo.Point,
      IsRectangleContainedBy Geo
        E B RP2 RP3 E B F E /\
      IsSquare Geo E G SEG0 SEG1 /\
      IsSquare Geo G F SGF0 SGF1 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3 +
         hilbertParallelogramTerm Geo E G SEG0 SEG1)
        (hilbertParallelogramTerm Geo G F SGF0 SGF1) := by

  --------------------------------------------------------------------
  -- Obtain the exact II.5 identity with Square(GB) on the right.
  --------------------------------------------------------------------

  rcases
      proposition2_14_ii5_exists
        Geo
        F B E G
        hMidG
        hFEG with
    ⟨RP2, RP3,
      SEG0, SEG1,
      SGB0, SGB1,
      hRectEB_FE,
      hSquareEG,
      hSquareGB,
      hII5⟩

  --------------------------------------------------------------------
  -- Midpoint congruence:
  --
  --   FG ~= GB
  --
  -- gives
  --
  --   GB ~= GF.
  --------------------------------------------------------------------

  have hGB_FG :
      Geo.Congruent G B F G :=
    hilbert_congruent_symmetry
      Geo
      F G
      G B
      hMidG.2

  have hGB_GF :
      Geo.Congruent G B G F :=
    CongruentSwapSecond
      Geo
      G B
      F G
      hGB_FG

  --------------------------------------------------------------------
  -- Construct the target square on GF.
  --------------------------------------------------------------------

  have hGF : Ne G F :=
    (HilbertOrder.between_incidence
      F G B hMidG.1).1.symm

  rcases
      euclid_proposition_46
        Geo
        G F
        hGF with
    ⟨SGF0, SGF1, hSquareGF⟩

  --------------------------------------------------------------------
  -- Transport Square(GB) to Square(GF).
  --------------------------------------------------------------------

  have hSqGB_GF :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo G B SGB0 SGB1)
        (hilbertParallelogramTerm Geo G F SGF0 SGF1) :=
    hilbert_square_transport
      Geo
      G B SGB0 SGB1
      G F SGF0 SGF1
      hSquareGB
      hSquareGF
      hGB_GF

  --------------------------------------------------------------------
  -- Exact II.5 equality weakens to equicomplementability.
  --------------------------------------------------------------------

  have hII5ec :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3 +
         hilbertParallelogramTerm Geo E G SEG0 SEG1)
        (hilbertParallelogramTerm Geo G B SGB0 SGB1) :=
    equicomplementable_of_scissorsEq
      Geo
      hII5

  have hNormalized :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3 +
         hilbertParallelogramTerm Geo E G SEG0 SEG1)
        (hilbertParallelogramTerm Geo G F SGF0 SGF1) :=
    equicomplementable_trans
      Geo
      hII5ec
      hSqGB_GF

  exact
    ⟨RP2, RP3,
     SEG0, SEG1,
     SGF0, SGF1,
     hRectEB_FE,
     hSquareEG,
     hSquareGF,
     hNormalized⟩


/--
Euclid II.14.

Pythagorean block for the oriented circle point.

Assume the II.14 rectangle/circle configuration with

  D-E-H,
  GH ~= GF,
  KH ~= GF,

and E the midpoint of GK.

Then construct concrete squares on EG, EH and GF and prove

  Square(GF) ~ec Square(EG) + Square(EH).

The proof is Euclid I.47 on the right triangle E-G-H, followed by
square transport along GH ~= GF.
-/
theorem proposition2_14_pythagorean_GF
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E G F K H : Geo.Point)
    (hRect : IsRectangle Geo B C D E)
    (hBGE : Geo.Between B G E)
    (hGEF : Geo.Between G E F)
    (hMidE : HilbertIsMidpoint Geo E G K)
    (hDEH : Geo.Between D E H)
    (hGH_GF : Geo.Congruent G H G F)
    (hKH_GF : Geo.Congruent K H G F) :
    exists
      SEG0 SEG1
      SEH0 SEH1
      SGF0 SGF1 : Geo.Point,
      IsSquare Geo E G SEG0 SEG1 /\
      IsSquare Geo E H SEH0 SEH1 /\
      IsSquare Geo G F SGF0 SGF1 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo G F SGF0 SGF1)
        (hilbertParallelogramTerm Geo E G SEG0 SEG1 +
         hilbertParallelogramTerm Geo E H SEH0 SEH1) := by

  --------------------------------------------------------------------
  -- GEH is a right triangle.
  --------------------------------------------------------------------

  have hRightGEH :
      HilbertRightAngle Geo G E H :=
    proposition2_14_right_triangle_after_H
      Geo
      B C D E G F H
      hRect
      hBGE
      hGEF
      hDEH

  --------------------------------------------------------------------
  -- H is off the line of the equal-circle centers GE.
  --------------------------------------------------------------------

  have hGE : Ne G E :=
    (HilbertOrder.between_incidence
      G E F hGEF).1

  have hEG : Ne E G :=
    hGE.symm

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        G E hGE with
    ⟨base, hGbase, hEbase⟩

  have hHoff :
      Not (HilbertIncidence.OnLine H base) :=
    proposition2_14_circle_point_off_center_line
      Geo
      G E F K H
      base
      hGEF
      hMidE
      hGH_GF
      hKH_GF
      hGbase
      hEbase

  have hEGHnc :
      Not (Collinear Geo E G H) :=
    hilbert_not_collinear_of_off_line
      Geo
      E G H
      base
      hEG
      hEbase
      hGbase
      hHoff

  --------------------------------------------------------------------
  -- I.47 on triangle E-G-H, right at E:
  --
  --   Square(GH) ~ec Square(EG) + Square(EH).
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        E G H
        hEGHnc
        hRightGEH with
    ⟨SGH1, SGH0,
      SEG0, SEG1,
      SEH1, SEH0,
      hSquareGH,
      hSquareEG,
      hSquareEH,
      hPythagoras⟩

  --------------------------------------------------------------------
  -- Construct Square(GF).
  --------------------------------------------------------------------

  have hGF : Ne G F :=
    (HilbertOrder.between_incidence
      G E F hGEF).2.2.1

  rcases
      euclid_proposition_46
        Geo
        G F
        hGF with
    ⟨SGF0, SGF1, hSquareGF⟩

  --------------------------------------------------------------------
  -- GH ~= GF, hence Square(GH) ~ec Square(GF).
  --------------------------------------------------------------------

  have hSqGH_GF :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo G H SGH0 SGH1)
        (hilbertParallelogramTerm Geo G F SGF0 SGF1) :=
    hilbert_square_transport
      Geo
      G H SGH0 SGH1
      G F SGF0 SGF1
      hSquareGH
      hSquareGF
      hGH_GF

  have hSqGF_GH :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo G F SGF0 SGF1)
        (hilbertParallelogramTerm Geo G H SGH0 SGH1) :=
    equicomplementable_symm
      Geo
      hSqGH_GF

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo G F SGF0 SGF1)
        (hilbertParallelogramTerm Geo E G SEG0 SEG1 +
         hilbertParallelogramTerm Geo E H SEH0 SEH1) :=
    equicomplementable_trans
      Geo
      hSqGF_GH
      hPythagoras

  exact
    ⟨SEG0, SEG1,
     SEH0, SEH1,
     SGF0, SGF1,
     hSquareEG,
     hSquareEH,
     hSquareGF,
     hFinal⟩


/--
Pure Common Notion 3 for the scissors-content relation.

If

  P + T ~ec Q + T,

then the common right summand T may be cancelled.
-/
private theorem proposition2_14_equicomplementable_cancel_right
    {P Q T : HilbertScissorsTerm Geo}
    (h :
      HilbertScissorsEquicomplementable Geo
        (P + T)
        (Q + T)) :
    HilbertScissorsEquicomplementable Geo P Q := by

  rcases h with
    ⟨R, S, hRS, hPQ⟩

  refine
    ⟨R + T, S + T, ?_, ?_⟩

  · exact
      HilbertScissorsEq.add
        (Geo := Geo)
        hRS
        (HilbertScissorsEq.refl
          (Geo := Geo) T)

  · have hPQ' :
        HilbertScissorsEq Geo
          (P + (R + T))
          (Q + (S + T)) := by

      simpa only
        [Multiset.add_assoc,
         Multiset.add_comm T R,
         Multiset.add_comm T S]
        using hPQ

    exact hPQ'


/--
Euclid II.14.

Common Notion 3 cancellation.

From II.5 we have

  Rect(EB,FE) + Square(EG) ~ec Square(GF).

From I.47 and GH ~= GF we have

  Square(GF) ~ec Square(EG) + Square(EH).

The independently constructed square representatives on GF and EG are
first normalized by square transport.  Then the common Square(EG) is
cancelled, yielding

  Rect(EB,FE) ~ec Square(EH).
-/
theorem proposition2_14_cancel_EG
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E F G K H : Geo.Point)
    (hRect : IsRectangle Geo B C D E)
    (hBGE : Geo.Between B G E)
    (hGEF : Geo.Between G E F)
    (hMidE : HilbertIsMidpoint Geo E G K)
    (hDEH : Geo.Between D E H)
    (hGH_GF : Geo.Congruent G H G F)
    (hKH_GF : Geo.Congruent K H G F)
    (hMidG : HilbertIsMidpoint Geo G F B)
    (hFEG : Geo.Between F E G) :
    exists
      RP2 RP3
      SEH0 SEH1 : Geo.Point,
      IsRectangleContainedBy Geo
        E B RP2 RP3 E B F E /\
      IsSquare Geo E H SEH0 SEH1 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3)
        (hilbertParallelogramTerm Geo E H SEH0 SEH1) := by

  --------------------------------------------------------------------
  -- II.5 block:
  --
  --   Rect(EB,FE) + Sq(EG_1) ~ec Sq(GF_1).
  --------------------------------------------------------------------

  rcases
      proposition2_14_ii5_normalized_GF
        Geo
        F B E G
        hMidG
        hFEG with
    ⟨RP2, RP3,
      SEG10, SEG11,
      SGF10, SGF11,
      hRectEB_FE,
      hSquareEG1,
      hSquareGF1,
      hII5⟩

  --------------------------------------------------------------------
  -- I.47 block:
  --
  --   Sq(GF_2) ~ec Sq(EG_2) + Sq(EH).
  --------------------------------------------------------------------

  rcases
      proposition2_14_pythagorean_GF
        Geo
        B C D E G F K H
        hRect
        hBGE
        hGEF
        hMidE
        hDEH
        hGH_GF
        hKH_GF with
    ⟨SEG20, SEG21,
      SEH0, SEH1,
      SGF20, SGF21,
      hSquareEG2,
      hSquareEH,
      hSquareGF2,
      hPythagoras⟩

  --------------------------------------------------------------------
  -- Normalize the two independently constructed squares on GF.
  --------------------------------------------------------------------

  have hGF_GF :
      Geo.Congruent G F G F :=
    hilbert_congruent_reflexive
      Geo G F

  have hGFtransport :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo G F SGF10 SGF11)
        (hilbertParallelogramTerm Geo G F SGF20 SGF21) :=
    hilbert_square_transport
      Geo
      G F SGF10 SGF11
      G F SGF20 SGF21
      hSquareGF1
      hSquareGF2
      hGF_GF

  have hThroughGF :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3 +
         hilbertParallelogramTerm Geo E G SEG10 SEG11)
        (hilbertParallelogramTerm Geo E G SEG20 SEG21 +
         hilbertParallelogramTerm Geo E H SEH0 SEH1) :=
    equicomplementable_trans
      Geo
      (equicomplementable_trans
        Geo
        hII5
        hGFtransport)
      hPythagoras

  --------------------------------------------------------------------
  -- Normalize the two independently constructed squares on EG.
  --------------------------------------------------------------------

  have hEG_EG :
      Geo.Congruent E G E G :=
    hilbert_congruent_reflexive
      Geo E G

  have hEGtransport :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E G SEG20 SEG21)
        (hilbertParallelogramTerm Geo E G SEG10 SEG11) :=
    hilbert_square_transport
      Geo
      E G SEG20 SEG21
      E G SEG10 SEG11
      hSquareEG2
      hSquareEG1
      hEG_EG

  have hEHrefl :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E H SEH0 SEH1)
        (hilbertParallelogramTerm Geo E H SEH0 SEH1) :=
    equicomplementable_refl
      Geo
      (hilbertParallelogramTerm Geo E H SEH0 SEH1)

  have hNormalizeRHS :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E G SEG20 SEG21 +
         hilbertParallelogramTerm Geo E H SEH0 SEH1)
        (hilbertParallelogramTerm Geo E G SEG10 SEG11 +
         hilbertParallelogramTerm Geo E H SEH0 SEH1) :=
    equicomplementable_add
      Geo
      hEGtransport
      hEHrefl

  have hWhole :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3 +
         hilbertParallelogramTerm Geo E G SEG10 SEG11)
        (hilbertParallelogramTerm Geo E G SEG10 SEG11 +
         hilbertParallelogramTerm Geo E H SEH0 SEH1) :=
    equicomplementable_trans
      Geo
      hThroughGF
      hNormalizeRHS

  --------------------------------------------------------------------
  -- Commute the right-hand sum so that Sq(EG) is literally the common
  -- right summand:
  --
  --   Rect + Sq(EG) ~ec Sq(EH) + Sq(EG).
  --------------------------------------------------------------------

  have hReorder :
      hilbertParallelogramTerm Geo E G SEG10 SEG11 +
        hilbertParallelogramTerm Geo E H SEH0 SEH1
      =
      hilbertParallelogramTerm Geo E H SEH0 SEH1 +
        hilbertParallelogramTerm Geo E G SEG10 SEG11 := by
    ac_rfl

  have hCommonRight :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3 +
         hilbertParallelogramTerm Geo E G SEG10 SEG11)
        (hilbertParallelogramTerm Geo E H SEH0 SEH1 +
         hilbertParallelogramTerm Geo E G SEG10 SEG11) := by
    rw [← hReorder]
    exact hWhole

  --------------------------------------------------------------------
  -- Common Notion 3.
  --------------------------------------------------------------------

  have hCancelled :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3)
        (hilbertParallelogramTerm Geo E H SEH0 SEH1) :=
    proposition2_14_equicomplementable_cancel_right
      Geo
      hCommonRight

  exact
    ⟨RP2, RP3,
     SEH0, SEH1,
     hRectEB_FE,
     hSquareEH,
     hCancelled⟩


/--
Euclid II.14.

Transport the rectangle from the II.5 notation back to the original
rectangle BCDE.

From the cancellation theorem:

  Rect(EB,FE) ~ec Square(EH).

The construction gives

  EF ~= ED,

hence also

  FE ~= DE.

The concrete rectangle BCDE is cyclically read as EBCD.  Its adjacent
sides are EB and BC, and the rectangle gives BC ~= DE.  Therefore EBCD
is a representative of the same contained-by data as Rect(EB,FE).

After rectangle transport and cyclic normalization:

  BCDE ~ec Square(EH).
-/
theorem proposition2_14_original_rectangle_equals_square
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E F G K H : Geo.Point)
    (hRect : IsRectangle Geo B C D E)
    (hBGE : Geo.Between B G E)
    (hGEF : Geo.Between G E F)
    (hMidE : HilbertIsMidpoint Geo E G K)
    (hDEH : Geo.Between D E H)
    (hGH_GF : Geo.Congruent G H G F)
    (hKH_GF : Geo.Congruent K H G F)
    (hMidG : HilbertIsMidpoint Geo G F B)
    (hFEG : Geo.Between F E G)
    (hEF_ED : Geo.Congruent E F E D) :
    exists SEH0 SEH1 : Geo.Point,
      IsSquare Geo E H SEH0 SEH1 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C D E)
        (hilbertParallelogramTerm Geo E H SEH0 SEH1) := by

  --------------------------------------------------------------------
  -- the cancellation theorem:
  --
  --   Rect(EB,FE) ~ec Square(EH).
  --------------------------------------------------------------------

  rcases
      proposition2_14_cancel_EG
        Geo
        B C D E F G K H
        hRect
        hBGE
        hGEF
        hMidE
        hDEH
        hGH_GF
        hKH_GF
        hMidG
        hFEG with
    ⟨RP2, RP3,
      SEH0, SEH1,
      hRectEB_FE,
      hSquareEH,
      hRect_SqEH⟩

  --------------------------------------------------------------------
  -- Cyclically normalize the original rectangle:
  --
  --   BCDE -> CDEB -> DEBC -> EBCD.
  --
  -- We first regard BCDE as contained by its literal adjacent sides
  -- BC and CD.  Three applications of rectangle_contained_by_swap
  -- rotate the distinguished corner to E.
  --------------------------------------------------------------------

  have hBC_BC :
      Geo.Congruent B C B C :=
    hilbert_congruent_reflexive
      Geo B C

  have hCD_CD :
      Geo.Congruent C D C D :=
    hilbert_congruent_reflexive
      Geo C D

  have hContained0 :
      IsRectangleContainedBy Geo
        B C D E B C C D :=
    ⟨hRect,
     hBC_BC,
     hCD_CD⟩

  rcases
      rectangle_contained_by_swap
        Geo
        B C D E
        B C C D
        hContained0 with
    ⟨hContained1, hRot01⟩

  rcases
      rectangle_contained_by_swap
        Geo
        C D E B
        C D B C
        hContained1 with
    ⟨hContained2, hRot12⟩

  rcases
      rectangle_contained_by_swap
        Geo
        D E B C
        B C C D
        hContained2 with
    ⟨hContained3, hRot23⟩

  have hBCDE_EBCD :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C D E)
        (hilbertParallelogramTerm Geo E B C D) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hRot01
      (HilbertScissorsEq.trans
        (Geo := Geo)
        hRot12
        hRot23)

  --------------------------------------------------------------------
  -- Side transport:
  --
  --   FE ~= DE
  --   DE ~= BC
  --
  -- therefore the second side of Rect(EB,FE) is congruent to BC.
  --------------------------------------------------------------------

  have hFE_DE :
      Geo.Congruent F E D E :=
    CongruentReverseBoth
      Geo
      E F
      E D
      hEF_ED

  have hSides :
      OppositeSidesCongruent Geo B C D E :=
    ParallelogramOppositeSidesCongruent
      Geo
      B C D E
      hRect.1

  have hBC_DE :
      Geo.Congruent B C D E :=
    hSides.1

  have hDE_BC :
      Geo.Congruent D E B C :=
    hilbert_congruent_symmetry
      Geo
      B C
      D E
      hBC_DE

  have hBRP2_DE :
      Geo.Congruent B RP2 D E :=
    hilbert_congruent_transitivity
      Geo
      B RP2
      F E
      D E
      hRectEB_FE.2.2
      hFE_DE

  have hBRP2_BC :
      Geo.Congruent B RP2 B C :=
    hilbert_congruent_transitivity
      Geo
      B RP2
      D E
      B C
      hBRP2_DE
      hDE_BC

  --------------------------------------------------------------------
  -- Rect(EB,FE) and the cyclic presentation EBCD have congruent
  -- adjacent sides, hence exact equal scissors content.
  --------------------------------------------------------------------

  have hRect_EBCD :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E B RP2 RP3)
        (hilbertParallelogramTerm Geo E B C D) :=
    rectangle_transport_scissorsEq
      Geo
      E B RP2 RP3
      E B C D
      hRectEB_FE.1
      hContained3.1
      hRectEB_FE.2.1
      hBRP2_BC

  --------------------------------------------------------------------
  -- Chain:
  --
  --   BCDE ~sc EBCD ~sc Rect(EB,FE) ~ec Square(EH).
  --------------------------------------------------------------------

  have hBCDE_EBCD_ec :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C D E)
        (hilbertParallelogramTerm Geo E B C D) :=
    equicomplementable_of_scissorsEq
      Geo
      hBCDE_EBCD

  have hEBCD_Rect_ec :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B C D)
        (hilbertParallelogramTerm Geo E B RP2 RP3) :=
    equicomplementable_of_scissorsEq
      Geo
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hRect_EBCD)

  have hBCDE_Rect :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C D E)
        (hilbertParallelogramTerm Geo E B RP2 RP3) :=
    equicomplementable_trans
      Geo
      hBCDE_EBCD_ec
      hEBCD_Rect_ec

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C D E)
        (hilbertParallelogramTerm Geo E H SEH0 SEH1) :=
    equicomplementable_trans
      Geo
      hBCDE_Rect
      hRect_SqEH

  exact
    ⟨SEH0, SEH1,
     hSquareEH,
     hFinal⟩


/--
Euclid II.14.

Every rectangle is equal in content to some square.

This is the complete rectangle-level core of II.14.  The adjacent side
magnitudes are compared by segment trichotomy:

* BE ~= ED: the rectangle is already a square, after cyclic reading;
* ED < BE: use the construction developed in the unequal-side construction below;
* BE < ED: rotate BCDE to CDEB, transport the strict comparison, and
  use the same unequal-side construction.

No rectilineal figure or Proposition I.45 appears yet.
-/
theorem proposition2_14_rectangle_to_square
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E : Geo.Point)
    (hRect : IsRectangle Geo B C D E) :
    exists Q0 Q1 Q2 Q3 : Geo.Point,
      IsSquare Geo Q0 Q1 Q2 Q3 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C D E)
        (hilbertParallelogramTerm Geo Q0 Q1 Q2 Q3) := by

  --------------------------------------------------------------------
  -- Rectangle side data and cyclic presentations.
  --------------------------------------------------------------------

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo
      B C D E
      hRect.1

  have hDEB :
      Not (Collinear Geo D E B) :=
    hNC.2.2.2

  have hDE : Ne D E :=
    hilbert_noncollinear_ne_first
      Geo
      D E B
      hDEB

  have hED : Ne E D :=
    hDE.symm

  have hSides :
      OppositeSidesCongruent Geo B C D E :=
    ParallelogramOppositeSidesCongruent
      Geo
      B C D E
      hRect.1

  have hBC_DE :
      Geo.Congruent B C D E :=
    hSides.1

  have hDE_BC :
      Geo.Congruent D E B C :=
    hilbert_congruent_symmetry
      Geo
      B C
      D E
      hBC_DE

  have hED_CB :
      Geo.Congruent E D C B :=
    CongruentReverseBoth
      Geo
      D E
      B C
      hDE_BC

  have hBC_BC :
      Geo.Congruent B C B C :=
    hilbert_congruent_reflexive
      Geo B C

  have hCD_CD :
      Geo.Congruent C D C D :=
    hilbert_congruent_reflexive
      Geo C D

  have hContained0 :
      IsRectangleContainedBy Geo
        B C D E B C C D :=
    ⟨hRect,
     hBC_BC,
     hCD_CD⟩

  rcases
      rectangle_contained_by_swap
        Geo
        B C D E
        B C C D
        hContained0 with
    ⟨hContained1, hRot01⟩

  rcases
      rectangle_contained_by_swap
        Geo
        C D E B
        C D B C
        hContained1 with
    ⟨hContained2, hRot12⟩

  rcases
      rectangle_contained_by_swap
        Geo
        D E B C
        B C C D
        hContained2 with
    ⟨hContained3, hRot23⟩

  have hRectCDEB :
      IsRectangle Geo C D E B :=
    hContained1.1

  have hRectEBCD :
      IsRectangle Geo E B C D :=
    hContained3.1

  have hBCDE_EBCD :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C D E)
        (hilbertParallelogramTerm Geo E B C D) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hRot01
      (HilbertScissorsEq.trans
        (Geo := Geo)
        hRot12
        hRot23)

  --------------------------------------------------------------------
  -- Compare the two adjacent side magnitudes BE and ED.
  --------------------------------------------------------------------

  rcases
      hilbert_segment_trichotomy
        Geo
        B E
        E D
        hED with
    hEq | hBEltED | hEDltBE

  --------------------------------------------------------------------
  -- Case 1: BE ~= ED.  The rectangle is already a square.
  --------------------------------------------------------------------

  · have hEB_ED :
        Geo.Congruent E B E D :=
      CongruentReverseFirst
        Geo
        B E
        E D
        hEq

    have hED_BC :
        Geo.Congruent E D B C :=
      CongruentReverseFirst
        Geo
        D E
        B C
        hDE_BC

    have hEB_BC :
        Geo.Congruent E B B C :=
      hilbert_congruent_transitivity
        Geo
        E B
        E D
        B C
        hEB_ED
        hED_BC

    have hSquare :
        IsSquare Geo E B C D :=
      proposition2_14_rectangle_equal_sides_square
        Geo
        E B C D
        hRectEBCD
        hEB_BC

    have hContent :
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo B C D E)
          (hilbertParallelogramTerm Geo E B C D) :=
      equicomplementable_of_scissorsEq
        Geo
        hBCDE_EBCD

    exact
      ⟨E, B, C, D,
       hSquare,
       hContent⟩

  --------------------------------------------------------------------
  -- Case 2: BE < ED.
  --
  -- Rotate once:
  --
  --   BCDE -> CDEB.
  --
  -- In the rotated rectangle the short side used by test02 is BE and
  -- the long side is CB.  Since ED ~= CB, transport BE < ED to
  -- BE < CB.
  --------------------------------------------------------------------

  · have hBEltCB :
        HilbertSegmentLess Geo B E C B :=
      bookZero_30_lessThanCongruence
        Geo
        B E
        E D
        C B
        hBEltED
        hED_CB

    rcases
        proposition2_14_ii5_baseline
          Geo
          C B E
          hBEltCB with
      ⟨F, G,
        hCGB,
        hGBF,
        hFBG,
        hMidG,
        hBF_BE⟩

    rcases
        proposition2_14_mirror_center
          Geo
          G B F
          hGBF with
      ⟨K, _hGBK, hMidB, _hBK_GB⟩

    rcases
        proposition2_14_oriented_circle_point
          Geo
          C D E B G F K
          hRectCDEB
          hCGB
          hGBF
          hMidB with
      ⟨H,
        hEBH,
        hGH_GF,
        hKH_GF⟩

    rcases
        proposition2_14_original_rectangle_equals_square
          Geo
          C D E B F G K H
          hRectCDEB
          hCGB
          hGBF
          hMidB
          hEBH
          hGH_GF
          hKH_GF
          hMidG
          hFBG
          hBF_BE with
      ⟨Q2, Q3,
        hSquare,
        hRotSquare⟩

    have hBCDE_CDEB_ec :
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo B C D E)
          (hilbertParallelogramTerm Geo C D E B) :=
      equicomplementable_of_scissorsEq
        Geo
        hRot01

    have hFinal :
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo B C D E)
          (hilbertParallelogramTerm Geo B H Q2 Q3) :=
      equicomplementable_trans
        Geo
        hBCDE_CDEB_ec
        hRotSquare

    exact
      ⟨B, H, Q2, Q3,
       hSquare,
       hFinal⟩

  --------------------------------------------------------------------
  -- Case 3: ED < BE.
  --
  -- This is exactly the orientation used throughout the unequal-side construction below.
  --------------------------------------------------------------------

  · rcases
        proposition2_14_ii5_baseline
          Geo
          B E D
          hEDltBE with
      ⟨F, G,
        hBGE,
        hGEF,
        hFEG,
        hMidG,
        hEF_ED⟩

    rcases
        proposition2_14_mirror_center
          Geo
          G E F
          hGEF with
      ⟨K, _hGEK, hMidE, _hEK_GE⟩

    rcases
        proposition2_14_oriented_circle_point
          Geo
          B C D E G F K
          hRect
          hBGE
          hGEF
          hMidE with
      ⟨H,
        hDEH,
        hGH_GF,
        hKH_GF⟩

    rcases
        proposition2_14_original_rectangle_equals_square
          Geo
          B C D E F G K H
          hRect
          hBGE
          hGEF
          hMidE
          hDEH
          hGH_GF
          hKH_GF
          hMidG
          hFEG
          hEF_ED with
      ⟨Q2, Q3,
        hSquare,
        hFinal⟩

    exact
      ⟨E, H, Q2, Q3,
       hSquare,
       hFinal⟩


/--
Euclid II.14.

Final public-shape theorem.

Given a nonempty rectilineal figure represented by a list of
nondegenerate triangles, construct a square equal to it in content.

The proof is exactly the classical outer architecture:

1. choose a right angle;
2. I.45 constructs a parallelogram equal to the given figure in that angle;
3. because the prescribed angle is right, the parallelogram is a rectangle;
4. the rectangle-to-square theorem constructs a square equal to that rectangle.

The auxiliary right angle is obtained without adding an external parameter:
take one side of the first nondegenerate triangle and construct its square
by I.46.  One corner of that square supplies a nondegenerate right angle.
-/
theorem euclid_proposition_2_14
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (L : HilbertTriangulatedFigure Geo)
    (hNonempty : Ne L [])
    (hTriangles :
      forall t, t ∈ L ->
        Not (Collinear Geo t.A t.B t.C)) :
    exists Q0 Q1 Q2 Q3 : Geo.Point,
      IsSquare Geo Q0 Q1 Q2 Q3 /\
      HilbertScissorsEquicomplementable Geo
        (rectilinealTerm Geo L)
        (hilbertParallelogramTerm Geo Q0 Q1 Q2 Q3) := by

  --------------------------------------------------------------------
  -- Since L is nonempty, expose its first triangle.
  --------------------------------------------------------------------

  cases L with
  | nil =>
      exact False.elim (hNonempty rfl)

  | cons t ts =>

      have ht :
          Not (Collinear Geo t.A t.B t.C) :=
        hTriangles
          t
          List.mem_cons_self

      have hAB : Ne t.A t.B :=
        hilbert_noncollinear_ne_first
          Geo
          t.A t.B t.C
          ht

      ----------------------------------------------------------------
      -- I.46: construct a square on AB.
      --
      -- Its angle R1-A-B is right and nondegenerate.  We use this
      -- angle as the prescribed angle in I.45.
      ----------------------------------------------------------------

      rcases
          euclid_proposition_46
            Geo
            t.A t.B
            hAB with
        ⟨R0, R1, hSquareAB⟩

      have hNCSquare :=
        parallelogram_vertices_noncollinear
          Geo
          t.A t.B R0 R1
          hSquareAB.1

      have hNCR1AB :
          Not (Collinear Geo R1 t.A t.B) :=
        hNCSquare.1

      have hRightR1AB :
          HilbertRightAngle Geo R1 t.A t.B :=
        hSquareAB.2.2.2.2.1

      ----------------------------------------------------------------
      -- I.45: construct a parallelogram equal to the whole
      -- rectilineal figure, with angle STU congruent to R1-A-B.
      ----------------------------------------------------------------

      rcases
          euclid_proposition_45
            Geo
            R1 t.A t.B
            hNCR1AB
            (t :: ts)
            hNonempty
            hTriangles with
        ⟨S, T, U, V,
          hPar,
          hAngle,
          hFigurePar⟩

      ----------------------------------------------------------------
      -- The prescribed angle was right, so STU is right.
      ----------------------------------------------------------------

      have hNCPar :=
        parallelogram_vertices_noncollinear
          Geo
          S T U V
          hPar

      have hNCSTU :
          Not (Collinear Geo S T U) :=
        hNCPar.2.1

      have hAngleSymm :
          Geo.AngleCongruent
            R1 t.A t.B
            S T U :=
        Geo.angle_congruent_symmetry
          S T U
          R1 t.A t.B
          hAngle

      have hRightSTU :
          HilbertRightAngle Geo S T U :=
        hilbert_right_angle_transport
          Geo
          R1 t.A t.B
          S T U
          hNCR1AB
          hNCSTU
          hRightR1AB
          hAngleSymm

      have hRect :
          IsRectangle Geo S T U V :=
        ⟨hPar, hRightSTU⟩

      ----------------------------------------------------------------
      -- the rectangle-to-square theorem: every rectangle is equal in content to a square.
      ----------------------------------------------------------------

      rcases
          proposition2_14_rectangle_to_square
            Geo
            S T U V
            hRect with
        ⟨Q0, Q1, Q2, Q3,
          hSquare,
          hParSquare⟩

      ----------------------------------------------------------------
      -- I.45 content equality followed by rectangle-to-square.
      ----------------------------------------------------------------

      have hFinal :
          HilbertScissorsEquicomplementable Geo
            (rectilinealTerm Geo (t :: ts))
            (hilbertParallelogramTerm Geo Q0 Q1 Q2 Q3) :=
        equicomplementable_trans
          Geo
          hFigurePar
          hParSquare

      exact
        ⟨Q0, Q1, Q2, Q3,
         hSquare,
         hFinal⟩

end Geometry

import CGJteamLab.Proposition2_2
import CGJteamLab.Proposition2_3

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid II.4.

If A-C-B, then the square on AB is scissors-equal to the two squares
on AC and CB together with two rectangles contained by AC and CB.

The proof is entirely in the geometric rectangle/scissors layer:
II.2 first splits the square on AB into Rect(AB,AC) and Rect(AB,CB),
and two applications of II.3 expand those two rectangles.

No segment multiplication or numerical area is used.
-/
theorem euclid_proposition_2_4
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C : Geo.Point)

    --------------------------------------------------------------------
    -- II.2 diagram: square on AB cut at C.
    --------------------------------------------------------------------

    (D0 E0 L0 X0 : Geo.Point)
    (hSquareAB : IsSquare Geo A B E0 D0)

    (hACB : Geo.Between A C B)
    (hD0L0E0 : Geo.Between D0 L0 E0)
    (hD0X0B : Geo.Between D0 X0 B)
    (hCX0L0 : Geo.Between C X0 L0)

    (hII2LeftPar :
      IsParallelogram Geo L0 D0 A C)
    (hII2RightPar :
      IsParallelogram Geo B E0 L0 C)

    -- Arbitrary representatives of Rect(AB,AC) and Rect(AB,CB).
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)

    (hAB_AC :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A B A C)

    (hAB_CB :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A B C B)

    --------------------------------------------------------------------
    -- II.3 diagram for the left term.
    --
    -- We read the divided whole segment in the reverse direction:
    --
    --   B-C-A.
    --
    -- Thus II.3 gives
    --
    --   Rect(BA,CA) = Rect(BC,CA) + Square(CA).
    --------------------------------------------------------------------

    (D1 E1 L1 X1 : Geo.Point)

    (hRectLeft :
      IsRectangle Geo B A E1 D1)

    (hAE1_CA :
      Geo.Congruent A E1 C A)

    (hD1L1E1 : Geo.Between D1 L1 E1)
    (hD1X1A : Geo.Between D1 X1 A)
    (hCX1L1 : Geo.Between C X1 L1)

    (hLeftLeftPar :
      IsParallelogram Geo L1 D1 B C)
    (hLeftRightPar :
      IsParallelogram Geo A E1 L1 C)

    -- Square on CA, i.e. on the same unoriented segment as AC.
    (F G : Geo.Point)
    (hSquareCA : IsSquare Geo C A F G)

    --------------------------------------------------------------------
    -- II.3 diagram for the right term:
    --
    --   Rect(AB,CB) = Rect(AC,CB) + Square(CB).
    --------------------------------------------------------------------

    (D2 E2 L2 X2 : Geo.Point)

    (hRectRight :
      IsRectangle Geo A B E2 D2)

    (hBE2_CB :
      Geo.Congruent B E2 C B)

    (hD2L2E2 : Geo.Between D2 L2 E2)
    (hD2X2B : Geo.Between D2 X2 B)
    (hCX2L2 : Geo.Between C X2 L2)

    (hRightLeftPar :
      IsParallelogram Geo L2 D2 A C)
    (hRightRightPar :
      IsParallelogram Geo B E2 L2 C)

    -- Square on CB.
    (H K : Geo.Point)
    (hSquareCB : IsSquare Geo C B H K)

    --------------------------------------------------------------------
    -- Two arbitrary representatives of the repeated cross rectangle
    -- Rect(AC,CB).
    --------------------------------------------------------------------

    (T10 T11 T12 T13 : Geo.Point)
    (T20 T21 T22 T23 : Geo.Point)

    (hCross1 :
      IsRectangleContainedBy Geo
        T10 T11 T12 T13 A C C B)

    (hCross2 :
      IsRectangleContainedBy Geo
        T20 T21 T22 T23 A C C B) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A B E0 D0)
      ((hilbertParallelogramTerm Geo T20 T21 T22 T23 +
        hilbertParallelogramTerm Geo C A F G) +
       (hilbertParallelogramTerm Geo T10 T11 T12 T13 +
        hilbertParallelogramTerm Geo C B H K)) := by

  --------------------------------------------------------------------
  -- Reverse A-C-B to B-C-A for the left application of II.3.
  --------------------------------------------------------------------

  have hBCA : Geo.Between B C A :=
    (HilbertOrder.between_incidence A C B hACB).2.2.2.2

  --------------------------------------------------------------------
  -- II.2:
  --
  --   Rect(AB,AC) + Rect(AB,CB) = Square(AB).
  --------------------------------------------------------------------

  have hII2 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3 +
         hilbertParallelogramTerm Geo V0 V1 V2 V3)
        (hilbertParallelogramTerm Geo A B E0 D0) :=
    euclid_proposition_2_2
      Geo
      A B D0 E0 L0 C X0
      hSquareAB
      hACB
      hD0L0E0
      hD0X0B
      hCX0L0
      hII2LeftPar
      hII2RightPar
      U0 U1 U2 U3
      V0 V1 V2 V3
      hAB_AC
      hAB_CB

  --------------------------------------------------------------------
  -- The same representative U also represents Rect(BA,CA).
  --------------------------------------------------------------------

  have hAB_AC_rev :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 B A C A :=
    And.intro
      hAB_AC.1
      (And.intro
        (CongruentSwapSecond
          Geo U0 U1 A B hAB_AC.2.1)
        (CongruentSwapSecond
          Geo U1 U2 A C hAB_AC.2.2))

  --------------------------------------------------------------------
  -- Rotate the second cross rectangle:
  --
  --   Rect(AC,CB) -> Rect(CB,AC).
  --
  -- Endpoint reversal then reads the rotated representative as
  -- Rect(BC,CA), exactly what the reversed II.3 needs.
  --------------------------------------------------------------------

  have hSwapResult :=
    rectangle_contained_by_swap
      Geo
      T20 T21 T22 T23
      A C C B
      hCross2

  have hCross2Swap :=
    hSwapResult.1

  have hRotateCross2 :=
    hSwapResult.2

  have hCross2ForLeft :
      IsRectangleContainedBy Geo
        T21 T22 T23 T20 B C C A :=
    And.intro
      hCross2Swap.1
      (And.intro
        (CongruentSwapSecond
          Geo T21 T22 C B hCross2Swap.2.1)
        (CongruentSwapSecond
          Geo T22 T23 A C hCross2Swap.2.2))

  --------------------------------------------------------------------
  -- Left II.3:
  --
  --   Rect(BA,CA)
  --     =
  --   Rect(BC,CA) + Square(CA).
  --------------------------------------------------------------------

  have hLeftRaw :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo T21 T22 T23 T20 +
         hilbertParallelogramTerm Geo C A F G) :=
    euclid_proposition_2_3
      Geo
      B A D1 E1 L1 C X1
      hRectLeft
      hAE1_CA
      hBCA
      hD1L1E1
      hD1X1A
      hCX1L1
      hLeftLeftPar
      hLeftRightPar
      F G
      hSquareCA
      U0 U1 U2 U3
      T21 T22 T23 T20
      hAB_AC_rev
      hCross2ForLeft

  --------------------------------------------------------------------
  -- Return the left cross term to the original arbitrary
  -- representative T20-T21-T22-T23.
  --------------------------------------------------------------------

  have hRotateCross2Back :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo T21 T22 T23 T20)
        (hilbertParallelogramTerm Geo T20 T21 T22 T23) :=
    HilbertScissorsEq.symm
      (Geo := Geo)
      hRotateCross2

  have hLeftTarget :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo T20 T21 T22 T23 +
         hilbertParallelogramTerm Geo C A F G) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hLeftRaw
      (HilbertScissorsEq.add
        (Geo := Geo)
        hRotateCross2Back
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertParallelogramTerm Geo C A F G)))

  --------------------------------------------------------------------
  -- Right II.3:
  --
  --   Rect(AB,CB)
  --     =
  --   Rect(AC,CB) + Square(CB).
  --------------------------------------------------------------------

  have hRight :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo V0 V1 V2 V3)
        (hilbertParallelogramTerm Geo T10 T11 T12 T13 +
         hilbertParallelogramTerm Geo C B H K) :=
    euclid_proposition_2_3
      Geo
      A B D2 E2 L2 C X2
      hRectRight
      hBE2_CB
      hACB
      hD2L2E2
      hD2X2B
      hCX2L2
      hRightLeftPar
      hRightRightPar
      H K
      hSquareCB
      V0 V1 V2 V3
      T10 T11 T12 T13
      hAB_CB
      hCross1

  --------------------------------------------------------------------
  -- Expand both II.2 summands simultaneously.
  --------------------------------------------------------------------

  have hExpanded :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3 +
         hilbertParallelogramTerm Geo V0 V1 V2 V3)
        ((hilbertParallelogramTerm Geo T20 T21 T22 T23 +
          hilbertParallelogramTerm Geo C A F G) +
         (hilbertParallelogramTerm Geo T10 T11 T12 T13 +
          hilbertParallelogramTerm Geo C B H K)) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hLeftTarget
      hRight

  --------------------------------------------------------------------
  -- Square(AB)
  --   = Rect(AB,AC) + Rect(AB,CB)
  --   = the four terms of II.4.
  --------------------------------------------------------------------

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hII2)
      hExpanded

end Geometry

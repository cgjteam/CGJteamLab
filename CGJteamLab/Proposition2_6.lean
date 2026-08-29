import CGJteamLab.Proposition2_5

namespace Geometry

universe u
variable (Geo : Geometry.Geo)

/--
Euclid II.6 -- test 01.

Order skeleton for the standard configuration

  A -- C -- B -- D

where C is the midpoint of AB and AB is produced beyond B to D.
-/
private theorem proposition2_6_test01_order
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D) :
    Geo.Between C B D /\
    Geo.Between A C D /\
    Geo.Congruent A C C B /\
    Geo.Congruent C A C B := by

  have hOrder :
      Geo.Between C B D /\
      Geo.Between A C D :=
    hilbert_between_inner_trans
      Geo A C B D
      hMidC.1
      hABD

  have hCBD : Geo.Between C B D :=
    hOrder.1

  have hACD : Geo.Between A C D :=
    hOrder.2

  have hAC_CB :
      Geo.Congruent A C C B :=
    hMidC.2

  have hCA_CB :
      Geo.Congruent C A C B :=
    CongruentReverseFirst
      Geo A C C B
      hAC_CB

  exact
    And.intro
      hCBD
      (And.intro
        hACD
        (And.intro
          hAC_CB
          hCA_CB))


/--
Euclid II.6 -- test 02.

First scissors-calculus decomposition:

  Rect(AD, BD) = Rect(AB, BD) + Square(BD).

This is Euclid II.3 applied to AD cut at B.
-/
private theorem proposition2_6_test02_ad_decomposition
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D)

    (E H L X : Geo.Point)
    (hRect : IsRectangle Geo A D H E)
    (hDH_BD : Geo.Congruent D H B D)
    (hELE : Geo.Between E L H)
    (hEXD : Geo.Between E X D)
    (hBXL : Geo.Between B X L)
    (hLeftPar : IsParallelogram Geo L E A B)
    (hRightPar : IsParallelogram Geo D H L B)

    (F G : Geo.Point)
    (hSquareBD : IsSquare Geo B D F G)

    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)
    (hWhole :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A D B D)
    (hProduct :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A B B D) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       hilbertParallelogramTerm Geo B D F G) := by

  have hOrder :=
    proposition2_6_test01_order
      Geo A B C D hMidC hABD

  have _hCBD : Geo.Between C B D :=
    hOrder.1

  have _hACD : Geo.Between A C D :=
    hOrder.2.1

  exact
    euclid_proposition_2_3
      Geo
      A D E H L B X
      hRect
      hDH_BD
      hABD
      hELE
      hEXD
      hBXL
      hLeftPar
      hRightPar
      F G
      hSquareBD
      U0 U1 U2 U3
      V0 V1 V2 V3
      hWhole
      hProduct


/--
Euclid II.6 -- test 03.

Split AB at its midpoint C, with BD as the fixed second side:

  Rect(AB, BD)
    =
  Rect(AC, BD) + Rect(CB, BD).

This is exactly the two-part form of Euclid II.1.
-/
private theorem proposition2_6_test03_ab_decomposition
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)

    -- Concrete II.1 cut diagram for Rect(AB, BD), cut at C.
    (E H L X : Geo.Point)
    (hRect : IsRectangle Geo A B H E)
    (hBH_BD : Geo.Congruent B H B D)
    (hELE : Geo.Between E L H)
    (hEXB : Geo.Between E X B)
    (hCXL : Geo.Between C X L)
    (hLeftPar : IsParallelogram Geo L E A C)
    (hRightPar : IsParallelogram Geo B H L C)

    -- Arbitrary representatives of
    --
    --   Rect(AB, BD),
    --   Rect(AC, BD),
    --   Rect(CB, BD).
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)
    (W0 W1 W2 W3 : Geo.Point)

    (hWhole :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A B B D)

    (hPart1 :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A C B D)

    (hPart2 :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 C B B D) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       hilbertParallelogramTerm Geo W0 W1 W2 W3) := by

  exact
    euclid_proposition_2_1_two
      Geo
      A B E H L C X B D
      hRect
      hBH_BD
      hMidC.1
      hELE
      hEXB
      hCXL
      hLeftPar
      hRightPar
      U0 U1 U2 U3
      V0 V1 V2 V3
      W0 W1 W2 W3
      hWhole
      hPart1
      hPart2


/--
Euclid II.6 -- test 04.

Compose test 02 and test 03.

Test 02:
  Rect(AD, BD) = Rect(AB, BD) + Square(BD).

Test 03:
  Rect(AB, BD) = Rect(AC, BD) + Rect(CB, BD).

Using the same representative for Rect(AB,BD), substitution gives

  Rect(AD, BD)
    =
  (Rect(AC, BD) + Rect(CB, BD)) + Square(BD).

No midpoint transport is used yet beyond the hypotheses already
carried by the two preceding tests.
-/
private theorem proposition2_6_test04_compose_decompositions
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D)

    ------------------------------------------------------------------
    -- Diagram for test 02:
    -- Rect(AD,BD) = Rect(AB,BD) + Square(BD).
    ------------------------------------------------------------------

    (E2 H2 L2 X2 : Geo.Point)
    (hRect2 : IsRectangle Geo A D H2 E2)
    (hDH_BD2 : Geo.Congruent D H2 B D)
    (hELE2 : Geo.Between E2 L2 H2)
    (hEXD2 : Geo.Between E2 X2 D)
    (hBXL2 : Geo.Between B X2 L2)
    (hLeftPar2 : IsParallelogram Geo L2 E2 A B)
    (hRightPar2 : IsParallelogram Geo D H2 L2 B)

    (F G : Geo.Point)
    (hSquareBD : IsSquare Geo B D F G)

    -- Rect(AD,BD).
    (U0 U1 U2 U3 : Geo.Point)
    (hAD_BD :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A D B D)

    -- Rect(AB,BD).  This SAME representative is used in test 03.
    (V0 V1 V2 V3 : Geo.Point)
    (hAB_BD :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A B B D)

    ------------------------------------------------------------------
    -- Diagram for test 03:
    -- Rect(AB,BD) = Rect(AC,BD) + Rect(CB,BD).
    ------------------------------------------------------------------

    (E3 H3 L3 X3 : Geo.Point)
    (hRect3 : IsRectangle Geo A B H3 E3)
    (hBH_BD3 : Geo.Congruent B H3 B D)
    (hELE3 : Geo.Between E3 L3 H3)
    (hEXB3 : Geo.Between E3 X3 B)
    (hCXL3 : Geo.Between C X3 L3)
    (hLeftPar3 : IsParallelogram Geo L3 E3 A C)
    (hRightPar3 : IsParallelogram Geo B H3 L3 C)

    -- Rect(AC,BD).
    (Y0 Y1 Y2 Y3 : Geo.Point)
    (hAC_BD :
      IsRectangleContainedBy Geo
        Y0 Y1 Y2 Y3 A C B D)

    -- Rect(CB,BD).
    (Z0 Z1 Z2 Z3 : Geo.Point)
    (hCB_BD :
      IsRectangleContainedBy Geo
        Z0 Z1 Z2 Z3 C B B D) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      ((hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
        hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) +
       hilbertParallelogramTerm Geo B D F G) := by

  --------------------------------------------------------------------
  -- test 02.
  --------------------------------------------------------------------

  have h02 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
         hilbertParallelogramTerm Geo B D F G) :=
    proposition2_6_test02_ad_decomposition
      Geo
      A B C D
      hMidC hABD
      E2 H2 L2 X2
      hRect2 hDH_BD2 hELE2 hEXD2 hBXL2
      hLeftPar2 hRightPar2
      F G
      hSquareBD
      U0 U1 U2 U3
      V0 V1 V2 V3
      hAD_BD
      hAB_BD

  --------------------------------------------------------------------
  -- test 03, using exactly V0 V1 V2 V3 as its whole rectangle.
  --------------------------------------------------------------------

  have h03 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo V0 V1 V2 V3)
        (hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
         hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) :=
    proposition2_6_test03_ab_decomposition
      Geo
      A B C D
      hMidC
      E3 H3 L3 X3
      hRect3 hBH_BD3 hELE3 hEXB3 hCXL3
      hLeftPar3 hRightPar3
      V0 V1 V2 V3
      Y0 Y1 Y2 Y3
      Z0 Z1 Z2 Z3
      hAB_BD
      hAC_BD
      hCB_BD

  --------------------------------------------------------------------
  -- Substitute test 03 into the first summand of test 02, leaving
  -- Square(BD) unchanged.
  --------------------------------------------------------------------

  have h03_with_square :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
         hilbertParallelogramTerm Geo B D F G)
        ((hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
          hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) +
         hilbertParallelogramTerm Geo B D F G) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      h03
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertParallelogramTerm Geo B D F G))

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      h02
      h03_with_square


/--
Euclid II.6 -- test 05.

Transport across the midpoint.

In the standard configuration

  A -- C -- B -- D

with C the midpoint of AB, we have AC ~= CB. Hence any rectangle
contained by AC, BD is scissors-equal to any rectangle contained by
CB, BD.

This is the II.6 analogue of the midpoint transport used in II.5.
-/
private theorem proposition2_6_test05_midpoint_rectangle_transport
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D)

    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)

    (hLeft :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A C B D)

    (hRight :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 C B B D) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3) := by

  --------------------------------------------------------------------
  -- Recover AC ~= CB from the II.6 order skeleton.
  --------------------------------------------------------------------

  have hOrder :=
    proposition2_6_test01_order
      Geo A B C D hMidC hABD

  have hAC_CB :
      Geo.Congruent A C C B :=
    hOrder.2.2.1

  --------------------------------------------------------------------
  -- First sides: U0U1 ~= AC ~= CB ~= V0V1.
  --------------------------------------------------------------------

  have hU01_AC :
      Geo.Congruent U0 U1 A C :=
    hLeft.2.1

  have hV01_CB :
      Geo.Congruent V0 V1 C B :=
    hRight.2.1

  have hCB_V01 :
      Geo.Congruent C B V0 V1 :=
    hilbert_congruent_symmetry
      Geo V0 V1 C B hV01_CB

  have hU01_CB :
      Geo.Congruent U0 U1 C B :=
    hilbert_congruent_transitivity
      Geo U0 U1 A C C B
      hU01_AC hAC_CB

  have hU01_V01 :
      Geo.Congruent U0 U1 V0 V1 :=
    hilbert_congruent_transitivity
      Geo U0 U1 C B V0 V1
      hU01_CB hCB_V01

  --------------------------------------------------------------------
  -- Second sides: both representatives are contained by BD.
  --------------------------------------------------------------------

  have hU12_BD :
      Geo.Congruent U1 U2 B D :=
    hLeft.2.2

  have hV12_BD :
      Geo.Congruent V1 V2 B D :=
    hRight.2.2

  have hBD_V12 :
      Geo.Congruent B D V1 V2 :=
    hilbert_congruent_symmetry
      Geo V1 V2 B D hV12_BD

  have hU12_V12 :
      Geo.Congruent U1 U2 V1 V2 :=
    hilbert_congruent_transitivity
      Geo U1 U2 B D V1 V2
      hU12_BD hBD_V12

  --------------------------------------------------------------------
  -- Rectangles with congruent adjacent sides have equal scissors
  -- content.
  --------------------------------------------------------------------

  exact
    rectangle_transport_scissorsEq
      Geo
      U0 U1 U2 U3
      V0 V1 V2 V3
      hLeft.1
      hRight.1
      hU01_V01
      hU12_V12


/--
Euclid II.6 -- test 06.

Insert the midpoint transport from test 05 into the assembled
decomposition from test 04.

Test 04 gives

  Rect(AD, BD)
    =
  (Rect(AC, BD) + Rect(CB, BD)) + Square(BD).

Test 05 gives

  Rect(AC, BD) = Rect(CB, BD).

Hence

  Rect(AD, BD)
    =
  (Rect(CB, BD) + Rect(CB, BD)) + Square(BD).

No new geometry is introduced here.
-/
private theorem proposition2_6_test06_double_cross
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D)

    ------------------------------------------------------------------
    -- Diagram for test 02 inside test 04.
    ------------------------------------------------------------------

    (E2 H2 L2 X2 : Geo.Point)
    (hRect2 : IsRectangle Geo A D H2 E2)
    (hDH_BD2 : Geo.Congruent D H2 B D)
    (hELE2 : Geo.Between E2 L2 H2)
    (hEXD2 : Geo.Between E2 X2 D)
    (hBXL2 : Geo.Between B X2 L2)
    (hLeftPar2 : IsParallelogram Geo L2 E2 A B)
    (hRightPar2 : IsParallelogram Geo D H2 L2 B)

    (F G : Geo.Point)
    (hSquareBD : IsSquare Geo B D F G)

    -- Rect(AD,BD).
    (U0 U1 U2 U3 : Geo.Point)
    (hAD_BD :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A D B D)

    -- Rect(AB,BD).
    (V0 V1 V2 V3 : Geo.Point)
    (hAB_BD :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A B B D)

    ------------------------------------------------------------------
    -- Diagram for test 03 inside test 04.
    ------------------------------------------------------------------

    (E3 H3 L3 X3 : Geo.Point)
    (hRect3 : IsRectangle Geo A B H3 E3)
    (hBH_BD3 : Geo.Congruent B H3 B D)
    (hELE3 : Geo.Between E3 L3 H3)
    (hEXB3 : Geo.Between E3 X3 B)
    (hCXL3 : Geo.Between C X3 L3)
    (hLeftPar3 : IsParallelogram Geo L3 E3 A C)
    (hRightPar3 : IsParallelogram Geo B H3 L3 C)

    -- Rect(AC,BD).
    (Y0 Y1 Y2 Y3 : Geo.Point)
    (hAC_BD :
      IsRectangleContainedBy Geo
        Y0 Y1 Y2 Y3 A C B D)

    -- Rect(CB,BD).
    (Z0 Z1 Z2 Z3 : Geo.Point)
    (hCB_BD :
      IsRectangleContainedBy Geo
        Z0 Z1 Z2 Z3 C B B D) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      ((hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3 +
        hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) +
       hilbertParallelogramTerm Geo B D F G) := by

  --------------------------------------------------------------------
  -- Assembled decomposition from test 04.
  --------------------------------------------------------------------

  have h04 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        ((hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
          hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) +
         hilbertParallelogramTerm Geo B D F G) :=
    proposition2_6_test04_compose_decompositions
      Geo
      A B C D
      hMidC hABD
      E2 H2 L2 X2
      hRect2 hDH_BD2 hELE2 hEXD2 hBXL2
      hLeftPar2 hRightPar2
      F G
      hSquareBD
      U0 U1 U2 U3
      hAD_BD
      V0 V1 V2 V3
      hAB_BD
      E3 H3 L3 X3
      hRect3 hBH_BD3 hELE3 hEXB3 hCXL3
      hLeftPar3 hRightPar3
      Y0 Y1 Y2 Y3
      hAC_BD
      Z0 Z1 Z2 Z3
      hCB_BD

  --------------------------------------------------------------------
  -- Midpoint transport from test 05.
  --------------------------------------------------------------------

  have h05 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3)
        (hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) :=
    proposition2_6_test05_midpoint_rectangle_transport
      Geo
      A B C D
      hMidC hABD
      Y0 Y1 Y2 Y3
      Z0 Z1 Z2 Z3
      hAC_BD
      hCB_BD

  --------------------------------------------------------------------
  -- Rewrite the first summand:
  --
  --   Rect(AC,BD) + Rect(CB,BD)
  --     =
  --   Rect(CB,BD) + Rect(CB,BD).
  --------------------------------------------------------------------

  have hPair :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
         hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3)
        (hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3 +
         hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      h05
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3))

  --------------------------------------------------------------------
  -- Leave Square(BD) unchanged.
  --------------------------------------------------------------------

  have hPairWithSquare :
      HilbertScissorsEq Geo
        ((hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
          hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) +
         hilbertParallelogramTerm Geo B D F G)
        ((hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3 +
          hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) +
         hilbertParallelogramTerm Geo B D F G) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hPair
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertParallelogramTerm Geo B D F G))

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      h04
      hPairWithSquare


/--
Euclid II.6 -- test 07.

Apply Euclid II.4 to the segment CD cut at B.

The standard II.6 order is

  A -- C -- B -- D,

so test 01 gives C-B-D.  Euclid II.4 with the substitution

  A := C,
  B := D,
  C := B

therefore gives

  Square(CD)
    =
  (Rect(CB,BD) + Square(BC))
    +
  (Rect(CB,BD) + Square(BD)).

This is exactly the second large decomposition needed for II.6.
-/
private theorem proposition2_6_test07_square_cd_decomposition
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D)

    ------------------------------------------------------------------
    -- II.4 diagram: square on CD cut at B.
    ------------------------------------------------------------------

    (D0 E0 L0 X0 : Geo.Point)
    (hSquareCD : IsSquare Geo C D E0 D0)

    (hD0L0E0 : Geo.Between D0 L0 E0)
    (hD0X0D : Geo.Between D0 X0 D)
    (hBX0L0 : Geo.Between B X0 L0)

    (hII4LeftPar :
      IsParallelogram Geo L0 D0 C B)

    (hII4RightPar :
      IsParallelogram Geo D E0 L0 B)

    -- Representatives of Rect(CD,CB) and Rect(CD,BD).
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)

    (hCD_CB :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 C D C B)

    (hCD_BD :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 C D B D)

    ------------------------------------------------------------------
    -- II.3 diagram for the left term.
    --
    -- II.4 reverses C-B-D to D-B-C and obtains
    --
    --   Rect(DC,BC) = Rect(DB,BC) + Square(BC).
    ------------------------------------------------------------------

    (D1 E1 L1 X1 : Geo.Point)

    (hRectLeft :
      IsRectangle Geo D C E1 D1)

    (hCE1_BC :
      Geo.Congruent C E1 B C)

    (hD1L1E1 : Geo.Between D1 L1 E1)
    (hD1X1C : Geo.Between D1 X1 C)
    (hBX1L1 : Geo.Between B X1 L1)

    (hLeftLeftPar :
      IsParallelogram Geo L1 D1 D B)

    (hLeftRightPar :
      IsParallelogram Geo C E1 L1 B)

    -- Square on BC.
    (F G : Geo.Point)
    (hSquareBC : IsSquare Geo B C F G)

    ------------------------------------------------------------------
    -- II.3 diagram for the right term:
    --
    --   Rect(CD,BD) = Rect(CB,BD) + Square(BD).
    ------------------------------------------------------------------

    (D2 E2 L2 X2 : Geo.Point)

    (hRectRight :
      IsRectangle Geo C D E2 D2)

    (hDE2_BD :
      Geo.Congruent D E2 B D)

    (hD2L2E2 : Geo.Between D2 L2 E2)
    (hD2X2D : Geo.Between D2 X2 D)
    (hBX2L2 : Geo.Between B X2 L2)

    (hRightLeftPar :
      IsParallelogram Geo L2 D2 C B)

    (hRightRightPar :
      IsParallelogram Geo D E2 L2 B)

    -- Square on BD.
    (H K : Geo.Point)
    (hSquareBD : IsSquare Geo B D H K)

    ------------------------------------------------------------------
    -- Two arbitrary representatives of the repeated cross rectangle
    -- Rect(CB,BD).
    ------------------------------------------------------------------

    (T10 T11 T12 T13 : Geo.Point)
    (T20 T21 T22 T23 : Geo.Point)

    (hCross1 :
      IsRectangleContainedBy Geo
        T10 T11 T12 T13 C B B D)

    (hCross2 :
      IsRectangleContainedBy Geo
        T20 T21 T22 T23 C B B D) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo C D E0 D0)
      ((hilbertParallelogramTerm Geo T20 T21 T22 T23 +
        hilbertParallelogramTerm Geo B C F G) +
       (hilbertParallelogramTerm Geo T10 T11 T12 T13 +
        hilbertParallelogramTerm Geo B D H K)) := by

  --------------------------------------------------------------------
  -- Recover C-B-D from the standard II.6 configuration.
  --------------------------------------------------------------------

  have hOrder :=
    proposition2_6_test01_order
      Geo A B C D hMidC hABD

  have hCBD : Geo.Between C B D :=
    hOrder.1

  --------------------------------------------------------------------
  -- Euclid II.4 with
  --
  --   A := C,
  --   B := D,
  --   C := B.
  --------------------------------------------------------------------

  exact
    euclid_proposition_2_4
      Geo
      C D B
      D0 E0 L0 X0
      hSquareCD
      hCBD
      hD0L0E0
      hD0X0D
      hBX0L0
      hII4LeftPar
      hII4RightPar
      U0 U1 U2 U3
      V0 V1 V2 V3
      hCD_CB
      hCD_BD
      D1 E1 L1 X1
      hRectLeft
      hCE1_BC
      hD1L1E1
      hD1X1C
      hBX1L1
      hLeftLeftPar
      hLeftRightPar
      F G
      hSquareBC
      D2 E2 L2 X2
      hRectRight
      hDE2_BD
      hD2L2E2
      hD2X2D
      hBX2L2
      hRightLeftPar
      hRightRightPar
      H K
      hSquareBD
      T10 T11 T12 T13
      T20 T21 T22 T23
      hCross1
      hCross2


/--
Euclid II.6 -- test 08, algebraic scissors bridge.

Suppose

  P = (R + R) + T

and

  Q = (R + S) + (R + T).

Then

  S + P = Q.

For II.6 the intended substitution is

  P = Rect(AD,BD),
  Q = Square(CD),
  R = Rect(CB,BD),
  S = Square(CB),
  T = Square(BD).

Thus this lemma is the exact purely algebraic bridge between
test 06 and test 07.
-/
private theorem proposition2_6_test08_scissors_bridge
    (P Q R S T : HilbertScissorsTerm Geo)
    (hP :
      HilbertScissorsEq Geo
        P
        ((R + R) + T))
    (hQ :
      HilbertScissorsEq Geo
        Q
        ((R + S) + (R + T))) :
    HilbertScissorsEq Geo
      (S + P)
      Q := by

  --------------------------------------------------------------------
  -- Add S to the decomposition of P.
  --------------------------------------------------------------------

  have hAddS :
      HilbertScissorsEq Geo
        (S + P)
        (S + ((R + R) + T)) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.refl
        (Geo := Geo) S)
      hP

  --------------------------------------------------------------------
  -- Pure AC rearrangement of the multiset sum:
  --
  --   S + ((R + R) + T)
  --     =
  --   (R + S) + (R + T).
  --------------------------------------------------------------------

  have hRegroup :
      S + ((R + R) + T)
        =
      (R + S) + (R + T) := by
    ac_rfl

  have hToQShape :
      HilbertScissorsEq Geo
        (S + P)
        ((R + S) + (R + T)) := by
    rw [hRegroup] at hAddS
    exact hAddS

  --------------------------------------------------------------------
  -- Substitute the decomposition of Q backwards.
  --------------------------------------------------------------------

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hToQShape
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hQ)


/--
Euclid II.6 -- test 09.

This is the first complete assembly of the proposition.

The three inputs are:

  test 06:
    Rect(AD,BD)
      =
    (Rect(CB,BD) + Rect(CB,BD)) + Square(BD),

  test 07:
    Square(CD)
      =
    (Rect(CB,BD) + Square(BC))
      +
    (Rect(CB,BD) + Square(BD)),

  test 08:
    the purely algebraic scissors bridge.

The same concrete representative Z of Rect(CB,BD) is fed into both
cross-rectangle slots of test 07, and the same square on BD is used
in tests 06 and 07.  Therefore no additional transport is needed.

Conclusion:

  Square(BC) + Rect(AD,BD) = Square(CD).
-/
private theorem proposition2_6_test09_assembly
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D)

    ------------------------------------------------------------------
    -- Data for test 06.
    ------------------------------------------------------------------

    (E2 H2 L2 X2 : Geo.Point)
    (hRect2 : IsRectangle Geo A D H2 E2)
    (hDH_BD2 : Geo.Congruent D H2 B D)
    (hELE2 : Geo.Between E2 L2 H2)
    (hEXD2 : Geo.Between E2 X2 D)
    (hBXL2 : Geo.Between B X2 L2)
    (hLeftPar2 : IsParallelogram Geo L2 E2 A B)
    (hRightPar2 : IsParallelogram Geo D H2 L2 B)

    -- Square on BD, shared by tests 06 and 07.
    (F G : Geo.Point)
    (hSquareBD : IsSquare Geo B D F G)

    -- Rect(AD,BD).
    (P0 P1 P2 P3 : Geo.Point)
    (hAD_BD :
      IsRectangleContainedBy Geo
        P0 P1 P2 P3 A D B D)

    -- Rect(AB,BD).
    (V0 V1 V2 V3 : Geo.Point)
    (hAB_BD :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A B B D)

    (E3 H3 L3 X3 : Geo.Point)
    (hRect3 : IsRectangle Geo A B H3 E3)
    (hBH_BD3 : Geo.Congruent B H3 B D)
    (hELE3 : Geo.Between E3 L3 H3)
    (hEXB3 : Geo.Between E3 X3 B)
    (hCXL3 : Geo.Between C X3 L3)
    (hLeftPar3 : IsParallelogram Geo L3 E3 A C)
    (hRightPar3 : IsParallelogram Geo B H3 L3 C)

    -- Rect(AC,BD).
    (Y0 Y1 Y2 Y3 : Geo.Point)
    (hAC_BD :
      IsRectangleContainedBy Geo
        Y0 Y1 Y2 Y3 A C B D)

    -- The single representative R = Rect(CB,BD).
    (Z0 Z1 Z2 Z3 : Geo.Point)
    (hCB_BD :
      IsRectangleContainedBy Geo
        Z0 Z1 Z2 Z3 C B B D)

    ------------------------------------------------------------------
    -- Data for test 07: II.4 on CD cut at B.
    ------------------------------------------------------------------

    (D0 E0 L0 X0 : Geo.Point)
    (hSquareCD : IsSquare Geo C D E0 D0)

    (hD0L0E0 : Geo.Between D0 L0 E0)
    (hD0X0D : Geo.Between D0 X0 D)
    (hBX0L0 : Geo.Between B X0 L0)

    (hII4LeftPar :
      IsParallelogram Geo L0 D0 C B)

    (hII4RightPar :
      IsParallelogram Geo D E0 L0 B)

    -- Representatives required internally by II.4.
    (J0 J1 J2 J3 : Geo.Point)
    (K0 K1 K2 K3 : Geo.Point)

    (hCD_CB :
      IsRectangleContainedBy Geo
        J0 J1 J2 J3 C D C B)

    (hCD_BD :
      IsRectangleContainedBy Geo
        K0 K1 K2 K3 C D B D)

    ------------------------------------------------------------------
    -- Left II.3 decomposition inside II.4.
    ------------------------------------------------------------------

    (D1 E1 L1 X1 : Geo.Point)

    (hRectLeft :
      IsRectangle Geo D C E1 D1)

    (hCE1_BC :
      Geo.Congruent C E1 B C)

    (hD1L1E1 : Geo.Between D1 L1 E1)
    (hD1X1C : Geo.Between D1 X1 C)
    (hBX1L1 : Geo.Between B X1 L1)

    (hLeftLeftPar :
      IsParallelogram Geo L1 D1 D B)

    (hLeftRightPar :
      IsParallelogram Geo C E1 L1 B)

    -- Square on BC.
    (S0 S1 : Geo.Point)
    (hSquareBC : IsSquare Geo B C S0 S1)

    ------------------------------------------------------------------
    -- Right II.3 decomposition inside II.4.
    ------------------------------------------------------------------

    (D2 E4 L4 X4 : Geo.Point)

    (hRectRight :
      IsRectangle Geo C D E4 D2)

    (hDE4_BD :
      Geo.Congruent D E4 B D)

    (hD2L4E4 : Geo.Between D2 L4 E4)
    (hD2X4D : Geo.Between D2 X4 D)
    (hBX4L4 : Geo.Between B X4 L4)

    (hRightLeftPar :
      IsParallelogram Geo L4 D2 C B)

    (hRightRightPar :
      IsParallelogram Geo D E4 L4 B) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo B C S0 S1 +
       hilbertParallelogramTerm Geo P0 P1 P2 P3)
      (hilbertParallelogramTerm Geo C D E0 D0) := by

  --------------------------------------------------------------------
  -- test 06:
  --
  -- P = (R + R) + T.
  --------------------------------------------------------------------

  have h06 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo P0 P1 P2 P3)
        ((hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3 +
          hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) +
         hilbertParallelogramTerm Geo B D F G) :=
    proposition2_6_test06_double_cross
      Geo
      A B C D
      hMidC hABD
      E2 H2 L2 X2
      hRect2 hDH_BD2 hELE2 hEXD2 hBXL2
      hLeftPar2 hRightPar2
      F G
      hSquareBD
      P0 P1 P2 P3
      hAD_BD
      V0 V1 V2 V3
      hAB_BD
      E3 H3 L3 X3
      hRect3 hBH_BD3 hELE3 hEXB3 hCXL3
      hLeftPar3 hRightPar3
      Y0 Y1 Y2 Y3
      hAC_BD
      Z0 Z1 Z2 Z3
      hCB_BD

  --------------------------------------------------------------------
  -- test 07:
  --
  -- Q = (R + S) + (R + T).
  --
  -- Use Z in BOTH cross-rectangle slots, and use the SAME square
  -- on BD, namely B D F G.
  --------------------------------------------------------------------

  have h07 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo C D E0 D0)
        ((hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3 +
          hilbertParallelogramTerm Geo B C S0 S1) +
         (hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3 +
          hilbertParallelogramTerm Geo B D F G)) :=
    proposition2_6_test07_square_cd_decomposition
      Geo
      A B C D
      hMidC hABD
      D0 E0 L0 X0
      hSquareCD
      hD0L0E0
      hD0X0D
      hBX0L0
      hII4LeftPar
      hII4RightPar
      J0 J1 J2 J3
      K0 K1 K2 K3
      hCD_CB
      hCD_BD
      D1 E1 L1 X1
      hRectLeft
      hCE1_BC
      hD1L1E1
      hD1X1C
      hBX1L1
      hLeftLeftPar
      hLeftRightPar
      S0 S1
      hSquareBC
      D2 E4 L4 X4
      hRectRight
      hDE4_BD
      hD2L4E4
      hD2X4D
      hBX4L4
      hRightLeftPar
      hRightRightPar
      F G
      hSquareBD
      Z0 Z1 Z2 Z3
      Z0 Z1 Z2 Z3
      hCB_BD
      hCB_BD

  --------------------------------------------------------------------
  -- test 08 with the literal substitutions
  --
  --   P := Rect(AD,BD)
  --   Q := Square(CD)
  --   R := Rect(CB,BD)
  --   S := Square(BC)
  --   T := Square(BD).
  --------------------------------------------------------------------

  exact
    proposition2_6_test08_scissors_bridge
      Geo
      (hilbertParallelogramTerm Geo P0 P1 P2 P3)
      (hilbertParallelogramTerm Geo C D E0 D0)
      (hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3)
      (hilbertParallelogramTerm Geo B C S0 S1)
      (hilbertParallelogramTerm Geo B D F G)
      h06
      h07


/--
Euclid, Elements II.6.

Public wrapper around proposition2_6_test09_assembly.
No new mathematical argument is introduced here.
-/
theorem euclid_proposition_2_6
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D)

    ------------------------------------------------------------------
    -- Data for test 06.
    ------------------------------------------------------------------

    (E2 H2 L2 X2 : Geo.Point)
    (hRect2 : IsRectangle Geo A D H2 E2)
    (hDH_BD2 : Geo.Congruent D H2 B D)
    (hELE2 : Geo.Between E2 L2 H2)
    (hEXD2 : Geo.Between E2 X2 D)
    (hBXL2 : Geo.Between B X2 L2)
    (hLeftPar2 : IsParallelogram Geo L2 E2 A B)
    (hRightPar2 : IsParallelogram Geo D H2 L2 B)

    -- Square on BD, shared by tests 06 and 07.
    (F G : Geo.Point)
    (hSquareBD : IsSquare Geo B D F G)

    -- Rect(AD,BD).
    (P0 P1 P2 P3 : Geo.Point)
    (hAD_BD :
      IsRectangleContainedBy Geo
        P0 P1 P2 P3 A D B D)

    -- Rect(AB,BD).
    (V0 V1 V2 V3 : Geo.Point)
    (hAB_BD :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A B B D)

    (E3 H3 L3 X3 : Geo.Point)
    (hRect3 : IsRectangle Geo A B H3 E3)
    (hBH_BD3 : Geo.Congruent B H3 B D)
    (hELE3 : Geo.Between E3 L3 H3)
    (hEXB3 : Geo.Between E3 X3 B)
    (hCXL3 : Geo.Between C X3 L3)
    (hLeftPar3 : IsParallelogram Geo L3 E3 A C)
    (hRightPar3 : IsParallelogram Geo B H3 L3 C)

    -- Rect(AC,BD).
    (Y0 Y1 Y2 Y3 : Geo.Point)
    (hAC_BD :
      IsRectangleContainedBy Geo
        Y0 Y1 Y2 Y3 A C B D)

    -- The single representative R = Rect(CB,BD).
    (Z0 Z1 Z2 Z3 : Geo.Point)
    (hCB_BD :
      IsRectangleContainedBy Geo
        Z0 Z1 Z2 Z3 C B B D)

    ------------------------------------------------------------------
    -- Data for test 07: II.4 on CD cut at B.
    ------------------------------------------------------------------

    (D0 E0 L0 X0 : Geo.Point)
    (hSquareCD : IsSquare Geo C D E0 D0)

    (hD0L0E0 : Geo.Between D0 L0 E0)
    (hD0X0D : Geo.Between D0 X0 D)
    (hBX0L0 : Geo.Between B X0 L0)

    (hII4LeftPar :
      IsParallelogram Geo L0 D0 C B)

    (hII4RightPar :
      IsParallelogram Geo D E0 L0 B)

    -- Representatives required internally by II.4.
    (J0 J1 J2 J3 : Geo.Point)
    (K0 K1 K2 K3 : Geo.Point)

    (hCD_CB :
      IsRectangleContainedBy Geo
        J0 J1 J2 J3 C D C B)

    (hCD_BD :
      IsRectangleContainedBy Geo
        K0 K1 K2 K3 C D B D)

    ------------------------------------------------------------------
    -- Left II.3 decomposition inside II.4.
    ------------------------------------------------------------------

    (D1 E1 L1 X1 : Geo.Point)

    (hRectLeft :
      IsRectangle Geo D C E1 D1)

    (hCE1_BC :
      Geo.Congruent C E1 B C)

    (hD1L1E1 : Geo.Between D1 L1 E1)
    (hD1X1C : Geo.Between D1 X1 C)
    (hBX1L1 : Geo.Between B X1 L1)

    (hLeftLeftPar :
      IsParallelogram Geo L1 D1 D B)

    (hLeftRightPar :
      IsParallelogram Geo C E1 L1 B)

    -- Square on BC.
    (S0 S1 : Geo.Point)
    (hSquareBC : IsSquare Geo B C S0 S1)

    ------------------------------------------------------------------
    -- Right II.3 decomposition inside II.4.
    ------------------------------------------------------------------

    (D2 E4 L4 X4 : Geo.Point)

    (hRectRight :
      IsRectangle Geo C D E4 D2)

    (hDE4_BD :
      Geo.Congruent D E4 B D)

    (hD2L4E4 : Geo.Between D2 L4 E4)
    (hD2X4D : Geo.Between D2 X4 D)
    (hBX4L4 : Geo.Between B X4 L4)

    (hRightLeftPar :
      IsParallelogram Geo L4 D2 C B)

    (hRightRightPar :
      IsParallelogram Geo D E4 L4 B) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo B C S0 S1 +
       hilbertParallelogramTerm Geo P0 P1 P2 P3)
      (hilbertParallelogramTerm Geo C D E0 D0) := by
  exact
    proposition2_6_test09_assembly
      Geo
      A B C D
      hMidC hABD
      E2 H2 L2 X2
      hRect2 hDH_BD2 hELE2 hEXD2 hBXL2
      hLeftPar2 hRightPar2
      F G
      hSquareBD
      P0 P1 P2 P3
      hAD_BD
      V0 V1 V2 V3
      hAB_BD
      E3 H3 L3 X3
      hRect3 hBH_BD3 hELE3 hEXB3 hCXL3
      hLeftPar3 hRightPar3
      Y0 Y1 Y2 Y3
      hAC_BD
      Z0 Z1 Z2 Z3
      hCB_BD
      D0 E0 L0 X0
      hSquareCD
      hD0L0E0
      hD0X0D
      hBX0L0
      hII4LeftPar
      hII4RightPar
      J0 J1 J2 J3
      K0 K1 K2 K3
      hCD_CB
      hCD_BD
      D1 E1 L1 X1
      hRectLeft
      hCE1_BC
      hD1L1E1
      hD1X1C
      hBX1L1
      hLeftLeftPar
      hLeftRightPar
      S0 S1
      hSquareBC
      D2 E4 L4 X4
      hRectRight
      hDE4_BD
      hD2L4E4
      hD2X4D
      hBX4L4
      hRightLeftPar
      hRightRightPar

end Geometry

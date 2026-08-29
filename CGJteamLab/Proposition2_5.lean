import CGJteamLab.Proposition2_4
namespace Geometry
universe u
variable (Geo : Geometry.Geo)


/--
Euclid II.5 -- test 01.

Order skeleton for the standard configuration

  A -- D -- C -- B

where C is the midpoint of AB and D is the arbitrary cut point on AC.

The important point is that `D-C-B` and `A-D-B` need not be assumed:
they follow from `A-D-C` and the midpoint condition `A-C-B`.

We also record the congruence of the two halves in both orientations,
which will be used to transport rectangle representatives later.
-/
private theorem proposition2_5_test01_order
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hADC : Geo.Between A D C) :
    Geo.Between D C B /\
    Geo.Between A D B /\
    Geo.Congruent A C C B /\
    Geo.Congruent C A C B := by

  --------------------------------------------------------------------
  -- Since A-D-C and A-C-B, Hilbert inner transitivity gives
  -- both D-C-B and A-D-B.
  --------------------------------------------------------------------

  have hOrder :
      Geo.Between D C B /\
      Geo.Between A D B :=
    hilbert_between_inner_trans
      Geo A D C B
      hADC
      hMidC.1

  have hDCB : Geo.Between D C B :=
    hOrder.1

  have hADB : Geo.Between A D B :=
    hOrder.2

  --------------------------------------------------------------------
  -- C is the midpoint of AB, hence AC ~= CB.
  --------------------------------------------------------------------

  have hAC_CB :
      Geo.Congruent A C C B :=
    hMidC.2

  --------------------------------------------------------------------
  -- The same equality with the first segment reversed.
  --------------------------------------------------------------------

  have hCA_CB :
      Geo.Congruent C A C B :=
    CongruentReverseFirst
      Geo A C C B
      hAC_CB

  exact
    And.intro
      hDCB
      (And.intro
        hADB
        (And.intro
          hAC_CB
          hCA_CB))


/--
Euclid II.5 -- test 02.

First scissors-calculus component of II.5.

In the order

  A -- D -- C -- B

apply Euclid II.3 to the segment AC cut at D, with DC as the fixed
second side.  This gives

  Rect(AC, DC) = Rect(AD, DC) + Square(DC).

At this stage the point B and the midpoint hypothesis are present only
because this lemma is intended to sit directly inside the II.5
configuration.  The actual II.3 application uses only A-D-C.
-/
private theorem proposition2_5_test02_left_decomposition
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hADC : Geo.Between A D C)

    -- Concrete II.1/II.3 cut diagram for Rect(AC, DC).
    (E H L X : Geo.Point)
    (hRect : IsRectangle Geo A C H E)
    (hCH_DC : Geo.Congruent C H D C)
    (hELE : Geo.Between E L H)
    (hEXC : Geo.Between E X C)
    (hDXL : Geo.Between D X L)
    (hLeftPar : IsParallelogram Geo L E A D)
    (hRightPar : IsParallelogram Geo C H L D)

    -- Square on DC.
    (F G : Geo.Point)
    (hSquare : IsSquare Geo D C F G)

    -- Arbitrary representatives of Rect(AC, DC) and Rect(AD, DC).
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)
    (hWhole :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A C D C)
    (hProduct :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A D D C) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       hilbertParallelogramTerm Geo D C F G) := by

  --------------------------------------------------------------------
  -- Keep the II.5 order skeleton available.  In particular this
  -- verifies that the present local diagram really lies in the
  -- standard configuration A-D-C-B.
  --------------------------------------------------------------------

  have hOrder :=
    proposition2_5_test01_order
      Geo A B C D hMidC hADC

  have hDCB : Geo.Between D C B := hOrder.1
  have hADB : Geo.Between A D B := hOrder.2.1

  -- These two facts are intentionally retained as named local facts:
  -- they will be used by the next II.5 test.  They are not needed by
  -- the II.3 call itself.
  have _hDCB := hDCB
  have _hADB := hADB

  --------------------------------------------------------------------
  -- Euclid II.3 with the substitution
  --
  --   B -> A,   M -> D,   C -> C.
  --
  -- Hence BC becomes AC and MC becomes DC.
  --------------------------------------------------------------------

  exact
    euclid_proposition_2_3
      Geo
      A C E H L D X
      hRect
      hCH_DC
      hADC
      hELE
      hEXC
      hDXL
      hLeftPar
      hRightPar
      F G
      hSquare
      U0 U1 U2 U3
      V0 V1 V2 V3
      hWhole
      hProduct


/--
Euclid II.5 -- test 03.

Transport across the midpoint.

In the standard configuration

  A -- D -- C -- B

with C the midpoint of AB, we have AC ~= CB.  Hence any rectangle
contained by AC, DC is scissors-equal to any rectangle contained by
CB, DC.

This is the bridge which replaces the left half AC by the right half
CB in the II.5 calculation.
-/
private theorem proposition2_5_test03_midpoint_rectangle_transport
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hADC : Geo.Between A D C)

    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)
    (hLeft :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A C D C)
    (hRight :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 C B D C) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3) := by

  --------------------------------------------------------------------
  -- Recover AC ~= CB from the standard II.5 order skeleton.
  --------------------------------------------------------------------

  have hOrder :=
    proposition2_5_test01_order
      Geo A B C D hMidC hADC

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
  -- Second sides: both representatives are contained by DC.
  --------------------------------------------------------------------

  have hU12_DC :
      Geo.Congruent U1 U2 D C :=
    hLeft.2.2

  have hV12_DC :
      Geo.Congruent V1 V2 D C :=
    hRight.2.2

  have hDC_V12 :
      Geo.Congruent D C V1 V2 :=
    hilbert_congruent_symmetry
      Geo V1 V2 D C hV12_DC

  have hU12_V12 :
      Geo.Congruent U1 U2 V1 V2 :=
    hilbert_congruent_transitivity
      Geo U1 U2 D C V1 V2
      hU12_DC hDC_V12

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
Euclid II.5 -- test 04.

First assembled identity in the II.5 configuration.

From test 02:

  Rect(AC, DC) = Rect(AD, DC) + Square(DC).

From test 03, using C as midpoint of AB:

  Rect(AC, DC) = Rect(CB, DC).

Therefore:

  Rect(CB, DC) = Rect(AD, DC) + Square(DC).

No new geometry is introduced here.  This test checks only that the two
previous increments compose cleanly in HilbertScissorsEq.
-/
private theorem proposition2_5_test04_first_assembled_identity
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hADC : Geo.Between A D C)

    -- Concrete II.3 cut diagram for Rect(AC, DC).
    (E H L X : Geo.Point)
    (hRect : IsRectangle Geo A C H E)
    (hCH_DC : Geo.Congruent C H D C)
    (hELE : Geo.Between E L H)
    (hEXC : Geo.Between E X C)
    (hDXL : Geo.Between D X L)
    (hLeftPar : IsParallelogram Geo L E A D)
    (hRightPar : IsParallelogram Geo C H L D)

    -- Square on DC.
    (F G : Geo.Point)
    (hSquare : IsSquare Geo D C F G)

    -- Representatives of Rect(AC, DC), Rect(AD, DC), Rect(CB, DC).
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)
    (W0 W1 W2 W3 : Geo.Point)
    (hWhole :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A C D C)
    (hProduct :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A D D C)
    (hHalf :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 C B D C) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo W0 W1 W2 W3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       hilbertParallelogramTerm Geo D C F G) := by

  --------------------------------------------------------------------
  -- test 02: Rect(AC, DC) = Rect(AD, DC) + Square(DC).
  --------------------------------------------------------------------

  have hDecomp :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
         hilbertParallelogramTerm Geo D C F G) :=
    proposition2_5_test02_left_decomposition
      Geo
      A B C D
      hMidC hADC
      E H L X
      hRect hCH_DC hELE hEXC hDXL
      hLeftPar hRightPar
      F G hSquare
      U0 U1 U2 U3
      V0 V1 V2 V3
      hWhole hProduct

  --------------------------------------------------------------------
  -- test 03: Rect(AC, DC) = Rect(CB, DC).
  --------------------------------------------------------------------

  have hTransport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo W0 W1 W2 W3) :=
    proposition2_5_test03_midpoint_rectangle_transport
      Geo
      A B C D
      hMidC hADC
      U0 U1 U2 U3
      W0 W1 W2 W3
      hWhole hHalf

  --------------------------------------------------------------------
  -- Reverse the transport and compose.
  --------------------------------------------------------------------

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      (HilbertScissorsEq.symm
        (Geo := Geo) hTransport)
      hDecomp


/--
Euclid II.5 -- test 05.

Second decomposition needed for II.5.

In the standard order

  A -- D -- C -- B

we have D-C-B.  Apply Euclid II.1 (two-part form) to the segment DB,
cut at C, with AD as the fixed second side.  This gives

  Rect(DB, AD) = Rect(DC, AD) + Rect(CB, AD).

This test deliberately keeps the factors in the order produced by II.1.
Commutativity of rectangle-contained-by will be handled in a later
increment.
-/
private theorem proposition2_5_test05_db_decomposition
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hADC : Geo.Between A D C)

    -- Concrete II.1 cut diagram for Rect(DB, AD).
    (E H L X : Geo.Point)
    (hRect : IsRectangle Geo D B H E)
    (hBH_AD : Geo.Congruent B H A D)
    (hELE : Geo.Between E L H)
    (hEXB : Geo.Between E X B)
    (hCXL : Geo.Between C X L)
    (hLeftPar : IsParallelogram Geo L E D C)
    (hRightPar : IsParallelogram Geo B H L C)

    -- Arbitrary representatives of Rect(DB,AD), Rect(DC,AD), Rect(CB,AD).
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)
    (W0 W1 W2 W3 : Geo.Point)

    (hWhole :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 D B A D)

    (hPart1 :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 D C A D)

    (hPart2 :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 C B A D) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       hilbertParallelogramTerm Geo W0 W1 W2 W3) := by

  --------------------------------------------------------------------
  -- From the midpoint configuration and A-D-C obtain D-C-B.
  --------------------------------------------------------------------

  have hOrder :=
    proposition2_5_test01_order
      Geo A B C D hMidC hADC

  have hDCB : Geo.Between D C B :=
    hOrder.1

  --------------------------------------------------------------------
  -- Euclid II.1 (two-part form) with
  --
  --   B -> D,   C -> B,   M -> C,   PQ -> AD.
  --
  -- Thus DB is split into DC and CB.
  --------------------------------------------------------------------

  exact
    euclid_proposition_2_1_two
      Geo
      D B E H L C X A D
      hRect
      hBH_AD
      hDCB
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
Euclid II.5 -- test 06.

Normalize the first summand in the decomposition from test 05.

Test 05 produces

  Rect(DB, AD) = Rect(DC, AD) + Rect(CB, AD).

By commutativity of rectangle-contained-by,

  Rect(DC, AD) = Rect(AD, DC).

This test lifts that equality through addition, giving

  Rect(DC, AD) + T = Rect(AD, DC) + T

for the concrete second term T used later.
-/
private theorem proposition2_5_test06_commute_first_piece
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A C D : Geo.Point)

    -- Representative of Rect(DC, AD).
    (V0 V1 V2 V3 : Geo.Point)
    (hDC_AD :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 D C A D)

    -- Representative of Rect(AD, DC).
    (X0 X1 X2 X3 : Geo.Point)
    (hAD_DC :
      IsRectangleContainedBy Geo
        X0 X1 X2 X3 A D D C)

    -- An arbitrary second summand, later Rect(CB, AD).
    (W0 W1 W2 W3 : Geo.Point) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
       hilbertParallelogramTerm Geo W0 W1 W2 W3)
      (hilbertParallelogramTerm Geo X0 X1 X2 X3 +
       hilbertParallelogramTerm Geo W0 W1 W2 W3) := by

  have hComm :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo V0 V1 V2 V3)
        (hilbertParallelogramTerm Geo X0 X1 X2 X3) :=
    rectangle_contained_by_comm
      Geo
      V0 V1 V2 V3
      X0 X1 X2 X3
      D C A D
      hDC_AD
      hAD_DC

  exact
    HilbertScissorsEq.add
      (Geo := Geo)
      hComm
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertParallelogramTerm Geo W0 W1 W2 W3))


/--
Euclid II.5 -- test 07.

Combine test 05 with the commutativity normalization from test 06.

Test 05 gives

  Rect(DB, AD) = Rect(DC, AD) + Rect(CB, AD),

and test 06 rewrites the first summand as

  Rect(DC, AD) + Rect(CB, AD)
    = Rect(AD, DC) + Rect(CB, AD).

Hence

  Rect(DB, AD)
    = Rect(AD, DC) + Rect(CB, AD).

No new geometry is introduced here; this is only transitivity of
HilbertScissorsEq.
-/
private theorem proposition2_5_test07_db_decomposition_normalized
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hADC : Geo.Between A D C)

    -- Concrete II.1 cut diagram for Rect(DB, AD).
    (E H L X : Geo.Point)
    (hRect : IsRectangle Geo D B H E)
    (hBH_AD : Geo.Congruent B H A D)
    (hELE : Geo.Between E L H)
    (hEXB : Geo.Between E X B)
    (hCXL : Geo.Between C X L)
    (hLeftPar : IsParallelogram Geo L E D C)
    (hRightPar : IsParallelogram Geo B H L C)

    -- Representatives of Rect(DB,AD), Rect(DC,AD), Rect(CB,AD).
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)
    (W0 W1 W2 W3 : Geo.Point)

    (hWhole :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 D B A D)

    (hPart1 :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 D C A D)

    (hPart2 :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 C B A D)

    -- A representative of the commuted rectangle Rect(AD,DC).
    (T0 T1 T2 T3 : Geo.Point)
    (hAD_DC :
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 A D D C) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo U0 U1 U2 U3)
      (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
       hilbertParallelogramTerm Geo W0 W1 W2 W3) := by

  have hDecomp :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
         hilbertParallelogramTerm Geo W0 W1 W2 W3) :=
    proposition2_5_test05_db_decomposition
      Geo
      A B C D
      hMidC
      hADC
      E H L X
      hRect
      hBH_AD
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

  have hNormalize :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo V0 V1 V2 V3 +
         hilbertParallelogramTerm Geo W0 W1 W2 W3)
        (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
         hilbertParallelogramTerm Geo W0 W1 W2 W3) :=
    proposition2_5_test06_commute_first_piece
      Geo
      A C D
      V0 V1 V2 V3
      hPart1
      T0 T1 T2 T3
      hAD_DC
      W0 W1 W2 W3

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hDecomp
      hNormalize


/--
Euclid II.5 -- test 08, algebraic scissors bridge.

Suppose

  P = X + Y
  Z = X + S.

Then

  P + S = Y + Z.

This is the exact formal rearrangement needed to combine test 07 with
 test 04.  Notice that no cancellation principle is needed.
-/
private theorem proposition2_5_test08_scissors_bridge
    (P X Y Z S : HilbertScissorsTerm Geo)
    (hP : HilbertScissorsEq Geo P (X + Y))
    (hZ : HilbertScissorsEq Geo Z (X + S)) :
    HilbertScissorsEq Geo
      (P + S)
      (Y + Z) := by

  have hAddS :
      HilbertScissorsEq Geo
        (P + S)
        ((X + Y) + S) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hP
      (HilbertScissorsEq.refl
        (Geo := Geo) S)

  have hRearranged :
      HilbertScissorsEq Geo
        (P + S)
        (Y + (X + S)) := by
    simpa only
      [Multiset.add_assoc,
       Multiset.add_comm X Y]
      using hAddS

  have hSubstitute :
      HilbertScissorsEq Geo
        (Y + (X + S))
        (Y + Z) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.refl
        (Geo := Geo) Y)
      (HilbertScissorsEq.symm
        (Geo := Geo) hZ)

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hRearranged
      hSubstitute

/--
Euclid II.5 -- test 08, first core identity.

Test 07 gives

  Rect(DB, AD)
    = Rect(AD, DC) + Rect(CB, AD).

Test 04 gives

  Rect(CB, DC)
    = Rect(AD, DC) + Square(DC).

The algebraic bridge above therefore yields

  Rect(DB, AD) + Square(DC)
    = Rect(CB, AD) + Rect(CB, DC).

This is already the main algebraic content of II.5.  The remaining work
will be to combine the two rectangles on the right into Rect(CB, AC),
and then identify that rectangle with the square on CB using AC = CB.
-/
private theorem proposition2_5_test08_core_identity
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hADC : Geo.Between A D C)

    ---------------------------------------------------------------
    -- Data for test 04:
    -- Rect(CB,DC) = Rect(AD,DC) + Square(DC).
    ---------------------------------------------------------------

    (E4 H4 L4 X4 : Geo.Point)
    (hRect4 : IsRectangle Geo A C H4 E4)
    (hCH_DC : Geo.Congruent C H4 D C)
    (hELE4 : Geo.Between E4 L4 H4)
    (hEXC4 : Geo.Between E4 X4 C)
    (hDXL4 : Geo.Between D X4 L4)
    (hLeftPar4 : IsParallelogram Geo L4 E4 A D)
    (hRightPar4 : IsParallelogram Geo C H4 L4 D)

    (F G : Geo.Point)
    (hSquare : IsSquare Geo D C F G)

    -- Rect(AC,DC).
    (R0 R1 R2 R3 : Geo.Point)
    (hAC_DC :
      IsRectangleContainedBy Geo
        R0 R1 R2 R3 A C D C)

    -- Common representative Rect(AD,DC), shared by test 04 and test 07.
    (T0 T1 T2 T3 : Geo.Point)
    (hAD_DC :
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 A D D C)

    -- Rect(CB,DC).
    (Z0 Z1 Z2 Z3 : Geo.Point)
    (hCB_DC :
      IsRectangleContainedBy Geo
        Z0 Z1 Z2 Z3 C B D C)

    ---------------------------------------------------------------
    -- Data for test 07:
    -- Rect(DB,AD) = Rect(AD,DC) + Rect(CB,AD).
    ---------------------------------------------------------------

    (E7 H7 L7 X7 : Geo.Point)
    (hRect7 : IsRectangle Geo D B H7 E7)
    (hBH_AD : Geo.Congruent B H7 A D)
    (hELE7 : Geo.Between E7 L7 H7)
    (hEXB7 : Geo.Between E7 X7 B)
    (hCXL7 : Geo.Between C X7 L7)
    (hLeftPar7 : IsParallelogram Geo L7 E7 D C)
    (hRightPar7 : IsParallelogram Geo B H7 L7 C)

    -- Rect(DB,AD).
    (P0 P1 P2 P3 : Geo.Point)
    (hDB_AD :
      IsRectangleContainedBy Geo
        P0 P1 P2 P3 D B A D)

    -- Rect(DC,AD), before commutativity normalization in test 07.
    (Q0 Q1 Q2 Q3 : Geo.Point)
    (hDC_AD :
      IsRectangleContainedBy Geo
        Q0 Q1 Q2 Q3 D C A D)

    -- Rect(CB,AD).
    (Y0 Y1 Y2 Y3 : Geo.Point)
    (hCB_AD :
      IsRectangleContainedBy Geo
        Y0 Y1 Y2 Y3 C B A D) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo P0 P1 P2 P3 +
       hilbertParallelogramTerm Geo D C F G)
      (hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
       hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) := by

  have h07 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo P0 P1 P2 P3)
        (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
         hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3) :=
    proposition2_5_test07_db_decomposition_normalized
      Geo
      A B C D
      hMidC hADC
      E7 H7 L7 X7
      hRect7 hBH_AD hELE7 hEXB7 hCXL7
      hLeftPar7 hRightPar7
      P0 P1 P2 P3
      Q0 Q1 Q2 Q3
      Y0 Y1 Y2 Y3
      hDB_AD
      hDC_AD
      hCB_AD
      T0 T1 T2 T3
      hAD_DC

  have h04 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3)
        (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
         hilbertParallelogramTerm Geo D C F G) :=
    proposition2_5_test04_first_assembled_identity
      Geo
      A B C D
      hMidC hADC
      E4 H4 L4 X4
      hRect4 hCH_DC hELE4 hEXC4 hDXL4
      hLeftPar4 hRightPar4
      F G hSquare
      R0 R1 R2 R3
      T0 T1 T2 T3
      Z0 Z1 Z2 Z3
      hAC_DC
      hAD_DC
      hCB_DC

  exact
    proposition2_5_test08_scissors_bridge
      Geo
      (hilbertParallelogramTerm Geo P0 P1 P2 P3)
      (hilbertParallelogramTerm Geo T0 T1 T2 T3)
      (hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3)
      (hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3)
      (hilbertParallelogramTerm Geo D C F G)
      h07
      h04


/--
Euclid II.5 -- test 09.

Assemble the two rectangles on the right-hand side of test 08.

Because A-D-C, Euclid II.1 gives

  Rect(AC, CB) = Rect(AD, CB) + Rect(DC, CB).

The rectangles already present after test 08 are written with the
factors in the opposite order:

  Rect(CB, AD) + Rect(CB, DC).

We use `rectangle_contained_by_swap` to rotate their concrete
representatives, apply II.1, and rotate the whole rectangle back.
Thus

  Rect(CB, AD) + Rect(CB, DC) = Rect(CB, AC).

No new geometric principle is introduced here.
-/
private theorem proposition2_5_test09_assemble_right_side
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hADC : Geo.Between A D C)

    ---------------------------------------------------------------
    -- Concrete II.1 cut diagram for Rect(AC, CB), cut at D.
    ---------------------------------------------------------------

    (E H L X : Geo.Point)
    (hRect : IsRectangle Geo A C H E)
    (hCH_CB : Geo.Congruent C H C B)
    (hELE : Geo.Between E L H)
    (hEXC : Geo.Between E X C)
    (hDXL : Geo.Between D X L)
    (hLeftPar : IsParallelogram Geo L E A D)
    (hRightPar : IsParallelogram Geo C H L D)

    ---------------------------------------------------------------
    -- The two summands already occurring in test 08.
    ---------------------------------------------------------------

    (Y0 Y1 Y2 Y3 : Geo.Point)
    (hCB_AD :
      IsRectangleContainedBy Geo
        Y0 Y1 Y2 Y3 C B A D)

    (Z0 Z1 Z2 Z3 : Geo.Point)
    (hCB_DC :
      IsRectangleContainedBy Geo
        Z0 Z1 Z2 Z3 C B D C)

    ---------------------------------------------------------------
    -- Target representative Rect(CB, AC).
    ---------------------------------------------------------------

    (W0 W1 W2 W3 : Geo.Point)
    (hCB_AC :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 C B A C) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
       hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3)
      (hilbertParallelogramTerm Geo W0 W1 W2 W3) := by

  --------------------------------------------------------------------
  -- Rotate Rect(CB,AD) into Rect(AD,CB).
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_swap
        Geo
        Y0 Y1 Y2 Y3
        C B A D
        hCB_AD with
    ⟨hAD_CB, hYRotate⟩

  --------------------------------------------------------------------
  -- Rotate Rect(CB,DC) into Rect(DC,CB).
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_swap
        Geo
        Z0 Z1 Z2 Z3
        C B D C
        hCB_DC with
    ⟨hDC_CB, hZRotate⟩

  --------------------------------------------------------------------
  -- Rotate the target Rect(CB,AC) into Rect(AC,CB).
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_swap
        Geo
        W0 W1 W2 W3
        C B A C
        hCB_AC with
    ⟨hAC_CB, hWRotate⟩

  --------------------------------------------------------------------
  -- II.1 on AC, cut at D, with common second side CB.
  --------------------------------------------------------------------

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo W1 W2 W3 W0)
        (hilbertParallelogramTerm Geo Y1 Y2 Y3 Y0 +
         hilbertParallelogramTerm Geo Z1 Z2 Z3 Z0) :=
    euclid_proposition_2_1_two
      Geo
      A C E H L D X C B
      hRect
      hCH_CB
      hADC
      hELE
      hEXC
      hDXL
      hLeftPar
      hRightPar
      W1 W2 W3 W0
      Y1 Y2 Y3 Y0
      Z1 Z2 Z3 Z0
      hAC_CB
      hAD_CB
      hDC_CB

  --------------------------------------------------------------------
  -- Transport both summands to the rotated representatives.
  --------------------------------------------------------------------

  have hPartsRotate :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
         hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3)
        (hilbertParallelogramTerm Geo Y1 Y2 Y3 Y0 +
         hilbertParallelogramTerm Geo Z1 Z2 Z3 Z0) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hYRotate
      hZRotate

  --------------------------------------------------------------------
  -- Rotated parts -> rotated whole -> original whole.
  --------------------------------------------------------------------

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hPartsRotate
      (HilbertScissorsEq.trans
        (Geo := Geo)
        (HilbertScissorsEq.symm
          (Geo := Geo) hSplit)
        (HilbertScissorsEq.symm
          (Geo := Geo) hWRotate))


/--
Euclid II.5 -- test 10.

Identify the final rectangle with the square on CB.

In the standard II.5 configuration C is the midpoint of AB, hence

  AC ~= CB.

Therefore a rectangle contained by CB and AC is also a rectangle
contained by CB and CB.  A square on CB is another representative
of exactly that same rectangle content.  By uniqueness of the
rectangle contained by two segments,

  Rect(CB, AC) = Square(CB).

No new geometric principle is introduced here.
-/
private theorem proposition2_5_test10_half_rectangle_is_square
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hADC : Geo.Between A D C)

    ---------------------------------------------------------------
    -- Representative of Rect(CB, AC).
    ---------------------------------------------------------------

    (W0 W1 W2 W3 : Geo.Point)
    (hCB_AC :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 C B A C)

    ---------------------------------------------------------------
    -- Square on CB.
    ---------------------------------------------------------------

    (S0 S1 S2 S3 : Geo.Point)
    (hSquareCB : IsSquare Geo S0 S1 S2 S3)
    (hS01_CB : Geo.Congruent S0 S1 C B) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo W0 W1 W2 W3)
      (hilbertParallelogramTerm Geo S0 S1 S2 S3) := by

  --------------------------------------------------------------------
  -- Midpoint gives AC ~= CB.
  --------------------------------------------------------------------

  have hOrder :=
    proposition2_5_test01_order
      Geo A B C D hMidC hADC

  have hAC_CB :
      Geo.Congruent A C C B :=
    hOrder.2.2.1

  --------------------------------------------------------------------
  -- Rect(CB,AC) is also a representative of Rect(CB,CB).
  --------------------------------------------------------------------

  have hW12_CB :
      Geo.Congruent W1 W2 C B :=
    hilbert_congruent_transitivity
      Geo W1 W2 A C C B
      hCB_AC.2.2 hAC_CB

  have hCB_CB :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 C B C B :=
    ⟨hCB_AC.1,
      hCB_AC.2.1,
      hW12_CB⟩

  --------------------------------------------------------------------
  -- The square on S0S1 is a rectangle contained by S0S1,S0S1.
  -- Transport the labels of the containing segments to CB,CB.
  --------------------------------------------------------------------

  have hSquareSelf :
      IsRectangleContainedBy Geo
        S0 S1 S2 S3 S0 S1 S0 S1 :=
    square_is_rectangle_contained_by_side
      Geo S0 S1 S2 S3 hSquareCB

  have hS12_CB :
      Geo.Congruent S1 S2 C B :=
    hilbert_congruent_transitivity
      Geo S1 S2 S0 S1 C B
      hSquareSelf.2.2 hS01_CB

  have hSquareCBContained :
      IsRectangleContainedBy Geo
        S0 S1 S2 S3 C B C B :=
    ⟨hSquareSelf.1,
      hS01_CB,
      hS12_CB⟩

  --------------------------------------------------------------------
  -- Both figures now represent Rect(CB,CB).
  --------------------------------------------------------------------

  exact
    rectangle_contained_by_unique
      Geo
      W0 W1 W2 W3
      S0 S1 S2 S3
      C B C B
      hCB_CB
      hSquareCBContained


/--
Euclid II.5.

If AB is bisected at C and cut again at D between A and C, then the
rectangle contained by the unequal parts AD, DB together with the
square on CD is scissors-equal to the square on CB.

The proof is assembled from the geometric rectangle/scissors layer:

  test08:
    Rect(DB, AD) + Square(DC)
      = Rect(CB, AD) + Rect(CB, DC)

  test09:
    Rect(CB, AD) + Rect(CB, DC)
      = Rect(CB, AC)

  test10:
    Rect(CB, AC)
      = Square(CB)

Hence

  Rect(DB, AD) + Square(DC)
    = Square(CB).

Since rectangle content is symmetric in its two containing segments,
Rect(DB,AD) is the rectangle contained by the unequal parts AD and DB.
No new geometric or scissors principle is used in this file.
-/
theorem euclid_proposition_2_5
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hADC : Geo.Between A D C)

    ---------------------------------------------------------------
    -- Data used by test 04 inside test 08.
    ---------------------------------------------------------------

    (E4 H4 L4 X4 : Geo.Point)
    (hRect4 : IsRectangle Geo A C H4 E4)
    (hCH_DC : Geo.Congruent C H4 D C)
    (hELE4 : Geo.Between E4 L4 H4)
    (hEXC4 : Geo.Between E4 X4 C)
    (hDXL4 : Geo.Between D X4 L4)
    (hLeftPar4 : IsParallelogram Geo L4 E4 A D)
    (hRightPar4 : IsParallelogram Geo C H4 L4 D)

    -- Square on DC.
    (F G : Geo.Point)
    (hSquareDC : IsSquare Geo D C F G)

    -- Rect(AC,DC).
    (R0 R1 R2 R3 : Geo.Point)
    (hAC_DC :
      IsRectangleContainedBy Geo
        R0 R1 R2 R3 A C D C)

    -- Common Rect(AD,DC).
    (T0 T1 T2 T3 : Geo.Point)
    (hAD_DC :
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 A D D C)

    -- Rect(CB,DC).
    (Z0 Z1 Z2 Z3 : Geo.Point)
    (hCB_DC :
      IsRectangleContainedBy Geo
        Z0 Z1 Z2 Z3 C B D C)

    ---------------------------------------------------------------
    -- Data used by test 07 inside test 08.
    ---------------------------------------------------------------

    (E7 H7 L7 X7 : Geo.Point)
    (hRect7 : IsRectangle Geo D B H7 E7)
    (hBH_AD : Geo.Congruent B H7 A D)
    (hELE7 : Geo.Between E7 L7 H7)
    (hEXB7 : Geo.Between E7 X7 B)
    (hCXL7 : Geo.Between C X7 L7)
    (hLeftPar7 : IsParallelogram Geo L7 E7 D C)
    (hRightPar7 : IsParallelogram Geo B H7 L7 C)

    -- Rect(DB,AD), the unequal-parts rectangle.
    (P0 P1 P2 P3 : Geo.Point)
    (hDB_AD :
      IsRectangleContainedBy Geo
        P0 P1 P2 P3 D B A D)

    -- Rect(DC,AD), before commutativity normalization.
    (Q0 Q1 Q2 Q3 : Geo.Point)
    (hDC_AD :
      IsRectangleContainedBy Geo
        Q0 Q1 Q2 Q3 D C A D)

    -- Rect(CB,AD).
    (Y0 Y1 Y2 Y3 : Geo.Point)
    (hCB_AD :
      IsRectangleContainedBy Geo
        Y0 Y1 Y2 Y3 C B A D)

    ---------------------------------------------------------------
    -- Data for test 09:
    -- assemble Rect(CB,AD) + Rect(CB,DC) into Rect(CB,AC).
    ---------------------------------------------------------------

    (E9 H9 L9 X9 : Geo.Point)
    (hRect9 : IsRectangle Geo A C H9 E9)
    (hCH_CB9 : Geo.Congruent C H9 C B)
    (hELE9 : Geo.Between E9 L9 H9)
    (hEXC9 : Geo.Between E9 X9 C)
    (hDXL9 : Geo.Between D X9 L9)
    (hLeftPar9 : IsParallelogram Geo L9 E9 A D)
    (hRightPar9 : IsParallelogram Geo C H9 L9 D)

    -- Rect(CB,AC).
    (W0 W1 W2 W3 : Geo.Point)
    (hCB_AC :
      IsRectangleContainedBy Geo
        W0 W1 W2 W3 C B A C)

    ---------------------------------------------------------------
    -- Data for test 10: square on CB.
    ---------------------------------------------------------------

    (S0 S1 S2 S3 : Geo.Point)
    (hSquareCB : IsSquare Geo S0 S1 S2 S3)
    (hS01_CB : Geo.Congruent S0 S1 C B) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo P0 P1 P2 P3 +
       hilbertParallelogramTerm Geo D C F G)
      (hilbertParallelogramTerm Geo S0 S1 S2 S3) := by

  --------------------------------------------------------------------
  -- test08:
  -- Rect(DB,AD) + Square(DC)
  --   = Rect(CB,AD) + Rect(CB,DC).
  --------------------------------------------------------------------

  have h08 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo P0 P1 P2 P3 +
         hilbertParallelogramTerm Geo D C F G)
        (hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
         hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3) :=
    proposition2_5_test08_core_identity
      Geo
      A B C D
      hMidC hADC
      E4 H4 L4 X4
      hRect4 hCH_DC hELE4 hEXC4 hDXL4
      hLeftPar4 hRightPar4
      F G hSquareDC
      R0 R1 R2 R3
      hAC_DC
      T0 T1 T2 T3
      hAD_DC
      Z0 Z1 Z2 Z3
      hCB_DC
      E7 H7 L7 X7
      hRect7 hBH_AD hELE7 hEXB7 hCXL7
      hLeftPar7 hRightPar7
      P0 P1 P2 P3
      hDB_AD
      Q0 Q1 Q2 Q3
      hDC_AD
      Y0 Y1 Y2 Y3
      hCB_AD

  --------------------------------------------------------------------
  -- test09:
  -- Rect(CB,AD) + Rect(CB,DC) = Rect(CB,AC).
  --------------------------------------------------------------------

  have h09 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo Y0 Y1 Y2 Y3 +
         hilbertParallelogramTerm Geo Z0 Z1 Z2 Z3)
        (hilbertParallelogramTerm Geo W0 W1 W2 W3) :=
    proposition2_5_test09_assemble_right_side
      Geo
      A B C D
      hADC
      E9 H9 L9 X9
      hRect9 hCH_CB9 hELE9 hEXC9 hDXL9
      hLeftPar9 hRightPar9
      Y0 Y1 Y2 Y3
      hCB_AD
      Z0 Z1 Z2 Z3
      hCB_DC
      W0 W1 W2 W3
      hCB_AC

  --------------------------------------------------------------------
  -- test10:
  -- Rect(CB,AC) = Square(CB).
  --------------------------------------------------------------------

  have h10 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo W0 W1 W2 W3)
        (hilbertParallelogramTerm Geo S0 S1 S2 S3) :=
    proposition2_5_test10_half_rectangle_is_square
      Geo
      A B C D
      hMidC hADC
      W0 W1 W2 W3
      hCB_AC
      S0 S1 S2 S3
      hSquareCB
      hS01_CB

  --------------------------------------------------------------------
  -- Full II.5.
  --------------------------------------------------------------------

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      h08
      (HilbertScissorsEq.trans
        (Geo := Geo)
        h09
        h10)

end Geometry

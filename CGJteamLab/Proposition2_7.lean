import CGJteamLab.Proposition2_4

namespace Geometry

universe u
variable (Geo : Geometry.Geo)

/--
Euclid II.7.

For A-C-B, prove

  Square(AB) + Square(AC)
    =
  2 * Rect(AB,AC) + Square(CB)

in the scissors calculus.

The proof uses only:

* Euclid II.4, normalized by supplying the same representative of
  Rect(AC,CB) for both cross rectangles;
* Euclid II.3 on the reversed divided segment B-C-A, giving
  Rect(AB,AC) = Rect(AC,CB) + Square(AC);
* associativity and commutativity of formal scissors sums.

No cancellation and no new area principle are used.
-/
theorem euclid_proposition_2_7
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C : Geo.Point)

    --------------------------------------------------------------------
    -- II.2 / II.4 diagram: square on AB cut at C.
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

    -- Representatives of Rect(AB,AC) and Rect(AB,CB) used by II.4.
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)

    (hAB_AC :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A B A C)

    (hAB_CB :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 A B C B)

    --------------------------------------------------------------------
    -- II.3 diagram for the left II.4 term, read on B-C-A.
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

    -- Square on CA, i.e. the same unoriented segment as AC.
    (F G : Geo.Point)
    (hSquareCA : IsSquare Geo C A F G)

    --------------------------------------------------------------------
    -- II.3 diagram for the right II.4 term.
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
    -- One representative of Rect(AC,CB), used twice in II.4.
    --------------------------------------------------------------------

    (T0 T1 T2 T3 : Geo.Point)

    (hCross :
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 A C C B) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A B E0 D0 +
       hilbertParallelogramTerm Geo C A F G)
      ((hilbertParallelogramTerm Geo U0 U1 U2 U3 +
        hilbertParallelogramTerm Geo U0 U1 U2 U3) +
       hilbertParallelogramTerm Geo C B H K) := by

  --------------------------------------------------------------------
  -- Abbreviate the four scissors terms appearing in the identity.
  --------------------------------------------------------------------

  let W : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo A B E0 D0

  let R : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo U0 U1 U2 U3

  let X : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo T0 T1 T2 T3

  let S : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo C A F G

  let T : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo C B H K

  --------------------------------------------------------------------
  -- II.4:
  --
  --   W = (X + S) + (X + T).
  --
  -- We use the same concrete cross rectangle twice.
  --------------------------------------------------------------------

  have hW :
      HilbertScissorsEq Geo
        W
        ((X + S) + (X + T)) := by
    dsimp [W, X, S, T]
    exact
      euclid_proposition_2_4
        Geo
        A B C
        D0 E0 L0 X0
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
        D1 E1 L1 X1
        hRectLeft
        hAE1_CA
        hD1L1E1
        hD1X1A
        hCX1L1
        hLeftLeftPar
        hLeftRightPar
        F G
        hSquareCA
        D2 E2 L2 X2
        hRectRight
        hBE2_CB
        hD2L2E2
        hD2X2B
        hCX2L2
        hRightLeftPar
        hRightRightPar
        H K
        hSquareCB
        T0 T1 T2 T3
        T0 T1 T2 T3
        hCross
        hCross

  --------------------------------------------------------------------
  -- II.3 on B-C-A:
  --
  --   R = X + S.
  --------------------------------------------------------------------

  have hBCA : Geo.Between B C A :=
    (HilbertOrder.between_incidence A C B hACB).2.2.2.2

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

  have hSwapResult :=
    rectangle_contained_by_swap
      Geo
      T0 T1 T2 T3
      A C C B
      hCross

  have hCrossSwap := hSwapResult.1
  have hRotateCross := hSwapResult.2

  have hCrossForII3 :
      IsRectangleContainedBy Geo
        T1 T2 T3 T0 B C C A :=
    And.intro
      hCrossSwap.1
      (And.intro
        (CongruentSwapSecond
          Geo T1 T2 C B hCrossSwap.2.1)
        (CongruentSwapSecond
          Geo T2 T3 A C hCrossSwap.2.2))

  have hRawR :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo T1 T2 T3 T0 +
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
      T1 T2 T3 T0
      hAB_AC_rev
      hCrossForII3

  have hRotateCrossBack :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo T1 T2 T3 T0)
        (hilbertParallelogramTerm Geo T0 T1 T2 T3) :=
    HilbertScissorsEq.symm
      (Geo := Geo)
      hRotateCross

  have hR_concrete :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo U0 U1 U2 U3)
        (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
         hilbertParallelogramTerm Geo C A F G) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hRawR
      (HilbertScissorsEq.add
        (Geo := Geo)
        hRotateCrossBack
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertParallelogramTerm Geo C A F G)))

  have hR :
      HilbertScissorsEq Geo
        R
        (X + S) := by
    dsimp [R, X, S]
    exact hR_concrete

  --------------------------------------------------------------------
  -- Pure scissors-calculus bridge:
  --
  --   W = (X+S) + (X+T)
  --   R = X+S
  --
  -- implies
  --
  --   W+S = (R+R)+T.
  --------------------------------------------------------------------

  have hAddS :
      HilbertScissorsEq Geo
        (W + S)
        (((X + S) + (X + T)) + S) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hW
      (HilbertScissorsEq.refl
        (Geo := Geo) S)

  have hRegroup :
      ((X + S) + (X + T)) + S
        =
      ((X + S) + (X + S)) + T := by
    ac_rfl

  have hTwoCopies :
      HilbertScissorsEq Geo
        (W + S)
        (((X + S) + (X + S)) + T) := by
    rw [hRegroup] at hAddS
    exact hAddS

  have hReplacePair :
      HilbertScissorsEq Geo
        ((X + S) + (X + S))
        (R + R) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.symm
        (Geo := Geo) hR)
      (HilbertScissorsEq.symm
        (Geo := Geo) hR)

  have hReplacePairWithT :
      HilbertScissorsEq Geo
        (((X + S) + (X + S)) + T)
        ((R + R) + T) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hReplacePair
      (HilbertScissorsEq.refl
        (Geo := Geo) T)

  have hFinal :
      HilbertScissorsEq Geo
        (W + S)
        ((R + R) + T) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hTwoCopies
      hReplacePairWithT

  dsimp [W, R, S, T] at hFinal
  exact hFinal

end Geometry

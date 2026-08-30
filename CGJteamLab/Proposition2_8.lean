import CGJteamLab.Proposition2_7

namespace Geometry

universe u
variable (Geo : Geometry.Geo)

/--
Euclid II.8.

If A-C-B-D and BD ~= BC, then four copies of the rectangle contained
by AB and BC together with the square on CA are scissors-equal to the
square on AD.

For

  A-C-B-D
  BD ~= BC,

the proof combines:

* II.4 on A-B-D,
* II.7 on the reversed division B-C-A,
* exact transport of the square on BD to the square on CB,
* associativity and commutativity of formal scissors sums.

The same concrete square on BA is used in both II.4 and II.7.
The same concrete rectangle T is used in II.4 as Rect(AB,BD)
and in II.7 as Rect(BA,BC).

The conclusion is the classical II.8 pattern:

  4 * Rect(AB,BC) + Square(CA) = Square(AD)

at the exact scissors level.
-/
theorem euclid_proposition_2_8
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)

    (hACB : Geo.Between A C B)
    (hABD : Geo.Between A B D)
    (hBD_BC : Geo.Congruent B D B C)

    -- ====================================================================
    -- II.4 on A-B-D.
    -- ====================================================================

    (D40 E40 L40 X40 : Geo.Point)
    (hSquareAD : IsSquare Geo A D E40 D40)

    (hD40L40E40 : Geo.Between D40 L40 E40)
    (hD40X40D : Geo.Between D40 X40 D)
    (hBX40L40 : Geo.Between B X40 L40)

    (hII4LeftPar :
      IsParallelogram Geo L40 D40 A B)

    (hII4RightPar :
      IsParallelogram Geo D E40 L40 B)

    -- Rect(AD,AB), Rect(AD,BD).
    (U40 U41 U42 U43 : Geo.Point)
    (V40 V41 V42 V43 : Geo.Point)

    (hAD_AB :
      IsRectangleContainedBy Geo
        U40 U41 U42 U43 A D A B)

    (hAD_BD :
      IsRectangleContainedBy Geo
        V40 V41 V42 V43 A D B D)

    --------------------------------------------------------------------
    -- Left II.3 branch inside II.4.
    --------------------------------------------------------------------

    (D41 E41 L41 X41 : Geo.Point)

    (hRect41 :
      IsRectangle Geo D A E41 D41)

    (hAE41_BA :
      Geo.Congruent A E41 B A)

    (hD41L41E41 : Geo.Between D41 L41 E41)
    (hD41X41A : Geo.Between D41 X41 A)
    (hBX41L41 : Geo.Between B X41 L41)

    (hLeft41 :
      IsParallelogram Geo L41 D41 D B)

    (hRight41 :
      IsParallelogram Geo A E41 L41 B)

    --------------------------------------------------------------------
    -- Common square on BA: used here and again as the outer square
    -- in the II.7 invocation below.
    --------------------------------------------------------------------

    (F G : Geo.Point)
    (hSquareBA : IsSquare Geo B A F G)

    --------------------------------------------------------------------
    -- Right II.3 branch inside II.4.
    --------------------------------------------------------------------

    (D42 E42 L42 X42 : Geo.Point)

    (hRect42 :
      IsRectangle Geo A D E42 D42)

    (hDE42_BD :
      Geo.Congruent D E42 B D)

    (hD42L42E42 : Geo.Between D42 L42 E42)
    (hD42X42D : Geo.Between D42 X42 D)
    (hBX42L42 : Geo.Between B X42 L42)

    (hLeft42 :
      IsParallelogram Geo L42 D42 A B)

    (hRight42 :
      IsParallelogram Geo D E42 L42 B)

    (H K : Geo.Point)
    (hSquareBD : IsSquare Geo B D H K)

    --------------------------------------------------------------------
    -- Common repeated rectangle:
    --
    --   in II.4: Rect(AB,BD),
    --   in II.7: Rect(BA,BC).
    --------------------------------------------------------------------

    (T0 T1 T2 T3 : Geo.Point)

    (hCross4 :
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 A B B D)

    -- ====================================================================
    -- II.7 on the reversed division B-C-A.
    --
    -- The outer square is exactly the common square B-A-F-G above.
    -- ====================================================================

    (L70 X70 : Geo.Point)

    (hGL70F : Geo.Between G L70 F)
    (hGX70A : Geo.Between G X70 A)
    (hCX70L70 : Geo.Between C X70 L70)

    (hII7LeftPar :
      IsParallelogram Geo L70 G B C)

    (hII7RightPar :
      IsParallelogram Geo A F L70 C)

    -- Second outer representative Rect(BA,CA).
    (V70 V71 V72 V73 : Geo.Point)

    (hBA_CA :
      IsRectangleContainedBy Geo
        V70 V71 V72 V73 B A C A)

    --------------------------------------------------------------------
    -- Left II.3 branch inside II.7.
    --------------------------------------------------------------------

    (D71 E71 L71 X71 : Geo.Point)

    (hRect71 :
      IsRectangle Geo A B E71 D71)

    (hBE71_CB :
      Geo.Congruent B E71 C B)

    (hD71L71E71 : Geo.Between D71 L71 E71)
    (hD71X71B : Geo.Between D71 X71 B)
    (hCX71L71 : Geo.Between C X71 L71)

    (hLeft71 :
      IsParallelogram Geo L71 D71 A C)

    (hRight71 :
      IsParallelogram Geo B E71 L71 C)

    (M N : Geo.Point)
    (hSquareCB : IsSquare Geo C B M N)

    --------------------------------------------------------------------
    -- Right II.3 branch inside II.7.
    --------------------------------------------------------------------

    (D72 E72 L72 X72 : Geo.Point)

    (hRect72 :
      IsRectangle Geo B A E72 D72)

    (hAE72_CA :
      Geo.Congruent A E72 C A)

    (hD72L72E72 : Geo.Between D72 L72 E72)
    (hD72X72A : Geo.Between D72 X72 A)
    (hCX72L72 : Geo.Between C X72 L72)

    (hLeft72 :
      IsParallelogram Geo L72 D72 B C)

    (hRight72 :
      IsParallelogram Geo A E72 L72 C)

    (P Q : Geo.Point)
    (hSquareCA : IsSquare Geo C A P Q)

    --------------------------------------------------------------------
    -- Cross rectangle internal to II.7: Rect(BC,CA).
    --------------------------------------------------------------------

    (Z0 Z1 Z2 Z3 : Geo.Point)

    (hCross7 :
      IsRectangleContainedBy Geo
        Z0 Z1 Z2 Z3 B C C A) :

    HilbertScissorsEq Geo
      (((hilbertParallelogramTerm Geo T0 T1 T2 T3 +
         hilbertParallelogramTerm Geo T0 T1 T2 T3) +
        (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
         hilbertParallelogramTerm Geo T0 T1 T2 T3)) +
       hilbertParallelogramTerm Geo C A P Q)
      (hilbertParallelogramTerm Geo A D E40 D40) := by

  --------------------------------------------------------------------
  -- Reverse A-C-B to B-C-A for II.7.
  --------------------------------------------------------------------

  have hBCA : Geo.Between B C A :=
    (HilbertOrder.between_incidence A C B hACB).2.2.2.2

  --------------------------------------------------------------------
  -- The repeated II.4 rectangle is also a representative of
  -- Rect(BA,BC).
  --------------------------------------------------------------------

  have hT_BA_BC :
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 B A B C := by

    have hT01_BA :
        Geo.Congruent T0 T1 B A :=
      CongruentSwapSecond
        Geo T0 T1 A B hCross4.2.1

    have hT12_BC :
        Geo.Congruent T1 T2 B C :=
      hilbert_congruent_transitivity
        Geo T1 T2 B D B C
        hCross4.2.2
        hBD_BC

    exact
      And.intro
        hCross4.1
        (And.intro
          hT01_BA
          hT12_BC)

  --------------------------------------------------------------------
  -- II.4 on A-B-D:
  --
  -- Sq(AD) = (T + Sq(BA)) + (T + Sq(BD)).
  --------------------------------------------------------------------

  have hII4 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A D E40 D40)
        ((hilbertParallelogramTerm Geo T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo B A F G) +
         (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo B D H K)) :=
    euclid_proposition_2_4
      Geo
      A D B
      D40 E40 L40 X40
      hSquareAD
      hABD
      hD40L40E40
      hD40X40D
      hBX40L40
      hII4LeftPar
      hII4RightPar
      U40 U41 U42 U43
      V40 V41 V42 V43
      hAD_AB
      hAD_BD
      D41 E41 L41 X41
      hRect41
      hAE41_BA
      hD41L41E41
      hD41X41A
      hBX41L41
      hLeft41
      hRight41
      F G
      hSquareBA
      D42 E42 L42 X42
      hRect42
      hDE42_BD
      hD42L42E42
      hD42X42D
      hBX42L42
      hLeft42
      hRight42
      H K
      hSquareBD
      T0 T1 T2 T3
      T0 T1 T2 T3
      hCross4
      hCross4

  --------------------------------------------------------------------
  -- II.7 on B-C-A:
  --
  -- Sq(BA) + Sq(CB) = (T + T) + Sq(CA).
  --------------------------------------------------------------------

  have hII7 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B A F G +
         hilbertParallelogramTerm Geo C B M N)
        ((hilbertParallelogramTerm Geo T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo T0 T1 T2 T3) +
         hilbertParallelogramTerm Geo C A P Q) :=
    euclid_proposition_2_7
      Geo
      B A C
      G F L70 X70
      hSquareBA
      hBCA
      hGL70F
      hGX70A
      hCX70L70
      hII7LeftPar
      hII7RightPar
      T0 T1 T2 T3
      V70 V71 V72 V73
      hT_BA_BC
      hBA_CA
      D71 E71 L71 X71
      hRect71
      hBE71_CB
      hD71L71E71
      hD71X71B
      hCX71L71
      hLeft71
      hRight71
      M N
      hSquareCB
      D72 E72 L72 X72
      hRect72
      hAE72_CA
      hD72L72E72
      hD72X72A
      hCX72L72
      hLeft72
      hRight72
      P Q
      hSquareCA
      Z0 Z1 Z2 Z3
      hCross7

  --------------------------------------------------------------------
  -- Exact square transport Sq(BD) = Sq(CB).
  --------------------------------------------------------------------

  have hBD_CB :
      Geo.Congruent B D C B :=
    CongruentSwapSecond
      Geo B D B C hBD_BC

  have hSquareBDContained :
      IsRectangleContainedBy Geo
        B D H K B D B D :=
    square_is_rectangle_contained_by_side
      Geo B D H K hSquareBD

  have hSquareCBContained :
      IsRectangleContainedBy Geo
        C B M N C B C B :=
    square_is_rectangle_contained_by_side
      Geo C B M N hSquareCB

  have hCB_BD :
      Geo.Congruent C B B D :=
    hilbert_congruent_symmetry
      Geo B D C B hBD_CB

  have hBM_BD :
      Geo.Congruent B M B D :=
    hilbert_congruent_transitivity
      Geo B M C B B D
      hSquareCBContained.2.2
      hCB_BD

  have hSquareCBAsBD :
      IsRectangleContainedBy Geo
        C B M N B D B D :=
    And.intro
      hSquareCBContained.1
      (And.intro
        hCB_BD
        hBM_BD)

  have hSquareTransport :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B D H K)
        (hilbertParallelogramTerm Geo C B M N) :=
    rectangle_contained_by_unique
      Geo
      B D H K
      C B M N
      B D B D
      hSquareBDContained
      hSquareCBAsBD

  --------------------------------------------------------------------
  -- Pure scissors bridge.
  --------------------------------------------------------------------

  let Dterm : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo A D E40 D40

  let W : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo B A F G

  let R : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo T0 T1 T2 T3

  let Sbd : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo B D H K

  let Sbc : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo C B M N

  let SCA : HilbertScissorsTerm Geo :=
    hilbertParallelogramTerm Geo C A P Q

  have hAD' :
      HilbertScissorsEq Geo
        Dterm
        ((R + W) + (R + Sbd)) := by
    dsimp [Dterm, R, W, Sbd]
    exact hII4

  have hSquareTransport' :
      HilbertScissorsEq Geo
        Sbd
        Sbc := by
    dsimp [Sbd, Sbc]
    exact hSquareTransport

  have hII7' :
      HilbertScissorsEq Geo
        (W + Sbc)
        ((R + R) + SCA) := by
    dsimp [W, Sbc, R, SCA]
    exact hII7

  have hRightTransport :
      HilbertScissorsEq Geo
        (R + Sbd)
        (R + Sbc) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.refl
        (Geo := Geo) R)
      hSquareTransport'

  have hOuterTransport :
      HilbertScissorsEq Geo
        ((R + W) + (R + Sbd))
        ((R + W) + (R + Sbc)) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.refl
        (Geo := Geo) (R + W))
      hRightTransport

  have hADTransported :
      HilbertScissorsEq Geo
        Dterm
        ((R + W) + (R + Sbc)) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hAD'
      hOuterTransport

  have hRegroup :
      (R + W) + (R + Sbc)
        =
      (R + R) + (W + Sbc) := by
    ac_rfl

  have hADRegrouped :
      HilbertScissorsEq Geo
        Dterm
        ((R + R) + (W + Sbc)) := by
    rw [hRegroup] at hADTransported
    exact hADTransported

  have hReplaceII7 :
      HilbertScissorsEq Geo
        ((R + R) + (W + Sbc))
        ((R + R) + ((R + R) + SCA)) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.refl
        (Geo := Geo) (R + R))
      hII7'

  have hAlmost :
      HilbertScissorsEq Geo
        Dterm
        ((R + R) + ((R + R) + SCA)) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hADRegrouped
      hReplaceII7

  have hFinalRegroup :
      (R + R) + ((R + R) + SCA)
        =
      ((R + R) + (R + R)) + SCA := by
    ac_rfl

  rw [hFinalRegroup] at hAlmost

  have hFinal :
      HilbertScissorsEq Geo
        (((R + R) + (R + R)) + SCA)
        Dterm :=
    HilbertScissorsEq.symm
      (Geo := Geo)
      hAlmost

  dsimp [R, SCA, Dterm] at hFinal
  exact hFinal

end Geometry

import CGJteamLab.HilbertTrihedralAngle
import CGJteamLab.Proposition20
import CGJteamLab.Proposition25

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
XI.20 bridge lemma.

Suppose the first face angle ZOX is strictly smaller than the target
face angle XOY.  By definition of `HilbertAngleLess`, there is an
interior ray OW of angle XOY such that

    angle ZOX ~= angle XOW.

Thus, to prove

    angle ZOX + angle ZOY > angle XOY,

it is enough to prove that the remaining component

    angle WOY

is strictly smaller than the second face angle

    angle ZOY.

This theorem isolates exactly the metric core that Euclid proves using
I.4, I.20 and I.25.
-/
theorem hilbert_XI20_two_angles_greater_of_first_less
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X Y Z : Geo.Point)
    (hFirstLess :
      HilbertAngleLess Geo
        Z O X
        X O Y)
    (hRemainder :
      forall W : Geo.Point,
        HilbertRayMeetsSegment Geo O W X Y ->
        Geo.AngleCongruent Z O X X O W ->
        HilbertAngleLess Geo W O Y Z O Y) :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      Z O X
      Z O Y
      X O Y := by

  rcases hFirstLess with
    ⟨hZOX,
      hXOY,
      W,
      hInside,
      hZOX_XOW⟩

  have hWOY_ZOY :
      HilbertAngleLess Geo W O Y Z O Y :=
    hRemainder W hInside hZOX_XOW

  have hZOY :
      Not (PrimCollinear Geo Z O Y) :=
    hWOY_ZOY.2.1

  exact
    hilbertTwoAnglesGreaterThanAngle_of_decomposition
      Geo
      Z O X
      Z O Y
      X O Y
      W
      hZOX
      hZOY
      hXOY
      hInside
      hZOX_XOW
      hWOY_ZOY

/--
XI.20 metric core, first step.

Triangles OZX and OWX have

    OZ ~= OW,
    angle ZOX ~= angle XOW,
    OX common.

Hence SAS gives

    ZX ~= WX.

In Euclid XI.20 this is exactly the step

    AD = AE,
    angle DAB = angle BAE,
    AB common
    -----------------------
    DB = BE.
-/
theorem hilbert_XI20_sas_base_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X Z W : Geo.Point)
    (hZOX :
      Not (PrimCollinear Geo Z O X))
    (hXOW :
      Not (PrimCollinear Geo X O W))
    (hOZ_OW :
      Geo.Congruent O Z O W)
    (hAngle :
      Geo.AngleCongruent Z O X X O W) :
    Geo.Congruent Z X W X := by

  have hOZX :
      Not (PrimCollinear Geo O Z X) := by
    intro h
    exact
      hZOX
        (PrimCollinearSwap
          Geo O Z X h)

  have hOWX :
      Not (PrimCollinear Geo O W X) := by
    intro h
    exact
      hXOW
        (PrimCollinearRotate
          Geo X W O
          (PrimCollinearSymm
            Geo O W X h))

  have hAngle' :
      Geo.AngleCongruent Z O X W O X := by
    exact
      (Geo.angle_congruent_reverse_second
        Z O X
        X O W).mp
        hAngle

  have hOX_OX :
      Geo.Congruent O X O X :=
    hilbert_congruent_reflexive
      Geo O X

  have hSAS :=
    SAS
      (Geo := Geo)
      O Z X
      O W X
      hOZX
      hOWX
      hOZ_OW
      hAngle'
      hOX_OX

  exact hSAS.sideBC

/--
XI.20 metric core, cancellation step.

Assume E lies between B and C and DB ~= BE.
For the nondegenerate triangle DBC, Euclid I.20 gives

    BC < DB + DC.

Since

    BC = BE + EC

and DB ~= BE, it follows synthetically that

    EC < DC.

The proof uses segment trichotomy.  Equality EC ~= DC and the opposite
inequality DC < EC are both incompatible with I.20 after segment
additivity.
-/
theorem hilbert_XI20_remainder_side_less
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (B C D E : Geo.Point)
    (hDBC :
      Not (PrimCollinear Geo D B C))
    (hBEC :
      Geo.Between B E C)
    (hDB_BE :
      Geo.Congruent D B B E) :
    HilbertSegmentLess Geo E C D C := by

  --------------------------------------------------------------------
  -- Nondegeneracy of DC.
  --------------------------------------------------------------------

  have hDCB :
      Not (PrimCollinear Geo D C B) := by
    intro h
    exact
      hDBC
        (PrimCollinearRotate
          Geo D C B h)

  have hDC :
      D ≠ C :=
    hilbert_noncollinear_ne_first
      Geo D C B hDCB

  --------------------------------------------------------------------
  -- I.20 in triangle DBC:
  --
  -- construct P with B-D-P, DP ~= DC, and BC < BP.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_20
        Geo
        D B C
        hDBC
    with
    ⟨P,
      hBDP,
      hDP_DC,
      hBC_BP⟩

  --------------------------------------------------------------------
  -- Put the first summands in the same orientation:
  -- BD ~= BE.
  --------------------------------------------------------------------

  have hBD_BE :
      Geo.Congruent B D B E :=
    CongruentReverseFirst
      Geo
      D B
      B E
      hDB_BE

  --------------------------------------------------------------------
  -- Compare EC and DC.
  --------------------------------------------------------------------

  rcases
      hilbert_segment_trichotomy
        Geo
        E C
        D C
        hDC
    with
    hEC_DC | hEC_lt_DC | hDC_lt_EC

  ·
    ------------------------------------------------------------------
    -- Case 1: EC ~= DC.
    --
    -- Then
    --   BD + DP ~= BE + EC,
    -- hence BP ~= BC, contradicting BC < BP.
    ------------------------------------------------------------------

    have hDC_EC :
        Geo.Congruent D C E C :=
      hilbert_congruent_symmetry
        Geo
        E C
        D C
        hEC_DC

    have hDP_EC :
        Geo.Congruent D P E C :=
      hilbert_congruent_transitivity
        Geo
        D P
        D C
        E C
        hDP_DC
        hDC_EC

    have hBP_BC :
        Geo.Congruent B P B C :=
      HilbertCongruence.segment_additivity
        (Geo := Geo)
        B D P
        B E C
        hBDP
        hBEC
        hBD_BE
        hDP_EC

    have hBC_BP_cong :
        Geo.Congruent B C B P :=
      hilbert_congruent_symmetry
        Geo
        B P
        B C
        hBP_BC

    exact
      False.elim
        ((hilbert_segmentLess_not_congruent
            Geo
            B C
            B P
            hBC_BP)
          hBC_BP_cong)

  ·
    ------------------------------------------------------------------
    -- Case 2: EC < DC.
    --
    -- This is the desired conclusion.
    ------------------------------------------------------------------

    exact hEC_lt_DC

  ·
    ------------------------------------------------------------------
    -- Case 3: DC < EC.
    --
    -- Choose Q with E-Q-C and EQ ~= DC.
    -- Since B-E-C, also B-E-Q and B-Q-C.
    --
    -- Hence
    --   BD + DP ~= BE + EQ,
    -- so BP ~= BQ.
    --
    -- But B-Q-C gives BQ < BC, hence BP < BC,
    -- contradicting BC < BP from I.20.
    ------------------------------------------------------------------

    rcases hDC_lt_EC with
      ⟨Q,
        hEQC,
        hDC_EQ⟩

    have hCQE :
        Geo.Between C Q E :=
      (HilbertOrder.between_incidence
        E Q C hEQC).2.2.2.2

    have hCEB :
        Geo.Between C E B :=
      (HilbertOrder.between_incidence
        B E C hBEC).2.2.2.2

    have hOrder :=
      hilbert_between_inner_trans
        Geo
        C Q E B
        hCQE
        hCEB

    have hQEB :
        Geo.Between Q E B :=
      hOrder.1

    have hCQB :
        Geo.Between C Q B :=
      hOrder.2

    have hBEQ :
        Geo.Between B E Q :=
      (HilbertOrder.between_incidence
        Q E B hQEB).2.2.2.2

    have hBQC :
        Geo.Between B Q C :=
      (HilbertOrder.between_incidence
        C Q B hCQB).2.2.2.2

    have hDP_EQ :
        Geo.Congruent D P E Q :=
      hilbert_congruent_transitivity
        Geo
        D P
        D C
        E Q
        hDP_DC
        hDC_EQ

    have hBP_BQ :
        Geo.Congruent B P B Q :=
      HilbertCongruence.segment_additivity
        (Geo := Geo)
        B D P
        B E Q
        hBDP
        hBEQ
        hBD_BE
        hDP_EQ

    have hBQ_BC :
        HilbertSegmentLess Geo B Q B C :=
      hilbert_segmentLess_of_between
        Geo
        B Q C
        hBQC

    have hBP_BC :
        HilbertSegmentLess Geo B P B C :=
      hilbert_segmentLess_congruent_left
        Geo
        B Q
        B P
        B C
        hBQ_BC
        hBP_BQ

    exact
      False.elim
        ((hilbert_segmentLess_asymm
            Geo
            B C
            B P
            hBC_BP)
          hBP_BC)

/--
XI.20 metric core, final comparison step.

For triangles OZY and OWY assume

    OZ ~= OW,
    OY common,
    WY < ZY.

Then Euclid I.25 gives

    angle WOY < angle ZOY.

This is the final metric implication used in the classical proof of XI.20.
-/
theorem hilbert_XI20_remainder_angle_less
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O Y Z W : Geo.Point)
    (hOZY :
      Not (PrimCollinear Geo O Z Y))
    (hOWY :
      Not (PrimCollinear Geo O W Y))
    (hOZ_OW :
      Geo.Congruent O Z O W)
    (hWY_ZY :
      HilbertSegmentLess Geo W Y Z Y) :
    HilbertAngleLess Geo W O Y Z O Y := by

  have hOY_OY :
      Geo.Congruent O Y O Y :=
    hilbert_congruent_reflexive
      Geo O Y

  exact
    euclid_proposition_25
      (Geo := Geo)
      O Z Y
      O W Y
      hOZY
      hOWY
      hOZ_OW
      hOY_OY
      hWY_ZY

/--
Reversing the two rays of the first summand angle does not change the
synthetic statement that two angles together are greater than a third.

This is a representational symmetry of the unoriented Hilbert angle.
It is useful in XI.20 because the one-cyclic theorem naturally returns

    angle BOA + angle BOC > angle AOC,

while the public cyclic statement is written as

    angle AOB + angle BOC > angle AOC.
-/
theorem hilbertTwoAnglesGreaterThanAngle_swap_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F) :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      B O A
      C P D
      E Q F := by

  rcases h with
    ⟨hAOB,
      hCPD,
      hEQF,
      hCore⟩

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hAOB_BOA :
      Geo.AngleCongruent A O B B O A := by
    unfold Geometry.Geo.AngleCongruent
    rw [Geo.angle_swap A O B]
    exact
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo)
        B O A
        hBOA

  refine
    ⟨hBOA,
      hCPD,
      hEQF,
      ?_⟩

  rcases hCore with
    hLess | hEq | hDecomp

  ·
    left

    exact
      hilbert_angleLess_transport_right
        Geo
        E Q F
        A O B
        B O A
        hLess
        hBOA
        hAOB_BOA

  ·
    right
    left

    exact
      Geometry.Geo.angle_congruent_transitivity
        Geo
        E Q F
        A O B
        B O A
        hEq
        hAOB_BOA

  ·
    right
    right

    rcases hDecomp with
      ⟨X,
        hInside,
        hFirstPart,
        hRemainder⟩

    have hBOA_AOB :
        Geo.AngleCongruent B O A A O B :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        A O B
        B O A
        hAOB_BOA

    have hFirstPart' :
        Geo.AngleCongruent B O A E Q X :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        B O A
        A O B
        E Q X
        hBOA_AOB
        hFirstPart

    exact
      ⟨X,
        hInside,
        hFirstPart',
        hRemainder⟩

end Geometry

import CGJteamLab.HilbertInterfaceXI
import CGJteamLab.Proposition11_22
import CGJteamLab.Proposition2_14
import CGJteamLab.Proposition11_12
import CGJteamLab.Hilbert3DRightAngle

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.23

This file owns the proposition-specific proof logic for XI.23.

Policy:

* reusable mathematics remains in `HilbertInterfaceXI`;
* XI.23 case analysis and assembly remain here;
* no general Book V/VI development is introduced merely to finish XI.23.
-/


------------------------------------------------------------------------
-- XI.23 chord triangle: noncollinearity and circumcenter
------------------------------------------------------------------------

/--
Suppose K realizes the triangle of the three equal-radius chords
constructed in Euclid XI.22:

    CK ~= AB,
    DK ~= EF,

while CD is the second chord itself.

Then the three cyclic angle inequalities imply that C,D,K form a
noncollinear triangle.
-/
theorem hilbert_XI23_chord_triangle_noncollinear_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hOA_OB :
      Geo.Congruent O A O B)
    (hOA_PC :
      Geo.Congruent O A P C)
    (hOA_PD :
      Geo.Congruent O A P D)
    (hOA_QE :
      Geo.Congruent O A Q E)
    (hOA_QF :
      Geo.Congruent O A Q F)
    (hCK_AB :
      Geo.Congruent C K A B)
    (hDK_EF :
      Geo.Congruent D K E F) :
    Not (PrimCollinear Geo C D K) := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h12_3.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h12_3.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h12_3.2.2.1

  have hAB :
      Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo
      A B O
      (by
        intro hcol
        exact
          hAOB
            (PrimCollinearRotate
              Geo A B O hcol))

  have hCD :
      Not (C = D) :=
    hilbert_noncollinear_ne_first
      Geo
      C D P
      (by
        intro hcol
        exact
          hCPD
            (PrimCollinearRotate
              Geo C D P hcol))

  have hEF :
      Not (E = F) :=
    hilbert_noncollinear_ne_first
      Geo
      E F Q
      (by
        intro hcol
        exact
          hEQF
            (PrimCollinearRotate
              Geo E F Q hcol))

  have hAB_CK :
      Geo.Congruent A B C K :=
    hilbert_congruent_symmetry
      Geo
      C K
      A B
      hCK_AB

  have hEF_DK :
      Geo.Congruent E F D K :=
    hilbert_congruent_symmetry
      Geo
      D K
      E F
      hDK_EF

  have hCK :
      Not (C = K) :=
    bookZero_nullSegment3
      Geo
      A B
      C K
      hAB
      hAB_CK

  have hDK :
      Not (D = K) :=
    bookZero_nullSegment3
      Geo
      E F
      D K
      hEF
      hEF_DK

  --------------------------------------------------------------------
  -- Source chord inequalities.
  --------------------------------------------------------------------

  have hEF_lt_ABCD :
      HilbertSegmentSumGreater
        Geo
        A B
        C D
        E F :=
    hilbert_twoAnglesGreaterThanAngle_equalRadius_chordSumGreater
      Geo
      A O B
      C P D
      E Q F
      h12_3
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      P C
      hOA_PC

  have hPC_PD :
      Geo.Congruent P C P D :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      P D
      hPC_OA
      hOA_PD

  have hPC_QE :
      Geo.Congruent P C Q E :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      Q E
      hPC_OA
      hOA_QE

  have hPC_QF :
      Geo.Congruent P C Q F :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      Q F
      hPC_OA
      hOA_QF

  have hPC_OB :
      Geo.Congruent P C O B :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      O B
      hPC_OA
      hOA_OB

  have hAB_lt_CDEF :
      HilbertSegmentSumGreater
        Geo
        C D
        E F
        A B :=
    hilbert_twoAnglesGreaterThanAngle_equalRadius_chordSumGreater
      Geo
      C P D
      E Q F
      A O B
      h23_1
      hPC_PD
      hPC_QE
      hPC_QF
      hPC_OA
      hPC_OB

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q E
      hOA_QE

  have hQE_QF :
      Geo.Congruent Q E Q F :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      Q F
      hQE_OA
      hOA_QF

  have hQE_OB :
      Geo.Congruent Q E O B :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      O B
      hQE_OA
      hOA_OB

  have hQE_PC :
      Geo.Congruent Q E P C :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      P C
      hQE_OA
      hOA_PC

  have hQE_PD :
      Geo.Congruent Q E P D :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      P D
      hQE_OA
      hOA_PD

  have hCD_lt_EFAB :
      HilbertSegmentSumGreater
        Geo
        E F
        A B
        C D :=
    hilbert_twoAnglesGreaterThanAngle_equalRadius_chordSumGreater
      Geo
      E Q F
      A O B
      C P D
      h31_2
      hQE_QF
      hQE_OA
      hQE_OB
      hQE_PC
      hQE_PD

  --------------------------------------------------------------------
  -- Transport the three source inequalities to triangle C-D-K.
  --------------------------------------------------------------------

  have hCD_CD :
      Geo.Congruent C D C D :=
    hilbert_congruent_reflexive
      Geo C D

  have hCD_DC :
      Geo.Congruent C D D C :=
    CongruentSwapSecond
      Geo
      C D
      C D
      hCD_CD

  have hEF_KD :
      Geo.Congruent E F K D :=
    CongruentSwapSecond
      Geo
      E F
      D K
      hEF_DK

  have hCD_DK_CK :
      HilbertSegmentSumGreater
        Geo
        C D
        D K
        C K :=
    hilbertSegmentSumGreater_transport_XI
      Geo
      C D
      E F
      A B
      C D
      D K
      C K
      hAB_lt_CDEF
      hCD_CD
      hEF_DK
      hAB_CK

  have hCD_AB_EF :
      HilbertSegmentSumGreater
        Geo
        C D
        A B
        E F :=
    hilbertSegmentSumGreater_swap
      Geo
      A B
      C D
      E F
      hEF_lt_ABCD

  have hDC_CK_DK :
      HilbertSegmentSumGreater
        Geo
        D C
        C K
        D K :=
    hilbertSegmentSumGreater_transport_XI
      Geo
      C D
      A B
      E F
      D C
      C K
      D K
      hCD_AB_EF
      hCD_DC
      hAB_CK
      hEF_DK

  have hAB_EF_CD :
      HilbertSegmentSumGreater
        Geo
        A B
        E F
        C D :=
    hilbertSegmentSumGreater_swap
      Geo
      E F
      A B
      C D
      hCD_lt_EFAB

  have hCK_KD_CD :
      HilbertSegmentSumGreater
        Geo
        C K
        K D
        C D :=
    hilbertSegmentSumGreater_transport_XI
      Geo
      A B
      E F
      C D
      C K
      K D
      C D
      hAB_EF_CD
      hAB_CK
      hEF_KD
      hCD_CD

  exact
    hilbert_triangle_noncollinear_of_segment_sums_XI
      Geo
      C D K
      hCD
      hDK
      hCK
      hCD_DK_CK
      hDC_CK_DK
      hCK_KD_CD


/--
The XI.22 chord triangle has a circumcenter once the two constructed
side congruences are supplied.
-/
theorem hilbert_XI23_chord_triangle_circumcenter_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hOA_OB :
      Geo.Congruent O A O B)
    (hOA_PC :
      Geo.Congruent O A P C)
    (hOA_PD :
      Geo.Congruent O A P D)
    (hOA_QE :
      Geo.Congruent O A Q E)
    (hOA_QF :
      Geo.Congruent O A Q F)
    (hCK_AB :
      Geo.Congruent C K A B)
    (hDK_EF :
      Geo.Congruent D K E F) :
    exists U : Geo.Point,
      Geo.Congruent U C U D /\
      Geo.Congruent U C U K := by

  have hCDK :
      Not (PrimCollinear Geo C D K) :=
    hilbert_XI23_chord_triangle_noncollinear_XI
      Geo
      A O B
      C P D
      E Q F
      K
      h12_3
      h23_1
      h31_2
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF

  exact
    hilbert_triangle_circumcenter_exists_XI
      Geo
      C D K
      hCDK


------------------------------------------------------------------------
-- XI.23 equal-radius case: central angles recover the given angles
------------------------------------------------------------------------

/--
If the circumradius of the XI.23 chord triangle is congruent to the
original common radius, then the three central angles are congruent to
the three given angles.

This is three applications of Euclid I.8 (SSS):

    OAB  ~=  UCK,
    PCD  ~=  UCD,
    QEF  ~=  UDK.
-/
theorem hilbert_XI23_central_angles_congruent_of_equal_radius_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F K U : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB :
      Geo.Congruent O A O B)
    (hOA_PC :
      Geo.Congruent O A P C)
    (hOA_PD :
      Geo.Congruent O A P D)
    (hOA_QE :
      Geo.Congruent O A Q E)
    (hOA_QF :
      Geo.Congruent O A Q F)
    (hCK_AB :
      Geo.Congruent C K A B)
    (hDK_EF :
      Geo.Congruent D K E F)
    (hUC_UD :
      Geo.Congruent U C U D)
    (hUC_UK :
      Geo.Congruent U C U K)
    (hUC_OA :
      Geo.Congruent U C O A) :
    Geo.AngleCongruent A O B C U K /\
    Geo.AngleCongruent C P D C U D /\
    Geo.AngleCongruent E Q F D U K := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h12_3.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h12_3.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h12_3.2.2.1

  have hOAB :
      Not (Collinear Geo O A B) := by
    intro h
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  have hPCD :
      Not (Collinear Geo P C D) := by
    intro h
    exact
      hCPD
        (PrimCollinearSwap
          Geo P C D h)

  have hQEF :
      Not (Collinear Geo Q E F) := by
    intro h
    exact
      hEQF
        (PrimCollinearSwap
          Geo Q E F h)

  have hOA_UC :
      Geo.Congruent O A U C :=
    hilbert_congruent_symmetry
      Geo
      U C
      O A
      hUC_OA

  --------------------------------------------------------------------
  -- First angle: AOB ~= CUK.
  --------------------------------------------------------------------

  have hOB_OA :
      Geo.Congruent O B O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      O B
      hOA_OB

  have hOB_UC :
      Geo.Congruent O B U C :=
    hilbert_congruent_transitivity
      Geo
      O B
      O A
      U C
      hOB_OA
      hOA_UC

  have hOB_UK :
      Geo.Congruent O B U K :=
    hilbert_congruent_transitivity
      Geo
      O B
      U C
      U K
      hOB_UC
      hUC_UK

  have hAB_CK :
      Geo.Congruent A B C K :=
    hilbert_congruent_symmetry
      Geo
      C K
      A B
      hCK_AB

  have hAlpha :=
    euclid_proposition_8
      Geo
      O A B
      U C K
      hOAB
      hOA_UC
      hAB_CK
      hOB_UK

  have hAOB_CUK :
      Geo.AngleCongruent A O B C U K :=
    hAlpha.1

  --------------------------------------------------------------------
  -- Second angle: CPD ~= CUD.
  --------------------------------------------------------------------

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      P C
      hOA_PC

  have hPC_UC :
      Geo.Congruent P C U C :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      U C
      hPC_OA
      hOA_UC

  have hPD_OA :
      Geo.Congruent P D O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      P D
      hOA_PD

  have hPD_UC :
      Geo.Congruent P D U C :=
    hilbert_congruent_transitivity
      Geo
      P D
      O A
      U C
      hPD_OA
      hOA_UC

  have hPD_UD :
      Geo.Congruent P D U D :=
    hilbert_congruent_transitivity
      Geo
      P D
      U C
      U D
      hPD_UC
      hUC_UD

  have hCD_CD :
      Geo.Congruent C D C D :=
    hilbert_congruent_reflexive
      Geo C D

  have hBeta :=
    euclid_proposition_8
      Geo
      P C D
      U C D
      hPCD
      hPC_UC
      hCD_CD
      hPD_UD

  have hCPD_CUD :
      Geo.AngleCongruent C P D C U D :=
    hBeta.1

  --------------------------------------------------------------------
  -- Third angle: EQF ~= DUK.
  --------------------------------------------------------------------

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q E
      hOA_QE

  have hQE_UC :
      Geo.Congruent Q E U C :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      U C
      hQE_OA
      hOA_UC

  have hQE_UD :
      Geo.Congruent Q E U D :=
    hilbert_congruent_transitivity
      Geo
      Q E
      U C
      U D
      hQE_UC
      hUC_UD

  have hQF_OA :
      Geo.Congruent Q F O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q F
      hOA_QF

  have hQF_UC :
      Geo.Congruent Q F U C :=
    hilbert_congruent_transitivity
      Geo
      Q F
      O A
      U C
      hQF_OA
      hOA_UC

  have hQF_UK :
      Geo.Congruent Q F U K :=
    hilbert_congruent_transitivity
      Geo
      Q F
      U C
      U K
      hQF_UC
      hUC_UK

  have hEF_DK :
      Geo.Congruent E F D K :=
    hilbert_congruent_symmetry
      Geo
      D K
      E F
      hDK_EF

  have hGamma :=
    euclid_proposition_8
      Geo
      Q E F
      U D K
      hQEF
      hQE_UD
      hEF_DK
      hQF_UK

  have hEQF_DUK :
      Geo.AngleCongruent E Q F D U K :=
    hGamma.1

  exact
    And.intro hAOB_CUK
      (And.intro hCPD_CUD hEQF_DUK)


------------------------------------------------------------------------
-- XI.23 radial equal-cut subtraction
------------------------------------------------------------------------

/--
If P and Q cut equal initial segments from two congruent radii,

    O-P-L,
    O-Q-M,
    OP ~= OQ,
    OL ~= OM,

then the remaining radial pieces are congruent:

    PL ~= QM.

This is the exact "equal remainders" step used by Euclid XI.23 in the
case where the proposed edge is shorter than the circumradius.
-/
theorem hilbert_XI23_equal_radial_remainders_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O P L Q M : Geo.Point)
    (hOPL : Geo.Between O P L)
    (hOQM : Geo.Between O Q M)
    (hOP_OQ : Geo.Congruent O P O Q)
    (hOL_OM : Geo.Congruent O L O M) :
    Geo.Congruent P L Q M := by

  exact
    bookZero_differenceOfParts
      Geo
      O P L
      O Q M
      hOP_OQ
      hOL_OM
      hOPL
      hOQM



/--
Three simultaneous central-angle bounds for the proper-central-angle
case of Euclid XI.23.

The points C,D,K form the chord triangle supplied by XI.22 and U is an
equidistant point:

    UC ~= UD,
    UC ~= UK.

If the common source radius OA is strictly smaller than UC, then each
of the three proper central angles is strictly smaller than the
corresponding prescribed angle.

This is the complete local I.25 comparison step for the three faces.
It does not assume that U lies inside triangle CDK.
-/
theorem hilbert_XI23_three_central_angles_less_of_smaller_radius_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F K U : Geo.Point)
    (hSource :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hCUK : Not (PrimCollinear Geo C U K))
    (hCUD : Not (PrimCollinear Geo C U D))
    (hDUK : Not (PrimCollinear Geo D U K))
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    HilbertAngleLess Geo C U K A O B /\
    HilbertAngleLess Geo C U D C P D /\
    HilbertAngleLess Geo D U K E Q F := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    hSource.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    hSource.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    hSource.2.2.1

  have hFirst :
      HilbertAngleLess Geo C U K A O B :=
    hilbert_equalRadiusChord_angleLess_of_radiusLess_XI
      Geo
      A O B
      C U K
      hAOB
      hCUK
      hOA_OB
      hUC_UK
      hCK_AB
      hRadiusLess

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      P C
      hOA_PC

  have hPC_PD :
      Geo.Congruent P C P D :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      P D
      hPC_OA
      hOA_PD

  have hPC_lt_UC :
      HilbertSegmentLess Geo P C U C :=
    hilbert_segmentLess_congruent_left
      Geo
      O A
      P C
      U C
      hRadiusLess
      hPC_OA

  have hCD_CD :
      Geo.Congruent C D C D :=
    hilbert_congruent_reflexive
      Geo C D

  have hSecond :
      HilbertAngleLess Geo C U D C P D :=
    hilbert_equalRadiusChord_angleLess_of_radiusLess_XI
      Geo
      C P D
      C U D
      hCPD
      hCUD
      hPC_PD
      hUC_UD
      hCD_CD
      hPC_lt_UC

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q E
      hOA_QE

  have hQE_QF :
      Geo.Congruent Q E Q F :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      Q F
      hQE_OA
      hOA_QF

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo
      U C
      U D
      hUC_UD

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      hUD_UC
      hUC_UK

  have hOA_lt_UD :
      HilbertSegmentLess Geo O A U D :=
    hilbert_segmentLess_congruent_right
      Geo
      O A
      U C
      U D
      hRadiusLess
      hUC_UD

  have hQE_lt_UD :
      HilbertSegmentLess Geo Q E U D :=
    hilbert_segmentLess_congruent_left
      Geo
      O A
      Q E
      U D
      hOA_lt_UD
      hQE_OA

  have hThird :
      HilbertAngleLess Geo D U K E Q F :=
    hilbert_equalRadiusChord_angleLess_of_radiusLess_XI
      Geo
      E Q F
      D U K
      hEQF
      hDUK
      hQE_QF
      hUD_UK
      hDK_EF
      hQE_lt_UD

  exact
    And.intro hFirst
      (And.intro hSecond hThird)


------------------------------------------------------------------------
-- XI.23: diameter cases in the smaller-radius branch
------------------------------------------------------------------------

/--
A proper source chord cannot be congruent to a diameter of a circle
whose radius is strictly larger than the source radius.

Assume

    C-U-K,
    UC ~= UK,
    OA ~= OB,
    OA < UC,
    CK ~= AB,

with AOB a proper angle. Then False.

The proof is fully synthetic. Choose P and Q on the two halves of the
diameter with UP ~= UQ ~= OA. The segment PQ is a proper subsegment of
CK. Euclid I.20 gives AB shorter than the sum OA + OB, while that sum
is congruent to PQ. Hence AB < PQ < CK, contradicting CK ~= AB.
-/
theorem hilbert_XI23_diameter_chord_impossible_of_smaller_radius_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C U K : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCUK : Geo.Between C U K)
    (hOA_OB : Geo.Congruent O A O B)
    (hUC_UK : Geo.Congruent U C U K)
    (hCK_AB : Geo.Congruent C K A B)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    False := by

  have hRadiusLessUK :
      HilbertSegmentLess Geo O B U K := by

    have hOB_OA :
        Geo.Congruent O B O A :=
      hilbert_congruent_symmetry
        Geo O A O B hOA_OB

    have hOB_UC :
        HilbertSegmentLess Geo O B U C :=
      hilbert_segmentLess_congruent_left
        Geo
        O A
        O B
        U C
        hRadiusLess
        hOB_OA

    exact
      hilbert_segmentLess_congruent_right
        Geo
        O B
        U C
        U K
        hOB_UC
        hUC_UK

  cases hRadiusLess with
  | intro P hP =>

      have hUPC :
          Geo.Between U P C :=
        hP.1

      have hOA_UP :
          Geo.Congruent O A U P :=
        hP.2

      cases hRadiusLessUK with
      | intro Q hQ =>

          have hUQK :
              Geo.Between U Q K :=
            hQ.1

          have hOB_UQ :
              Geo.Congruent O B U Q :=
            hQ.2

          have hCPU :
              Geo.Between C P U :=
            (HilbertOrder.between_incidence
              U P C hUPC).2.2.2.2

          have hPUK :
              Geo.Between P U K :=
            bookZero_3_6a
              Geo
              C P U K
              hCPU
              hCUK

          have hPQK :
              Geo.Between P Q K :=
            bookZero_3_5b
              Geo
              P U Q K
              hPUK
              hUQK

          have hCPK :
              Geo.Between C P K :=
            bookZero_3_6b
              Geo
              C P U K
              hCPU
              hCUK

          have hKP_C :
              Geo.Between K P C :=
            (HilbertOrder.between_incidence
              C P K hCPK).2.2.2.2

          ------------------------------------------------------------
          -- PQ is a proper subsegment of CK.
          ------------------------------------------------------------

          have hPQ_PK :
              HilbertSegmentLess Geo P Q P K :=
            hilbert_segmentLess_of_between
              Geo
              P Q K
              hPQK

          have hKP_KC :
              HilbertSegmentLess Geo K P K C :=
            hilbert_segmentLess_of_between
              Geo
              K P C
              hKP_C

          have hPK_KP :
              Geo.Congruent P K K P :=
            CongruentReverseFirst
              Geo
              K P
              K P
              (hilbert_congruent_reflexive
                Geo K P)

          have hPK_KC :
              HilbertSegmentLess Geo P K K C :=
            hilbert_segmentLess_congruent_left
              Geo
              K P
              P K
              K C
              hKP_KC
              hPK_KP

          have hKC_CK :
              Geo.Congruent K C C K :=
            CongruentReverseFirst
              Geo
              C K
              C K
              (hilbert_congruent_reflexive
                Geo C K)

          have hPK_CK :
              HilbertSegmentLess Geo P K C K :=
            hilbert_segmentLess_congruent_right
              Geo
              P K
              K C
              C K
              hPK_KC
              hKC_CK

          have hPQ_CK :
              HilbertSegmentLess Geo P Q C K :=
            bookZero_52_lessThanTransitive
              Geo
              P Q
              P K
              C K
              hPQ_PK
              hPK_CK

          ------------------------------------------------------------
          -- Euclid I.20: AB is shorter than OA + OB.
          ------------------------------------------------------------

          have hOAB :
              Not (PrimCollinear Geo O A B) := by
            intro h
            exact
              hAOB
                (PrimCollinearSwap
                  Geo O A B h)

          cases
              euclid_proposition_20
                Geo
                O A B
                hOAB
          with
          | intro D hD =>

              have hAOD :
                  Geo.Between A O D :=
                hD.1

              have hOD_OB :
                  Geo.Congruent O D O B :=
                hD.2.1

              have hAB_AD :
                  HilbertSegmentLess Geo A B A D :=
                hD.2.2

              --------------------------------------------------------
              -- AD ~= PQ because AO ~= PU and OD ~= UQ.
              --------------------------------------------------------

              have hAO_UP :
                  Geo.Congruent A O U P :=
                CongruentReverseFirst
                  Geo
                  O A
                  U P
                  hOA_UP

              have hOD_UQ :
                  Geo.Congruent O D U Q :=
                hilbert_congruent_transitivity
                  Geo
                  O D
                  O B
                  U Q
                  hOD_OB
                  hOB_UQ

              have hPUQ :
                  Geo.Between P U Q := by

                have hKUP :
                    Geo.Between K U P :=
                  (HilbertOrder.between_incidence
                    P U K hPUK).2.2.2.2

                have hKQU :
                    Geo.Between K Q U :=
                  (HilbertOrder.between_incidence
                    U Q K hUQK).2.2.2.2

                have hQUP :
                    Geo.Between Q U P :=
                  bookZero_3_6a
                    Geo
                    K Q U P
                    hKQU
                    hKUP

                exact
                  (HilbertOrder.between_incidence
                    Q U P hQUP).2.2.2.2

              have hUP_AO :
                  Geo.Congruent U P A O :=
                hilbert_congruent_symmetry
                  Geo
                  A O
                  U P
                  hAO_UP

              have hPU_AO :
                  Geo.Congruent P U A O :=
                CongruentReverseFirst
                  Geo
                  U P
                  A O
                  hUP_AO

              have hAO_PU :
                  Geo.Congruent A O P U :=
                hilbert_congruent_symmetry
                  Geo
                  P U
                  A O
                  hPU_AO

              have hAD_PQ :
                  Geo.Congruent A D P Q :=
                bookZero_sumOfParts
                  Geo
                  A O D
                  P U Q
                  hAO_PU
                  hOD_UQ
                  hAOD
                  hPUQ

              have hAB_PQ :
                  HilbertSegmentLess Geo A B P Q :=
                hilbert_segmentLess_congruent_right
                  Geo
                  A B
                  A D
                  P Q
                  hAB_AD
                  hAD_PQ

              have hAB_CK :
                  HilbertSegmentLess Geo A B C K :=
                bookZero_52_lessThanTransitive
                  Geo
                  A B
                  P Q
                  C K
                  hAB_PQ
                  hPQ_CK

              have hAB_CK_cong :
                  Geo.Congruent A B C K :=
                hilbert_congruent_symmetry
                  Geo
                  C K
                  A B
                  hCK_AB

              exact
                (hilbert_segmentLess_not_congruent
                  Geo
                  A B
                  C K
                  hAB_CK)
                  hAB_CK_cong



/--
In the smaller-radius branch of XI.23, U cannot lie between C and K.
-/
theorem hilbert_XI23_not_between_C_U_K_of_smaller_radius_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C K U : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOA_OB : Geo.Congruent O A O B)
    (hUC_UK : Geo.Congruent U C U K)
    (hCK_AB : Geo.Congruent C K A B)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    Not (Geo.Between C U K) := by

  intro hCUK

  exact
    hilbert_XI23_diameter_chord_impossible_of_smaller_radius_XI
      Geo
      A O B
      C U K
      hAOB
      hCUK
      hOA_OB
      hUC_UK
      hCK_AB
      hRadiusLess



/--
In the smaller-radius branch of XI.23, U cannot lie between C and D.
-/
theorem hilbert_XI23_not_between_C_U_D_of_smaller_radius_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (C P D U : Geo.Point)
    (hCPD : Not (PrimCollinear Geo C P D))
    (hPC_PD : Geo.Congruent P C P D)
    (hUC_UD : Geo.Congruent U C U D)
    (hCD_CD : Geo.Congruent C D C D)
    (hRadiusLess : HilbertSegmentLess Geo P C U C) :
    Not (Geo.Between C U D) := by

  intro hCUD

  exact
    hilbert_XI23_diameter_chord_impossible_of_smaller_radius_XI
      Geo
      C P D
      C U D
      hCPD
      hCUD
      hPC_PD
      hUC_UD
      hCD_CD
      hRadiusLess



/--
In the smaller-radius branch of XI.23, U cannot lie between D and K.
-/
theorem hilbert_XI23_not_between_D_U_K_of_smaller_radius_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (E Q F D U K : Geo.Point)
    (hEQF : Not (PrimCollinear Geo E Q F))
    (hQE_QF : Geo.Congruent Q E Q F)
    (hUD_UK : Geo.Congruent U D U K)
    (hDK_EF : Geo.Congruent D K E F)
    (hRadiusLess : HilbertSegmentLess Geo Q E U D) :
    Not (Geo.Between D U K) := by

  intro hDUK

  exact
    hilbert_XI23_diameter_chord_impossible_of_smaller_radius_XI
      Geo
      E Q F
      D U K
      hEQF
      hDUK
      hQE_QF
      hUD_UK
      hDK_EF
      hRadiusLess


/--
In the XI.23 branch OA < UC, the three central angles CUK, CUD and
DUK are automatically proper.

The previous diameter-case lemmas exclude U from the open segments
CK, CD and DK.  Equal circumradii then rule out collinearity by the
generic equal-radii lemma above.
-/
theorem hilbert_XI23_central_angles_proper_of_smaller_radius_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F K U : Geo.Point)
    (hSource :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    Not (PrimCollinear Geo C U K) /\
    Not (PrimCollinear Geo C U D) /\
    Not (PrimCollinear Geo D U K) := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    hSource.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    hSource.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    hSource.2.2.1

  --------------------------------------------------------------------
  -- The three chord sides are non-null.
  --------------------------------------------------------------------

  have hAB : Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo
      A B O
      (by
        intro h
        exact
          hAOB
            (PrimCollinearRotate
              Geo A B O h))

  have hCD : Not (C = D) :=
    hilbert_noncollinear_ne_first
      Geo
      C D P
      (by
        intro h
        exact
          hCPD
            (PrimCollinearRotate
              Geo C D P h))

  have hEF : Not (E = F) :=
    hilbert_noncollinear_ne_first
      Geo
      E F Q
      (by
        intro h
        exact
          hEQF
            (PrimCollinearRotate
              Geo E F Q h))

  have hAB_CK :
      Geo.Congruent A B C K :=
    hilbert_congruent_symmetry
      Geo
      C K
      A B
      hCK_AB

  have hEF_DK :
      Geo.Congruent E F D K :=
    hilbert_congruent_symmetry
      Geo
      D K
      E F
      hDK_EF

  have hCK : Not (C = K) :=
    bookZero_nullSegment3
      Geo
      A B
      C K
      hAB
      hAB_CK

  have hDK : Not (D = K) :=
    bookZero_nullSegment3
      Geo
      E F
      D K
      hEF
      hEF_DK

  --------------------------------------------------------------------
  -- Radius/chord data for the CD and DK instances.
  --------------------------------------------------------------------

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      P C
      hOA_PC

  have hPC_PD :
      Geo.Congruent P C P D :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      P D
      hPC_OA
      hOA_PD

  have hPC_lt_UC :
      HilbertSegmentLess Geo P C U C :=
    hilbert_segmentLess_congruent_left
      Geo
      O A
      P C
      U C
      hRadiusLess
      hPC_OA

  have hCD_CD :
      Geo.Congruent C D C D :=
    hilbert_congruent_reflexive
      Geo C D

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      Q E
      hOA_QE

  have hQE_QF :
      Geo.Congruent Q E Q F :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      Q F
      hQE_OA
      hOA_QF

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo
      U C
      U D
      hUC_UD

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      hUD_UC
      hUC_UK

  have hOA_lt_UD :
      HilbertSegmentLess Geo O A U D :=
    hilbert_segmentLess_congruent_right
      Geo
      O A
      U C
      U D
      hRadiusLess
      hUC_UD

  have hQE_lt_UD :
      HilbertSegmentLess Geo Q E U D :=
    hilbert_segmentLess_congruent_left
      Geo
      O A
      Q E
      U D
      hOA_lt_UD
      hQE_OA

  --------------------------------------------------------------------
  -- Exclude the three diameter configurations.
  --------------------------------------------------------------------

  have hNotCUK :
      Not (Geo.Between C U K) :=
    hilbert_XI23_not_between_C_U_K_of_smaller_radius_XI
      Geo
      A O B
      C K U
      hAOB
      hOA_OB
      hUC_UK
      hCK_AB
      hRadiusLess

  have hNotCUD :
      Not (Geo.Between C U D) :=
    hilbert_XI23_not_between_C_U_D_of_smaller_radius_XI
      Geo
      C P D U
      hCPD
      hPC_PD
      hUC_UD
      hCD_CD
      hPC_lt_UC

  have hNotDUK :
      Not (Geo.Between D U K) :=
    hilbert_XI23_not_between_D_U_K_of_smaller_radius_XI
      Geo
      E Q F
      D U K
      hEQF
      hQE_QF
      hUD_UK
      hDK_EF
      hQE_lt_UD

  --------------------------------------------------------------------
  -- Equal radii + not-a-diameter give proper central angles.
  --------------------------------------------------------------------

  have hCUK :
      Not (PrimCollinear Geo C U K) :=
    hilbert_equal_radii_noncollinear_of_not_between_XI
      Geo
      C U K
      hCK
      hUC_UK
      hNotCUK

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hilbert_equal_radii_noncollinear_of_not_between_XI
      Geo
      C U D
      hCD
      hUC_UD
      hNotCUD

  have hDUK :
      Not (PrimCollinear Geo D U K) :=
    hilbert_equal_radii_noncollinear_of_not_between_XI
      Geo
      D U K
      hDK
      hUD_UK
      hNotDUK

  exact
    And.intro hCUK
      (And.intro hCUD hDUK)



/--
Closed local comparison package for the XI.23 branch OA < UC.

Unlike `hilbert_XI23_three_central_angles_less_of_smaller_radius_XI`,
this wrapper needs no explicit properness assumptions for CUK, CUD or
DUK.  They are derived from the diameter exclusions of v37.
-/
theorem hilbert_XI23_three_central_angles_less_of_smaller_radius_auto_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F K U : Geo.Point)
    (hSource :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    HilbertAngleLess Geo C U K A O B /\
    HilbertAngleLess Geo C U D C P D /\
    HilbertAngleLess Geo D U K E Q F := by

  have hProper :=
    hilbert_XI23_central_angles_proper_of_smaller_radius_XI
      Geo
      A O B
      C P D
      E Q F
      K U
      hSource
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hRadiusLess

  exact
    hilbert_XI23_three_central_angles_less_of_smaller_radius_XI
      Geo
      A O B
      C P D
      E Q F
      K U
      hSource
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hProper.1
      hProper.2.1
      hProper.2.2
      hRadiusLess



/-- UD interior to angle CUK: CK is strictly longer than CD and DK. -/
theorem hilbert_XI23_inside_D_longest_CK_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (U C D K : Geo.Point)
    (hCUK : Not (PrimCollinear Geo C U K))
    (hInside : HilbertRayMeetsSegment Geo U D C K)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K) :
    HilbertSegmentLess Geo C D C K /\
    HilbertSegmentLess Geo D K C K :=
  hilbert_equalRadius_interiorRay_two_chords_less_XI
    Geo U C D K hCUK hInside hUC_UD hUC_UK



/-- UC interior to angle DUK: DK is strictly longer than CD and CK. -/
theorem hilbert_XI23_inside_C_longest_DK_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (U C D K : Geo.Point)
    (hDUK : Not (PrimCollinear Geo D U K))
    (hInside : HilbertRayMeetsSegment Geo U C D K)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K) :
    HilbertSegmentLess Geo C D D K /\
    HilbertSegmentLess Geo C K D K := by

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo U C U D hUC_UD

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      hUD_UC
      hUC_UK

  have h :=
    hilbert_equalRadius_interiorRay_two_chords_less_XI
      Geo
      U D C K
      hDUK
      hInside
      hUD_UC
      hUD_UK

  have hDC_CD :
      Geo.Congruent D C C D :=
    CongruentReverseFirst
      Geo C D C D
      (hilbert_congruent_reflexive Geo C D)

  have hCD_DK :
      HilbertSegmentLess Geo C D D K :=
    bookZero_32_lessThanCongruence2
      Geo
      D C
      D K
      C D
      h.1
      hDC_CD

  exact ⟨hCD_DK, h.2⟩



/-- UK interior to angle CUD: CD is strictly longer than CK and DK. -/
theorem hilbert_XI23_inside_K_longest_CD_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (U C D K : Geo.Point)
    (hCUD : Not (PrimCollinear Geo C U D))
    (hInside : HilbertRayMeetsSegment Geo U K C D)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K) :
    HilbertSegmentLess Geo C K C D /\
    HilbertSegmentLess Geo D K C D := by

  have hUC_UK' :
      Geo.Congruent U C U K := hUC_UK

  have hUC_UD' :
      Geo.Congruent U C U D := hUC_UD

  have h :=
    hilbert_equalRadius_interiorRay_two_chords_less_XI
      Geo
      U C K D
      hCUD
      hInside
      hUC_UK'
      hUC_UD'

  have hKD_DK :
      Geo.Congruent K D D K :=
    CongruentReverseFirst
      Geo D K D K
      (hilbert_congruent_reflexive Geo D K)

  have hDK_CD :
      HilbertSegmentLess Geo D K C D :=
    bookZero_32_lessThanCongruence2
      Geo
      K D
      C D
      D K
      h.2
      hKD_DK

  exact ⟨h.1, hDK_CD⟩



/--
XI.23 outside-type branch, D-ray version.

If UD is interior to angle CUK, then CK is the longest of the three
circumcircle chords.  Since CK ~= AB, the source inequality

    angle CPD + angle EQF > angle AOB

cannot be witnessed by `AOB < CPD` or `AOB ~= CPD`; it is forced into
the genuine decomposition branch.
-/
theorem hilbert_XI23_inside_D_forces_source_decomposition_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (hCUK : Not (PrimCollinear Geo C U K))
    (hInsideD : HilbertRayMeetsSegment Geo U D C K)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hCK_AB : Geo.Congruent C K A B) :
    exists X : Geo.Point,
      HilbertRayMeetsSegment Geo O X A B /\
      Geo.AngleCongruent C P D A O X /\
      HilbertAngleLess Geo X O B E Q F := by

  have hLongest :=
    hilbert_XI23_inside_D_longest_CK_XI
      Geo
      U C D K
      hCUK
      hInsideD
      hUC_UD
      hUC_UK

  have hCD_CK :
      HilbertSegmentLess Geo C D C K :=
    hLongest.1

  have hCD_AB :
      HilbertSegmentLess Geo C D A B :=
    hilbert_segmentLess_congruent_right
      Geo
      C D
      C K
      A B
      hCD_CK
      hCK_AB

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo O A P C hOA_PC

  have hPD_OA :
      Geo.Congruent P D O A :=
    hilbert_congruent_symmetry
      Geo O A P D hOA_PD

  have hPD_OB :
      Geo.Congruent P D O B :=
    hilbert_congruent_transitivity
      Geo
      P D
      O A
      O B
      hPD_OA
      hOA_OB

  exact
    hilbert_twoAnglesGreater_decomposition_forced_of_firstChord_less_targetChord_XI
      Geo
      C P D
      E Q F
      A O B
      h23_1
      hPC_OA
      hPD_OB
      hCD_AB



/--
XI.23 outside-type branch, C-ray version.

If UC is interior to angle DUK, then DK is the longest chord.  With
CK ~= AB and DK ~= EF, the inequality

    angle AOB + angle CPD > angle EQF

is forced into its decomposition branch.
-/
theorem hilbert_XI23_inside_C_forces_source_decomposition_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hDUK : Not (PrimCollinear Geo D U K))
    (hInsideC : HilbertRayMeetsSegment Geo U C D K)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F) :
    exists X : Geo.Point,
      HilbertRayMeetsSegment Geo Q X E F /\
      Geo.AngleCongruent A O B E Q X /\
      HilbertAngleLess Geo X Q F C P D := by

  have hLongest :=
    hilbert_XI23_inside_C_longest_DK_XI
      Geo
      U C D K
      hDUK
      hInsideC
      hUC_UD
      hUC_UK

  have hCK_DK :
      HilbertSegmentLess Geo C K D K :=
    hLongest.2

  have hAB_CK :
      Geo.Congruent A B C K :=
    hilbert_congruent_symmetry
      Geo C K A B hCK_AB

  have hAB_DK :
      HilbertSegmentLess Geo A B D K :=
    hilbert_segmentLess_congruent_left
      Geo
      C K
      A B
      D K
      hCK_DK
      hAB_CK

  have hAB_EF :
      HilbertSegmentLess Geo A B E F :=
    hilbert_segmentLess_congruent_right
      Geo
      A B
      D K
      E F
      hAB_DK
      hDK_EF

  have hOB_OA :
      Geo.Congruent O B O A :=
    hilbert_congruent_symmetry
      Geo O A O B hOA_OB

  have hOB_QF :
      Geo.Congruent O B Q F :=
    hilbert_congruent_transitivity
      Geo
      O B
      O A
      Q F
      hOB_OA
      hOA_QF

  exact
    hilbert_twoAnglesGreater_decomposition_forced_of_firstChord_less_targetChord_XI
      Geo
      A O B
      C P D
      E Q F
      h12_3
      hOA_QE
      hOB_QF
      hAB_EF



/--
XI.23 outside-type branch, K-ray version.

If UK is interior to angle CUD, then CD is the longest chord.  With
DK ~= EF, the inequality

    angle EQF + angle AOB > angle CPD

is forced into its decomposition branch.
-/
theorem hilbert_XI23_inside_K_forces_source_decomposition_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hCUD : Not (PrimCollinear Geo C U D))
    (hInsideK : HilbertRayMeetsSegment Geo U K C D)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hDK_EF : Geo.Congruent D K E F) :
    exists X : Geo.Point,
      HilbertRayMeetsSegment Geo P X C D /\
      Geo.AngleCongruent E Q F C P X /\
      HilbertAngleLess Geo X P D A O B := by

  have hLongest :=
    hilbert_XI23_inside_K_longest_CD_XI
      Geo
      U C D K
      hCUD
      hInsideK
      hUC_UD
      hUC_UK

  have hDK_CD :
      HilbertSegmentLess Geo D K C D :=
    hLongest.2

  have hEF_DK :
      Geo.Congruent E F D K :=
    hilbert_congruent_symmetry
      Geo D K E F hDK_EF

  have hEF_CD :
      HilbertSegmentLess Geo E F C D :=
    hilbert_segmentLess_congruent_left
      Geo
      D K
      E F
      C D
      hDK_CD
      hEF_DK

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo O A Q E hOA_QE

  have hQE_PC :
      Geo.Congruent Q E P C :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      P C
      hQE_OA
      hOA_PC

  have hQF_OA :
      Geo.Congruent Q F O A :=
    hilbert_congruent_symmetry
      Geo O A Q F hOA_QF

  have hQF_PD :
      Geo.Congruent Q F P D :=
    hilbert_congruent_transitivity
      Geo
      Q F
      O A
      P D
      hQF_OA
      hOA_PD

  exact
    hilbert_twoAnglesGreater_decomposition_forced_of_firstChord_less_targetChord_XI
      Geo
      E Q F
      A O B
      C P D
      h31_2
      hQE_PC
      hQF_PD
      hEF_CD



------------------------------------------------------------------------
-- XI.23 v43: the D-inside branch forces a concrete short remainder
-- chord on the source circle.
------------------------------------------------------------------------

/--
Complete chord-level reduction of the `UD inside CUK` branch.

Assume the central ray `UD` lies inside angle `CUK`.  By v40, `CK` is
the longest of the three circumcircle chords.  Hence the source
inequality

    angle CPD + angle EQF > angle AOB

is forced by v41 into its genuine decomposition branch.  Realizing
that decomposition on the common source circle by v42 gives a point
`R` on the interior source ray such that

    AR ~= CD

and the remainder chord is strictly shorter than the third chord:

    RB < DK.

Thus the whole outside-circumcenter problem for this branch is reduced
to proving the opposite radial inequality `DK < RB` from `OA < UC`.
No radius comparison is used in the present lemma.
-/
theorem hilbert_XI23_inside_D_forces_source_remainder_chord_less_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (hCUK : Not (PrimCollinear Geo C U K))
    (hInsideD : HilbertRayMeetsSegment Geo U D C K)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F) :
    exists R : Geo.Point,
      HilbertRayMeetsSegment Geo O R A B /\
      Geo.Congruent O R O A /\
      Geo.Congruent A R C D /\
      HilbertSegmentLess Geo R B D K := by

  rcases
      hilbert_XI23_inside_D_forces_source_decomposition_XI
        Geo
        A O B C P D E Q F U K
        h23_1
        hCUK
        hInsideD
        hUC_UD
        hUC_UK
        hOA_OB
        hOA_PC
        hOA_PD
        hCK_AB
    with
    ⟨X,
      hInsideX,
      hCPD_AOX,
      hXOB_EQF⟩

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h23_1.2.2.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h23_1.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h23_1.2.1

  rcases
      hilbert_angleDecomposition_sourceRadius_chord_witness_XI
        Geo
        A O B
        C P D
        E Q F
        X
        hAOB
        hCPD
        hEQF
        hInsideX
        hCPD_AOX
        hXOB_EQF
        hOA_OB
        hOA_PC
        hOA_PD
        hOA_QE
        hOA_QF
    with
    ⟨R,
      hRayOXR,
      hOR_OA,
      hAR_CD,
      hRB_EF⟩

  have hEF_DK :
      Geo.Congruent E F D K :=
    hilbert_congruent_symmetry
      Geo
      D K
      E F
      hDK_EF

  have hRB_DK :
      HilbertSegmentLess Geo R B D K :=
    hilbert_segmentLess_congruent_right
      Geo
      R B
      E F
      D K
      hRB_EF
      hEF_DK

  rcases hInsideX with
    ⟨H,
      hAHB,
      hRayOXH⟩

  have hRayORH :
      HilbertSameRay Geo O R H :=
    hilbert_sameRay_of_common
      Geo
      O X R H
      hRayOXR
      hRayOXH

  have hInsideR :
      HilbertRayMeetsSegment Geo O R A B :=
    ⟨H,
      hAHB,
      hRayORH⟩

  exact
    ⟨R,
      hInsideR,
      hOR_OA,
      hAR_CD,
      hRB_DK⟩


------------------------------------------------------------------------
-- XI.23 v44: common inner radial section of the circumcircle triangle
------------------------------------------------------------------------

/--
Cut the three equal circumradii UC, UD, UK at the common shorter
length OA.

The resulting points P,S,Q satisfy

    U-P-C,
    U-S-D,
    U-Q-K,

with UP ~= US ~= UQ ~= OA.  Hence the three inner chords are parallel
to the corresponding outer chords:

    PS || CD,
    SQ || DK,
    PQ || CK,

and each inner chord is strictly shorter than its outer mate.

This packages the full synthetic homothetic information needed in the
outside-circumcenter branch of XI.23.  No segment ratio is introduced.
-/
theorem hilbert_XI23_inner_radial_section_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O A C D K U : Geo.Point)
    (hCUD : Not (PrimCollinear Geo C U D))
    (hDUK : Not (PrimCollinear Geo D U K))
    (hCUK : Not (PrimCollinear Geo C U K))
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    exists P S Q : Geo.Point,
      Geo.Between U P C /\
      Geo.Between U S D /\
      Geo.Between U Q K /\
      Geo.Congruent O A U P /\
      Geo.Congruent O A U S /\
      Geo.Congruent O A U Q /\
      Geo.Parallel P S C D /\
      Geo.Parallel S Q D K /\
      Geo.Parallel P Q C K /\
      HilbertSegmentLess Geo P S C D /\
      HilbertSegmentLess Geo S Q D K /\
      HilbertSegmentLess Geo P Q C K := by

  have hRadiusLessUD :
      HilbertSegmentLess Geo O A U D :=
    hilbert_segmentLess_congruent_right
      Geo
      O A
      U C
      U D
      hRadiusLess
      hUC_UD

  have hRadiusLessUK :
      HilbertSegmentLess Geo O A U K :=
    hilbert_segmentLess_congruent_right
      Geo
      O A
      U C
      U K
      hRadiusLess
      hUC_UK

  rcases hRadiusLess with
    ⟨P, hUPC, hOA_UP⟩

  rcases hRadiusLessUD with
    ⟨S, hUSD, hOA_US⟩

  rcases hRadiusLessUK with
    ⟨Q, hUQK, hOA_UQ⟩

  have hUP_OA :
      Geo.Congruent U P O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      U P
      hOA_UP

  have hUS_OA :
      Geo.Congruent U S O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      U S
      hOA_US

  have hUP_US :
      Geo.Congruent U P U S :=
    hilbert_congruent_transitivity
      Geo
      U P
      O A
      U S
      hUP_OA
      hOA_US

  have hUS_UQ :
      Geo.Congruent U S U Q :=
    hilbert_congruent_transitivity
      Geo
      U S
      O A
      U Q
      hUS_OA
      hOA_UQ

  have hUP_UQ :
      Geo.Congruent U P U Q :=
    hilbert_congruent_transitivity
      Geo
      U P
      O A
      U Q
      hUP_OA
      hOA_UQ

  have hUCD :
      Not (PrimCollinear Geo U C D) := by
    intro h
    exact
      hCUD
        (PrimCollinearSwap
          Geo U C D h)

  have hUDK :
      Not (PrimCollinear Geo U D K) := by
    intro h
    exact
      hDUK
        (PrimCollinearSwap
          Geo U D K h)

  have hUCK :
      Not (PrimCollinear Geo U C K) := by
    intro h
    exact
      hCUK
        (PrimCollinearSwap
          Geo U C K h)

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      (hilbert_congruent_symmetry
        Geo
        U C
        U D
        hUC_UD)
      hUC_UK

  have hPS_CD :
      Geo.Parallel P S C D :=
    hilbert_equal_cuts_on_equal_sides_parallel_XI
      Geo
      U P C S D
      hUCD
      hUPC
      hUSD
      hUC_UD
      hUP_US

  have hSQ_DK :
      Geo.Parallel S Q D K :=
    hilbert_equal_cuts_on_equal_sides_parallel_XI
      Geo
      U S D Q K
      hUDK
      hUSD
      hUQK
      hUD_UK
      hUS_UQ

  have hPQ_CK :
      Geo.Parallel P Q C K :=
    hilbert_equal_cuts_on_equal_sides_parallel_XI
      Geo
      U P C Q K
      hUCK
      hUPC
      hUQK
      hUC_UK
      hUP_UQ

  have hPSltCD :
      HilbertSegmentLess Geo P S C D :=
    hilbert_equal_cuts_on_equal_sides_less_XI
      Geo
      U P C S D
      hUCD
      hUPC
      hUSD
      hUC_UD
      hUP_US

  have hSQltDK :
      HilbertSegmentLess Geo S Q D K :=
    hilbert_equal_cuts_on_equal_sides_less_XI
      Geo
      U S D Q K
      hUDK
      hUSD
      hUQK
      hUD_UK
      hUS_UQ

  have hPQltCK :
      HilbertSegmentLess Geo P Q C K :=
    hilbert_equal_cuts_on_equal_sides_less_XI
      Geo
      U P C Q K
      hUCK
      hUPC
      hUQK
      hUC_UK
      hUP_UQ

  exact
    ⟨P, S, Q,
      hUPC,
      hUSD,
      hUQK,
      hOA_UP,
      hOA_US,
      hOA_UQ,
      hPS_CD,
      hSQ_DK,
      hPQ_CK,
      hPSltCD,
      hSQltDK,
      hPQltCK⟩



------------------------------------------------------------------------
-- XI.23 v45: complete reduction of the D-inside outside-center branch
------------------------------------------------------------------------

/--
Bundle the two constructions needed in the `UD inside CUK` branch.

Under the bad radius assumption `OA < UC`, v43 gives a point `R` on
an interior source ray with

    AR ~= CD,
    RB < DK.

Independently, v44 cuts the three circumradii at the common length OA,
producing `Pc, Sc, Qc` with

    PcSc || CD,  ScQc || DK,  PcQc || CK

and all three inner chords strictly shorter than their outer mates.
Transport through `AR ~= CD` and `CK ~= AB` yields the two concrete
strict comparisons

    PcSc < AR,
    PcQc < AB.

Thus every datum of the outside-center branch is exposed in one planar
configuration.  The only missing geometric fact is the radial remainder
comparison `DK < RB`.
-/
theorem hilbert_XI23_inside_D_radial_reduction_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (hCUD : Not (PrimCollinear Geo C U D))
    (hDUK : Not (PrimCollinear Geo D U K))
    (hCUK : Not (PrimCollinear Geo C U K))
    (hInsideD : HilbertRayMeetsSegment Geo U D C K)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    exists R Pc Sc Qc : Geo.Point,
      HilbertRayMeetsSegment Geo O R A B /\
      Geo.Congruent O R O A /\
      Geo.Congruent A R C D /\
      HilbertSegmentLess Geo R B D K /\
      Geo.Between U Pc C /\
      Geo.Between U Sc D /\
      Geo.Between U Qc K /\
      Geo.Congruent O A U Pc /\
      Geo.Congruent O A U Sc /\
      Geo.Congruent O A U Qc /\
      Geo.Parallel Pc Sc C D /\
      Geo.Parallel Sc Qc D K /\
      Geo.Parallel Pc Qc C K /\
      HilbertSegmentLess Geo Pc Sc C D /\
      HilbertSegmentLess Geo Sc Qc D K /\
      HilbertSegmentLess Geo Pc Qc C K /\
      HilbertSegmentLess Geo Pc Sc A R /\
      HilbertSegmentLess Geo Pc Qc A B := by

  rcases
      hilbert_XI23_inside_D_forces_source_remainder_chord_less_XI
        Geo
        A O B C P D E Q F U K
        h23_1
        hCUK
        hInsideD
        hUC_UD
        hUC_UK
        hOA_OB
        hOA_PC
        hOA_PD
        hOA_QE
        hOA_QF
        hCK_AB
        hDK_EF
    with
    ⟨R, hInsideR, hOR_OA, hAR_CD, hRB_DK⟩

  rcases
      hilbert_XI23_inner_radial_section_XI
        Geo
        O A C D K U
        hCUD
        hDUK
        hCUK
        hUC_UD
        hUC_UK
        hRadiusLess
    with
    ⟨Pc, Sc, Qc,
      hUPcC,
      hUScD,
      hUQcK,
      hOA_UPc,
      hOA_USc,
      hOA_UQc,
      hPcSc_CD,
      hScQc_DK,
      hPcQc_CK,
      hPcSc_lt_CD,
      hScQc_lt_DK,
      hPcQc_lt_CK⟩

  have hCD_AR :
      Geo.Congruent C D A R :=
    hilbert_congruent_symmetry
      Geo
      A R
      C D
      hAR_CD

  have hPcSc_lt_AR :
      HilbertSegmentLess Geo Pc Sc A R :=
    hilbert_segmentLess_congruent_right
      Geo
      Pc Sc
      C D
      A R
      hPcSc_lt_CD
      hCD_AR

  have hPcQc_lt_AB :
      HilbertSegmentLess Geo Pc Qc A B :=
    hilbert_segmentLess_congruent_right
      Geo
      Pc Qc
      C K
      A B
      hPcQc_lt_CK
      hCK_AB

  exact
    ⟨R, Pc, Sc, Qc,
      hInsideR,
      hOR_OA,
      hAR_CD,
      hRB_DK,
      hUPcC,
      hUScD,
      hUQcK,
      hOA_UPc,
      hOA_USc,
      hOA_UQc,
      hPcSc_CD,
      hScQc_DK,
      hPcQc_CK,
      hPcSc_lt_CD,
      hScQc_lt_DK,
      hPcQc_lt_CK,
      hPcSc_lt_AR,
      hPcQc_lt_AB⟩



/--
Logical closure of the D-inside branch once the radial remainder
comparison has been established.

This lemma is intentionally tiny: it records the exact interface that a
future radial-superadditivity theorem must provide.  No new geometric
assumption is introduced into the project; `hDK_RB` is an explicit local
hypothesis of this wrapper.
-/
theorem hilbert_XI23_inside_D_false_of_radial_remainder_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (R B D K : Geo.Point)
    (hRB_DK : HilbertSegmentLess Geo R B D K)
    (hDK_RB : HilbertSegmentLess Geo D K R B) :
    False := by

  exact
    (hilbert_segmentLess_asymm
      Geo
      R B
      D K
      hRB_DK)
      hDK_RB





------------------------------------------------------------------------
-- XI.23 v47: corrected minimal radial-remainder interface
------------------------------------------------------------------------

/--
The outside-circumcenter branch with D inside angle CUK is reduced to
one independent planar radial-remainder theorem.

The radial theorem is stated only with the geometric data that are
mathematically essential:

* A,R,B lie on one circle centered at O;
* C,D,K lie on a larger circle centered at U;
* R is inside angle AOB and D is inside angle CUK;
* AR ~= CD and AB ~= CK;
* OA < UC.

Its conclusion is the missing comparison DK < RB.

The auxiliary inner radial-section points from v44-v45 are deliberately
not part of this interface.  They are a proof device for the future
radial theorem, not hypotheses of the theorem itself.
-/
theorem hilbert_XI23_inside_D_impossible_of_radial_remainder_rule_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (hCUK : Not (PrimCollinear Geo C U K))
    (hInsideD : HilbertRayMeetsSegment Geo U D C K)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hRadiusLess : HilbertSegmentLess Geo O A U C)
    (hRadialRemainder :
      forall
        A0 O0 B0 R0 C0 U0 D0 K0 : Geo.Point,
        Not (PrimCollinear Geo A0 O0 B0) ->
        Not (PrimCollinear Geo C0 U0 K0) ->
        HilbertRayMeetsSegment Geo O0 R0 A0 B0 ->
        HilbertRayMeetsSegment Geo U0 D0 C0 K0 ->
        Geo.Congruent O0 A0 O0 B0 ->
        Geo.Congruent O0 R0 O0 A0 ->
        Geo.Congruent U0 C0 U0 D0 ->
        Geo.Congruent U0 C0 U0 K0 ->
        Geo.Congruent A0 R0 C0 D0 ->
        Geo.Congruent C0 K0 A0 B0 ->
        HilbertSegmentLess Geo O0 A0 U0 C0 ->
        HilbertSegmentLess Geo D0 K0 R0 B0) :
    False := by

  rcases
      hilbert_XI23_inside_D_forces_source_remainder_chord_less_XI
        Geo
        A O B C P D E Q F U K
        h23_1
        hCUK
        hInsideD
        hUC_UD
        hUC_UK
        hOA_OB
        hOA_PC
        hOA_PD
        hOA_QE
        hOA_QF
        hCK_AB
        hDK_EF
    with
    ⟨R, hInsideR, hOR_OA, hAR_CD, hRB_DK⟩

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h23_1.2.2.1

  have hDK_RB :
      HilbertSegmentLess Geo D K R B :=
    hRadialRemainder
      A O B R C U D K
      hAOB
      hCUK
      hInsideR
      hInsideD
      hOA_OB
      hOR_OA
      hUC_UD
      hUC_UK
      hAR_CD
      hCK_AB
      hRadiusLess

  exact
    hilbert_XI23_inside_D_false_of_radial_remainder_XI
      Geo
      R B D K
      hRB_DK
      hDK_RB


------------------------------------------------------------------------
-- XI.23 v48: angular reduction of the planar radial-remainder problem
------------------------------------------------------------------------

/--
First intrinsic step toward the planar radial-remainder theorem.

Assume two three-ray configurations

    A - R - B  around O,
    C - D - K  around U,

with R and D interior rays, equal radii inside each configuration,
matching chords

    AR ~= CD,   AB ~= CK,

and the source radius OA strictly shorter than UC.

Cut UC, UD, UK at the common inner radius OA.  The resulting points
P,S,Q satisfy equal radii UP ~= US ~= UQ ~= OA.  The radial contraction
strictly shortens the chords corresponding to AR and AB, hence at the
common radius OA we obtain

    angle PUS < angle AOR,
    angle PUQ < angle AOB.

Moreover US is still an interior ray of angle PUQ.  Thus the remaining
radial-remainder problem is reduced to comparing the two complementary
angles SUQ and ROB.
-/
theorem hilbert_radial_remainder_angular_reduction_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B R C U D K : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCUK : Not (PrimCollinear Geo C U K))
    (hInsideR : HilbertRayMeetsSegment Geo O R A B)
    (hInsideD : HilbertRayMeetsSegment Geo U D C K)
    (hOA_OB : Geo.Congruent O A O B)
    (hOR_OA : Geo.Congruent O R O A)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hAR_CD : Geo.Congruent A R C D)
    (hCK_AB : Geo.Congruent C K A B)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    exists P S Q : Geo.Point,
      Geo.Between U P C /\
      Geo.Between U S D /\
      Geo.Between U Q K /\
      Geo.Congruent O A U P /\
      Geo.Congruent O A U S /\
      Geo.Congruent O A U Q /\
      HilbertRayMeetsSegment Geo U S P Q /\
      HilbertAngleLess Geo P U S A O R /\
      HilbertAngleLess Geo P U Q A O B := by

  have hCUD_less :
      HilbertAngleLess Geo C U D C U K :=
    hilbert_interior_angle_less
      Geo
      U D C K
      hCUK
      hInsideD

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hCUD_less.1

  have hInsideDrev :
      HilbertRayMeetsSegment Geo U D K C :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      U D C K
      hInsideD

  have hKUC :
      Not (PrimCollinear Geo K U C) := by
    intro h
    exact
      hCUK
        (PrimCollinearSymm
          Geo K U C h)

  have hKUD_less :
      HilbertAngleLess Geo K U D K U C :=
    hilbert_interior_angle_less
      Geo
      U D K C
      hKUC
      hInsideDrev

  have hKUD :
      Not (PrimCollinear Geo K U D) :=
    hKUD_less.1

  have hDUK :
      Not (PrimCollinear Geo D U K) := by
    intro h
    exact
      hKUD
        (PrimCollinearSymm
          Geo D U K h)

  rcases
      hilbert_XI23_inner_radial_section_XI
        Geo
        O A C D K U
        hCUD
        hDUK
        hCUK
        hUC_UD
        hUC_UK
        hRadiusLess
    with
    ⟨P, S, Q,
      hUPC,
      hUSD,
      hUQK,
      hOA_UP,
      hOA_US,
      hOA_UQ,
      hPS_CD,
      hSQ_DK,
      hPQ_CK,
      hPS_lt_CD,
      hSQ_lt_DK,
      hPQ_lt_CK⟩

  have hUP : Not (U = P) :=
    (HilbertOrder.between_incidence
      U P C hUPC).1

  have hUS : Not (U = S) :=
    (HilbertOrder.between_incidence
      U S D hUSD).1

  have hUQ : Not (U = Q) :=
    (HilbertOrder.between_incidence
      U Q K hUQK).1

  have hUPCcol :
      PrimCollinear Geo U P C :=
    (HilbertOrder.between_incidence
      U P C hUPC).2.2.2.1

  have hUSDcol :
      PrimCollinear Geo U S D :=
    (HilbertOrder.between_incidence
      U S D hUSD).2.2.2.1

  have hUQKcol :
      PrimCollinear Geo U Q K :=
    (HilbertOrder.between_incidence
      U Q K hUQK).2.2.2.1

  have hCUP :
      PrimCollinear Geo C U P :=
    PrimCollinearCycle
      Geo
      P C U
      (PrimCollinearCycle
        Geo U P C hUPCcol)

  have hKUQ :
      PrimCollinear Geo K U Q :=
    PrimCollinearCycle
      Geo
      Q K U
      (PrimCollinearCycle
        Geo U Q K hUQKcol)

  have hPUS :
      Not (PrimCollinear Geo P U S) := by
    intro hPUScol

    have hUPS :
        PrimCollinear Geo U P S :=
      PrimCollinearSwap
        Geo P U S hPUScol

    have hCUS :
        PrimCollinear Geo C U S :=
      hilbert_primCollinear_trans
        Geo
        C U P S
        hUP
        hCUP
        hUPS

    have hCUDcol :
        PrimCollinear Geo C U D :=
      hilbert_primCollinear_trans
        Geo
        C U S D
        hUS
        hCUS
        hUSDcol

    exact hCUD hCUDcol

  have hPUQ :
      Not (PrimCollinear Geo P U Q) := by
    intro hPUQcol

    have hUPQ :
        PrimCollinear Geo U P Q :=
      PrimCollinearSwap
        Geo P U Q hPUQcol

    have hCUQ :
        PrimCollinear Geo C U Q :=
      hilbert_primCollinear_trans
        Geo
        C U P Q
        hUP
        hCUP
        hUPQ

    have hCUKcol :
        PrimCollinear Geo C U K :=
      hilbert_primCollinear_trans
        Geo
        C U Q K
        hUQ
        hCUQ
        hUQKcol

    exact hCUK hCUKcol

  have hRayUPC :
      HilbertSameRay Geo U P C :=
    hilbert_sameRay_of_between
      Geo U P C hUPC

  have hRayUCP :
      HilbertSameRay Geo U C P :=
    hilbert_sameRay_symm
      Geo U P C hRayUPC

  have hRayUQK :
      HilbertSameRay Geo U Q K :=
    hilbert_sameRay_of_between
      Geo U Q K hUQK

  have hRayUKQ :
      HilbertSameRay Geo U K Q :=
    hilbert_sameRay_symm
      Geo U Q K hRayUQK

  have hInsideD_PQ :
      HilbertRayMeetsSegment Geo U D P Q :=
    hilbert_ray_meets_segment_sameRays
      Geo
      U D
      C K
      P Q
      hInsideD
      hRayUCP
      hRayUKQ
      hCUK
      hPUQ

  have hRayUSD :
      HilbertSameRay Geo U S D :=
    hilbert_sameRay_of_between
      Geo U S D hUSD

  have hRayUDS :
      HilbertSameRay Geo U D S :=
    hilbert_sameRay_symm
      Geo U S D hRayUSD

  rcases hInsideD_PQ with
    ⟨H, hPHQ, hRayUDH⟩

  have hRayUSH :
      HilbertSameRay Geo U S H :=
    hilbert_sameRay_of_common
      Geo
      U D S H
      hRayUDS
      hRayUDH

  have hInsideS :
      HilbertRayMeetsSegment Geo U S P Q :=
    ⟨H, hPHQ, hRayUSH⟩

  have hAOR_less :
      HilbertAngleLess Geo A O R A O B :=
    hilbert_interior_angle_less
      Geo
      O R A B
      hAOB
      hInsideR

  have hAOR :
      Not (PrimCollinear Geo A O R) :=
    hAOR_less.1

  have hCD_AR :
      Geo.Congruent C D A R :=
    hilbert_congruent_symmetry
      Geo
      A R
      C D
      hAR_CD

  have hPS_AR :
      HilbertSegmentLess Geo P S A R :=
    hilbert_segmentLess_congruent_right
      Geo
      P S
      C D
      A R
      hPS_lt_CD
      hCD_AR

  have hUP_OA :
      Geo.Congruent U P O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      U P
      hOA_UP

  have hUS_OA :
      Geo.Congruent U S O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      U S
      hOA_US

  have hOA_OR :
      Geo.Congruent O A O R :=
    hilbert_congruent_symmetry
      Geo
      O R
      O A
      hOR_OA

  have hUS_OR :
      Geo.Congruent U S O R :=
    hilbert_congruent_transitivity
      Geo
      U S
      O A
      O R
      hUS_OA
      hOA_OR

  have hPUS_AOR :
      HilbertAngleLess Geo P U S A O R :=
    hilbert_equalRadiusChord_angleLess_of_chordLess_XI
      Geo
      U P S
      O A R
      hPUS
      hAOR
      hUP_OA
      hUS_OR
      hPS_AR

  have hPQ_AB :
      HilbertSegmentLess Geo P Q A B :=
    hilbert_segmentLess_congruent_right
      Geo
      P Q
      C K
      A B
      hPQ_lt_CK
      hCK_AB

  have hUQ_OA :
      Geo.Congruent U Q O A :=
    hilbert_congruent_symmetry
      Geo
      O A
      U Q
      hOA_UQ

  have hUQ_OB :
      Geo.Congruent U Q O B :=
    hilbert_congruent_transitivity
      Geo
      U Q
      O A
      O B
      hUQ_OA
      hOA_OB

  have hPUQ_AOB :
      HilbertAngleLess Geo P U Q A O B :=
    hilbert_equalRadiusChord_angleLess_of_chordLess_XI
      Geo
      U P Q
      O A B
      hPUQ
      hAOB
      hUP_OA
      hUQ_OB
      hPQ_AB

  exact
    ⟨P, S, Q,
      hUPC,
      hUSD,
      hUQK,
      hOA_UP,
      hOA_US,
      hOA_UQ,
      hInsideS,
      hPUS_AOR,
      hPUQ_AOB⟩




------------------------------------------------------------------------
-- XI.23 v53: adjacent copy of the third source angle
------------------------------------------------------------------------

/--
Auxiliary construction for the exterior-circumcenter branch of XI.23.

Start with the proper source angles CPD and EQF.  On the ray PD,
construct on the side opposite C a copy of angle EQF, and on that
new ray lay off PT congruent to QF.  If also PD ~= QE, then SAS gives

    DT ~= EF.

Thus, whenever DK ~= EF, the constructed point T satisfies

    DT ~= DK.

The opposite-side conclusion records the essential orientation of the
classical auxiliary construction: ray PT is adjacent to angle CPD,
not inside it.
-/
theorem hilbert_XI23_adjacent_third_angle_chord_witness_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C P D E Q F K : Geo.Point)
    (hCPD : Not (PrimCollinear Geo C P D))
    (hEQF : Not (PrimCollinear Geo E Q F))
    (hPD_QE : Geo.Congruent P D Q E)
    (hDK_EF : Geo.Congruent D K E F) :
    exists T : Geo.Point,
      exists base : Geo.Line,
        HilbertIncidence.OnLine P base /\
        HilbertIncidence.OnLine D base /\
        HilbertOppositeSide Geo C T base /\
        Geo.AngleCongruent E Q F D P T /\
        Geo.Congruent P T Q F /\
        Geo.Congruent D T D K := by

  --------------------------------------------------------------------
  -- The carrier PD and a point S opposite C across PD.
  --------------------------------------------------------------------

  have hPDC :
      Not (PrimCollinear Geo P D C) := by
    intro h
    exact
      hCPD
        (PrimCollinearRotate
          Geo
          C D P
          (PrimCollinearSymm
            Geo P D C h))

  have hPD :
      Not (P = D) :=
    hilbert_noncollinear_ne_first
      Geo P D C hPDC

  rcases
      HilbertPlaneIncidence.line_through
        P D hPD
    with
    ⟨base, hPbase, hDbase⟩

  have hCP :
      Not (C = P) :=
    hilbert_noncollinear_ne_first
      Geo C P D hCPD

  rcases
      HilbertOrder.between_extension
        C P hCP
    with
    ⟨S, hCPS⟩

  have hCoff :
      Not (HilbertIncidence.OnLine C base) := by
    intro hCbase
    exact
      hCPD
        ⟨base,
          hCbase,
          hPbase,
          hDbase⟩

  have hPS :
      Not (P = S) :=
    (HilbertOrder.between_incidence
      C P S hCPS).2.1

  have hCPScol :
      PrimCollinear Geo C P S :=
    (HilbertOrder.between_incidence
      C P S hCPS).2.2.2.1

  have hPSCcol :
      PrimCollinear Geo P S C :=
    PrimCollinearCycle
      Geo C P S hCPScol

  have hSoff :
      Not (HilbertIncidence.OnLine S base) := by
    intro hSbase

    have hCbase :
        HilbertIncidence.OnLine C base :=
      hilbert_collinear_on_line
        Geo
        P S C
        base
        hPS
        hPbase
        hSbase
        hPSCcol

    exact hCoff hCbase

  have hOppCS :
      HilbertOppositeSide Geo C S base :=
    ⟨hCoff,
      hSoff,
      ⟨P,
        hCPS,
        hPbase⟩⟩

  --------------------------------------------------------------------
  -- Copy angle EQF at P, starting from ray PD, on the selected side.
  --------------------------------------------------------------------

  have hDP :
      Not (D = P) := by
    intro h
    exact hPD h.symm

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        E Q F
        D P
        S
        hEQF
        hDP
        base
        hDbase
        hPbase
        hSoff
    with
    ⟨T0,
      hT0SSame,
      hEQF_DPT0,
      _hUnique⟩

  have hST0Same :
      HilbertSameSide Geo S T0 base :=
    hilbert_sameSide_symm
      Geo T0 S base hT0SSame

  have hOppCT0 :
      HilbertOppositeSide Geo C T0 base :=
    hilbert_oppositeSide_transport_right
      Geo
      C S T0
      base
      hOppCS
      hST0Same

  have hPT0 :
      Not (P = T0) := by
    intro h
    subst T0
    exact hOppCT0.2.1 hPbase

  --------------------------------------------------------------------
  -- Lay off PT ~= QF on the constructed ray PT0.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        Q F
        P T0
        hPT0
    with
    ⟨T,
      hRayT0T,
      hPT_QF⟩

  rcases
      HilbertPlaneIncidence.line_through
        P T0 hPT0
    with
    ⟨rayLine,
      hPray,
      hT0ray⟩

  have hDray :
      Not (HilbertIncidence.OnLine D rayLine) := by
    intro hDray

    have hBaseRay :
        base = rayLine :=
      HilbertPlaneIncidence.line_unique
        P D hPD
        base rayLine
        hPbase hDbase
        hPray hDray

    exact
      hOppCT0.2.1
        (hBaseRay ▸ hT0ray)

  have hT0TSame :
      HilbertSameSide Geo T0 T base :=
    hilbert_sameRay_points_sameSide
      Geo
      P T0
      T0 T
      D
      rayLine base
      hPray
      hT0ray
      hPbase
      hDbase
      hDray
      (hilbert_sameRay_refl
        Geo P T0
        (by
          intro hT0P
          exact hPT0 hT0P.symm))
      hRayT0T

  have hSTSame :
      HilbertSameSide Geo S T base :=
    hilbert_sameSide_trans
      Geo
      S T0 T
      base
      hST0Same
      hT0TSame

  have hOppCT :
      HilbertOppositeSide Geo C T base :=
    hilbert_oppositeSide_transport_right
      Geo
      C S T
      base
      hOppCS
      hSTSame

  --------------------------------------------------------------------
  -- Replacing T0 by T on the same ray preserves the copied angle.
  --------------------------------------------------------------------

  have hDPT0_DPT :
      Geo.Angle D P T0 =
      Geo.Angle D P T :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      P D T0 T
      hRayT0T

  have hEQF_DPT :
      Geo.AngleCongruent E Q F D P T := by
    unfold Geometry.Geo.AngleCongruent
      at hEQF_DPT0 |-
    rw [<- hDPT0_DPT]
    exact hEQF_DPT0

  --------------------------------------------------------------------
  -- SAS: PDT ~= QEF, hence DT ~= EF ~= DK.
  --------------------------------------------------------------------

  have hPDT :
      Not (PrimCollinear Geo P D T) :=
    hilbert_not_collinear_of_off_line
      Geo
      P D T
      base
      hPD
      hPbase
      hDbase
      hOppCT.2.1

  have hQEF :
      Not (PrimCollinear Geo Q E F) := by
    intro h
    exact
      hEQF
        (PrimCollinearSwap
          Geo Q E F h)

  have hDPT_EQF :
      Geo.AngleCongruent D P T E Q F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E Q F
      D P T
      hEQF_DPT

  have hSAS :=
    SAS
      (Geo := Geo)
      P D T
      Q E F
      hPDT
      hQEF
      hPD_QE
      hDPT_EQF
      hPT_QF

  have hDT_EF :
      Geo.Congruent D T E F :=
    hSAS.sideBC

  have hEF_DK :
      Geo.Congruent E F D K :=
    hilbert_congruent_symmetry
      Geo
      D K
      E F
      hDK_EF

  have hDT_DK :
      Geo.Congruent D T D K :=
    hilbert_congruent_transitivity
      Geo
      D T
      E F
      D K
      hDT_EF
      hEF_DK

  exact
    ⟨T,
      base,
      hPbase,
      hDbase,
      hOppCT,
      hEQF_DPT,
      hPT_QF,
      hDT_DK⟩



------------------------------------------------------------------------
-- XI.23 v54: the two copied central angles shrink at the larger radius
------------------------------------------------------------------------

/--
In the adjacent-copy configuration, assume the source circle at `P`
has smaller radius than the target circle at `U`.

For the common chord `CD`, and for the congruent chords `DT` and `DK`,
the corresponding central angles at the larger radius are strictly
smaller:

    angle CUD < angle CPD,
    angle DUK < angle DPT.

This is just the already established equal-radius chord monotonicity,
applied twice.  No angle addition is used here.
-/
theorem hilbert_XI23_adjacent_copy_central_angles_shrink_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (C P D T U K : Geo.Point)
    (hCPD : Not (PrimCollinear Geo C P D))
    (hDPT : Not (PrimCollinear Geo D P T))
    (hCUD : Not (PrimCollinear Geo C U D))
    (hDUK : Not (PrimCollinear Geo D U K))
    (hPC_PD : Geo.Congruent P C P D)
    (hPD_PT : Geo.Congruent P D P T)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hDT_DK : Geo.Congruent D T D K)
    (hRadiusLess : HilbertSegmentLess Geo P C U C) :
    HilbertAngleLess Geo C U D C P D /\
    HilbertAngleLess Geo D U K D P T := by

  --------------------------------------------------------------------
  -- First common chord: CD.
  --------------------------------------------------------------------

  have hCD_CD :
      Geo.Congruent C D C D :=
    hilbert_congruent_reflexive Geo C D

  have hFirst :
      HilbertAngleLess Geo C U D C P D :=
    hilbert_equalRadiusChord_angleLess_of_radiusLess_XI
      Geo
      C P D
      C U D
      hCPD
      hCUD
      hPC_PD
      hUC_UD
      hCD_CD
      hRadiusLess

  --------------------------------------------------------------------
  -- Transfer the radius inequality from PC < UC to PD < UD.
  --------------------------------------------------------------------

  have hPD_PC :
      Geo.Congruent P D P C :=
    hilbert_congruent_symmetry
      Geo P C P D hPC_PD

  have hPD_lt_UC :
      HilbertSegmentLess Geo P D U C :=
    hilbert_segmentLess_congruent_left
      Geo
      P C
      P D
      U C
      hRadiusLess
      hPD_PC

  have hPD_lt_UD :
      HilbertSegmentLess Geo P D U D :=
    hilbert_segmentLess_congruent_right
      Geo
      P D
      U C
      U D
      hPD_lt_UC
      hUC_UD

  --------------------------------------------------------------------
  -- Second congruent chord: DT ~= DK.
  --------------------------------------------------------------------

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo U C U D hUC_UD

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      hUD_UC
      hUC_UK

  have hDK_DT :
      Geo.Congruent D K D T :=
    hilbert_congruent_symmetry
      Geo D T D K hDT_DK

  have hSecond :
      HilbertAngleLess Geo D U K D P T :=
    hilbert_equalRadiusChord_angleLess_of_radiusLess_XI
      Geo
      D P T
      D U K
      hDPT
      hDUK
      hPD_PT
      hUD_UK
      hDK_DT
      hPD_lt_UD

  exact And.intro hFirst hSecond



/--
Base-angle data for the four isosceles triangles occurring in the
corrected outside-circumcenter branch of XI.23.

The two source triangles are

    PCD, PDT,

and the two target-radius triangles are

    UCD, UDK.

The conclusion is deliberately oriented at the common vertices `C`
and `D`, ready for the I.32 comparison in the next step.
-/
theorem hilbert_XI23_adjacent_copy_isosceles_base_pairs_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C P D T U K : Geo.Point)
    (hCPD : Not (PrimCollinear Geo C P D))
    (hDPT : Not (PrimCollinear Geo D P T))
    (hCUD : Not (PrimCollinear Geo C U D))
    (hDUK : Not (PrimCollinear Geo D U K))
    (hPC_PD : Geo.Congruent P C P D)
    (hPD_PT : Geo.Congruent P D P T)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K) :
    Geo.AngleCongruent P C D C D P /\
    Geo.AngleCongruent P D T D T P /\
    Geo.AngleCongruent U C D C D U /\
    Geo.AngleCongruent U D K D K U := by

  have hPCD :
      Not (PrimCollinear Geo P C D) := by
    intro h
    exact hCPD
      (PrimCollinearSwap Geo P C D h)

  have hPDT :
      Not (PrimCollinear Geo P D T) := by
    intro h
    exact hDPT
      (PrimCollinearSwap Geo P D T h)

  have hUCD :
      Not (PrimCollinear Geo U C D) := by
    intro h
    exact hCUD
      (PrimCollinearSwap Geo U C D h)

  have hUDK :
      Not (PrimCollinear Geo U D K) := by
    intro h
    exact hDUK
      (PrimCollinearSwap Geo U D K h)

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo U C U D hUC_UD

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      hUD_UC
      hUC_UK

  have hPCD_CDP :
      Geo.AngleCongruent P C D C D P :=
    hilbert_isosceles_base_angles_oriented_XI
      Geo
      P C D
      hPCD
      hPC_PD

  have hPDT_DTP :
      Geo.AngleCongruent P D T D T P :=
    hilbert_isosceles_base_angles_oriented_XI
      Geo
      P D T
      hPDT
      hPD_PT

  have hUCD_CDU :
      Geo.AngleCongruent U C D C D U :=
    hilbert_isosceles_base_angles_oriented_XI
      Geo
      U C D
      hUCD
      hUC_UD

  have hUDK_DKU :
      Geo.AngleCongruent U D K D K U :=
    hilbert_isosceles_base_angles_oriented_XI
      Geo
      U D K
      hUDK
      hUD_UK

  exact
    ⟨hPCD_CDP,
      hPDT_DTP,
      hUCD_CDU,
      hUDK_DKU⟩



/--
The two base-angle inequalities needed in the corrected
outside-circumcenter branch of XI.23.

From PC < UC and the equal-radius data we obtain

    angle CDP < angle CDU,
    angle PDT < angle UDK.

The second comparison also uses the copied chord DT ~= DK.
-/
theorem hilbert_XI23_adjacent_copy_base_angles_expand_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C P D T U K : Geo.Point)
    (hCPD : Not (PrimCollinear Geo C P D))
    (hDPT : Not (PrimCollinear Geo D P T))
    (hCUD : Not (PrimCollinear Geo C U D))
    (hDUK : Not (PrimCollinear Geo D U K))
    (hPC_PD : Geo.Congruent P C P D)
    (hPD_PT : Geo.Congruent P D P T)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hDT_DK : Geo.Congruent D T D K)
    (hRadiusLess : HilbertSegmentLess Geo P C U C) :
    HilbertAngleLess Geo C D P C D U /\
    HilbertAngleLess Geo P D T U D K := by

  --------------------------------------------------------------------
  -- Transfer PC < UC to PD < UD.
  --------------------------------------------------------------------

  have hPD_PC :
      Geo.Congruent P D P C :=
    hilbert_congruent_symmetry
      Geo P C P D hPC_PD

  have hPD_UC :
      HilbertSegmentLess Geo P D U C :=
    bookZero_32_lessThanCongruence2
      Geo
      P C
      U C
      P D
      hRadiusLess
      hPC_PD

  have hPD_UD :
      HilbertSegmentLess Geo P D U D :=
    bookZero_30_lessThanCongruence
      Geo
      P D
      U C
      U D
      hPD_UC
      hUC_UD

  --------------------------------------------------------------------
  -- First pair: triangles PDC and UDC.
  --------------------------------------------------------------------

  have hPDC :
      Not (PrimCollinear Geo P D C) := by
    intro h

    have hDCP :
        PrimCollinear Geo D C P :=
      PrimCollinearCycle Geo P D C h

    have hCPDcol :
        PrimCollinear Geo C P D :=
      PrimCollinearCycle Geo D C P hDCP

    exact hCPD hCPDcol

  have hUDC :
      Not (PrimCollinear Geo U D C) := by
    intro h

    have hCDU :
        PrimCollinear Geo C D U :=
      PrimCollinearSymm Geo U D C h

    have hCUDcol :
        PrimCollinear Geo C U D :=
      PrimCollinearRotate Geo C D U hCDU

    exact hCUD hCUDcol

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo U C U D hUC_UD

  have hDC_DC :
      Geo.Congruent D C D C :=
    hilbert_congruent_reflexive Geo D C

  have hPDC_UDC :
      HilbertAngleLess Geo P D C U D C :=
    hilbert_isosceles_base_angle_less_of_smaller_equal_sides_XI
      Geo
      P D C
      U D C
      hPDC
      hUDC
      hPD_PC
      hUD_UC
      hDC_DC
      hPD_UD

  have hPDCrefl :
      Geo.AngleCongruent P D C P D C :=
    Geometry.Geo.angle_congruent_reflexive
      Geo P D C

  have hCDP_PDC :
      Geo.AngleCongruent C D P P D C :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      P D C
      P D C).mp
      hPDCrefl

  have hCDP_UDC :
      HilbertAngleLess Geo C D P U D C :=
    hilbert_angleLess_transport_left
      Geo
      P D C
      C D P
      U D C
      hPDC_UDC
      (by
        intro h
        exact hPDC
          (PrimCollinearSymm Geo C D P h))
      hCDP_PDC

  have hUDCrefl :
      Geo.AngleCongruent U D C U D C :=
    Geometry.Geo.angle_congruent_reflexive
      Geo U D C

  have hUDC_CDU :
      Geo.AngleCongruent U D C C D U :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      U D C
      U D C).mp
      hUDCrefl

  have hFirst :
      HilbertAngleLess Geo C D P C D U :=
    hilbert_angleLess_transport_right
      Geo
      C D P
      U D C
      C D U
      hCDP_UDC
      (by
        intro h
        exact hCUD
          (PrimCollinearRotate Geo C D U h))
      hUDC_CDU

  --------------------------------------------------------------------
  -- Second pair: triangles PDT and UDK.
  --------------------------------------------------------------------

  have hPDT :
      Not (PrimCollinear Geo P D T) := by
    intro h
    exact hDPT
      (PrimCollinearSwap Geo P D T h)

  have hUDK :
      Not (PrimCollinear Geo U D K) := by
    intro h
    exact hDUK
      (PrimCollinearSwap Geo U D K h)

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      hUD_UC
      hUC_UK

  have hSecond :
      HilbertAngleLess Geo P D T U D K :=
    hilbert_isosceles_base_angle_less_of_smaller_equal_sides_XI
      Geo
      P D T
      U D K
      hPDT
      hUDK
      hPD_PT
      hUD_UK
      hDT_DK
      hPD_UD

  exact ⟨hFirst, hSecond⟩



/--
XI.23 specialization of the preceding divider lemma.

The auxiliary construction v53 gives C and T on opposite sides of PD.
If PC ~= PD and PD ~= PT, then DP is an interior ray of angle CDT.
-/
theorem hilbert_XI23_adjacent_copy_reverse_divider_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C P D T : Geo.Point)
    (base : Geo.Line)
    (hPbase : HilbertIncidence.OnLine P base)
    (hDbase : HilbertIncidence.OnLine D base)
    (hOppCT : HilbertOppositeSide Geo C T base)
    (hCPD : Not (PrimCollinear Geo C P D))
    (hPC_PD : Geo.Congruent P C P D)
    (hPD_PT : Geo.Congruent P D P T) :
    HilbertRayMeetsSegment Geo D P C T := by

  have hPC_PT :
      Geo.Congruent P C P T :=
    hilbert_congruent_transitivity
      Geo
      P C
      P D
      P T
      hPC_PD
      hPD_PT

  exact
    hilbert_equalRadius_oppositeSides_reverse_divider_XI
      Geo
      P C D T
      base
      hPbase
      hDbase
      hOppCT
      hCPD
      hPC_PD
      hPC_PT



/--
XI.23 local angle assembly.

Suppose DP divides angle CDT and DU divides angle CDK.  If

    angle CDP < angle CDU
    angle PDT < angle UDK,

then, after reversing the arms of the second pair of unoriented angles,
we have the componentwise comparison required by v59, hence

    angle CDT < angle CDK.
-/
theorem hilbert_XI23_adjacent_copy_whole_angle_less_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C P D T U K : Geo.Point)
    (hInsideP : HilbertRayMeetsSegment Geo D P C T)
    (hInsideU : HilbertRayMeetsSegment Geo D U C K)
    (hLeft : HilbertAngleLess Geo C D P C D U)
    (hRight : HilbertAngleLess Geo P D T U D K) :
    HilbertAngleLess Geo C D T C D K := by

  have hCDP :
      Not (PrimCollinear Geo C D P) :=
    hLeft.1

  have hCDU :
      Not (PrimCollinear Geo C D U) :=
    hLeft.2.1

  have hCDT :
      Not (PrimCollinear Geo C D T) :=
    hilbert_angleDecomposition_whole_noncollinear_of_left_XI
      Geo
      D C T P
      hInsideP
      hCDP

  have hCDK :
      Not (PrimCollinear Geo C D K) :=
    hilbert_angleDecomposition_whole_noncollinear_of_left_XI
      Geo
      D C K U
      hInsideU
      hCDU

  --------------------------------------------------------------------
  -- Reorient the second component inequality:
  --
  --   PDT < UDK
  --
  -- becomes
  --
  --   TDP < KDU.
  --------------------------------------------------------------------

  have hPDT :
      Not (PrimCollinear Geo P D T) :=
    hRight.1

  have hUDK :
      Not (PrimCollinear Geo U D K) :=
    hRight.2.1

  have hTDP :
      Not (PrimCollinear Geo T D P) := by
    intro h
    exact hPDT
      (PrimCollinearSymm Geo T D P h)

  have hKDU :
      Not (PrimCollinear Geo K D U) := by
    intro h
    exact hUDK
      (PrimCollinearSymm Geo K D U h)

  have hPDTrefl :
      Geo.AngleCongruent P D T P D T :=
    Geometry.Geo.angle_congruent_reflexive
      Geo P D T

  have hTDP_PDT :
      Geo.AngleCongruent T D P P D T :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      P D T
      P D T).mp
      hPDTrefl

  have hTDP_UDK :
      HilbertAngleLess Geo T D P U D K :=
    hilbert_angleLess_transport_left
      Geo
      P D T
      T D P
      U D K
      hRight
      hTDP
      hTDP_PDT

  have hUDKrefl :
      Geo.AngleCongruent U D K U D K :=
    Geometry.Geo.angle_congruent_reflexive
      Geo U D K

  have hUDK_KDU :
      Geo.AngleCongruent U D K K D U :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      U D K
      U D K).mp
      hUDKrefl

  have hRightOriented :
      HilbertAngleLess Geo T D P K D U :=
    hilbert_angleLess_transport_right
      Geo
      T D P
      U D K
      K D U
      hTDP_UDK
      hKDU
      hUDK_KDU

  exact
    hilbert_angleDecomposition_componentwise_less_whole_XI
      Geo
      D C T P
      D C K U
      hCDT
      hCDK
      hInsideP
      hInsideU
      hLeft
      hRightOriented



------------------------------------------------------------------------
-- XI.23 v61: convert the assembled angle inequality to a chord inequality
------------------------------------------------------------------------

/--
If the auxiliary triangle CDT and the target triangle CDK share the
side CD, have DT congruent to DK, and

    angle CDT < angle CDK,

then Euclid I.24 gives

    CT < CK.

This is the side form of the local outside-circumcenter comparison.
-/
theorem hilbert_XI23_adjacent_copy_third_side_less_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C D T K : Geo.Point)
    (hCDT : Not (PrimCollinear Geo C D T))
    (hCDK : Not (PrimCollinear Geo C D K))
    (hDT_DK : Geo.Congruent D T D K)
    (hAngle : HilbertAngleLess Geo C D T C D K) :
    HilbertSegmentLess Geo C T C K := by

  have hDC_DC :
      Geo.Congruent D C D C :=
    hilbert_congruent_reflexive Geo D C

  have hDK_DT :
      Geo.Congruent D K D T :=
    hilbert_congruent_symmetry
      Geo D T D K hDT_DK

  exact
    euclid_proposition_24
      (Geo := Geo)
      D C K
      D C T
      (by
        intro h
        exact hCDK
          (PrimCollinearSwap Geo D C K h))
      (by
        intro h
        exact hCDT
          (PrimCollinearSwap Geo D C T h))
      hDC_DC
      hDK_DT
      hAngle



/--
XI.23 packaged local conclusion.

Once DP and DU are the two interior dividers and the two corresponding
component inequalities are known, the auxiliary chord CT is strictly
shorter than CK.
-/
theorem hilbert_XI23_adjacent_copy_chord_less_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C P D T U K : Geo.Point)
    (hInsideP : HilbertRayMeetsSegment Geo D P C T)
    (hInsideU : HilbertRayMeetsSegment Geo D U C K)
    (hLeft : HilbertAngleLess Geo C D P C D U)
    (hRight : HilbertAngleLess Geo P D T U D K)
    (hDT_DK : Geo.Congruent D T D K) :
    HilbertSegmentLess Geo C T C K := by

  have hWhole :
      HilbertAngleLess Geo C D T C D K :=
    hilbert_XI23_adjacent_copy_whole_angle_less_XI
      Geo
      C P D T U K
      hInsideP
      hInsideU
      hLeft
      hRight

  exact
    hilbert_XI23_adjacent_copy_third_side_less_XI
      Geo
      C D T K
      hWhole.1
      hWhole.2.1
      hDT_DK
      hWhole



------------------------------------------------------------------------
-- XI.23 v62: chord inequality gives the source-angle contradiction input
------------------------------------------------------------------------

/--
Convert the v61 chord inequality into an angle inequality on the common
source circle.

Assume

    CT < CK,
    CK ~= AB,

and that triangle PCT and angle AOB are cut by the same radius:

    PC ~= PT,
    PC ~= OA,
    OA ~= OB.

Then CT < AB, so the converse equal-radius chord comparison gives

    angle CPT < angle AOB.

This is the exact angular input needed for the final outside-center
case split: either ray PD or its opposite ray is the interior divider
of angle CPT.
-/
theorem hilbert_XI23_adjacent_copy_angle_less_source_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P T K : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCPT : Not (PrimCollinear Geo C P T))
    (hPC_PT : Geo.Congruent P C P T)
    (hPC_OA : Geo.Congruent P C O A)
    (hOA_OB : Geo.Congruent O A O B)
    (hCK_AB : Geo.Congruent C K A B)
    (hCT_CK : HilbertSegmentLess Geo C T C K) :
    HilbertAngleLess Geo C P T A O B := by

  have hCT_AB :
      HilbertSegmentLess Geo C T A B :=
    hilbert_segmentLess_congruent_right
      Geo
      C T
      C K
      A B
      hCT_CK
      hCK_AB

  have hPT_PC :
      Geo.Congruent P T P C :=
    hilbert_congruent_symmetry
      Geo P C P T hPC_PT

  have hPT_OA :
      Geo.Congruent P T O A :=
    hilbert_congruent_transitivity
      Geo
      P T
      P C
      O A
      hPT_PC
      hPC_OA

  have hPT_OB :
      Geo.Congruent P T O B :=
    hilbert_congruent_transitivity
      Geo
      P T
      O A
      O B
      hPT_OA
      hOA_OB

  exact
    hilbert_equalRadiusChord_angleLess_of_chordLess_XI
      Geo
      P C T
      O A B
      hCPT
      hAOB
      hPC_OA
      hPT_OB
      hCT_AB




------------------------------------------------------------------------
-- XI.23 v65: close the direct-PD branch of the bad-radius case
------------------------------------------------------------------------

/--
XI.23 bad-radius branch, direct divider at P.

In the auxiliary adjacent-copy configuration, suppose ray PD is interior
to angle CPT.  Since angle DPT is a copy of EQF, the source hypothesis

    angle CPD + angle EQF > angle AOB

becomes

    angle CPD + angle DPT > angle AOB.

Because PD is the interior divider of CPT, v64 yields

    angle AOB < angle CPT.

But v62 gives the opposite strict inequality

    angle CPT < angle AOB.

Hence this branch is impossible.
-/
theorem hilbert_XI23_adjacent_copy_inside_PD_impossible_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F T : Geo.Point)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (hDPT : Not (PrimCollinear Geo D P T))
    (hInsideD :
      HilbertRayMeetsSegment Geo P D C T)
    (hEQF_DPT :
      Geo.AngleCongruent E Q F D P T)
    (hCPT_AOB :
      HilbertAngleLess Geo C P T A O B) :
    False := by

  have hSum :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        D P T
        A O B :=
    hilbertTwoAnglesGreaterThanAngle_transport_second
      Geo
      C P D
      E Q F
      D P T
      A O B
      h23_1
      hDPT
      hEQF_DPT

  have hAOB_CPT :
      HilbertAngleLess Geo A O B C P T :=
    hilbert_twoAnglesGreaterThanAngle_of_interior_split_gives_whole_greater_XI
      Geo
      C P T D
      A O B
      hCPT_AOB.1
      hInsideD
      hSum

  have hCycle :
      HilbertAngleLess Geo C P T C P T :=
    hilbert_angleLess_trans
      Geo
      C P T
      A O B
      C P T
      hCPT_AOB
      hAOB_CPT

  exact
    (hilbert_angleLess_irrefl
      Geo C P T)
      hCycle




------------------------------------------------------------------------
-- XI.23 v66: isolate the sole remaining four-right-angle obligation
------------------------------------------------------------------------

/--
XI.23 bad-radius branch, opposite-PD orientation.

At this stage all geometry of the auxiliary point T has already been
settled.  If the ray PY opposite to PD is interior to angle CPT, then
the only four-right-angle information needed is the cyclic comparison

    angle CPY + angle YPT > angle AOB.

That comparison makes AOB strictly smaller than CPT, contradicting the
already established inequality CPT < AOB.

Thus this theorem isolates the sole remaining obligation of the
bad-radius branch: deriving the displayed cyclic comparison from
`HilbertThreeAnglesLessThanFourRightAngles`.
-/
theorem hilbert_XI23_adjacent_copy_inside_opposite_PD_impossible_of_cyclic_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P T Y : Geo.Point)
    (hInsideY :
      HilbertRayMeetsSegment Geo P Y C T)
    (hCyclic :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P Y
        Y P T
        A O B)
    (hCPT_AOB :
      HilbertAngleLess Geo C P T A O B) :
    False := by

  have hAOB_CPT :
      HilbertAngleLess Geo A O B C P T :=
    hilbert_twoAnglesGreaterThanAngle_of_interior_split_gives_whole_greater_XI
      Geo
      C P T Y
      A O B
      hCPT_AOB.1
      hInsideY
      hCyclic

  have hCycle :
      HilbertAngleLess Geo C P T C P T :=
    hilbert_angleLess_trans
      Geo
      C P T
      A O B
      C P T
      hCPT_AOB
      hAOB_CPT

  exact
    (hilbert_angleLess_irrefl
      Geo C P T)
      hCycle




------------------------------------------------------------------------
-- XI.23 v67: discharge the opposite-PD branch from the actual <4R hypothesis
------------------------------------------------------------------------

/--
XI.23 bad-radius branch, opposite-PD orientation, with the real XI.23
four-right-angle hypothesis.

The cyclic four-right-angle theorem gives witnesses Y0 and Z with

    angle CPY0 + angle EQZ > angle AOB.

The chosen ray PY in the local auxiliary configuration is another
opposite ray to PD, so CPY0 ~= CPY.  Likewise, because DPT ~= EQF,
their supplementary angles satisfy EQZ ~= YPT.

After transporting both summands, the cyclic comparison becomes

    angle CPY + angle YPT > angle AOB,

and v66 closes the branch.
-/
theorem hilbert_XI23_adjacent_copy_inside_opposite_PD_impossible_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F T Y : Geo.Point)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hDPY : Geo.Between D P Y)
    (hEQF_DPT :
      Geo.AngleCongruent E Q F D P T)
    (hInsideY :
      HilbertRayMeetsSegment Geo P Y C T)
    (hCPT_AOB :
      HilbertAngleLess Geo C P T A O B) :
    False := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    hFour.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    hFour.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    hFour.2.2.1

  have hCPT :
      Not (PrimCollinear Geo C P T) :=
    hCPT_AOB.1

  --------------------------------------------------------------------
  -- Cyclic form of the four-right-angle bound:
  --
  --   supplement(CPD) + supplement(EQF) > AOB.
  --------------------------------------------------------------------

  have hFourCyclic :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        C P D
        E Q F
        A O B :=
    hilbertThreeAnglesLessThanFourRightAngles_cycle
      Geo
      A O B
      C P D
      E Q F
      hFour

  rcases
      hilbertThreeAnglesLessThanFourRightAngles_elim
        Geo
        C P D
        E Q F
        A O B
        hFourCyclic
    with
    ⟨Y0, Z,
      hDPY0,
      hFQZ,
      hCompare0⟩

  --------------------------------------------------------------------
  -- The first cyclic supplement CPY0 is congruent to the locally
  -- chosen supplement CPY, because both are supplements of DPC.
  --------------------------------------------------------------------

  have hDPC :
      Not (PrimCollinear Geo D P C) := by
    intro hcol
    exact hCPD
      (PrimCollinearSymm Geo D P C hcol)

  have hCP :
      Ne C P :=
    hilbert_noncollinear_ne_first
      Geo C P D hCPD

  have hDPCrefl :
      Geo.AngleCongruent D P C D P C :=
    Geometry.Geo.angle_congruent_reflexive
      Geo D P C

  have hSuppY0 :
      BookZeroSupplement Geo D P C C Y0 :=
    ⟨hilbert_sameRay_refl
        Geo P C hCP,
      hDPY0⟩

  have hSuppY :
      BookZeroSupplement Geo D P C C Y :=
    ⟨hilbert_sameRay_refl
        Geo P C hCP,
      hDPY⟩

  have hCPY0_CPY :
      Geo.AngleCongruent C P Y0 C P Y :=
    bookZero_43_supplements
      Geo
      D P C C Y0
      D P C C Y
      hDPCrefl
      hSuppY0
      hSuppY
      hDPC
      hDPC

  have hCPY :
      Not (PrimCollinear Geo C P Y) :=
    (hilbert_interior_angle_less
      Geo
      P Y C T
      hCPT
      hInsideY).1

  have hCompare1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P Y
        E Q Z
        A O B :=
    hilbertTwoAnglesGreaterThanAngle_transport_first
      Geo
      C P Y0
      C P Y
      E Q Z
      A O B
      hCompare0
      hCPY
      hCPY0_CPY

  --------------------------------------------------------------------
  -- EQZ and YPT are supplements of congruent angles EQF and DPT.
  --------------------------------------------------------------------

  have hFQE :
      Not (PrimCollinear Geo F Q E) := by
    intro hcol
    exact hEQF
      (PrimCollinearSymm Geo F Q E hcol)

  have hTPC :
      Not (PrimCollinear Geo T P C) := by
    intro hcol
    exact hCPT
      (PrimCollinearSymm Geo T P C hcol)

  have hInsideYrev :
      HilbertRayMeetsSegment Geo P Y T C :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      P Y C T
      hInsideY

  have hTPY :
      Not (PrimCollinear Geo T P Y) :=
    (hilbert_interior_angle_less
      Geo
      P Y T C
      hTPC
      hInsideYrev).1

  have hDPYdata :=
    HilbertOrder.between_incidence
      D P Y hDPY

  have hPD :
      Ne P D :=
    hDPYdata.1.symm

  have hDPYcol :
      PrimCollinear Geo D P Y :=
    hDPYdata.2.2.2.1

  have hDPT :
      Not (PrimCollinear Geo D P T) := by
    intro hDPTcol

    have hTPD :
        PrimCollinear Geo T P D :=
      PrimCollinearSymm
        Geo D P T hDPTcol

    have hPDY :
        PrimCollinear Geo P D Y :=
      PrimCollinearSwap
        Geo D P Y hDPYcol

    have hTPYcol :
        PrimCollinear Geo T P Y :=
      hilbert_primCollinear_trans
        Geo
        T P D Y
        hPD
        hTPD
        hPDY

    exact hTPY hTPYcol

  have hYPT :
      Not (PrimCollinear Geo Y P T) := by
    intro hcol
    exact hTPY
      (PrimCollinearSymm Geo Y P T hcol)

  have hEQ :
      Ne E Q :=
    hilbert_noncollinear_ne_first
      Geo E Q F hEQF

  have hTP :
      Ne T P :=
    hilbert_noncollinear_ne_first
      Geo T P Y hTPY

  have hSuppEQZ :
      BookZeroSupplement Geo F Q E E Z :=
    ⟨hilbert_sameRay_refl
        Geo Q E hEQ,
      hFQZ⟩

  have hSuppTPY :
      BookZeroSupplement Geo D P T T Y :=
    ⟨hilbert_sameRay_refl
        Geo P T hTP,
      hDPY⟩

  have hFQE_DPT :
      Geo.AngleCongruent F Q E D P T :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      E Q F
      D P T).mp
      hEQF_DPT

  have hEQZ_TPY :
      Geo.AngleCongruent E Q Z T P Y :=
    bookZero_43_supplements
      Geo
      F Q E E Z
      D P T T Y
      hFQE_DPT
      hSuppEQZ
      hSuppTPY
      hFQE
      hDPT

  have hEQZ_YPT :
      Geo.AngleCongruent E Q Z Y P T :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      E Q Z
      T P Y).mp
      hEQZ_TPY

  have hCyclic :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P Y
        Y P T
        A O B :=
    hilbertTwoAnglesGreaterThanAngle_transport_second
      Geo
      C P Y
      E Q Z
      Y P T
      A O B
      hCompare1
      hYPT
      hEQZ_YPT

  exact
    hilbert_XI23_adjacent_copy_inside_opposite_PD_impossible_of_cyclic_XI
      Geo
      A O B
      C P T Y
      hInsideY
      hCyclic
      hCPT_AOB




------------------------------------------------------------------------
-- XI.23 v68: close the complete DU-inside bad-radius branch
------------------------------------------------------------------------

/--
Complete XI.23 contradiction for the smaller-source-radius branch when
DU is an interior ray of angle CDK.

Starting from OA < UC:

1. construct the adjacent copy T from v53;
2. compare the two base-angle components (v56);
3. use DP and DU as the interior dividers at D (v57-v58);
4. obtain CT < CK (v60-v61);
5. if CPT is degenerate, then CT is the source diameter, contradicting
   CT < CK ~= AB and Euclid I.20 in triangle OAB;
6. otherwise v62 gives CPT < AOB, and the crossing of CT with line PD
   puts either PD or its opposite ray inside CPT.  These are exactly
   the two branches closed by v65 and v67.

No new angle calculus is introduced here; this theorem only assembles
the previously verified XI.23 lemmas.
-/
theorem hilbert_XI23_smaller_radius_inside_D_impossible_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hInsideD :
      HilbertRayMeetsSegment Geo U D C K)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    False := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h12_3.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h12_3.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h12_3.2.2.1

  --------------------------------------------------------------------
  -- Source equal-radius data.
  --------------------------------------------------------------------

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo O A P C hOA_PC

  have hPD_OA :
      Geo.Congruent P D O A :=
    hilbert_congruent_symmetry
      Geo O A P D hOA_PD

  have hPC_PD :
      Geo.Congruent P C P D :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      P D
      hPC_OA
      hOA_PD

  have hPD_QE :
      Geo.Congruent P D Q E :=
    hilbert_congruent_transitivity
      Geo
      P D
      O A
      Q E
      hPD_OA
      hOA_QE

  have hPD_QF :
      Geo.Congruent P D Q F :=
    hilbert_congruent_transitivity
      Geo
      P D
      O A
      Q F
      hPD_OA
      hOA_QF

  have hPC_lt_UC :
      HilbertSegmentLess Geo P C U C :=
    hilbert_segmentLess_congruent_left
      Geo
      O A
      P C
      U C
      hRadiusLess
      hPC_OA

  --------------------------------------------------------------------
  -- Proper central angles are automatic in the smaller-radius branch.
  --------------------------------------------------------------------

  have hProper :=
    hilbert_XI23_central_angles_proper_of_smaller_radius_XI
      Geo
      A O B
      C P D
      E Q F
      K U
      h12_3
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hRadiusLess

  have hCUK :
      Not (PrimCollinear Geo C U K) :=
    hProper.1

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hProper.2.1

  have hDUK :
      Not (PrimCollinear Geo D U K) :=
    hProper.2.2

  --------------------------------------------------------------------
  -- v53: adjacent copy of the third source angle.
  --------------------------------------------------------------------

  rcases
      hilbert_XI23_adjacent_third_angle_chord_witness_XI
        Geo
        C P D
        E Q F
        K
        hCPD
        hEQF
        hPD_QE
        hDK_EF
    with
    ⟨T,
      base,
      hPbase,
      hDbase,
      hOppCT,
      hEQF_DPT,
      hPT_QF,
      hDT_DK⟩

  have hDP :
      Ne D P :=
    (hilbert_noncollinear_ne_first
      Geo P D C
      (by
        intro hcol
        exact hCPD
          (PrimCollinearRotate
            Geo
            C D P
            (PrimCollinearSymm
              Geo P D C hcol)))).symm

  have hDPT :
      Not (PrimCollinear Geo D P T) := by
    intro hcol

    have hTbase :
        HilbertIncidence.OnLine T base :=
      hilbert_collinear_on_line
        Geo
        D P T
        base
        hDP
        hDbase
        hPbase
        hcol

    exact hOppCT.2.1 hTbase

  have hQF_PT :
      Geo.Congruent Q F P T :=
    hilbert_congruent_symmetry
      Geo P T Q F hPT_QF

  have hPD_PT :
      Geo.Congruent P D P T :=
    hilbert_congruent_transitivity
      Geo
      P D
      Q F
      P T
      hPD_QF
      hQF_PT

  have hPC_PT :
      Geo.Congruent P C P T :=
    hilbert_congruent_transitivity
      Geo
      P C
      P D
      P T
      hPC_PD
      hPD_PT

  --------------------------------------------------------------------
  -- v56: both component angles expand at the larger circumradius.
  --------------------------------------------------------------------

  have hExpand :=
    hilbert_XI23_adjacent_copy_base_angles_expand_XI
      Geo
      C P D T U K
      hCPD
      hDPT
      hCUD
      hDUK
      hPC_PD
      hPD_PT
      hUC_UD
      hUC_UK
      hDT_DK
      hPC_lt_UC

  have hLeft :
      HilbertAngleLess Geo C D P C D U :=
    hExpand.1

  have hRight :
      HilbertAngleLess Geo P D T U D K :=
    hExpand.2

  --------------------------------------------------------------------
  -- v57-v58: the two actual interior dividers at D.
  --------------------------------------------------------------------

  have hInsideU :
      HilbertRayMeetsSegment Geo D U C K :=
    hilbert_equalRadius_interiorRay_reverse_XI
      Geo
      U C D K
      hCUK
      hInsideD
      hUC_UD
      hUC_UK

  have hInsideP :
      HilbertRayMeetsSegment Geo D P C T :=
    hilbert_XI23_adjacent_copy_reverse_divider_XI
      Geo
      C P D T
      base
      hPbase
      hDbase
      hOppCT
      hCPD
      hPC_PD
      hPD_PT

  --------------------------------------------------------------------
  -- v60-v61: assemble the two comparisons and obtain CT < CK.
  --------------------------------------------------------------------

  have hCT_CK :
      HilbertSegmentLess Geo C T C K :=
    hilbert_XI23_adjacent_copy_chord_less_XI
      Geo
      C P D T U K
      hInsideP
      hInsideU
      hLeft
      hRight
      hDT_DK

  have hCT_AB :
      HilbertSegmentLess Geo C T A B :=
    hilbert_segmentLess_congruent_right
      Geo
      C T
      C K
      A B
      hCT_CK
      hCK_AB

  --------------------------------------------------------------------
  -- First eliminate the degenerate possibility C,P,T collinear.
  --------------------------------------------------------------------

  by_cases hCPTcol :
      PrimCollinear Geo C P T

  · have hCP :
        Ne C P :=
      hilbert_noncollinear_ne_first
        Geo C P D hCPD

    have hPT :
        Ne P T := by
      intro hPT
      subst T
      exact hOppCT.2.1 hPbase

    have hCT :
        Ne C T := by
      intro hCTeq
      subst T
      rcases hOppCT.2.2 with
        ⟨H, hCHC, _hHbase⟩
      exact
        (HilbertOrder.between_incidence
          C H C hCHC).2.2.1 rfl

    have hCPT :
        Geo.Between C P T := by

      rcases
          hilbert_between_trichotomy
            Geo
            C P T
            hCP
            hPT
            hCT
            hCPTcol
        with
        hCPT | hPCT | hCTP

      · exact hCPT

      · have hPC_PT_less :
            HilbertSegmentLess Geo P C P T :=
          hilbert_segmentLess_of_between
            Geo
            P C T
            hPCT

        exact
          False.elim
            ((hilbert_segmentLess_not_congruent
              Geo
              P C
              P T
              hPC_PT_less)
              hPC_PT)

      · have hPTC :
            Geo.Between P T C :=
          (HilbertOrder.between_incidence
            C T P hCTP).2.2.2.2

        have hPT_PC_less :
            HilbertSegmentLess Geo P T P C :=
          hilbert_segmentLess_of_between
            Geo
            P T C
            hPTC

        exact
          False.elim
            ((hilbert_segmentLess_not_congruent
              Geo
              P T
              P C
              hPT_PC_less)
              (hilbert_congruent_symmetry
                Geo P C P T hPC_PT))

    ------------------------------------------------------------------
    -- I.20 in OAB: AB is shorter than OA + OB.  Because C-P-T and
    -- PC ~= OA, PT ~= OB, that sum is congruent to CT.
    ------------------------------------------------------------------

    have hOAB :
        Not (PrimCollinear Geo O A B) := by
      intro hcol
      exact hAOB
        (PrimCollinearSwap Geo O A B hcol)

    rcases
        euclid_proposition_20
          Geo
          O A B
          hOAB
      with
      ⟨R,
        hAOR,
        hOR_OB,
        hAB_AR⟩

    have hAO_CP :
        Geo.Congruent A O C P :=
      CongruentReverseBoth
        Geo
        O A
        P C
        hOA_PC

    have hOB_OA :
        Geo.Congruent O B O A :=
      hilbert_congruent_symmetry
        Geo O A O B hOA_OB

    have hOB_PC :
        Geo.Congruent O B P C :=
      hilbert_congruent_transitivity
        Geo
        O B
        O A
        P C
        hOB_OA
        hOA_PC

    have hOB_PT :
        Geo.Congruent O B P T :=
      hilbert_congruent_transitivity
        Geo
        O B
        P C
        P T
        hOB_PC
        hPC_PT

    have hOR_PT :
        Geo.Congruent O R P T :=
      hilbert_congruent_transitivity
        Geo
        O R
        O B
        P T
        hOR_OB
        hOB_PT

    have hAR_CT :
        Geo.Congruent A R C T :=
      bookZero_sumOfParts
        Geo
        A O R
        C P T
        hAO_CP
        hOR_PT
        hAOR
        hCPT

    have hAB_CT :
        HilbertSegmentLess Geo A B C T :=
      hilbert_segmentLess_congruent_right
        Geo
        A B
        A R
        C T
        hAB_AR
        hAR_CT

    exact
      (hilbert_segmentLess_asymm
        Geo
        A B
        C T
        hAB_CT)
        hCT_AB

  ·
    ------------------------------------------------------------------
    -- Proper angle CPT.  v62 gives CPT < AOB.
    ------------------------------------------------------------------

    have hCPT :
        Not (PrimCollinear Geo C P T) :=
      hCPTcol

    have hCPT_AOB :
        HilbertAngleLess Geo C P T A O B :=
      hilbert_XI23_adjacent_copy_angle_less_source_XI
        Geo
        A O B
        C P T K
        hAOB
        hCPT
        hPC_PT
        hPC_OA
        hOA_OB
        hCK_AB
        hCT_CK

    ------------------------------------------------------------------
    -- The crossing point H of CT with line PD determines the final
    -- orientation at P.
    ------------------------------------------------------------------

    rcases hOppCT.2.2 with
      ⟨H,
        hCHT,
        hHbase⟩

    have hPH :
        Ne P H := by
      intro hPH
      subst H
      exact
        hCPT
          (HilbertOrder.between_incidence
            C P T hCHT).2.2.2.1

    by_cases hHD : H = D

    · subst H

      have hRayPDD :
          HilbertSameRay Geo P D D :=
        hilbert_sameRay_refl
          Geo P D hDP

      have hInsidePD :
          HilbertRayMeetsSegment Geo P D C T :=
        ⟨D, hCHT, hRayPDD⟩

      exact
        hilbert_XI23_adjacent_copy_inside_PD_impossible_XI
          Geo
          A O B
          C P D
          E Q F
          T
          h23_1
          hDPT
          hInsidePD
          hEQF_DPT
          hCPT_AOB

    · have hDH :
          Ne D H := by
        intro h
        exact hHD h.symm

      have hPD :
          Ne P D :=
        hDP.symm

      have hPDHcol :
          PrimCollinear Geo P D H :=
        ⟨base,
          hPbase,
          hDbase,
          hHbase⟩

      rcases
          hilbert_between_trichotomy
            Geo
            P D H
            hPD
            hDH
            hPH
            hPDHcol
        with
        hPDH | hDPH | hPHD

      · have hRayPDH :
            HilbertSameRay Geo P D H :=
          hilbert_sameRay_of_between
            Geo P D H hPDH

        have hInsidePD :
            HilbertRayMeetsSegment Geo P D C T :=
          ⟨H, hCHT, hRayPDH⟩

        exact
          hilbert_XI23_adjacent_copy_inside_PD_impossible_XI
            Geo
            A O B
            C P D
            E Q F
            T
            h23_1
            hDPT
            hInsidePD
            hEQF_DPT
            hCPT_AOB

      ·
        ----------------------------------------------------------------
        -- D-P-H: H itself is a point on the ray opposite to PD.
        ----------------------------------------------------------------

        have hRayPHH :
            HilbertSameRay Geo P H H :=
          hilbert_sameRay_refl
            Geo P H hPH.symm

        have hInsideH :
            HilbertRayMeetsSegment Geo P H C T :=
          ⟨H, hCHT, hRayPHH⟩

        exact
          hilbert_XI23_adjacent_copy_inside_opposite_PD_impossible_XI
            Geo
            A O B
            C P D
            E Q F
            T H
            hFour
            hDPH
            hEQF_DPT
            hInsideH
            hCPT_AOB

      ·
        ----------------------------------------------------------------
        -- P-H-D: H is on the same ray PD.
        ----------------------------------------------------------------

        have hRayPHD :
            HilbertSameRay Geo P H D :=
          hilbert_sameRay_of_between
            Geo P H D hPHD

        have hRayPDH :
            HilbertSameRay Geo P D H :=
          hilbert_sameRay_symm
            Geo P H D hRayPHD

        have hInsidePD :
            HilbertRayMeetsSegment Geo P D C T :=
          ⟨H, hCHT, hRayPDH⟩

        exact
          hilbert_XI23_adjacent_copy_inside_PD_impossible_XI
            Geo
            A O B
            C P D
            E Q F
            T
            h23_1
            hDPT
            hInsidePD
            hEQF_DPT
            hCPT_AOB




------------------------------------------------------------------------
-- XI.23 v69: close the UC-inside bad-radius branch
------------------------------------------------------------------------

/--
Complete XI.23 contradiction for the smaller-source-radius branch when
UC is an interior ray of angle DUK.

This is the cyclic companion of v68, but it is proved directly from
the already verified XI.23 machinery rather than by introducing a new
abstract symmetry layer.

The auxiliary construction copies angle AOB adjacent to the reversed
source angle DPC.  The resulting triangle DCT is compared with DCK,
giving DT < DK and hence angle DPT < angle EQF.  The crossing of DT
with line PC then has two orientations:

* ray PC is interior to angle DPT: use h12_3;
* the ray opposite PC is interior: use the original <4R certificate.

Both contradict DPT < EQF.
-/
theorem hilbert_XI23_smaller_radius_inside_C_impossible_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hInsideC :
      HilbertRayMeetsSegment Geo U C D K)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    False := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h12_3.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h12_3.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h12_3.2.2.1

  have hDPC :
      Not (PrimCollinear Geo D P C) := by
    intro hcol
    exact hCPD
      (PrimCollinearSymm Geo D P C hcol)

  --------------------------------------------------------------------
  -- Common source-radius data.
  --------------------------------------------------------------------

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo O A P C hOA_PC

  have hPD_OA :
      Geo.Congruent P D O A :=
    hilbert_congruent_symmetry
      Geo O A P D hOA_PD

  have hPD_PC :
      Geo.Congruent P D P C :=
    hilbert_congruent_transitivity
      Geo
      P D
      O A
      P C
      hPD_OA
      hOA_PC

  have hPC_OB :
      Geo.Congruent P C O B :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      O B
      hPC_OA
      hOA_OB

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo O A Q E hOA_QE

  have hQE_QF :
      Geo.Congruent Q E Q F :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      Q F
      hQE_OA
      hOA_QF

  have hPD_QE :
      Geo.Congruent P D Q E :=
    hilbert_congruent_transitivity
      Geo
      P D
      O A
      Q E
      hPD_OA
      hOA_QE

  --------------------------------------------------------------------
  -- Proper central angles in the smaller-radius branch.
  --------------------------------------------------------------------

  have hProper :=
    hilbert_XI23_central_angles_proper_of_smaller_radius_XI
      Geo
      A O B
      C P D
      E Q F
      K U
      h12_3
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hRadiusLess

  have hCUK :
      Not (PrimCollinear Geo C U K) :=
    hProper.1

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hProper.2.1

  have hDUK :
      Not (PrimCollinear Geo D U K) :=
    hProper.2.2

  have hDUC :
      Not (PrimCollinear Geo D U C) := by
    intro hcol
    exact hCUD
      (PrimCollinearSymm Geo D U C hcol)

  --------------------------------------------------------------------
  -- Copy AOB adjacent to DPC along ray PC.
  --------------------------------------------------------------------

  rcases
      hilbert_XI23_adjacent_third_angle_chord_witness_XI
        Geo
        D P C
        A O B
        K
        hDPC
        hAOB
        hPC_OA
        hCK_AB
    with
    ⟨T,
      base,
      hPbase,
      hCbase,
      hOppDT,
      hAOB_CPT,
      hPT_OB,
      hCT_CK⟩

  have hPC :
      Ne P C := by
    exact
      (hilbert_noncollinear_ne_first
        Geo C P D hCPD).symm

  have hCPT :
      Not (PrimCollinear Geo C P T) := by
    intro hcol

    have hTbase :
        HilbertIncidence.OnLine T base :=
      hilbert_collinear_on_line
        Geo
        P C T
        base
        hPC
        hPbase
        hCbase
        (PrimCollinearSwap
          Geo C P T hcol)

    exact hOppDT.2.1 hTbase

  have hOB_PT :
      Geo.Congruent O B P T :=
    hilbert_congruent_symmetry
      Geo P T O B hPT_OB

  have hOA_PT :
      Geo.Congruent O A P T :=
    hilbert_congruent_transitivity
      Geo
      O A
      O B
      P T
      hOA_OB
      hOB_PT

  have hPC_PT :
      Geo.Congruent P C P T :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      P T
      hPC_OA
      hOA_PT

  --------------------------------------------------------------------
  -- Transfer OA < UC to PD < UD, the relabelled v56 radius input.
  --------------------------------------------------------------------

  have hPD_OA' :
      Geo.Congruent P D O A :=
    hPD_OA

  have hPD_UC :
      HilbertSegmentLess Geo P D U C :=
    hilbert_segmentLess_congruent_left
      Geo
      O A
      P D
      U C
      hRadiusLess
      hPD_OA'

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo U C U D hUC_UD

  have hPD_UD :
      HilbertSegmentLess Geo P D U D :=
    hilbert_segmentLess_congruent_right
      Geo
      P D
      U C
      U D
      hPD_UC
      hUC_UD

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      hUD_UC
      hUC_UK

  --------------------------------------------------------------------
  -- v56 with the cyclic relabelling D,C,K.
  --------------------------------------------------------------------

  have hExpand :=
    hilbert_XI23_adjacent_copy_base_angles_expand_XI
      Geo
      D P C T U K
      hDPC
      hCPT
      hDUC
      hCUK
      hPD_PC
      hPC_PT
      hUD_UC
      hUD_UK
      hCT_CK
      hPD_UD

  have hLeft :
      HilbertAngleLess Geo D C P D C U :=
    hExpand.1

  have hRight :
      HilbertAngleLess Geo P C T U C K :=
    hExpand.2

  --------------------------------------------------------------------
  -- The two actual interior dividers at C.
  --------------------------------------------------------------------

  have hInsideU :
      HilbertRayMeetsSegment Geo C U D K :=
    hilbert_equalRadius_interiorRay_reverse_XI
      Geo
      U D C K
      hDUK
      hInsideC
      hUD_UC
      hUD_UK

  have hInsideP :
      HilbertRayMeetsSegment Geo C P D T :=
    hilbert_XI23_adjacent_copy_reverse_divider_XI
      Geo
      D P C T
      base
      hPbase
      hCbase
      hOppDT
      hDPC
      hPD_PC
      hPC_PT

  --------------------------------------------------------------------
  -- Assemble at C: DCT < DCK, hence DT < DK.
  --------------------------------------------------------------------

  have hDT_DK :
      HilbertSegmentLess Geo D T D K :=
    hilbert_XI23_adjacent_copy_chord_less_XI
      Geo
      D P C T U K
      hInsideP
      hInsideU
      hLeft
      hRight
      hCT_CK

  --------------------------------------------------------------------
  -- Degenerate D,P,T: then DT is a source diameter, contradicting
  -- DT < DK ~= EF and I.20 in triangle QEF.
  --------------------------------------------------------------------

  by_cases hDPTcol :
      PrimCollinear Geo D P T

  · have hPD :
        Ne D P :=
      hilbert_noncollinear_ne_first
        Geo D P C hDPC

    have hPT :
        Ne P T := by
      intro hPT
      subst T
      exact hOppDT.2.1 hPbase

    have hDT :
        Ne D T := by
      intro hDT
      subst T
      rcases hOppDT.2.2 with
        ⟨H, hDHD, _hHbase⟩
      exact
        (HilbertOrder.between_incidence
          D H D hDHD).2.2.1 rfl

    have hDPT :
        Geo.Between D P T := by

      rcases
          hilbert_between_trichotomy
            Geo
            D P T
            hPD
            hPT
            hDT
            hDPTcol
        with
        hDPT | hPDT | hDTP

      · exact hDPT

      · have hPD_PT_less :
            HilbertSegmentLess Geo P D P T :=
          hilbert_segmentLess_of_between
            Geo
            P D T
            hPDT

        exact
          False.elim
            ((hilbert_segmentLess_not_congruent
              Geo
              P D
              P T
              hPD_PT_less)
              (hilbert_congruent_transitivity
                Geo
                P D
                P C
                P T
                hPD_PC
                hPC_PT))

      · have hPTD :
            Geo.Between P T D :=
          (HilbertOrder.between_incidence
            D T P hDTP).2.2.2.2

        have hPT_PD_less :
            HilbertSegmentLess Geo P T P D :=
          hilbert_segmentLess_of_between
            Geo
            P T D
            hPTD

        have hPD_PT :
            Geo.Congruent P D P T :=
          hilbert_congruent_transitivity
            Geo
            P D
            P C
            P T
            hPD_PC
            hPC_PT

        exact
          False.elim
            ((hilbert_segmentLess_not_congruent
              Geo
              P T
              P D
              hPT_PD_less)
              (hilbert_congruent_symmetry
                Geo P D P T hPD_PT))

    have hQEF :
        Not (PrimCollinear Geo Q E F) := by
      intro hcol
      exact hEQF
        (PrimCollinearSwap Geo Q E F hcol)

    rcases
        euclid_proposition_20
          Geo
          Q E F
          hQEF
      with
      ⟨R,
        hEQR,
        hQR_QF,
        hEF_ER⟩

    have hQE_PD :
        Geo.Congruent Q E P D :=
      hilbert_congruent_transitivity
        Geo
        Q E
        O A
        P D
        hQE_OA
        hOA_PD

    have hQF_PT :
        Geo.Congruent Q F P T :=
      hilbert_congruent_transitivity
        Geo
        Q F
        O A
        P T
        (hilbert_congruent_symmetry
          Geo O A Q F hOA_QF)
        hOA_PT

    have hQR_PT :
        Geo.Congruent Q R P T :=
      hilbert_congruent_transitivity
        Geo
        Q R
        Q F
        P T
        hQR_QF
        hQF_PT

    have hER_DT :
        Geo.Congruent E R D T :=
      bookZero_sumOfParts
        Geo
        E Q R
        D P T
        (CongruentReverseBoth
          Geo
          Q E
          P D
          hQE_PD)
        hQR_PT
        hEQR
        hDPT

    have hEF_DT :
        HilbertSegmentLess Geo E F D T :=
      hilbert_segmentLess_congruent_right
        Geo
        E F
        E R
        D T
        hEF_ER
        hER_DT

    have hDT_EF :
        HilbertSegmentLess Geo D T E F :=
      hilbert_segmentLess_congruent_right
        Geo
        D T
        D K
        E F
        hDT_DK
        hDK_EF

    exact
      (hilbert_segmentLess_asymm
        Geo
        E F
        D T
        hEF_DT)
        hDT_EF

  ·
    ------------------------------------------------------------------
    -- Proper DPT.  DT < DK ~= EF gives DPT < EQF.
    ------------------------------------------------------------------

    have hDPT :
        Not (PrimCollinear Geo D P T) :=
      hDPTcol

    have hPD_PT :
        Geo.Congruent P D P T :=
      hilbert_congruent_transitivity
        Geo
        P D
        P C
        P T
        hPD_PC
        hPC_PT

    have hDPT_EQF :
        HilbertAngleLess Geo D P T E Q F :=
      hilbert_XI23_adjacent_copy_angle_less_source_XI
        Geo
        E Q F
        D P T K
        hEQF
        hDPT
        hPD_PT
        hPD_QE
        (hilbert_congruent_transitivity
          Geo
          Q E
          O A
          Q F
          hQE_OA
          hOA_QF)
        hDK_EF
        hDT_DK

    have hTPD :
        Not (PrimCollinear Geo T P D) := by
      intro hcol
      exact hDPT
        (PrimCollinearSymm Geo T P D hcol)

    have hDPTrefl :
        Geo.AngleCongruent D P T D P T :=
      Geometry.Geo.angle_congruent_reflexive
        Geo D P T

    have hTPD_DPT :
        Geo.AngleCongruent T P D D P T :=
      (Geometry.Geo.angle_congruent_reverse_first
        Geo
        D P T
        D P T).mp
        hDPTrefl

    have hTPD_EQF :
        HilbertAngleLess Geo T P D E Q F :=
      hilbert_angleLess_transport_left
        Geo
        D P T
        T P D
        E Q F
        hDPT_EQF
        hTPD
        hTPD_DPT

    ------------------------------------------------------------------
    -- The crossing point of DT with line PC determines whether PC or
    -- its opposite ray is the interior divider of TPD.
    ------------------------------------------------------------------

    rcases hOppDT.2.2 with
      ⟨H,
        hDHT,
        hHbase⟩

    have hPH :
        Ne P H := by
      intro hPH
      subst H
      exact
        hDPT
          (HilbertOrder.between_incidence
            D P T hDHT).2.2.2.1

    have hAOB_TPC :
        Geo.AngleCongruent A O B T P C :=
      (Geometry.Geo.angle_congruent_reverse_second
        Geo
        A O B
        C P T).mp
        hAOB_CPT

    have hSumDirect :
        HilbertTwoAnglesGreaterThanAngle
          Geo
          T P C
          C P D
          E Q F :=
      hilbertTwoAnglesGreaterThanAngle_transport_first
        Geo
        A O B
        T P C
        C P D
        E Q F
        h12_3
        (by
          intro hcol
          exact hCPT
            (PrimCollinearSymm Geo T P C hcol))
        hAOB_TPC

    have hDirectFalse :
        HilbertRayMeetsSegment Geo P C T D ->
        False := by
      intro hInsidePC

      have hEQF_TPD :
          HilbertAngleLess Geo E Q F T P D :=
        hilbert_twoAnglesGreaterThanAngle_of_interior_split_gives_whole_greater_XI
          Geo
          T P D C
          E Q F
          hTPD
          hInsidePC
          hSumDirect

      have hCycle :
          HilbertAngleLess Geo T P D T P D :=
        hilbert_angleLess_trans
          Geo
          T P D
          E Q F
          T P D
          hTPD_EQF
          hEQF_TPD

      exact
        (hilbert_angleLess_irrefl
          Geo T P D)
          hCycle

    by_cases hHC : H = C

    · subst H

      have hRayPCC :
          HilbertSameRay Geo P C C :=
        hilbert_sameRay_refl
          Geo P C hPC.symm

      have hInsidePC0 :
          HilbertRayMeetsSegment Geo P C D T :=
        ⟨C, hDHT, hRayPCC⟩

      have hInsidePC :
          HilbertRayMeetsSegment Geo P C T D :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo
          P C D T
          hInsidePC0

      exact hDirectFalse hInsidePC

    · have hCH :
          Ne C H := by
        intro h
        exact hHC h.symm

      have hPCHcol :
          PrimCollinear Geo P C H :=
        ⟨base,
          hPbase,
          hCbase,
          hHbase⟩

      rcases
          hilbert_between_trichotomy
            Geo
            P C H
            hPC
            hCH
            hPH
            hPCHcol
        with
        hPCH | hCPH | hPHC

      ·
        have hRayPCH :
            HilbertSameRay Geo P C H :=
          hilbert_sameRay_of_between
            Geo P C H hPCH

        have hInsidePC0 :
            HilbertRayMeetsSegment Geo P C D T :=
          ⟨H, hDHT, hRayPCH⟩

        have hInsidePC :
            HilbertRayMeetsSegment Geo P C T D :=
          hilbert_angleDecomposition_ray_meets_segment_reverse
            Geo
            P C D T
            hInsidePC0

        exact hDirectFalse hInsidePC

      ·
        ----------------------------------------------------------------
        -- C-P-H: H is on the ray opposite PC.
        --
        -- The original <4R certificate already has exactly the needed
        -- complement order:
        --
        --   supp(AOB) + supp(CPD) > EQF.
        ----------------------------------------------------------------

        have hRayPHH :
            HilbertSameRay Geo P H H :=
          hilbert_sameRay_refl
            Geo P H hPH.symm

        have hInsideH0 :
            HilbertRayMeetsSegment Geo P H D T :=
          ⟨H, hDHT, hRayPHH⟩

        have hInsideH :
            HilbertRayMeetsSegment Geo P H T D :=
          hilbert_angleDecomposition_ray_meets_segment_reverse
            Geo
            P H D T
            hInsideH0

        rcases
            hilbertThreeAnglesLessThanFourRightAngles_elim
              Geo
              A O B
              C P D
              E Q F
              hFour
          with
          ⟨X0, Y0,
            hBOX0,
            hDPY0,
            hCompare0⟩

        ----------------------------------------------------------------
        -- First supplement:
        -- AOX0 ~= TPH.
        ----------------------------------------------------------------

        have hBOA :
            Not (PrimCollinear Geo B O A) := by
          intro hcol
          exact hAOB
            (PrimCollinearSymm Geo B O A hcol)

        have hBOA_CPT :
            Geo.AngleCongruent B O A C P T :=
          (Geometry.Geo.angle_congruent_reverse_first
            Geo
            A O B
            C P T).mp
            hAOB_CPT

        have hOA :
            Ne A O :=
          hilbert_noncollinear_ne_first
            Geo A O B hAOB

        have hPT :
            Ne T P :=
          hilbert_noncollinear_ne_first
            Geo T P C
            (by
              intro hcol
              exact hCPT
                (PrimCollinearSymm Geo T P C hcol))

        have hSuppAX :
            BookZeroSupplement Geo B O A A X0 :=
          ⟨hilbert_sameRay_refl
              Geo O A hOA,
            hBOX0⟩

        have hSuppTH :
            BookZeroSupplement Geo C P T T H :=
          ⟨hilbert_sameRay_refl
              Geo P T hPT,
            hCPH⟩

        have hAOX0_TPH :
            Geo.AngleCongruent A O X0 T P H :=
          bookZero_43_supplements
            Geo
            B O A A X0
            C P T T H
            hBOA_CPT
            hSuppAX
            hSuppTH
            hBOA
            hCPT

        ----------------------------------------------------------------
        -- Second supplement:
        -- CPY0 ~= HPD.
        ----------------------------------------------------------------

        have hDPCrefl :
            Geo.AngleCongruent D P C D P C :=
          Geometry.Geo.angle_congruent_reflexive
            Geo D P C

        have hDPC_CPD :
            Geo.AngleCongruent D P C C P D :=
          (Geometry.Geo.angle_congruent_reverse_first
            Geo
            C P D
            C P D).mp
            (Geometry.Geo.angle_congruent_reflexive
              Geo C P D)

        have hPD :
            Ne D P :=
          hilbert_noncollinear_ne_first
            Geo D P C hDPC

        have hSuppCY0 :
            BookZeroSupplement Geo D P C C Y0 :=
          ⟨hilbert_sameRay_refl
              Geo P C hPC.symm,
            hDPY0⟩

        have hSuppDH :
            BookZeroSupplement Geo C P D D H :=
          ⟨hilbert_sameRay_refl
              Geo P D hPD,
            hCPH⟩

        have hCPY0_DPH :
            Geo.AngleCongruent C P Y0 D P H :=
          bookZero_43_supplements
            Geo
            D P C C Y0
            C P D D H
            hDPC_CPD
            hSuppCY0
            hSuppDH
            hDPC
            hCPD

        have hDPH_HPD :
            Geo.AngleCongruent D P H H P D :=
          (Geometry.Geo.angle_congruent_reverse_second
            Geo
            D P H
            D P H).mp
            (Geometry.Geo.angle_congruent_reflexive
              Geo D P H)

        have hCPY0_HPD :
            Geo.AngleCongruent C P Y0 H P D :=
          Geometry.Geo.angle_congruent_transitivity
            Geo
            C P Y0
            D P H
            H P D
            hCPY0_DPH
            hDPH_HPD

        have hTPH :
            Not (PrimCollinear Geo T P H) :=
          (hilbert_interior_angle_less
            Geo
            P H T D
            hTPD
            hInsideH).1

        have hDPH :
            Not (PrimCollinear Geo D P H) :=
          (hilbert_interior_angle_less
            Geo
            P H D T
            hDPT
            hInsideH0).1

        have hHPD :
            Not (PrimCollinear Geo H P D) := by
          intro hcol
          exact hDPH
            (PrimCollinearSymm Geo H P D hcol)

        have hCompare1 :
            HilbertTwoAnglesGreaterThanAngle
              Geo
              T P H
              C P Y0
              E Q F :=
          hilbertTwoAnglesGreaterThanAngle_transport_first
            Geo
            A O X0
            T P H
            C P Y0
            E Q F
            hCompare0
            hTPH
            hAOX0_TPH

        have hCompare2 :
            HilbertTwoAnglesGreaterThanAngle
              Geo
              T P H
              H P D
              E Q F :=
          hilbertTwoAnglesGreaterThanAngle_transport_second
            Geo
            T P H
            C P Y0
            H P D
            E Q F
            hCompare1
            hHPD
            hCPY0_HPD

        exact
          hilbert_XI23_adjacent_copy_inside_opposite_PD_impossible_of_cyclic_XI
            Geo
            E Q F
            T P D H
            hInsideH
            hCompare2
            hTPD_EQF

      ·
        have hRayPHC :
            HilbertSameRay Geo P H C :=
          hilbert_sameRay_of_between
            Geo P H C hPHC

        have hRayPCH :
            HilbertSameRay Geo P C H :=
          hilbert_sameRay_symm
            Geo P H C hRayPHC

        have hInsidePC0 :
            HilbertRayMeetsSegment Geo P C D T :=
          ⟨H, hDHT, hRayPCH⟩

        have hInsidePC :
            HilbertRayMeetsSegment Geo P C T D :=
          hilbert_angleDecomposition_ray_meets_segment_reverse
            Geo
            P C D T
            hInsidePC0

        exact hDirectFalse hInsidePC


------------------------------------------------------------------------
-- XI.23 v70: close the UK-inside bad-radius branch
------------------------------------------------------------------------

/--
Complete XI.23 contradiction for the smaller-source-radius branch when
UK is an interior ray of angle CUD.

This is the asymmetric third outside-circumcenter branch.  Unlike the
C- and D-branches, K is not one of the original endpoints of the
second source angle, so the proof first creates at Q an adjacent copy
of angle AOB next to EQF.

The construction gives a point T such that

    QE ~= QF ~= QT,
    angle FQT ~= AOB,
    FT ~= AB ~= CK.

Because UK meets CD, equal-radius reversal gives KU as an interior
divider of angle DKC.  The opposite-side construction gives FQ as an
interior divider of angle EFT.

The smaller source radius then gives the two base-angle comparisons

    angle QFE < angle UKD,
    angle QFT < angle UKC.

Strict addition yields

    angle EFT < angle DKC,

and Euclid I.24 gives

    ET < DC.

If Q,E,T are collinear, ET is a source diameter and I.20 in triangle
PCD contradicts ET < DC.

Otherwise the equal-radius chord converse gives

    angle EQT < angle CPD.

Finally the crossing of ET with line QF has two orientations.

* If ray QF meets ET, the cyclic XI.20 inequality

      EQF + AOB > CPD

  contradicts angle EQT < angle CPD.

* If the opposite ray meets ET, the cyclic four-right-angle certificate
  gives the contradiction exactly as in the previous XI.23 branches.
-/
theorem hilbert_XI23_smaller_radius_inside_K_impossible_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hInsideK :
      HilbertRayMeetsSegment Geo U K C D)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    False := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h12_3.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h12_3.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h12_3.2.2.1

  have hQF_OA :
      Geo.Congruent Q F O A :=
    hilbert_congruent_symmetry
      Geo O A Q F hOA_QF

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo O A Q E hOA_QE

  have hQF_QE :
      Geo.Congruent Q F Q E :=
    hilbert_congruent_transitivity
      Geo Q F O A Q E
      hQF_OA hOA_QE

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo O A P C hOA_PC

  have hPD_OA :
      Geo.Congruent P D O A :=
    hilbert_congruent_symmetry
      Geo O A P D hOA_PD

  have hQFE :
      Not (PrimCollinear Geo Q F E) := by
    intro hcol
    have hFQE :
        PrimCollinear Geo F Q E :=
      PrimCollinearSwap Geo Q F E hcol
    exact
      hEQF
        (PrimCollinearSymm Geo F Q E hFQE)

  have hQF :
      Ne Q F :=
    hilbert_noncollinear_ne_first
      Geo Q F E hQFE

  have hFEQ :
      Not (PrimCollinear Geo F E Q) := by
    intro hcol
    have hQEF :
        PrimCollinear Geo Q E F :=
      PrimCollinearSymm Geo F E Q hcol
    exact
      hEQF
        (PrimCollinearSwap Geo Q E F hQEF)

  have hFE :
      Ne F E :=
    hilbert_noncollinear_ne_first
      Geo F E Q hFEQ

  have hABO :
      Not (PrimCollinear Geo A B O) := by
    intro hcol
    have hBAO :
        PrimCollinear Geo B A O :=
      PrimCollinearSwap Geo A B O hcol
    have hOAB0 :
        PrimCollinear Geo O A B :=
      PrimCollinearSymm Geo B A O hBAO
    exact
      hAOB
        (PrimCollinearSwap Geo O A B hOAB0)

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B O hABO

  rcases
      bookZero_49_layoff
        Geo
        F E
        A B
        hFE
        hAB
    with
    ⟨W, hRayFEW, hFW_AB⟩

  rcases
      hilbert_XI23_adjacent_third_angle_chord_witness_XI
        Geo
        E Q F
        A O B
        W
        hEQF
        hAOB
        hQF_OA
        hFW_AB
    with
    ⟨T,
      base,
      hQbase,
      hFbase,
      hOppET,
      hAOB_FQT,
      hQT_OB,
      hFT_FW⟩

  have hFT_AB :
      Geo.Congruent F T A B :=
    hilbert_congruent_transitivity
      Geo F T F W A B
      hFT_FW hFW_AB

  have hAB_CK :
      Geo.Congruent A B C K :=
    hilbert_congruent_symmetry
      Geo C K A B hCK_AB

  have hFT_CK :
      Geo.Congruent F T C K :=
    hilbert_congruent_transitivity
      Geo F T A B C K
      hFT_AB hAB_CK

  have hOB_QT :
      Geo.Congruent O B Q T :=
    hilbert_congruent_symmetry
      Geo Q T O B hQT_OB

  have hQF_OB :
      Geo.Congruent Q F O B :=
    hilbert_congruent_transitivity
      Geo Q F O A O B
      hQF_OA hOA_OB

  have hQF_QT :
      Geo.Congruent Q F Q T :=
    hilbert_congruent_transitivity
      Geo Q F O B Q T
      hQF_OB hOB_QT

  have hQE_QT :
      Geo.Congruent Q E Q T :=
    hilbert_congruent_transitivity
      Geo Q E Q F Q T
      (hilbert_congruent_symmetry
        Geo Q F Q E hQF_QE)
      hQF_QT

  have hProper :=
    hilbert_XI23_central_angles_proper_of_smaller_radius_XI
      Geo
      A O B
      C P D
      E Q F
      K U
      h12_3
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hRadiusLess

  have hCUK :
      Not (PrimCollinear Geo C U K) :=
    hProper.1

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hProper.2.1

  have hDUK :
      Not (PrimCollinear Geo D U K) :=
    hProper.2.2

  have hUKD :
      Not (PrimCollinear Geo U K D) := by
    intro hcol
    have hKUD :
        PrimCollinear Geo K U D :=
      PrimCollinearSwap Geo U K D hcol
    exact
      hDUK
        (PrimCollinearSymm Geo K U D hKUD)

  have hUKC :
      Not (PrimCollinear Geo U K C) := by
    intro hcol
    have hKUC :
        PrimCollinear Geo K U C :=
      PrimCollinearSwap Geo U K C hcol
    exact
      hCUK
        (PrimCollinearSymm Geo K U C hKUC)

  have hUK_UC :
      Geo.Congruent U K U C :=
    hilbert_congruent_symmetry
      Geo U C U K hUC_UK

  have hUK_UD :
      Geo.Congruent U K U D :=
    hilbert_congruent_transitivity
      Geo U K U C U D
      hUK_UC hUC_UD

  have hQF_lt_UC :
      HilbertSegmentLess Geo Q F U C :=
    hilbert_segmentLess_congruent_left
      Geo
      O A
      Q F
      U C
      hRadiusLess
      hQF_OA

  have hQF_lt_UK :
      HilbertSegmentLess Geo Q F U K :=
    hilbert_segmentLess_congruent_right
      Geo
      Q F
      U C
      U K
      hQF_lt_UC
      hUC_UK

  have hToff :
      Not (HilbertIncidence.OnLine T base) :=
    hOppET.2.1

  have hQFT :
      Not (PrimCollinear Geo Q F T) :=
    hilbert_not_collinear_of_off_line
      Geo
      Q F T
      base
      hQF
      hQbase
      hFbase
      hToff

  have hEF_DK :
      Geo.Congruent E F D K :=
    hilbert_congruent_symmetry
      Geo D K E F hDK_EF

  have hFE_KD :
      Geo.Congruent F E K D :=
    CongruentReverseBoth
      Geo
      E F
      D K
      hEF_DK

  have hFT_KC :
      Geo.Congruent F T K C :=
    CongruentSwapSecond
      Geo
      F T
      C K
      hFT_CK

  have hFirstBase :
      HilbertAngleLess Geo Q F E U K D :=
    hilbert_isosceles_base_angle_less_of_smaller_equal_sides_XI
      Geo
      Q F E
      U K D
      hQFE
      hUKD
      hQF_QE
      hUK_UD
      hFE_KD
      hQF_lt_UK

  have hSecondBase :
      HilbertAngleLess Geo Q F T U K C :=
    hilbert_isosceles_base_angle_less_of_smaller_equal_sides_XI
      Geo
      Q F T
      U K C
      hQFT
      hUKC
      hQF_QT
      hUK_UC
      hFT_KC
      hQF_lt_UK

  have hInsideKU0 :
      HilbertRayMeetsSegment Geo K U C D :=
    hilbert_equalRadius_interiorRay_reverse_XI
      Geo
      U C K D
      hCUD
      hInsideK
      hUC_UK
      hUC_UD

  have hInsideKU :
      HilbertRayMeetsSegment Geo K U D C :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      K U C D
      hInsideKU0

  have hInsideFQ :
      HilbertRayMeetsSegment Geo F Q E T :=
    hilbert_equalRadius_oppositeSides_reverse_divider_XI
      Geo
      Q E F T
      base
      hQbase
      hFbase
      hOppET
      hEQF
      (hilbert_congruent_symmetry
        Geo Q F Q E hQF_QE)
      hQE_QT

  have hEFQ_QFE :
      Geo.AngleCongruent E F Q Q F E :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      Q F E
      Q F E).mp
      (Geometry.Geo.angle_congruent_reflexive
        Geo Q F E)

  have hDKU_UKD :
      Geo.AngleCongruent D K U U K D :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      U K D
      U K D).mp
      (Geometry.Geo.angle_congruent_reflexive
        Geo U K D)

  have hUKD_DKU :
      Geo.AngleCongruent U K D D K U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      D K U
      U K D
      hDKU_UKD

  have hEFQ_UKD :
      HilbertAngleLess Geo E F Q U K D :=
    hilbert_angleLess_transport_left
      Geo
      Q F E
      E F Q
      U K D
      hFirstBase
      (by
        intro h
        exact hQFE
          (PrimCollinearSymm Geo E F Q h))
      hEFQ_QFE

  have hEFQ_DKU :
      HilbertAngleLess Geo E F Q D K U :=
    hilbert_angleLess_transport_right
      Geo
      E F Q
      U K D
      D K U
      hEFQ_UKD
      (by
        intro h
        exact hUKD
          (PrimCollinearSymm Geo D K U h))
      hUKD_DKU

  have hTFQ_QFT :
      Geo.AngleCongruent T F Q Q F T :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      Q F T
      Q F T).mp
      (Geometry.Geo.angle_congruent_reflexive
        Geo Q F T)

  have hCKU_UKC :
      Geo.AngleCongruent C K U U K C :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      U K C
      U K C).mp
      (Geometry.Geo.angle_congruent_reflexive
        Geo U K C)

  have hUKC_CKU :
      Geo.AngleCongruent U K C C K U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      C K U
      U K C
      hCKU_UKC

  have hTFQ_UKC :
      HilbertAngleLess Geo T F Q U K C :=
    hilbert_angleLess_transport_left
      Geo
      Q F T
      T F Q
      U K C
      hSecondBase
      (by
        intro h
        exact hQFT
          (PrimCollinearSymm Geo T F Q h))
      hTFQ_QFT

  have hTFQ_CKU :
      HilbertAngleLess Geo T F Q C K U :=
    hilbert_angleLess_transport_right
      Geo
      T F Q
      U K C
      C K U
      hTFQ_UKC
      (by
        intro h
        exact hUKC
          (PrimCollinearSymm Geo C K U h))
      hUKC_CKU

  have hEFT_DKC :
      HilbertAngleLess Geo E F T D K C :=
    hilbert_angleDecomposition_componentwise_less_whole_XI
      Geo
      F E T Q
      K D C U
      (hilbert_angleDecomposition_whole_noncollinear_of_left_XI
        Geo
        F E T Q
        hInsideFQ
        hEFQ_DKU.1)
      (hilbert_angleDecomposition_whole_noncollinear_of_left_XI
        Geo
        K D C U
        hInsideKU
        hEFQ_DKU.2.1)
      hInsideFQ
      hInsideKU
      hEFQ_DKU
      hTFQ_CKU

  have hFET :
      Not (PrimCollinear Geo F E T) := by
    intro h
    exact
      hEFT_DKC.1
        (PrimCollinearSwap Geo F E T h)

  have hKDC :
      Not (PrimCollinear Geo K D C) := by
    intro hKDCcol
    exact
      hEFT_DKC.2.1
        (PrimCollinearSwap
          Geo K D C hKDCcol)

  have hKD_FE :
      Geo.Congruent K D F E :=
    hilbert_congruent_symmetry
      Geo F E K D hFE_KD

  have hKC_FT :
      Geo.Congruent K C F T :=
    hilbert_congruent_symmetry
      Geo F T K C hFT_KC

  have hET_DC :
      HilbertSegmentLess Geo E T D C :=
    euclid_proposition_24
      (Geo := Geo)
      K D C
      F E T
      hKDC
      hFET
      hKD_FE
      hKC_FT
      hEFT_DKC

  have hDC_CD :
      Geo.Congruent D C C D :=
    CongruentSwapSecond
      Geo
      D C
      D C
      (hilbert_congruent_reflexive
        Geo D C)

  have hET_CD :
      HilbertSegmentLess Geo E T C D :=
    hilbert_segmentLess_congruent_right
      Geo
      E T
      D C
      C D
      hET_DC
      hDC_CD

  by_cases hQETcol :
      PrimCollinear Geo Q E T

  ·
    have hET :
        Ne E T := by
      rcases hOppET.2.2 with
        ⟨H, hEHT, _hHbase⟩
      exact
        (HilbertOrder.between_incidence
          E H T hEHT).2.2.1

    have hQE :
        Ne Q E := by
      intro h
      subst E
      exact hOppET.1 hQbase

    have hQT :
        Ne Q T := by
      intro h
      subst T
      exact hOppET.2.1 hQbase

    have hEQTcol :
        PrimCollinear Geo E Q T :=
      PrimCollinearSwap Geo Q E T hQETcol

    have hEQT :
        Geo.Between E Q T := by

      rcases
          hilbert_between_trichotomy
            Geo
            E Q T
            hQE.symm
            hQT
            hET
            hEQTcol
        with
        hEQT | hQET | hETQ

      · exact hEQT

      ·
        have hQE_QT_less :
            HilbertSegmentLess Geo Q E Q T :=
          hilbert_segmentLess_of_between
            Geo Q E T hQET

        exact
          False.elim
            ((hilbert_segmentLess_not_congruent
              Geo
              Q E
              Q T
              hQE_QT_less)
              hQE_QT)

      ·
        have hQTE :
            Geo.Between Q T E :=
          (HilbertOrder.between_incidence
            E T Q hETQ).2.2.2.2

        have hQT_QE_less :
            HilbertSegmentLess Geo Q T Q E :=
          hilbert_segmentLess_of_between
            Geo Q T E hQTE

        exact
          False.elim
            ((hilbert_segmentLess_not_congruent
              Geo
              Q T
              Q E
              hQT_QE_less)
              (hilbert_congruent_symmetry
                Geo Q E Q T hQE_QT))

    have hPCD0 :
        Not (PrimCollinear Geo P C D) := by
      intro h
      exact hCPD
        (PrimCollinearSwap Geo P C D h)

    rcases
        euclid_proposition_20
          Geo
          P C D
          hPCD0
      with
      ⟨R,
        hCPR,
        hPR_PD,
        hCD_CR⟩

    have hPC_QE :
        Geo.Congruent P C Q E :=
      hilbert_congruent_transitivity
        Geo
        P C
        O A
        Q E
        hPC_OA
        hOA_QE

    have hCP_EQ :
        Geo.Congruent C P E Q :=
      CongruentReverseBoth
        Geo
        P C
        Q E
        hPC_QE

    have hOA_QT :
        Geo.Congruent O A Q T :=
      hilbert_congruent_transitivity
        Geo
        O A
        O B
        Q T
        hOA_OB
        hOB_QT

    have hPD_QT :
        Geo.Congruent P D Q T :=
      hilbert_congruent_transitivity
        Geo
        P D
        O A
        Q T
        hPD_OA
        hOA_QT

    have hPR_QT :
        Geo.Congruent P R Q T :=
      hilbert_congruent_transitivity
        Geo
        P R
        P D
        Q T
        hPR_PD
        hPD_QT

    have hCR_ET :
        Geo.Congruent C R E T :=
      bookZero_sumOfParts
        Geo
        C P R
        E Q T
        hCP_EQ
        hPR_QT
        hCPR
        hEQT

    have hCD_ET :
        HilbertSegmentLess Geo C D E T :=
      hilbert_segmentLess_congruent_right
        Geo
        C D
        C R
        E T
        hCD_CR
        hCR_ET

    exact
      (hilbert_segmentLess_asymm
        Geo
        E T
        C D
        hET_CD)
        hCD_ET

  ·
    have hEQTproper :
        Not (PrimCollinear Geo E Q T) := by
      intro h
      exact
        hQETcol
          (PrimCollinearSwap Geo E Q T h)

    have hQE_PC :
        Geo.Congruent Q E P C :=
      hilbert_congruent_transitivity
        Geo
        Q E
        O A
        P C
        hQE_OA
        hOA_PC

    have hQT_OB' :
        Geo.Congruent Q T O B :=
      hQT_OB

    have hOB_OA :
        Geo.Congruent O B O A :=
      hilbert_congruent_symmetry
        Geo O A O B hOA_OB

    have hOB_PD :
        Geo.Congruent O B P D :=
      hilbert_congruent_transitivity
        Geo
        O B
        O A
        P D
        hOB_OA
        hOA_PD

    have hQT_PD :
        Geo.Congruent Q T P D :=
      hilbert_congruent_transitivity
        Geo
        Q T
        O B
        P D
        hQT_OB'
        hOB_PD

    have hEQT_CPD :
        HilbertAngleLess Geo E Q T C P D :=
      hilbert_equalRadiusChord_angleLess_of_chordLess_XI
        Geo
        Q E T
        P C D
        hEQTproper
        hCPD
        hQE_PC
        hQT_PD
        hET_CD

    rcases hOppET.2.2 with
      ⟨H,
        hEHT,
        hHbase⟩

    have hQH :
        Ne Q H := by
      intro h
      subst H
      exact
        hEQTproper
          (HilbertOrder.between_incidence
            E Q T hEHT).2.2.2.1

    have hFQT :
        Not (PrimCollinear Geo F Q T) := by
      intro h
      exact
        hQFT
          (PrimCollinearSwap Geo F Q T h)

    by_cases hHF : H = F

    ·
      subst H

      have hRayQFF :
          HilbertSameRay Geo Q F F :=
        hilbert_sameRay_refl
          Geo Q F hQF.symm

      have hInsideQF :
          HilbertRayMeetsSegment Geo Q F E T :=
        ⟨F, hEHT, hRayQFF⟩

      exact
        hilbert_XI23_adjacent_copy_inside_PD_impossible_XI
          Geo
          C P D
          E Q F
          A O B
          T
          h31_2
          hFQT
          hInsideQF
          hAOB_FQT
          hEQT_CPD

    ·
      have hFH :
          Ne F H := by
        intro h
        exact hHF h.symm

      have hQFHcol :
          PrimCollinear Geo Q F H :=
        ⟨base,
          hQbase,
          hFbase,
          hHbase⟩

      rcases
          hilbert_between_trichotomy
            Geo
            Q F H
            hQF
            hFH
            hQH
            hQFHcol
        with
        hQFH | hFQH | hQHF

      ·
        have hRayQFH :
            HilbertSameRay Geo Q F H :=
          hilbert_sameRay_of_between
            Geo Q F H hQFH

        have hInsideQF :
            HilbertRayMeetsSegment Geo Q F E T :=
          ⟨H, hEHT, hRayQFH⟩

        exact
          hilbert_XI23_adjacent_copy_inside_PD_impossible_XI
            Geo
            C P D
            E Q F
            A O B
            T
            h31_2
            hFQT
            hInsideQF
            hAOB_FQT
            hEQT_CPD

      ·
        have hRayQHH :
            HilbertSameRay Geo Q H H :=
          hilbert_sameRay_refl
            Geo Q H hQH.symm

        have hInsideH :
            HilbertRayMeetsSegment Geo Q H E T :=
          ⟨H, hEHT, hRayQHH⟩

        have hFourCyclic :
            HilbertThreeAnglesLessThanFourRightAngles
              Geo
              C P D
              E Q F
              A O B :=
          hilbertThreeAnglesLessThanFourRightAngles_cycle
            Geo
            A O B
            C P D
            E Q F
            hFour

        exact
          hilbert_XI23_adjacent_copy_inside_opposite_PD_impossible_XI
            Geo
            C P D
            E Q F
            A O B
            T H
            hFourCyclic
            hFQH
            hAOB_FQT
            hInsideH
            hEQT_CPD

      ·
        have hRayQHF :
            HilbertSameRay Geo Q H F :=
          hilbert_sameRay_of_between
            Geo Q H F hQHF

        have hRayQFH :
            HilbertSameRay Geo Q F H :=
          hilbert_sameRay_symm
            Geo Q H F hRayQHF

        have hInsideQF :
            HilbertRayMeetsSegment Geo Q F E T :=
          ⟨H, hEHT, hRayQFH⟩

        exact
          hilbert_XI23_adjacent_copy_inside_PD_impossible_XI
            Geo
            C P D
            E Q F
            A O B
            T
            h31_2
            hFQT
            hInsideQF
            hAOB_FQT
            hEQT_CPD


------------------------------------------------------------------------
-- XI.23: complete three-ray order split
------------------------------------------------------------------------

/--
Order classification for three proper rays with common vertex.

For three pairwise noncollinear rays UC, UD, UK, one of the following
holds:

1. UC meets the open segment DK;
2. UD meets the open segment CK;
3. UK meets the open segment CD;
4. there is H with D-U-H and C-H-K.

The fourth case is the cyclic/full-turn case: the ray UH opposite to
UD crosses the chord CK.

This is a purely planar order theorem. It contains no metric input.
-/
theorem hilbert_three_rays_order_or_cyclic_XI
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (U C D K : Geo.Point)
    (hCUD : Not (PrimCollinear Geo C U D))
    (hDUK : Not (PrimCollinear Geo D U K))
    (hCUK : Not (PrimCollinear Geo C U K)) :
    HilbertRayMeetsSegment Geo U C D K \/
    HilbertRayMeetsSegment Geo U D C K \/
    HilbertRayMeetsSegment Geo U K C D \/
    exists H : Geo.Point,
      Geo.Between D U H /\
      Geo.Between C H K := by

  have hUDC :
      Not (PrimCollinear Geo U D C) := by
    intro h
    exact
      hCUD
        (PrimCollinearCycle
          Geo
          D C U
          (PrimCollinearCycle
            Geo U D C h))

  have hUD :
      Ne U D :=
    hilbert_noncollinear_ne_first
      Geo U D C hUDC

  cases
      HilbertPlaneIncidence.line_through
        U D hUD
  with
  | intro lineUD hLineUD =>

      have hUline :
          HilbertIncidence.OnLine U lineUD :=
        hLineUD.1

      have hDline :
          HilbertIncidence.OnLine D lineUD :=
        hLineUD.2

      have hCoff :
          Not (HilbertIncidence.OnLine C lineUD) := by
        intro hCline
        exact
          hCUD
            (Exists.intro lineUD
              (And.intro hCline
                (And.intro hUline hDline)))

      have hKoff :
          Not (HilbertIncidence.OnLine K lineUD) := by
        intro hKline
        exact
          hDUK
            (Exists.intro lineUD
              (And.intro hDline
                (And.intro hUline hKline)))

      by_cases hSame :
          HilbertSameSide Geo C K lineUD

      case pos =>
        have hOrder :=
          hilbert_sameSide_rays_order
            Geo
            U C D K
            lineUD
            hUD
            hUline
            hDline
            hCoff
            hKoff
            hSame
            hCUK

        cases hOrder with
        | inl hInsideC =>
            have hInsideC' :
                HilbertRayMeetsSegment Geo U C D K :=
              hilbert_angleDecomposition_ray_meets_segment_reverse
                Geo
                U C K D
                hInsideC

            exact Or.inl hInsideC'

        | inr hInsideK =>
            exact
              Or.inr
                (Or.inr
                  (Or.inl hInsideK))

      case neg =>
        have hOpp :
            HilbertOppositeSide Geo C K lineUD :=
          hilbert_order_oppositeSide_of_not_sameSide
            Geo
            C K
            lineUD
            hCoff
            hKoff
            hSame

        cases hOpp.2.2 with
        | intro H hData =>

            have hCHK :
                Geo.Between C H K :=
              hData.1

            have hHline :
                HilbertIncidence.OnLine H lineUD :=
              hData.2

            have hHU :
                Ne H U := by
              intro hHU
              subst H
              exact
                hCUK
                  (HilbertOrder.between_incidence
                    C U K hCHK).2.2.2.1

            by_cases hHD :
                H = D

            case pos =>
              subst H

              have hRayUDD :
                  HilbertSameRay Geo U D D :=
                hilbert_sameRay_refl
                  Geo U D hUD.symm

              exact
                Or.inr
                  (Or.inl
                    (Exists.intro D
                      (And.intro hCHK hRayUDD)))

            case neg =>
              have hDH :
                  Ne D H := by
                intro h
                exact hHD h.symm

              have hUH :
                  Ne U H :=
                hHU.symm

              have hUDH :
                  PrimCollinear Geo U D H :=
                Exists.intro lineUD
                  (And.intro hUline
                    (And.intro hDline hHline))

              have hBetween :=
                hilbert_between_trichotomy
                  Geo
                  U D H
                  hUD
                  hDH
                  hUH
                  hUDH

              cases hBetween with
              | inl hUDHbet =>
                  have hRayUDH :
                      HilbertSameRay Geo U D H :=
                    hilbert_sameRay_of_between
                      Geo U D H hUDHbet

                  exact
                    Or.inr
                      (Or.inl
                        (Exists.intro H
                          (And.intro hCHK hRayUDH)))

              | inr hRest =>
                  cases hRest with
                  | inl hDUH =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr
                              (Exists.intro H
                                (And.intro hDUH hCHK))))

                  | inr hUHD =>
                      have hRayUHD :
                          HilbertSameRay Geo U H D :=
                        hilbert_sameRay_of_between
                          Geo U H D hUHD

                      have hRayUDH :
                          HilbertSameRay Geo U D H :=
                        hilbert_sameRay_symm
                          Geo U H D hRayUHD

                      exact
                        Or.inr
                          (Or.inl
                            (Exists.intro H
                              (And.intro hCHK hRayUDH)))

------------------------------------------------------------------------
-- XI.23: cyclic bad-radius branch
------------------------------------------------------------------------

/--
The fourth branch of `hilbert_three_rays_order_or_cyclic_XI` is
impossible when the source radius OA is strictly smaller than the
circumradius UC.

The cyclic witness consists of

    D - U - H
    C - H - K.

Thus UH is the ray opposite UD and meets the open chord CK.

From OA < UC the three central angles are strictly smaller than the
corresponding source angles:

    CUK < AOB,
    CUD < CPD,
    DUK < EQF.

Cycle the four-right-angle certificate once.  It supplies source
supplements CPY and EQZ satisfying

    CPY + EQZ > AOB.

Supplement order reversal gives

    CPY < CUH,
    EQZ < KUH.

The three defining cases of `HilbertTwoAnglesGreaterThanAngle` now all
force AOB < CUK.  This contradicts CUK < AOB.
-/
theorem hilbert_XI23_smaller_radius_cyclic_impossible_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F U K H : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hDUH : Geo.Between D U H)
    (hCHK : Geo.Between C H K)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    False := by

  --------------------------------------------------------------------
  -- The three strict central/source comparisons.
  --------------------------------------------------------------------

  have hCentralLess :=
    hilbert_XI23_three_central_angles_less_of_smaller_radius_auto_XI
      Geo
      A O B
      C P D
      E Q F
      K U
      h12_3
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hRadiusLess

  have hCUK_AOB :
      HilbertAngleLess Geo C U K A O B :=
    hCentralLess.1

  have hCUD_CPD :
      HilbertAngleLess Geo C U D C P D :=
    hCentralLess.2.1

  have hDUK_EQF :
      HilbertAngleLess Geo D U K E Q F :=
    hCentralLess.2.2

  have hCUK :
      Not (PrimCollinear Geo C U K) :=
    hCUK_AOB.1

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hCUD_CPD.1

  have hDUK :
      Not (PrimCollinear Geo D U K) :=
    hDUK_EQF.1

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    hCUK_AOB.2.1

  --------------------------------------------------------------------
  -- UH is the opposite ray to UD and crosses the open chord CK.
  --------------------------------------------------------------------

  have hDUHdata :=
    HilbertOrder.between_incidence
      D U H hDUH

  have hUH :
      Ne U H :=
    hDUHdata.2.1

  have hRayUHH :
      HilbertSameRay Geo U H H :=
    hilbert_sameRay_refl
      Geo U H hUH.symm

  have hInsideH :
      HilbertRayMeetsSegment Geo U H C K :=
    ⟨H, hCHK, hRayUHH⟩

  have hCUH_CUK :
      HilbertAngleLess Geo C U H C U K :=
    hilbert_interior_angle_less
      Geo
      U H C K
      hCUK
      hInsideH

  have hCUH :
      Not (PrimCollinear Geo C U H) :=
    hCUH_CUK.1

  have hKUH :
      Not (PrimCollinear Geo K U H) := by
    have hInsideHrev :
        HilbertRayMeetsSegment Geo U H K C :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo U H C K hInsideH

    have hKUC :
        Not (PrimCollinear Geo K U C) := by
      intro hcol
      exact
        hCUK
          (PrimCollinearSymm
            Geo K U C hcol)

    exact
      (hilbert_interior_angle_less
        Geo
        U H K C
        hKUC
        hInsideHrev).1

  --------------------------------------------------------------------
  -- Cycle hFour:
  --
  --   supplement(CPD) + supplement(EQF) > AOB.
  --------------------------------------------------------------------

  have hFourCyclic :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        C P D
        E Q F
        A O B :=
    hilbertThreeAnglesLessThanFourRightAngles_cycle
      Geo
      A O B
      C P D
      E Q F
      hFour

  rcases
      hilbertThreeAnglesLessThanFourRightAngles_elim
        Geo
        C P D
        E Q F
        A O B
        hFourCyclic
    with
    ⟨Y, Z,
      hDPY,
      hFQZ,
      hCompare⟩

  --------------------------------------------------------------------
  -- First supplement:
  --
  --   CUD < CPD
  --   D-U-H, D-P-Y
  --   ----------------
  --   CPY < CUH.
  --------------------------------------------------------------------

  have hCPY_CUH :
      HilbertAngleLess Geo C P Y C U H :=
    hilbert_angleLess_supplements_reverse
      Geo
      C U D
      C P D
      H Y
      hCUD_CPD
      hDUH
      hDPY

  --------------------------------------------------------------------
  -- Second supplement:
  --
  -- Reverse DUK to KUD, then use D-U-H and F-Q-Z:
  --
  --   KUD < EQF
  --   ----------------
  --   EQZ < KUH.
  --------------------------------------------------------------------

  have hDUKrefl :
      Geo.AngleCongruent D U K D U K :=
    Geometry.Geo.angle_congruent_reflexive
      Geo D U K

  have hKUD_DUK :
      Geo.AngleCongruent K U D D U K :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      D U K
      D U K).mp
      hDUKrefl

  have hKUD :
      Not (PrimCollinear Geo K U D) := by
    intro hcol
    exact
      hDUK
        (PrimCollinearSymm
          Geo K U D hcol)

  have hKUD_EQF :
      HilbertAngleLess Geo K U D E Q F :=
    hilbert_angleLess_transport_left
      Geo
      D U K
      K U D
      E Q F
      hDUK_EQF
      hKUD
      hKUD_DUK

  have hEQZ_KUH :
      HilbertAngleLess Geo E Q Z K U H :=
    hilbert_angleLess_supplements_reverse
      Geo
      K U D
      E Q F
      H Z
      hKUD_EQF
      hDUH
      hFQZ

  --------------------------------------------------------------------
  -- Analyze the synthetic sum certificate.
  --------------------------------------------------------------------

  rcases hCompare with
    ⟨hCPY,
      hEQZ,
      _hAOB0,
      hCore⟩

  rcases hCore with
    hAOB_CPY | hRest

  --------------------------------------------------------------------
  -- Case 1: AOB < CPY.
  --------------------------------------------------------------------

  · have hAOB_CUH :
        HilbertAngleLess Geo A O B C U H :=
      hilbert_angleLess_trans
        Geo
        A O B
        C P Y
        C U H
        hAOB_CPY
        hCPY_CUH

    have hAOB_CUK :
        HilbertAngleLess Geo A O B C U K :=
      hilbert_angleLess_trans
        Geo
        A O B
        C U H
        C U K
        hAOB_CUH
        hCUH_CUK

    have hCycle :
        HilbertAngleLess Geo C U K C U K :=
      hilbert_angleLess_trans
        Geo
        C U K
        A O B
        C U K
        hCUK_AOB
        hAOB_CUK

    exact
      (hilbert_angleLess_irrefl
        Geo C U K)
        hCycle

  · rcases hRest with hAOB_CPY_eq | hDecomp

    ------------------------------------------------------------------
    -- Case 2: AOB ~= CPY.
    ------------------------------------------------------------------

    · have hAOB_CUH :
          HilbertAngleLess Geo A O B C U H :=
        hilbert_angleLess_transport_left
          Geo
          C P Y
          A O B
          C U H
          hCPY_CUH
          hAOB
          hAOB_CPY_eq

      have hAOB_CUK :
          HilbertAngleLess Geo A O B C U K :=
        hilbert_angleLess_trans
          Geo
          A O B
          C U H
          C U K
          hAOB_CUH
          hCUH_CUK

      have hCycle :
          HilbertAngleLess Geo C U K C U K :=
        hilbert_angleLess_trans
          Geo
          C U K
          A O B
          C U K
          hCUK_AOB
          hAOB_CUK

      exact
        (hilbert_angleLess_irrefl
          Geo C U K)
          hCycle

    ------------------------------------------------------------------
    -- Case 3:
    --
    --   W is interior to AOB,
    --   CPY ~= AOW,
    --   WOB < EQZ.
    --
    -- Compare the two components with CUH and KUH and use strict
    -- componentwise angle addition.
    ------------------------------------------------------------------

    · rcases hDecomp with
        ⟨W,
          hInsideW,
          hCPY_AOW,
          hWOB_EQZ⟩

      have hAOW :
          Not (PrimCollinear Geo A O W) :=
        (hilbert_interior_angle_less
          Geo
          O W A B
          hAOB
          hInsideW).1

      have hAOW_CPY :
          Geo.AngleCongruent A O W C P Y :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          C P Y
          A O W
          hCPY_AOW

      have hAOW_CUH :
          HilbertAngleLess Geo A O W C U H :=
        hilbert_angleLess_transport_left
          Geo
          C P Y
          A O W
          C U H
          hCPY_CUH
          hAOW
          hAOW_CPY

      have hWOB_KUH :
          HilbertAngleLess Geo W O B K U H :=
        hilbert_angleLess_trans
          Geo
          W O B
          E Q Z
          K U H
          hWOB_EQZ
          hEQZ_KUH

      have hBOW :
          Not (PrimCollinear Geo B O W) := by
        intro hcol
        exact
          hWOB_KUH.1
            (PrimCollinearSymm
              Geo B O W hcol)

      have hWOBrefl :
          Geo.AngleCongruent W O B W O B :=
        Geometry.Geo.angle_congruent_reflexive
          Geo W O B

      have hBOW_WOB :
          Geo.AngleCongruent B O W W O B :=
        (Geometry.Geo.angle_congruent_reverse_first
          Geo
          W O B
          W O B).mp
          hWOBrefl

      have hBOW_KUH :
          HilbertAngleLess Geo B O W K U H :=
        hilbert_angleLess_transport_left
          Geo
          W O B
          B O W
          K U H
          hWOB_KUH
          hBOW
          hBOW_WOB

      have hAOB_CUK :
          HilbertAngleLess Geo A O B C U K :=
        hilbert_angleDecomposition_componentwise_less_whole_XI
          Geo
          O A B W
          U C K H
          hAOB
          hCUK
          hInsideW
          hInsideH
          hAOW_CUH
          hBOW_KUH

      have hCycle :
          HilbertAngleLess Geo C U K C U K :=
        hilbert_angleLess_trans
          Geo
          C U K
          A O B
          C U K
          hCUK_AOB
          hAOB_CUK

      exact
        (hilbert_angleLess_irrefl
          Geo C U K)
          hCycle


------------------------------------------------------------------------
-- XI.23: the source radius cannot be smaller than the circumradius
------------------------------------------------------------------------

/--
The complete bad-radius contradiction for XI.23.

The three proper central rays have exactly four order configurations:

1. UC meets DK;
2. UD meets CK;
3. UK meets CD;
4. the cyclic/full-turn witness D-U-H and C-H-K.

The first three are closed by the previously verified C/D/K branches.
The fourth is closed by
`hilbert_XI23_smaller_radius_cyclic_impossible_XI`.

Hence OA < UC is impossible.
-/
theorem hilbert_XI23_smaller_radius_impossible_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    False := by

  have hCentralLess :=
    hilbert_XI23_three_central_angles_less_of_smaller_radius_auto_XI
      Geo
      A O B
      C P D
      E Q F
      K U
      h12_3
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hRadiusLess

  have hCUK :
      Not (PrimCollinear Geo C U K) :=
    hCentralLess.1.1

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hCentralLess.2.1.1

  have hDUK :
      Not (PrimCollinear Geo D U K) :=
    hCentralLess.2.2.1

  have hCases :=
    hilbert_three_rays_order_or_cyclic_XI
      Geo
      U C D K
      hCUD
      hDUK
      hCUK

  rcases hCases with
    hInsideC | hRest1

  · exact
      hilbert_XI23_smaller_radius_inside_C_impossible_XI
        Geo
        A O B
        C P D
        E Q F
        U K
        h12_3
        hFour
        hInsideC
        hOA_OB
        hOA_PC
        hOA_PD
        hOA_QE
        hOA_QF
        hCK_AB
        hDK_EF
        hUC_UD
        hUC_UK
        hRadiusLess

  · rcases hRest1 with
      hInsideD | hRest2

    · exact
        hilbert_XI23_smaller_radius_inside_D_impossible_XI
          Geo
          A O B
          C P D
          E Q F
          U K
          h12_3
          h23_1
          hFour
          hInsideD
          hOA_OB
          hOA_PC
          hOA_PD
          hOA_QE
          hOA_QF
          hCK_AB
          hDK_EF
          hUC_UD
          hUC_UK
          hRadiusLess

    · rcases hRest2 with
        hInsideK | hCyclic

      · exact
          hilbert_XI23_smaller_radius_inside_K_impossible_XI
            Geo
            A O B
            C P D
            E Q F
            U K
            h12_3
            h31_2
            hFour
            hInsideK
            hOA_OB
            hOA_PC
            hOA_PD
            hOA_QE
            hOA_QF
            hCK_AB
            hDK_EF
            hUC_UD
            hUC_UK
            hRadiusLess

      · rcases hCyclic with
          ⟨H, hDUH, hCHK⟩

        exact
          hilbert_XI23_smaller_radius_cyclic_impossible_XI
            Geo
            A O B
            C P D
            E Q F
            U K H
            h12_3
            hFour
            hDUH
            hCHK
            hOA_OB
            hOA_PC
            hOA_PD
            hOA_QE
            hOA_QF
            hCK_AB
            hDK_EF
            hUC_UD
            hUC_UK
            hRadiusLess

------------------------------------------------------------------------
-- XI.23: equal-radius branch
------------------------------------------------------------------------

/--
A proper source chord cannot be congruent to a diameter of an
equal-radius circle.

Assume

    C-U-K,
    UC ~= UK,
    OA ~= OB,
    UC ~= OA,
    CK ~= AB,

with AOB proper.  Euclid I.20 gives AB < OA + OB.  The diameter CK
is congruent to exactly that sum, so AB < CK, contradicting CK ~= AB.
-/
theorem hilbert_XI23_diameter_chord_impossible_of_equal_radius_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C U K : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCUK : Geo.Between C U K)
    (hOA_OB : Geo.Congruent O A O B)
    (hUC_UK : Geo.Congruent U C U K)
    (hCK_AB : Geo.Congruent C K A B)
    (hUC_OA : Geo.Congruent U C O A) :
    False := by

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro hcol
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B hcol)

  rcases
      euclid_proposition_20
        Geo
        O A B
        hOAB
    with
    ⟨D,
      hAOD,
      hOD_OB,
      hAB_AD⟩

  have hOA_UC :
      Geo.Congruent O A U C :=
    hilbert_congruent_symmetry
      Geo U C O A hUC_OA

  have hAO_CU :
      Geo.Congruent A O C U :=
    CongruentReverseBoth
      Geo
      O A
      U C
      hOA_UC

  have hOB_OA :
      Geo.Congruent O B O A :=
    hilbert_congruent_symmetry
      Geo O A O B hOA_OB

  have hOB_UC :
      Geo.Congruent O B U C :=
    hilbert_congruent_transitivity
      Geo
      O B
      O A
      U C
      hOB_OA
      hOA_UC

  have hOB_UK :
      Geo.Congruent O B U K :=
    hilbert_congruent_transitivity
      Geo
      O B
      U C
      U K
      hOB_UC
      hUC_UK

  have hOD_UK :
      Geo.Congruent O D U K :=
    hilbert_congruent_transitivity
      Geo
      O D
      O B
      U K
      hOD_OB
      hOB_UK

  have hAD_CK :
      Geo.Congruent A D C K :=
    bookZero_sumOfParts
      Geo
      A O D
      C U K
      hAO_CU
      hOD_UK
      hAOD
      hCUK

  have hAB_CK :
      HilbertSegmentLess Geo A B C K :=
    hilbert_segmentLess_congruent_right
      Geo
      A B
      A D
      C K
      hAB_AD
      hAD_CK

  have hAB_CK_cong :
      Geo.Congruent A B C K :=
    hilbert_congruent_symmetry
      Geo C K A B hCK_AB

  exact
    (hilbert_segmentLess_not_congruent
      Geo
      A B
      C K
      hAB_CK)
      hAB_CK_cong


/--
In the equal-radius XI.23 branch the three central angles CUK, CUD
and DUK are proper.

Each possible diameter configuration would make a proper source chord
congruent to a diameter of an equal-radius circle, contradicting the
previous theorem.
-/
theorem hilbert_XI23_central_angles_proper_of_equal_radius_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F K U : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hUC_OA : Geo.Congruent U C O A) :
    Not (PrimCollinear Geo C U K) /\
    Not (PrimCollinear Geo C U D) /\
    Not (PrimCollinear Geo D U K) := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h12_3.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h12_3.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h12_3.2.2.1

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo
      A B O
      (by
        intro hcol
        exact
          hAOB
            (PrimCollinearRotate
              Geo A B O hcol))

  have hCD :
      Ne C D :=
    hilbert_noncollinear_ne_first
      Geo
      C D P
      (by
        intro hcol
        exact
          hCPD
            (PrimCollinearRotate
              Geo C D P hcol))

  have hEF :
      Ne E F :=
    hilbert_noncollinear_ne_first
      Geo
      E F Q
      (by
        intro hcol
        exact
          hEQF
            (PrimCollinearRotate
              Geo E F Q hcol))

  have hAB_CK :
      Geo.Congruent A B C K :=
    hilbert_congruent_symmetry
      Geo C K A B hCK_AB

  have hEF_DK :
      Geo.Congruent E F D K :=
    hilbert_congruent_symmetry
      Geo D K E F hDK_EF

  have hCK :
      Ne C K :=
    bookZero_nullSegment3
      Geo
      A B
      C K
      hAB
      hAB_CK

  have hDK :
      Ne D K :=
    bookZero_nullSegment3
      Geo
      E F
      D K
      hEF
      hEF_DK

  have hPC_OA :
      Geo.Congruent P C O A :=
    hilbert_congruent_symmetry
      Geo O A P C hOA_PC

  have hPC_PD :
      Geo.Congruent P C P D :=
    hilbert_congruent_transitivity
      Geo
      P C
      O A
      P D
      hPC_OA
      hOA_PD

  have hUC_PC :
      Geo.Congruent U C P C :=
    hilbert_congruent_transitivity
      Geo
      U C
      O A
      P C
      hUC_OA
      hOA_PC

  have hQE_OA :
      Geo.Congruent Q E O A :=
    hilbert_congruent_symmetry
      Geo O A Q E hOA_QE

  have hQE_QF :
      Geo.Congruent Q E Q F :=
    hilbert_congruent_transitivity
      Geo
      Q E
      O A
      Q F
      hQE_OA
      hOA_QF

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo U C U D hUC_UD

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      hUD_UC
      hUC_UK

  have hUD_OA :
      Geo.Congruent U D O A :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      O A
      hUD_UC
      hUC_OA

  have hUD_QE :
      Geo.Congruent U D Q E :=
    hilbert_congruent_transitivity
      Geo
      U D
      O A
      Q E
      hUD_OA
      hOA_QE

  have hCD_CD :
      Geo.Congruent C D C D :=
    hilbert_congruent_reflexive
      Geo C D

  have hNotCUK :
      Not (Geo.Between C U K) := by
    intro hBetween

    exact
      hilbert_XI23_diameter_chord_impossible_of_equal_radius_XI
        Geo
        A O B
        C U K
        hAOB
        hBetween
        hOA_OB
        hUC_UK
        hCK_AB
        hUC_OA

  have hNotCUD :
      Not (Geo.Between C U D) := by
    intro hBetween

    exact
      hilbert_XI23_diameter_chord_impossible_of_equal_radius_XI
        Geo
        C P D
        C U D
        hCPD
        hBetween
        hPC_PD
        hUC_UD
        hCD_CD
        hUC_PC

  have hNotDUK :
      Not (Geo.Between D U K) := by
    intro hBetween

    exact
      hilbert_XI23_diameter_chord_impossible_of_equal_radius_XI
        Geo
        E Q F
        D U K
        hEQF
        hBetween
        hQE_QF
        hUD_UK
        hDK_EF
        hUD_QE

  have hCUK :
      Not (PrimCollinear Geo C U K) :=
    hilbert_equal_radii_noncollinear_of_not_between_XI
      Geo
      C U K
      hCK
      hUC_UK
      hNotCUK

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hilbert_equal_radii_noncollinear_of_not_between_XI
      Geo
      C U D
      hCD
      hUC_UD
      hNotCUD

  have hDUK :
      Not (PrimCollinear Geo D U K) :=
    hilbert_equal_radii_noncollinear_of_not_between_XI
      Geo
      D U K
      hDK
      hUD_UK
      hNotDUK

  exact
    ⟨hCUK, hCUD, hDUK⟩


/--
The equal-radius branch of XI.23 is impossible.

When UC ~= OA, SSS identifies the three source angles with the three
central angles.  The three XI.20 inequalities therefore transport to
the central configuration.

The three-ray order theorem has four cases.

* If one central ray is interior to the angle of the other two, the
  corresponding transported XI.20 inequality says that the two exact
  component angles are together strictly greater than the whole angle,
  giving whole < whole.

* In the cyclic case, the cyclic four-right-angle certificate transports
  its two supplementary summands to the two exact components cut by the
  opposite ray, again giving whole < whole.
-/
theorem hilbert_XI23_equal_radius_impossible_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K)
    (hUC_OA : Geo.Congruent U C O A) :
    False := by

  have hProper :=
    hilbert_XI23_central_angles_proper_of_equal_radius_XI
      Geo
      A O B
      C P D
      E Q F
      K U
      h12_3
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hUC_OA

  have hCUK :
      Not (PrimCollinear Geo C U K) :=
    hProper.1

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hProper.2.1

  have hDUK :
      Not (PrimCollinear Geo D U K) :=
    hProper.2.2

  have hAngles :=
    hilbert_XI23_central_angles_congruent_of_equal_radius_XI
      Geo
      A O B
      C P D
      E Q F
      K U
      h12_3
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hUC_OA

  have hAOB_CUK :
      Geo.AngleCongruent A O B C U K :=
    hAngles.1

  have hCPD_CUD :
      Geo.AngleCongruent C P D C U D :=
    hAngles.2.1

  have hEQF_DUK :
      Geo.AngleCongruent E Q F D U K :=
    hAngles.2.2

  have hCentral :=
    hilbertThreeAngleInequalities_transport_XI
      Geo
      A O B
      C P D
      E Q F
      C U K
      C U D
      D U K
      h12_3
      h23_1
      h31_2
      hCUK
      hCUD
      hDUK
      hAOB_CUK
      hCPD_CUD
      hEQF_DUK

  have h12c :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C U K
        C U D
        D U K :=
    hCentral.1

  have h23c :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C U D
        D U K
        C U K :=
    hCentral.2.1

  have h31c :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        D U K
        C U K
        C U D :=
    hCentral.2.2

  have hCases :=
    hilbert_three_rays_order_or_cyclic_XI
      Geo
      U C D K
      hCUD
      hDUK
      hCUK

  rcases hCases with
    hInsideC | hRest1

  --------------------------------------------------------------------
  -- UC inside angle DUK.
  --------------------------------------------------------------------

  ·
    have hKUC :
        Not (PrimCollinear Geo K U C) := by
      intro hcol
      exact
        hCUK
          (PrimCollinearSymm
            Geo K U C hcol)

    have hKUD :
        Not (PrimCollinear Geo K U D) := by
      intro hcol
      exact
        hDUK
          (PrimCollinearSymm
            Geo K U D hcol)

    have hCUKrefl :
        Geo.AngleCongruent C U K C U K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo C U K

    have hKUC_CUK :
        Geo.AngleCongruent K U C C U K :=
      (Geometry.Geo.angle_congruent_reverse_first
        Geo
        C U K
        C U K).mp
        hCUKrefl

    have hCUK_KUC :
        Geo.AngleCongruent C U K K U C :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        K U C
        C U K
        hKUC_CUK

    have hDUKrefl :
        Geo.AngleCongruent D U K D U K :=
      Geometry.Geo.angle_congruent_reflexive
        Geo D U K

    have hKUD_DUK :
        Geo.AngleCongruent K U D D U K :=
      (Geometry.Geo.angle_congruent_reverse_first
        Geo
        D U K
        D U K).mp
        hDUKrefl

    have hDUK_KUD :
        Geo.AngleCongruent D U K K U D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        K U D
        D U K
        hKUD_DUK

    have hCUDrefl :
        Geo.AngleCongruent C U D C U D :=
      Geometry.Geo.angle_congruent_reflexive
        Geo C U D

    have hSum :
        HilbertTwoAnglesGreaterThanAngle
          Geo
          K U C
          C U D
          K U D :=
      hilbertTwoAnglesGreaterThanAngle_transport_all_XI
        Geo
        C U K
        C U D
        D U K
        K U C
        C U D
        K U D
        h12c
        hKUC
        hCUD
        hKUD
        hCUK_KUC
        hCUDrefl
        hDUK_KUD

    have hInsideCrev :
        HilbertRayMeetsSegment Geo U C K D :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo
        U C D K
        hInsideC

    have hCycle :
        HilbertAngleLess Geo K U D K U D :=
      hilbert_twoAnglesGreaterThanAngle_of_interior_split_gives_whole_greater_XI
        Geo
        K U D C
        K U D
        hKUD
        hInsideCrev
        hSum

    exact
      (hilbert_angleLess_irrefl
        Geo K U D)
        hCycle

  · rcases hRest1 with
      hInsideD | hRest2

    ------------------------------------------------------------------
    -- UD inside angle CUK.
    ------------------------------------------------------------------

    ·
      have hCycle :
          HilbertAngleLess Geo C U K C U K :=
        hilbert_twoAnglesGreaterThanAngle_of_interior_split_gives_whole_greater_XI
          Geo
          C U K D
          C U K
          hCUK
          hInsideD
          h23c

      exact
        (hilbert_angleLess_irrefl
          Geo C U K)
          hCycle

    · rcases hRest2 with
        hInsideK | hCyclic

      ----------------------------------------------------------------
      -- UK inside angle CUD.
      ----------------------------------------------------------------

      ·
        have hKUC :
            Not (PrimCollinear Geo K U C) := by
          intro hcol
          exact
            hCUK
              (PrimCollinearSymm
                Geo K U C hcol)

        have hDUC :
            Not (PrimCollinear Geo D U C) := by
          intro hcol
          exact
            hCUD
              (PrimCollinearSymm
                Geo D U C hcol)

        have hCUKrefl :
            Geo.AngleCongruent C U K C U K :=
          Geometry.Geo.angle_congruent_reflexive
            Geo C U K

        have hKUC_CUK :
            Geo.AngleCongruent K U C C U K :=
          (Geometry.Geo.angle_congruent_reverse_first
            Geo
            C U K
            C U K).mp
            hCUKrefl

        have hCUK_KUC :
            Geo.AngleCongruent C U K K U C :=
          Geometry.Geo.angle_congruent_symmetry
            Geo
            K U C
            C U K
            hKUC_CUK

        have hCUDrefl :
            Geo.AngleCongruent C U D C U D :=
          Geometry.Geo.angle_congruent_reflexive
            Geo C U D

        have hDUC_CUD :
            Geo.AngleCongruent D U C C U D :=
          (Geometry.Geo.angle_congruent_reverse_first
            Geo
            C U D
            C U D).mp
            hCUDrefl

        have hCUD_DUC :
            Geo.AngleCongruent C U D D U C :=
          Geometry.Geo.angle_congruent_symmetry
            Geo
            D U C
            C U D
            hDUC_CUD

        have hDUKrefl :
            Geo.AngleCongruent D U K D U K :=
          Geometry.Geo.angle_congruent_reflexive
            Geo D U K

        have hSum :
            HilbertTwoAnglesGreaterThanAngle
              Geo
              D U K
              K U C
              D U C :=
          hilbertTwoAnglesGreaterThanAngle_transport_all_XI
            Geo
            D U K
            C U K
            C U D
            D U K
            K U C
            D U C
            h31c
            hDUK
            hKUC
            hDUC
            hDUKrefl
            hCUK_KUC
            hCUD_DUC

        have hInsideKrev :
            HilbertRayMeetsSegment Geo U K D C :=
          hilbert_angleDecomposition_ray_meets_segment_reverse
            Geo
            U K C D
            hInsideK

        have hCycle :
            HilbertAngleLess Geo D U C D U C :=
          hilbert_twoAnglesGreaterThanAngle_of_interior_split_gives_whole_greater_XI
            Geo
            D U C K
            D U C
            hDUC
            hInsideKrev
            hSum

        exact
          (hilbert_angleLess_irrefl
            Geo D U C)
            hCycle

      ----------------------------------------------------------------
      -- Cyclic/full-turn branch.
      ----------------------------------------------------------------

      ·
        rcases hCyclic with
          ⟨H, hDUH, hCHK⟩

        have hDUHdata :=
          HilbertOrder.between_incidence
            D U H hDUH

        have hUH :
            Ne U H :=
          hDUHdata.2.1

        have hRayUHH :
            HilbertSameRay Geo U H H :=
          hilbert_sameRay_refl
            Geo U H hUH.symm

        have hInsideH :
            HilbertRayMeetsSegment Geo U H C K :=
          ⟨H, hCHK, hRayUHH⟩

        have hCUH_CUK :
            HilbertAngleLess Geo C U H C U K :=
          hilbert_interior_angle_less
            Geo
            U H C K
            hCUK
            hInsideH

        have hCUH :
            Not (PrimCollinear Geo C U H) :=
          hCUH_CUK.1

        have hInsideHrev :
            HilbertRayMeetsSegment Geo U H K C :=
          hilbert_angleDecomposition_ray_meets_segment_reverse
            Geo
            U H C K
            hInsideH

        have hKUC :
            Not (PrimCollinear Geo K U C) := by
          intro hcol
          exact
            hCUK
              (PrimCollinearSymm
                Geo K U C hcol)

        have hKUH :
            Not (PrimCollinear Geo K U H) :=
          (hilbert_interior_angle_less
            Geo
            U H K C
            hKUC
            hInsideHrev).1

        have hFourCyclic :
            HilbertThreeAnglesLessThanFourRightAngles
              Geo
              C P D
              E Q F
              A O B :=
          hilbertThreeAnglesLessThanFourRightAngles_cycle
            Geo
            A O B
            C P D
            E Q F
            hFour

        rcases
            hilbertThreeAnglesLessThanFourRightAngles_elim
              Geo
              C P D
              E Q F
              A O B
              hFourCyclic
          with
          ⟨Y, Z,
            hDPY,
            hFQZ,
            hCompare0⟩

        have hDPC :
            Not (PrimCollinear Geo D P C) := by
          intro hcol
          exact
            h12_3.2.1
              (PrimCollinearSymm
                Geo D P C hcol)

        have hDUC :
            Not (PrimCollinear Geo D U C) := by
          intro hcol
          exact
            hCUD
              (PrimCollinearSymm
                Geo D U C hcol)

        have hCP :
            Ne C P :=
          hilbert_noncollinear_ne_first
            Geo C P D h12_3.2.1

        have hCU :
            Ne C U :=
          hilbert_noncollinear_ne_first
            Geo C U D hCUD

        have hSuppY :
            BookZeroSupplement Geo D P C C Y :=
          ⟨hilbert_sameRay_refl
              Geo P C hCP,
            hDPY⟩

        have hSuppH :
            BookZeroSupplement Geo D U C C H :=
          ⟨hilbert_sameRay_refl
              Geo U C hCU,
            hDUH⟩

        have hDPC_CUD :
            Geo.AngleCongruent D P C C U D :=
          (Geometry.Geo.angle_congruent_reverse_first
            Geo
            C P D
            C U D).mp
            hCPD_CUD

        have hDPC_DUC :
            Geo.AngleCongruent D P C D U C :=
          (Geometry.Geo.angle_congruent_reverse_second
            Geo
            D P C
            C U D).mp
            hDPC_CUD

        have hCPY_CUH :
            Geo.AngleCongruent C P Y C U H :=
          bookZero_43_supplements
            Geo
            D P C C Y
            D U C C H
            hDPC_DUC
            hSuppY
            hSuppH
            hDPC
            hDUC

        have hEQF :
            Not (PrimCollinear Geo E Q F) :=
          h12_3.2.2.1

        have hFQE :
            Not (PrimCollinear Geo F Q E) := by
          intro hcol
          exact
            hEQF
              (PrimCollinearSymm
                Geo F Q E hcol)

        have hEQ :
            Ne E Q :=
          hilbert_noncollinear_ne_first
            Geo E Q F hEQF

        have hKU :
            Ne K U :=
          hilbert_noncollinear_ne_first
            Geo K U H hKUH

        have hSuppZ :
            BookZeroSupplement Geo F Q E E Z :=
          ⟨hilbert_sameRay_refl
              Geo Q E hEQ,
            hFQZ⟩

        have hSuppKUH :
            BookZeroSupplement Geo D U K K H :=
          ⟨hilbert_sameRay_refl
              Geo U K hKU,
            hDUH⟩

        have hFQE_DUK :
            Geo.AngleCongruent F Q E D U K :=
          (Geometry.Geo.angle_congruent_reverse_first
            Geo
            E Q F
            D U K).mp
            hEQF_DUK

        have hEQZ_KUH :
            Geo.AngleCongruent E Q Z K U H :=
          bookZero_43_supplements
            Geo
            F Q E E Z
            D U K K H
            hFQE_DUK
            hSuppZ
            hSuppKUH
            hFQE
            hDUK

        have hCompare :
            HilbertTwoAnglesGreaterThanAngle
              Geo
              C U H
              K U H
              C U K :=
          hilbertTwoAnglesGreaterThanAngle_transport_all_XI
            Geo
            C P Y
            E Q Z
            A O B
            C U H
            K U H
            C U K
            hCompare0
            hCUH
            hKUH
            hCUK
            hCPY_CUH
            hEQZ_KUH
            hAOB_CUK

        have hHUK :
            Not (PrimCollinear Geo H U K) := by
          intro hcol
          exact
            hKUH
              (PrimCollinearSymm
                Geo H U K hcol)

        have hKUHrefl :
            Geo.AngleCongruent K U H K U H :=
          Geometry.Geo.angle_congruent_reflexive
            Geo K U H

        have hHUK_KUH :
            Geo.AngleCongruent H U K K U H :=
          (Geometry.Geo.angle_congruent_reverse_first
            Geo
            K U H
            K U H).mp
            hKUHrefl

        have hKUH_HUK :
            Geo.AngleCongruent K U H H U K :=
          Geometry.Geo.angle_congruent_symmetry
            Geo
            H U K
            K U H
            hHUK_KUH

        have hCompare' :
            HilbertTwoAnglesGreaterThanAngle
              Geo
              C U H
              H U K
              C U K :=
          hilbertTwoAnglesGreaterThanAngle_transport_second
            Geo
            C U H
            K U H
            H U K
            C U K
            hCompare
            hHUK
            hKUH_HUK

        have hCycle :
            HilbertAngleLess Geo C U K C U K :=
          hilbert_twoAnglesGreaterThanAngle_of_interior_split_gives_whole_greater_XI
            Geo
            C U K H
            C U K
            hCUK
            hInsideH
            hCompare'

        exact
          (hilbert_angleLess_irrefl
            Geo C U K)
            hCycle

------------------------------------------------------------------------
-- XI.23: final planar radius comparison
------------------------------------------------------------------------

/--
Final planar radius comparison for XI.23.

The source radius OA is strictly longer than the circumradius UC.

Proof:
* OA < UC is impossible by the complete smaller-radius analysis;
* UC ~= OA is impossible by the equal-radius analysis;
* if UC < OA also failed, Book Zero trichotomy would force UC ~= OA.

Hence UC < OA.
-/
theorem hilbert_XI23_circumradius_less_source_radius_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C P D E Q F U K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K) :
    HilbertSegmentLess Geo U C O A := by

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h12_3.1

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro hcol
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B hcol)

  have hOA :
      Ne O A :=
    hilbert_noncollinear_ne_first
      Geo O A B hOAB

  have hABO :
      Not (PrimCollinear Geo A B O) := by
    intro hcol
    have hBAO :
        PrimCollinear Geo B A O :=
      PrimCollinearSwap
        Geo A B O hcol
    have hOABcol :
        PrimCollinear Geo O A B :=
      PrimCollinearSymm
        Geo B A O hBAO
    exact hOAB hOABcol

  have hAB :
      Ne A B :=
    hilbert_noncollinear_ne_first
      Geo A B O hABO

  have hAB_CK :
      Geo.Congruent A B C K :=
    hilbert_congruent_symmetry
      Geo C K A B hCK_AB

  have hCK :
      Ne C K :=
    bookZero_nullSegment3
      Geo
      A B
      C K
      hAB
      hAB_CK

  have hUC :
      Ne U C := by
    intro hUCeq
    subst U

    have hCK_null :
        Geo.Congruent C K C C :=
      hilbert_congruent_symmetry
        Geo
        C C
        C K
        hUC_UK

    have hCKeq :
        C = K :=
      bookZero_nullSegment1
        Geo
        C K C
        hCK_null

    exact hCK hCKeq

  have hNotOA_UC :
      Not (HilbertSegmentLess Geo O A U C) := by
    intro hLess

    exact
      hilbert_XI23_smaller_radius_impossible_XI
        Geo
        A O B
        C P D
        E Q F
        U K
        h12_3
        h23_1
        h31_2
        hFour
        hOA_OB
        hOA_PC
        hOA_PD
        hOA_QE
        hOA_QF
        hCK_AB
        hDK_EF
        hUC_UD
        hUC_UK
        hLess

  by_contra hNotUC_OA

  have hUC_OA :
      Geo.Congruent U C O A :=
    bookZero_31_trichotomy1
      Geo
      U C
      O A
      hNotUC_OA
      hNotOA_UC
      hUC
      hOA

  exact
    hilbert_XI23_equal_radius_impossible_XI
      Geo
      A O B
      C P D
      E Q F
      U K
      h12_3
      h23_1
      h31_2
      hFour
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK
      hUC_OA

------------------------------------------------------------------------
-- XI.23: local construction of the normal-length segment
------------------------------------------------------------------------

/--
Local XI.23 replacement for Euclid's post-proposition square-difference
lemma.

From a strict comparison

    UC < OA

construct points E,K,H such that

    O-E-A,
    OE ~= UC,
    E is the midpoint of OK,
    OH ~= OA,
    KH ~= OA,
    angle OEH is right.

Thus EH is the length which will later be laid off on the XI.12 normal
through U.

The construction reuses the already formalized equal-circle mechanism
from Proposition II.14:

1. lay off OE ~= UC on ray OA;
2. reflect O across E to K;
3. intersect the two equal circles centered at O and K, both with
   radius OA;
4. the common point H is equidistant from O,K, hence EH is
   perpendicular to OK at its midpoint E.

No Book III/IV development and no segment multiplication are introduced.
-/
theorem hilbert_XI23_height_segment_exists_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O A U C : Geo.Point)
    (hOA : Ne O A)
    (hUC_OA : HilbertSegmentLess Geo U C O A) :
    exists E K H : Geo.Point,
      Geo.Between O E A /\
      Geo.Congruent O E U C /\
      HilbertIsMidpoint Geo E O K /\
      Geo.Congruent O H O A /\
      Geo.Congruent K H O A /\
      Not (PrimCollinear Geo E O H) /\
      HilbertRightAngle Geo O E H := by

  --------------------------------------------------------------------
  -- Lay off UC on ray OA.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        U C
        O A
        hOA
    with
    ⟨E, hRayOAE, hOE_UC⟩

  have hUC_OE :
      Geo.Congruent U C O E :=
    hilbert_congruent_symmetry
      Geo O E U C hOE_UC

  have hOE_OA :
      HilbertSegmentLess Geo O E O A :=
    hilbert_segmentLess_congruent_left
      Geo
      U C
      O E
      O A
      hUC_OA
      hOE_UC

  have hRayOEA :
      HilbertSameRay Geo O E A :=
    bookZero_39_ray5
      Geo
      O A E
      hRayOAE

  have hOEA :
      Geo.Between O E A :=
    bookZero_51_lessThanBetween
      Geo
      O E A
      hOE_OA
      hRayOEA

  --------------------------------------------------------------------
  -- Reflect O across E.
  --------------------------------------------------------------------

  rcases
      proposition2_14_mirror_center
        Geo
        O E A
        hOEA
    with
    ⟨K,
      _hOEK,
      hMidE,
      _hEK_OE⟩

  --------------------------------------------------------------------
  -- Equal circles centered at O,K with radius OA meet at H.
  --------------------------------------------------------------------

  rcases
      proposition2_14_equal_circles_intersect
        Geo
        O E A K
        hOEA
        hMidE
    with
    ⟨H,
      hOH_OA,
      hKH_OA⟩

  --------------------------------------------------------------------
  -- H is off the center line OE.
  --------------------------------------------------------------------

  have hOE :
      Ne O E :=
    (HilbertOrder.between_incidence
      O E A hOEA).1

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        O E
        hOE
    with
    ⟨base, hObase, hEbase⟩

  have hHoff :
      Not (HilbertIncidence.OnLine H base) :=
    proposition2_14_circle_point_off_center_line
      Geo
      O E A K H
      base
      hOEA
      hMidE
      hOH_OA
      hKH_OA
      hObase
      hEbase

  have hEO :
      Ne E O :=
    hOE.symm

  have hEOH :
      Not (PrimCollinear Geo E O H) :=
    hilbert_not_collinear_of_off_line
      Geo
      E O H
      base
      hEO
      hEbase
      hObase
      hHoff

  --------------------------------------------------------------------
  -- H is equidistant from O and K.
  --------------------------------------------------------------------

  have hHO_OA :
      Geo.Congruent H O O A :=
    CongruentReverseFirst
      Geo
      O H
      O A
      hOH_OA

  have hOA_KH :
      Geo.Congruent O A K H :=
    hilbert_congruent_symmetry
      Geo K H O A hKH_OA

  have hHO_KH :
      Geo.Congruent H O K H :=
    hilbert_congruent_transitivity
      Geo
      H O
      O A
      K H
      hHO_OA
      hOA_KH

  have hHO_HK :
      Geo.Congruent H O H K :=
    CongruentSwapSecond
      Geo
      H O
      K H
      hHO_KH

  --------------------------------------------------------------------
  -- Midpoint + equidistance gives the right angle OEH.
  --------------------------------------------------------------------

  have hRight :
      HilbertRightAngle Geo O E H :=
    proposition2_14_equidistant_right_angle
      Geo
      O E K H
      hMidE
      hEOH
      hHO_HK

  exact
    ⟨E, K, H,
      hOEA,
      hOE_UC,
      hMidE,
      hOH_OA,
      hKH_OA,
      hEOH,
      hRight⟩

------------------------------------------------------------------------
-- XI.23: run the planar radius/height core inside one spatial plane
------------------------------------------------------------------------

/--
The existing planar XI.23 radius comparison and auxiliary height
construction can be run unchanged inside any fixed ambient plane.

This is the architectural bridge we need before removing the global
`HilbertEuclideanPlane Geo` assumption from the spatial theorem:

* the hypotheses are stated entirely in `PlaneGeo Geo pi`;
* spatial Group IV supplies `HilbertEuclideanPlane (PlaneGeo Geo pi)`;
* the long planar proof is reused verbatim;
* no global planar instance is installed on the ambient space.
-/
theorem hilbert_XI23_radius_height_in_plane_XI
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi : S.Plane)
    (A O B C P D E Q F U K : PlanePoint Geo pi)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo pi)
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo pi)
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo pi)
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        (PlaneGeo Geo pi)
        A O B
        C P D
        E Q F)
    (hOA_OB :
      (PlaneGeo Geo pi).Congruent O A O B)
    (hOA_PC :
      (PlaneGeo Geo pi).Congruent O A P C)
    (hOA_PD :
      (PlaneGeo Geo pi).Congruent O A P D)
    (hOA_QE :
      (PlaneGeo Geo pi).Congruent O A Q E)
    (hOA_QF :
      (PlaneGeo Geo pi).Congruent O A Q F)
    (hCK_AB :
      (PlaneGeo Geo pi).Congruent C K A B)
    (hDK_EF :
      (PlaneGeo Geo pi).Congruent D K E F)
    (hUC_UD :
      (PlaneGeo Geo pi).Congruent U C U D)
    (hUC_UK :
      (PlaneGeo Geo pi).Congruent U C U K) :
    HilbertSegmentLess
      (PlaneGeo Geo pi)
      U C O A /\
    exists E0 K0 H0 : PlanePoint Geo pi,
      (PlaneGeo Geo pi).Between O E0 A /\
      (PlaneGeo Geo pi).Congruent O E0 U C /\
      HilbertIsMidpoint (PlaneGeo Geo pi) E0 O K0 /\
      (PlaneGeo Geo pi).Congruent O H0 O A /\
      (PlaneGeo Geo pi).Congruent K0 H0 O A /\
      Not (PrimCollinear (PlaneGeo Geo pi) E0 O H0) /\
      HilbertRightAngle (PlaneGeo Geo pi) O E0 H0 := by

  have hUC_OA :
      HilbertSegmentLess
        (PlaneGeo Geo pi)
        U C O A :=
    hilbert_XI23_circumradius_less_source_radius_XI
      (PlaneGeo Geo pi)
      A O B
      C P D
      E Q F
      U K
      h12_3
      h23_1
      h31_2
      hFour
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK

  have hAO :
      Ne A O :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo pi)
      A O B
      h12_3.1

  have hOA :
      Ne O A :=
    hAO.symm

  refine And.intro hUC_OA ?_

  exact
    hilbert_XI23_height_segment_exists_XI
      (PlaneGeo Geo pi)
      O A U C
      hOA
      hUC_OA

------------------------------------------------------------------------
-- XI.23: copy one ambient angle into a fixed spatial plane
------------------------------------------------------------------------

/--
Copy a proper ambient angle into a prescribed spatial plane, using the
fixed first ray PC and then laying off the radius PC on the copied second
ray.

The output point R satisfies:

    R lies in pi,
    PR ~= PC,
    C-P-R is a proper angle,
    angle AOB ~= angle CPR.

This is the local bridge needed to run the planar XI.22/XI.23 core inside
`PlaneGeo Geo pi` without introducing a global `HilbertCongruence Geo`
instance on the ambient space.
-/
theorem hilbert_XI23_copy_angle_equal_radius_in_plane_XI
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A O B C P D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCpi : S.OnPlane C pi)
    (hPpi : S.OnPlane P pi)
    (hDpi : S.OnPlane D pi)
    (hCPD : Not (PrimCollinear Geo C P D)) :
    exists R : Geo.Point,
      S.OnPlane R pi /\
      Geo.Congruent P R P C /\
      Not (PrimCollinear Geo C P R) /\
      Geo.AngleCongruent A O B C P R := by

  have hCP :
      Ne C P :=
    hilbert_noncollinear_ne_first
      Geo C P D hCPD

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        C P hCP
    with
    ⟨base, hCbase, hPbase⟩

  have hBasePi :
      HilbertLineInPlane Geo base pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      C P hCP
      base hCbase hPbase
      pi hCpi hPpi

  have hDoff :
      Not (H.OnLine D base) := by
    intro hDbase
    exact
      hCPD
        ⟨base,
         hCbase,
         hPbase,
         hDbase⟩

  rcases
      HilbertSpaceCongruence.angle_construction_in_plane
        (Geo := Geo)
        A O B
        C P D
        hAOB
        hCP
        pi
        base
        hBasePi
        hCbase
        hPbase
        hDpi
        hDoff
    with
    ⟨X, hXSameSide, hAOB_CPX, _hUnique⟩

  have hXpi :
      S.OnPlane X pi :=
    hXSameSide.1

  have hXoff :
      Not (H.OnLine X base) :=
    hXSameSide.2.2.1

  have hPX :
      Ne P X := by
    intro hPXeq
    subst X
    exact hXoff hPbase

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        P C
        P X
        hPX
    with
    ⟨R, hRayPXR, hPR_PC⟩

  have hRpi :
      S.OnPlane R pi :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      pi
      P X R
      hPX
      hPpi hXpi
      hRayPXR.2.2.1

  have hPR :
      Ne P R :=
    hRayPXR.2.1.symm

  have hCPR :
      Not (PrimCollinear Geo C P R) := by
    intro hCol

    have hRbase :
        H.OnLine R base :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hCP
        hCbase hPbase
        hCol

    rcases hRayPXR.2.2.1 with
      ⟨rayLine, hPray, hXray, hRray⟩

    have hRayBase :
        rayLine = base :=
      HilbertPlaneIncidence.line_unique
        P R hPR
        rayLine base
        hPray hRray
        hPbase hRbase

    subst rayLine
    exact hXoff hXray

  --------------------------------------------------------------------
  -- Same-ray angle transport must be performed locally in PlaneGeo pi.
  -- The generic planar lemma uses HilbertOrder, so applying it directly
  -- to the ambient Geo would reintroduce a forbidden global plane/order
  -- instance.  All four points C,P,X,R already lie in pi.
  --------------------------------------------------------------------

  let Cp : PlanePoint Geo pi :=
    ⟨C, hCpi⟩

  let Pp : PlanePoint Geo pi :=
    ⟨P, hPpi⟩

  let Xp : PlanePoint Geo pi :=
    ⟨X, hXpi⟩

  let Rp : PlanePoint Geo pi :=
    ⟨R, hRpi⟩

  have hCPX :
      Not (PrimCollinear Geo C P X) := by
    intro hCol

    have hXbase' :
        H.OnLine X base :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hCP
        hCbase hPbase
        hCol

    exact hXoff hXbase'

  have hCPXPlane :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Cp Pp Xp) := by
    intro hCol
    exact
      hCPX
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          pi
          Cp Pp Xp
          hCol)

  have hRayPlane :
      HilbertSameRay
        (PlaneGeo Geo pi)
        Pp Xp Rp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi
        Pp Xp Rp).mpr
    simpa [Pp, Xp, Rp] using hRayPXR

  have hAngleEqPlane :
      (PlaneGeo Geo pi).Angle Cp Pp Xp =
      (PlaneGeo Geo pi).Angle Cp Pp Rp :=
    hilbert_angle_eq_of_sameRay_second
      (PlaneGeo Geo pi)
      Pp Cp Xp Rp
      hRayPlane

  have hCPXreflPlane :
      (PlaneGeo Geo pi).AngleCongruent
        Cp Pp Xp
        Cp Pp Xp :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := PlaneGeo Geo pi)
      Cp Pp Xp
      hCPXPlane

  have hCPX_CPR_plane :
      (PlaneGeo Geo pi).AngleCongruent
        Cp Pp Xp
        Cp Pp Rp := by
    unfold Geometry.Geo.AngleCongruent
      at hCPXreflPlane ⊢
    rw [hAngleEqPlane.symm]
    exact hCPXreflPlane

  have hCPX_CPR :
      Geo.AngleCongruent C P X C P R := by
    have h :=
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        pi
        Cp Pp Xp
        Cp Pp Rp).mp
        hCPX_CPR_plane
    simpa [Cp, Pp, Xp, Rp] using h

  have hAOB_CPR :
      Geo.AngleCongruent A O B C P R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A O B
      C P X
      C P R
      hAOB_CPX
      hCPX_CPR

  exact
    ⟨R,
      hRpi,
      hPR_PC,
      hCPR,
      hAOB_CPR⟩


------------------------------------------------------------------------
-- XI.23: pure spatial apex engine from a prepared right triangle
------------------------------------------------------------------------

/--
Pure spatial engine for the final XI.23 construction.

This theorem contains no planar XI.23 radius comparison and no auxiliary
II.14 construction.  It assumes that the base plane pi and its center U
have already been prepared, together with a right triangle O-E0-H0 whose
legs match the base radius and the future normal segment.

Its only job is spatial:

1. use XI.12 to erect the normal through U to pi;
2. lay off UR ~= E0H0 on that normal;
3. compare UCR, UDR, UKR with E0OH0 by spatial SAS.

The conclusion is deliberately left in the orientation produced directly
by spatial SAS:

    CR ~= OH0, DR ~= OH0, KR ~= OH0.

No ambient `HilbertEuclideanPlane Geo` instance is required.
-/
theorem hilbert_XI23_spatial_apex_from_right_triangle_XI
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (C D K U E0 O H0 : Geo.Point)
    (pi : S.Plane)
    (hCpi : S.OnPlane C pi)
    (hDpi : S.OnPlane D pi)
    (hKpi : S.OnPlane K pi)
    (hUpi : S.OnPlane U pi)
    (hUC : Ne U C)
    (hUD : Ne U D)
    (hUK : Ne U K)
    (hUC_E0O : Geo.Congruent U C E0 O)
    (hUD_E0O : Geo.Congruent U D E0 O)
    (hUK_E0O : Geo.Congruent U K E0 O)
    (hE0OH0 : Not (PrimCollinear Geo E0 O H0))
    (hRightOE0H0 : HilbertRightAngle Geo O E0 H0) :
    exists R : Geo.Point,
      Not (S.OnPlane R pi) /\
      Geo.Congruent C R O H0 /\
      Geo.Congruent D R O H0 /\
      Geo.Congruent K R O H0 := by

  have hOE0H0 :
      Not (PrimCollinear Geo O E0 H0) := by
    intro hcol
    exact
      hE0OH0
        (PrimCollinearSwap
          Geo O E0 H0 hcol)

  --------------------------------------------------------------------
  -- XI.12: erect the normal l to pi through U.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_12
        (Geo := Geo)
        pi U
        hUpi
    with
    ⟨l, hPerp⟩

  have hUl :
      H.OnLine U l :=
    (HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo)
      hPerp).1

  --------------------------------------------------------------------
  -- Choose a direction on l and lay off E0H0 from U.
  --------------------------------------------------------------------

  rcases
      hilbert_other_point_on_line
        (Geo := Geo)
        l U
    with
    ⟨T, hTU, hTl⟩

  have hUT :
      Ne U T :=
    hTU.symm

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        E0 H0
        U T
        hUT
    with
    ⟨R, hRayUTR, hUR_E0H0⟩

  have hRU :
      Ne R U :=
    hRayUTR.2.1

  have hUR :
      Ne U R :=
    hRU.symm

  have hRl :
      H.OnLine R l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hUT
      hUl
      hTl
      hRayUTR.2.2.1

  --------------------------------------------------------------------
  -- R is outside pi.
  --------------------------------------------------------------------

  have hRoff :
      Not (S.OnPlane R pi) := by
    intro hRpi

    have hRUeq :
        R = U :=
      hilbert_XI12_perpendicular_foot_unique
        (Geo := Geo)
        pi l U R
        hPerp
        hRl
        hRpi

    exact
      hRU hRUeq

  --------------------------------------------------------------------
  -- Generic spatial radial calculation.
  --------------------------------------------------------------------

  have hRadial :
      forall X : Geo.Point,
        S.OnPlane X pi ->
        Ne U X ->
        Geo.Congruent U X E0 O ->
        Geo.Congruent X R O H0 := by

    intro X hXpi hUX hUX_E0O

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          U X
          hUX
      with
      ⟨m, hUm, hXm⟩

    have hmpi :
        HilbertLineInPlane Geo m pi :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        U X hUX
        m hUm hXm
        pi hUpi hXpi

    have hPerpM :
        HilbertLinesPerpendicularAt Geo l m U :=
      HilbertLinePerpendicularPlaneAt.perpendicular_to_line
        (Geo := Geo)
        hPerp
        hmpi
        hUm

    rcases hPerpM with
      ⟨_hUl0, _hUm0,
       A0, B0,
       hA0U, hB0U,
       hA0l, hB0m,
       hA0UB0,
       hRightA0UB0⟩

    have hUA0R :
        PrimCollinear Geo U A0 R :=
      ⟨l, hUl, hA0l, hRl⟩

    have hUB0X :
        PrimCollinear Geo U B0 X :=
      ⟨m, hUm, hB0m, hXm⟩

    have hRUX :
        Not (PrimCollinear Geo R U X) :=
      hilbert_not_collinear_collinear_arms_XI
        Geo
        A0 U B0
        R X
        hA0UB0
        hUA0R
        hUB0X
        hUR
        hUX

    ------------------------------------------------------------------
    -- The planar right-angle transport lemmas cannot be used directly
    -- on the ambient Geo: there is deliberately no global
    -- HilbertCongruence Geo instance in the spatial architecture.
    --
    -- Instead put the two intersecting carrier lines l,m into their
    -- own plane rho, do the transport in PlaneGeo Geo rho, and bridge
    -- the resulting right angle back to the ambient space.
    ------------------------------------------------------------------

    rcases
        HilbertSpaceIncidence.plane_through
          (Geo := Geo)
          A0 U B0
          hA0UB0
      with
      ⟨rho, hA0rho, hUrho, hB0rho⟩

    have hRrho :
        S.OnPlane R rho :=
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        rho
        A0 U R
        hA0U
        hA0rho hUrho
        (PrimCollinearSwap
          Geo U A0 R hUA0R)

    have hXrho :
        S.OnPlane X rho :=
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        rho
        B0 U X
        hB0U
        hB0rho hUrho
        (PrimCollinearSwap
          Geo U B0 X hUB0X)

    let A0p : PlanePoint Geo rho :=
      ⟨A0, hA0rho⟩

    let Up : PlanePoint Geo rho :=
      ⟨U, hUrho⟩

    let B0p : PlanePoint Geo rho :=
      ⟨B0, hB0rho⟩

    let Rp : PlanePoint Geo rho :=
      ⟨R, hRrho⟩

    let Xp : PlanePoint Geo rho :=
      ⟨X, hXrho⟩

    have hA0pUpB0p :
        Not
          (PrimCollinear
            (PlaneGeo Geo rho)
            A0p Up B0p) := by
      intro hcol
      exact
        hA0UB0
          (planeGeo_primCollinear_to_ambient
            (Geo := Geo)
            rho
            A0p Up B0p
            hcol)

    have hRightA0pUpB0p :
        HilbertRightAngle
          (PlaneGeo Geo rho)
          A0p Up B0p := by
      apply
        (planeGeo_rightAngle_iff_ambient
          (Geo := Geo)
          rho
          A0p Up B0p).mpr
      simpa [A0p, Up, B0p] using hRightA0UB0

    have hUpA0pRp :
        PrimCollinear
          (PlaneGeo Geo rho)
          Up A0p Rp :=
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        rho
        Up A0p Rp
        hA0U.symm
        hUA0R

    have hUpB0pXp :
        PrimCollinear
          (PlaneGeo Geo rho)
          Up B0p Xp :=
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        rho
        Up B0p Xp
        hB0U.symm
        hUB0X

    have hUpRp :
        Ne Up Rp := by
      intro h
      exact hUR (congrArg Subtype.val h)

    have hUpXp :
        Ne Up Xp := by
      intro h
      exact hUX (congrArg Subtype.val h)

    have hRightRpUpXp :
        HilbertRightAngle
          (PlaneGeo Geo rho)
          Rp Up Xp :=
      hilbert_right_angle_collinear_both_XI
        (PlaneGeo Geo rho)
        A0p Up B0p
        Rp Xp
        hA0pUpB0p
        hRightA0pUpB0p
        hUpA0pRp
        hUpB0pXp
        hUpRp
        hUpXp

    have hRightRUX :
        HilbertRightAngle Geo R U X := by
      apply
        (planeGeo_rightAngle_iff_ambient
          (Geo := Geo)
          rho
          Rp Up Xp).mp
      exact hRightRpUpXp

    have hXUR :
        Not (PrimCollinear Geo X U R) := by
      intro hcol
      exact
        hRUX
          (PrimCollinearSymm
            Geo X U R hcol)

    have hRpUpXp :
        Not
          (PrimCollinear
            (PlaneGeo Geo rho)
            Rp Up Xp) := by
      intro hcol
      exact
        hRUX
          (planeGeo_primCollinear_to_ambient
            (Geo := Geo)
            rho
            Rp Up Xp
            hcol)

    have hRightXpUpRp :
        HilbertRightAngle
          (PlaneGeo Geo rho)
          Xp Up Rp :=
      hilbert_right_angle_swap_XI
        (PlaneGeo Geo rho)
        Rp Up Xp
        hRpUpXp
        hRightRpUpXp

    have hRightXUR :
        HilbertRightAngle Geo X U R := by
      apply
        (planeGeo_rightAngle_iff_ambient
          (Geo := Geo)
          rho
          Xp Up Rp).mp
      exact hRightXpUpRp

    have hRightCong :
        Geo.AngleCongruent
          X U R
          O E0 H0 :=
      hilbert_space_all_right_angles_congruent
        (Geo := Geo)
        X U R
        O E0 H0
        hXUR
        hOE0H0
        hRightXUR
        hRightOE0H0

    have hUXR :
        Not (PrimCollinear Geo U X R) := by
      intro hcol
      exact
        hXUR
          (PrimCollinearSwap
            Geo U X R hcol)

    exact
      hilbert_space_sas_third_side
        (Geo := Geo)
        U X R
        E0 O H0
        hUXR
        hE0OH0
        hUX_E0O
        hUR_E0H0
        hRightCong

  have hCR_OH0 :
      Geo.Congruent C R O H0 :=
    hRadial C hCpi hUC hUC_E0O

  have hDR_OH0 :
      Geo.Congruent D R O H0 :=
    hRadial D hDpi hUD hUD_E0O

  have hKR_OH0 :
      Geo.Congruent K R O H0 :=
    hRadial K hKpi hUK hUK_E0O

  exact
    ⟨R,
      hRoff,
      hCR_OH0,
      hDR_OH0,
      hKR_OH0⟩

------------------------------------------------------------------------
-- XI.23: spatial apex package
------------------------------------------------------------------------

/--
Spatial XI.23 package after XI.22 has supplied the chord triangle CDK.

The circumcenter is deliberately reconstructed inside the actual
spatial plane through C,D,K.  This avoids using an ambient planar
circumcenter without a proof that it belongs to the base plane.

The theorem then:

1. constructs the base plane pi through C,D,K;
2. constructs its circumcenter U inside `PlaneGeo Geo pi`;
3. applies the already proved planar XI.23 radius comparison UC < OA;
4. constructs the auxiliary right-triangle height segment EH;
5. uses XI.12 to erect the normal l through U to pi;
6. lays off UR ~= EH on l;
7. compares the three right triangles UCR, UDR, UKR with the auxiliary
   right triangle EOH by spatial SAS.

The resulting point R is outside pi and satisfies

    RC ~= OA,
    RD ~= OA,
    RK ~= OA.
-/
theorem hilbert_XI23_spatial_apex_XI
    [H : HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (A O B C P D E Q F K : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F)
    (hCK_AB : Geo.Congruent C K A B)
    (hDK_EF : Geo.Congruent D K E F) :
    exists pi : S.Plane,
    exists U R : Geo.Point,
      S.OnPlane C pi /\
      S.OnPlane D pi /\
      S.OnPlane K pi /\
      S.OnPlane U pi /\
      Not (S.OnPlane R pi) /\
      Geo.Congruent R C O A /\
      Geo.Congruent R D O A /\
      Geo.Congruent R K O A := by

  --------------------------------------------------------------------
  -- The XI.22 chord triangle is proper.
  --------------------------------------------------------------------

  have hCDK :
      Not (PrimCollinear Geo C D K) :=
    hilbert_XI23_chord_triangle_noncollinear_XI
      Geo
      A O B
      C P D
      E Q F
      K
      h12_3
      h23_1
      h31_2
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF

  --------------------------------------------------------------------
  -- Put C,D,K in their actual spatial plane.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        C D K
        hCDK
    with
    ⟨pi, hCpi, hDpi, hKpi⟩

  let Cp : PlanePoint Geo pi :=
    ⟨C, hCpi⟩

  let Dp : PlanePoint Geo pi :=
    ⟨D, hDpi⟩

  let Kp : PlanePoint Geo pi :=
    ⟨K, hKpi⟩

  have hCDKplane :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi)
          Cp Dp Kp) := by
    intro hcol
    exact
      hCDK
        (planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          pi
          Cp Dp Kp
          hcol)

  --------------------------------------------------------------------
  -- Circumcenter inside PlaneGeo pi.
  --------------------------------------------------------------------

  rcases
      hilbert_triangle_circumcenter_exists_XI
        (PlaneGeo Geo pi)
        Cp Dp Kp
        hCDKplane
    with
    ⟨Up,
      hUC_UD_plane,
      hUC_UK_plane⟩

  let U : Geo.Point := Up.1

  have hUpi :
      S.OnPlane U pi := by
    simpa [U] using Up.2

  have hUC_UD :
      Geo.Congruent U C U D := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi
        Up Cp
        Up Dp).mp
        hUC_UD_plane
    simpa [U, Cp, Dp] using h

  have hUC_UK :
      Geo.Congruent U C U K := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi
        Up Cp
        Up Kp).mp
        hUC_UK_plane
    simpa [U, Cp, Kp] using h

  --------------------------------------------------------------------
  -- The circumradius is strictly smaller than the source radius.
  --------------------------------------------------------------------

  have hUC_OA :
      HilbertSegmentLess Geo U C O A :=
    hilbert_XI23_circumradius_less_source_radius_XI
      Geo
      A O B
      C P D
      E Q F
      U K
      h12_3
      h23_1
      h31_2
      hFour
      hOA_OB
      hOA_PC
      hOA_PD
      hOA_QE
      hOA_QF
      hCK_AB
      hDK_EF
      hUC_UD
      hUC_UK

  have hNonzero :=
    bookZero_48_lessThanNotEqual
      Geo
      U C
      O A
      hUC_OA

  have hUC :
      Ne U C :=
    hNonzero.1

  have hOA :
      Ne O A :=
    hNonzero.2

  --------------------------------------------------------------------
  -- Construct the auxiliary right triangle O-E0-H0.
  --
  -- Use E0,J,H0 to avoid collision with the source points E,Q,F
  -- and the XI.22 vertex K.
  --------------------------------------------------------------------

  rcases
      hilbert_XI23_height_segment_exists_XI
        Geo
        O A
        U C
        hOA
        hUC_OA
    with
    ⟨E0, J, H0,
      hOE0A,
      hOE0_UC,
      hMidE0,
      hOH0_OA,
      hJH0_OA,
      hE0OH0,
      hRightOE0H0⟩

  --------------------------------------------------------------------
  -- Normalize the prepared right triangle against the three base radii.
  --------------------------------------------------------------------

  have hUC_OE0 :
      Geo.Congruent U C O E0 :=
    hilbert_congruent_symmetry
      Geo
      O E0
      U C
      hOE0_UC

  have hUC_E0O :
      Geo.Congruent U C E0 O :=
    CongruentSwapSecond
      Geo
      U C
      O E0
      hUC_OE0

  have hUD :
      Ne U D :=
    bookZero_nullSegment3
      Geo
      U C
      U D
      hUC
      hUC_UD

  have hUK :
      Ne U K :=
    bookZero_nullSegment3
      Geo
      U C
      U K
      hUC
      hUC_UK

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo
      U C
      U D
      hUC_UD

  have hUK_UC :
      Geo.Congruent U K U C :=
    hilbert_congruent_symmetry
      Geo
      U C
      U K
      hUC_UK

  have hUD_E0O :
      Geo.Congruent U D E0 O :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      E0 O
      hUD_UC
      hUC_E0O

  have hUK_E0O :
      Geo.Congruent U K E0 O :=
    hilbert_congruent_transitivity
      Geo
      U K
      U C
      E0 O
      hUK_UC
      hUC_E0O

  --------------------------------------------------------------------
  -- Pure spatial engine: XI.12 + normal layoff + three SAS steps.
  --------------------------------------------------------------------

  rcases
      hilbert_XI23_spatial_apex_from_right_triangle_XI
        Geo
        C D K U E0 O H0
        pi
        hCpi
        hDpi
        hKpi
        hUpi
        hUC
        hUD
        hUK
        hUC_E0O
        hUD_E0O
        hUK_E0O
        hE0OH0
        hRightOE0H0
    with
    ⟨R,
      hRoff,
      hCR_OH0,
      hDR_OH0,
      hKR_OH0⟩

  --------------------------------------------------------------------
  -- Replace the auxiliary hypotenuse OH0 by the source radius OA.
  --------------------------------------------------------------------

  have hCR_OA :
      Geo.Congruent C R O A :=
    hilbert_congruent_transitivity
      Geo
      C R
      O H0
      O A
      hCR_OH0
      hOH0_OA

  have hDR_OA :
      Geo.Congruent D R O A :=
    hilbert_congruent_transitivity
      Geo
      D R
      O H0
      O A
      hDR_OH0
      hOH0_OA

  have hKR_OA :
      Geo.Congruent K R O A :=
    hilbert_congruent_transitivity
      Geo
      K R
      O H0
      O A
      hKR_OH0
      hOH0_OA

  have hRC_OA :
      Geo.Congruent R C O A :=
    CongruentReverseFirst
      Geo
      C R
      O A
      hCR_OA

  have hRD_OA :
      Geo.Congruent R D O A :=
    CongruentReverseFirst
      Geo
      D R
      O A
      hDR_OA

  have hRK_OA :
      Geo.Congruent R K O A :=
    CongruentReverseFirst
      Geo
      K R
      O A
      hKR_OA

  exact
    ⟨pi, U, R,
      hCpi,
      hDpi,
      hKpi,
      hUpi,
      hRoff,
      hRC_OA,
      hRD_OA,
      hRK_OA⟩

------------------------------------------------------------------------
-- XI.23: normalize the three prescribed angles in one plane and run XI.22
------------------------------------------------------------------------

theorem hilbert_XI23_normalized_XI22_in_one_plane_XI
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    (A O B C P D E Q F : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    exists pi : S.Plane,
    exists R1 R2 R3 K : Geo.Point,
      S.OnPlane C pi /\
      S.OnPlane P pi /\
      S.OnPlane R1 pi /\
      S.OnPlane R2 pi /\
      S.OnPlane R3 pi /\
      S.OnPlane K pi /\
      Geo.AngleCongruent A O B C P R1 /\
      Geo.AngleCongruent C P D C P R2 /\
      Geo.AngleCongruent E Q F C P R3 /\
      Geo.Congruent P C P R1 /\
      Geo.Congruent P C P R2 /\
      Geo.Congruent P C P R3 /\
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P R1
        C P R2
        C P R3 /\
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P R2
        C P R3
        C P R1 /\
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P R3
        C P R1
        C P R2 /\
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        C P R1
        C P R2
        C P R3 /\
      Geo.Congruent C K C R1 /\
      Geo.Congruent R2 K C R3 := by

  --------------------------------------------------------------------
  -- Properness of the three original angles.
  --------------------------------------------------------------------

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    h12_3.1

  have hCPD :
      Not (PrimCollinear Geo C P D) :=
    h12_3.2.1

  have hEQF :
      Not (PrimCollinear Geo E Q F) :=
    h12_3.2.2.1

  --------------------------------------------------------------------
  -- Use the plane of the second input angle.
  --------------------------------------------------------------------

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        C P D hCPD
    with
    ⟨pi, hCpi, hPpi, hDpi⟩

  --------------------------------------------------------------------
  -- Copy all three angles onto the same base ray PC and normalize
  -- every second radius to PC.
  --------------------------------------------------------------------

  rcases
      hilbert_XI23_copy_angle_equal_radius_in_plane_XI
        (Geo := Geo)
        pi
        A O B
        C P D
        hAOB
        hCpi hPpi hDpi
        hCPD
    with
    ⟨R1,
      hR1pi,
      hPR1_PC,
      hCPR1,
      hAOB_CPR1⟩

  rcases
      hilbert_XI23_copy_angle_equal_radius_in_plane_XI
        (Geo := Geo)
        pi
        C P D
        C P D
        hCPD
        hCpi hPpi hDpi
        hCPD
    with
    ⟨R2,
      hR2pi,
      hPR2_PC,
      hCPR2,
      hCPD_CPR2⟩

  rcases
      hilbert_XI23_copy_angle_equal_radius_in_plane_XI
        (Geo := Geo)
        pi
        E Q F
        C P D
        hEQF
        hCpi hPpi hDpi
        hCPD
    with
    ⟨R3,
      hR3pi,
      hPR3_PC,
      hCPR3,
      hEQF_CPR3⟩

  --------------------------------------------------------------------
  -- Transport all four XI.23 input conditions to the normalized
  -- ambient representatives.
  --------------------------------------------------------------------

  have h12N :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P R1
        C P R2
        C P R3 :=
    hilbert_space_twoAnglesGreater_transport_all_in_plane
      (Geo := Geo)
      pi
      A O B
      C P D
      E Q F
      C P R1
      C P R2
      C P R3
      hCpi hPpi hR1pi
      hCpi hPpi hR2pi
      hCpi hPpi hR3pi
      h12_3
      hCPR1
      hCPR2
      hCPR3
      hAOB_CPR1
      hCPD_CPR2
      hEQF_CPR3

  have h23N :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P R2
        C P R3
        C P R1 :=
    hilbert_space_twoAnglesGreater_transport_all_in_plane
      (Geo := Geo)
      pi
      C P D
      E Q F
      A O B
      C P R2
      C P R3
      C P R1
      hCpi hPpi hR2pi
      hCpi hPpi hR3pi
      hCpi hPpi hR1pi
      h23_1
      hCPR2
      hCPR3
      hCPR1
      hCPD_CPR2
      hEQF_CPR3
      hAOB_CPR1

  have h31N :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P R3
        C P R1
        C P R2 :=
    hilbert_space_twoAnglesGreater_transport_all_in_plane
      (Geo := Geo)
      pi
      E Q F
      A O B
      C P D
      C P R3
      C P R1
      C P R2
      hCpi hPpi hR3pi
      hCpi hPpi hR1pi
      hCpi hPpi hR2pi
      h31_2
      hCPR3
      hCPR1
      hCPR2
      hEQF_CPR3
      hAOB_CPR1
      hCPD_CPR2

  have hFourN :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        C P R1
        C P R2
        C P R3 :=
    hilbert_space_threeAnglesLessThanFourRight_transport_all_in_plane
      (Geo := Geo)
      pi
      A O B
      C P D
      E Q F
      C P R1
      C P R2
      C P R3
      hCpi hPpi hR1pi
      hCpi hPpi hR2pi
      hCpi hPpi hR3pi
      hFour
      hCPR1
      hCPR2
      hCPR3
      hAOB_CPR1
      hCPD_CPR2
      hEQF_CPR3

  --------------------------------------------------------------------
  -- PlanePoint representatives.
  --------------------------------------------------------------------

  let Cp : PlanePoint Geo pi :=
    ⟨C, hCpi⟩

  let Pp : PlanePoint Geo pi :=
    ⟨P, hPpi⟩

  let R1p : PlanePoint Geo pi :=
    ⟨R1, hR1pi⟩

  let R2p : PlanePoint Geo pi :=
    ⟨R2, hR2pi⟩

  let R3p : PlanePoint Geo pi :=
    ⟨R3, hR3pi⟩

  --------------------------------------------------------------------
  -- Repackage the four transported conditions in PlaneGeo pi.
  --------------------------------------------------------------------

  have h12Plane :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo pi)
        Cp Pp R1p
        Cp Pp R2p
        Cp Pp R3p := by
    simpa [Cp, Pp, R1p, R2p, R3p] using
      (hilbert_space_twoAnglesGreater_to_plane
        (Geo := Geo)
        pi
        C P R1
        C P R2
        C P R3
        hCpi hPpi hR1pi
        hCpi hPpi hR2pi
        hCpi hPpi hR3pi
        h12N)

  have h23Plane :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo pi)
        Cp Pp R2p
        Cp Pp R3p
        Cp Pp R1p := by
    simpa [Cp, Pp, R1p, R2p, R3p] using
      (hilbert_space_twoAnglesGreater_to_plane
        (Geo := Geo)
        pi
        C P R2
        C P R3
        C P R1
        hCpi hPpi hR2pi
        hCpi hPpi hR3pi
        hCpi hPpi hR1pi
        h23N)

  have h31Plane :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo pi)
        Cp Pp R3p
        Cp Pp R1p
        Cp Pp R2p := by
    simpa [Cp, Pp, R1p, R2p, R3p] using
      (hilbert_space_twoAnglesGreater_to_plane
        (Geo := Geo)
        pi
        C P R3
        C P R1
        C P R2
        hCpi hPpi hR3pi
        hCpi hPpi hR1pi
        hCpi hPpi hR2pi
        h31N)

  have hFourPlane :
      HilbertThreeAnglesLessThanFourRightAngles
        (PlaneGeo Geo pi)
        Cp Pp R1p
        Cp Pp R2p
        Cp Pp R3p := by
    simpa [Cp, Pp, R1p, R2p, R3p] using
      (hilbert_space_threeAnglesFourRight_to_plane
        (Geo := Geo)
        pi
        C P R1
        C P R2
        C P R3
        hCpi hPpi hR1pi
        hCpi hPpi hR2pi
        hCpi hPpi hR3pi
        hFourN)

  --------------------------------------------------------------------
  -- Equal-radius data for XI.22.
  --------------------------------------------------------------------

  have hPC : Ne P C :=
    (hilbert_noncollinear_ne_first
      Geo C P D hCPD).symm

  have hPR1C :
      Not (PrimCollinear Geo P R1 C) := by
    intro hCol
    apply hCPR1
    rcases hCol with
      ⟨l, hPl, hR1l, hCl⟩
    exact ⟨l, hCl, hPl, hR1l⟩

  have hPR2C :
      Not (PrimCollinear Geo P R2 C) := by
    intro hCol
    apply hCPR2
    rcases hCol with
      ⟨l, hPl, hR2l, hCl⟩
    exact ⟨l, hCl, hPl, hR2l⟩

  have hPR3C :
      Not (PrimCollinear Geo P R3 C) := by
    intro hCol
    apply hCPR3
    rcases hCol with
      ⟨l, hPl, hR3l, hCl⟩
    exact ⟨l, hCl, hPl, hR3l⟩

  have hPR1 : Ne P R1 :=
    hilbert_noncollinear_ne_first
      Geo P R1 C hPR1C

  have hPR2 : Ne P R2 :=
    hilbert_noncollinear_ne_first
      Geo P R2 C hPR2C

  have hPR3 : Ne P R3 :=
    hilbert_noncollinear_ne_first
      Geo P R3 C hPR3C

  have hPC_PR1 :
      Geo.Congruent P C P R1 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      P R1
      P C
      hPR1
      hPR1_PC

  have hPC_PR2 :
      Geo.Congruent P C P R2 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      P R2
      P C
      hPR2
      hPR2_PC

  have hPC_PR3 :
      Geo.Congruent P C P R3 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      P R3
      P C
      hPR3
      hPR3_PC

  have hPC_PC :
      Geo.Congruent P C P C :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      P C hPC

  have hPC_PR1_plane :
      (PlaneGeo Geo pi).Congruent
        Pp Cp Pp R1p := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Pp Cp Pp R1p).mpr
    simpa [Pp, Cp, R1p] using hPC_PR1

  have hPC_PR2_plane :
      (PlaneGeo Geo pi).Congruent
        Pp Cp Pp R2p := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Pp Cp Pp R2p).mpr
    simpa [Pp, Cp, R2p] using hPC_PR2

  have hPC_PR3_plane :
      (PlaneGeo Geo pi).Congruent
        Pp Cp Pp R3p := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Pp Cp Pp R3p).mpr
    simpa [Pp, Cp, R3p] using hPC_PR3

  have hPC_PC_plane :
      (PlaneGeo Geo pi).Congruent
        Pp Cp Pp Cp := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Pp Cp Pp Cp).mpr
    simpa [Pp, Cp] using hPC_PC

  --------------------------------------------------------------------
  -- XI.22 now runs entirely inside PlaneGeo pi.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_11_22
        (PlaneGeo Geo pi)
        Cp Pp R1p
        Cp Pp R2p
        Cp Pp R3p
        h12Plane
        h23Plane
        h31Plane
        hPC_PR1_plane
        hPC_PC_plane
        hPC_PR2_plane
        hPC_PC_plane
        hPC_PR3_plane
    with
    ⟨Kp,
      hCK_CR1_plane,
      hR2K_CR3_plane⟩

  let K : Geo.Point :=
    Kp.1

  have hKpi :
      S.OnPlane K pi := by
    simpa [K] using Kp.2

  have hCK_CR1 :
      Geo.Congruent C K C R1 := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi
        Cp Kp
        Cp R1p).mp
        hCK_CR1_plane
    simpa [Cp, R1p, K] using h

  have hR2K_CR3 :
      Geo.Congruent R2 K C R3 := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi
        R2p Kp
        Cp R3p).mp
        hR2K_CR3_plane
    simpa [R2p, Cp, R3p, K] using h

  exact
    ⟨pi,
      R1, R2, R3, K,
      hCpi,
      hPpi,
      hR1pi,
      hR2pi,
      hR3pi,
      hKpi,
      hAOB_CPR1,
      hCPD_CPR2,
      hEQF_CPR3,
      hPC_PR1,
      hPC_PR2,
      hPC_PR3,
      h12N,
      h23N,
      h31N,
      hFourN,
      hCK_CR1,
      hR2K_CR3⟩

------------------------------------------------------------------------
-- XI.23: circumcenter, radius comparison, and auxiliary right triangle
------------------------------------------------------------------------

theorem hilbert_XI23_normalized_radius_height_XI
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (A O B C P D E Q F : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    exists pi : S.Plane,
    exists R1 R2 R3 K U E0 H0 : Geo.Point,
      S.OnPlane C pi /\
      S.OnPlane P pi /\
      S.OnPlane R1 pi /\
      S.OnPlane R2 pi /\
      S.OnPlane R3 pi /\
      S.OnPlane K pi /\
      S.OnPlane U pi /\
      S.OnPlane E0 pi /\
      S.OnPlane H0 pi /\
      Geo.AngleCongruent A O B C P R1 /\
      Geo.AngleCongruent C P D C P R2 /\
      Geo.AngleCongruent E Q F C P R3 /\
      Not (PrimCollinear Geo C P R1) /\
      Not (PrimCollinear Geo C P R2) /\
      Not (PrimCollinear Geo C P R3) /\
      Geo.Congruent P C P R1 /\
      Geo.Congruent P C P R2 /\
      Geo.Congruent P C P R3 /\
      Geo.Congruent C K C R1 /\
      Geo.Congruent R2 K C R3 /\
      Not (PrimCollinear Geo C R2 K) /\
      Geo.Congruent U C U R2 /\
      Geo.Congruent U C U K /\
      Ne U C /\
      Ne U R2 /\
      Ne U K /\
      Geo.Congruent U C E0 P /\
      Geo.Congruent U R2 E0 P /\
      Geo.Congruent U K E0 P /\
      Geo.Congruent P H0 P C /\
      Not (PrimCollinear Geo E0 P H0) /\
      HilbertRightAngle Geo P E0 H0 := by

  --------------------------------------------------------------------
  -- Run the completed normalized XI.22 block.
  --------------------------------------------------------------------

  rcases
      hilbert_XI23_normalized_XI22_in_one_plane_XI
        (Geo := Geo)
        A O B C P D E Q F
        h12_3 h23_1 h31_2 hFour
    with
    ⟨pi,
      R1, R2, R3, K,
      hCpi, hPpi,
      hR1pi, hR2pi, hR3pi, hKpi,
      hAOB_CPR1,
      hCPD_CPR2,
      hEQF_CPR3,
      hPC_PR1,
      hPC_PR2,
      hPC_PR3,
      h12N,
      h23N,
      h31N,
      hFourN,
      hCK_CR1,
      hR2K_CR3⟩

  have hCPR1 :
      Not (PrimCollinear Geo C P R1) :=
    h12N.1

  have hCPR2 :
      Not (PrimCollinear Geo C P R2) :=
    h12N.2.1

  have hCPR3 :
      Not (PrimCollinear Geo C P R3) :=
    h12N.2.2.1

  --------------------------------------------------------------------
  -- PlanePoint representatives.
  --------------------------------------------------------------------

  let Cp : PlanePoint Geo pi :=
    ⟨C, hCpi⟩

  let Pp : PlanePoint Geo pi :=
    ⟨P, hPpi⟩

  let R1p : PlanePoint Geo pi :=
    ⟨R1, hR1pi⟩

  let R2p : PlanePoint Geo pi :=
    ⟨R2, hR2pi⟩

  let R3p : PlanePoint Geo pi :=
    ⟨R3, hR3pi⟩

  let Kp : PlanePoint Geo pi :=
    ⟨K, hKpi⟩

  --------------------------------------------------------------------
  -- Transport the four normalized hypotheses to PlaneGeo pi.
  --------------------------------------------------------------------

  have h12Plane :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo pi)
        Cp Pp R1p
        Cp Pp R2p
        Cp Pp R3p := by
    simpa [Cp, Pp, R1p, R2p, R3p] using
      (hilbert_space_twoAnglesGreater_to_plane
        (Geo := Geo)
        pi
        C P R1
        C P R2
        C P R3
        hCpi hPpi hR1pi
        hCpi hPpi hR2pi
        hCpi hPpi hR3pi
        h12N)

  have h23Plane :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo pi)
        Cp Pp R2p
        Cp Pp R3p
        Cp Pp R1p := by
    simpa [Cp, Pp, R1p, R2p, R3p] using
      (hilbert_space_twoAnglesGreater_to_plane
        (Geo := Geo)
        pi
        C P R2
        C P R3
        C P R1
        hCpi hPpi hR2pi
        hCpi hPpi hR3pi
        hCpi hPpi hR1pi
        h23N)

  have h31Plane :
      HilbertTwoAnglesGreaterThanAngle
        (PlaneGeo Geo pi)
        Cp Pp R3p
        Cp Pp R1p
        Cp Pp R2p := by
    simpa [Cp, Pp, R1p, R2p, R3p] using
      (hilbert_space_twoAnglesGreater_to_plane
        (Geo := Geo)
        pi
        C P R3
        C P R1
        C P R2
        hCpi hPpi hR3pi
        hCpi hPpi hR1pi
        hCpi hPpi hR2pi
        h31N)

  have hFourPlane :
      HilbertThreeAnglesLessThanFourRightAngles
        (PlaneGeo Geo pi)
        Cp Pp R1p
        Cp Pp R2p
        Cp Pp R3p := by
    simpa [Cp, Pp, R1p, R2p, R3p] using
      (hilbert_space_threeAnglesFourRight_to_plane
        (Geo := Geo)
        pi
        C P R1
        C P R2
        C P R3
        hCpi hPpi hR1pi
        hCpi hPpi hR2pi
        hCpi hPpi hR3pi
        hFourN)

  --------------------------------------------------------------------
  -- Equal-radius data in PlaneGeo pi.
  --------------------------------------------------------------------

  have hPC : Ne P C :=
    (hilbert_noncollinear_ne_first
      Geo C P R1 hCPR1).symm

  have hPC_PC :
      Geo.Congruent P C P C :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      P C hPC

  have hPC_PR1_plane :
      (PlaneGeo Geo pi).Congruent
        Pp Cp Pp R1p := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Pp Cp Pp R1p).mpr
    simpa [Pp, Cp, R1p] using hPC_PR1

  have hPC_PR2_plane :
      (PlaneGeo Geo pi).Congruent
        Pp Cp Pp R2p := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Pp Cp Pp R2p).mpr
    simpa [Pp, Cp, R2p] using hPC_PR2

  have hPC_PR3_plane :
      (PlaneGeo Geo pi).Congruent
        Pp Cp Pp R3p := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Pp Cp Pp R3p).mpr
    simpa [Pp, Cp, R3p] using hPC_PR3

  have hPC_PC_plane :
      (PlaneGeo Geo pi).Congruent
        Pp Cp Pp Cp := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Pp Cp Pp Cp).mpr
    simpa [Pp, Cp] using hPC_PC

  have hCK_CR1_plane :
      (PlaneGeo Geo pi).Congruent
        Cp Kp Cp R1p := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi Cp Kp Cp R1p).mpr
    simpa [Cp, Kp, R1p] using hCK_CR1

  have hR2K_CR3_plane :
      (PlaneGeo Geo pi).Congruent
        R2p Kp Cp R3p := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        pi R2p Kp Cp R3p).mpr
    simpa [R2p, Kp, Cp, R3p] using hR2K_CR3

  --------------------------------------------------------------------
  -- The XI.22 chord triangle C-R2-K is proper.
  --------------------------------------------------------------------

  have hCR2KPlane :
      Not (PrimCollinear
        (PlaneGeo Geo pi)
        Cp R2p Kp) :=
    hilbert_XI23_chord_triangle_noncollinear_XI
      (PlaneGeo Geo pi)
      Cp Pp R1p
      Cp Pp R2p
      Cp Pp R3p
      Kp
      h12Plane
      h23Plane
      h31Plane
      hPC_PR1_plane
      hPC_PC_plane
      hPC_PR2_plane
      hPC_PC_plane
      hPC_PR3_plane
      hCK_CR1_plane
      hR2K_CR3_plane

  have hCR2K :
      Not (PrimCollinear Geo C R2 K) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      pi
      Cp R2p Kp
      hCR2KPlane

  --------------------------------------------------------------------
  -- Circumcenter U inside PlaneGeo pi.
  --------------------------------------------------------------------

  rcases
      hilbert_triangle_circumcenter_exists_XI
        (PlaneGeo Geo pi)
        Cp R2p Kp
        hCR2KPlane
    with
    ⟨Up,
      hUC_UR2_plane,
      hUC_UK_plane⟩

  let U : Geo.Point :=
    Up.1

  have hUpi :
      S.OnPlane U pi := by
    simpa [U] using Up.2

  have hUC_UR2 :
      Geo.Congruent U C U R2 := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi
        Up Cp
        Up R2p).mp
        hUC_UR2_plane
    simpa [U, Cp, R2p] using h

  have hUC_UK :
      Geo.Congruent U C U K := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi
        Up Cp
        Up Kp).mp
        hUC_UK_plane
    simpa [U, Cp, Kp] using h

  --------------------------------------------------------------------
  -- Run the complete local planar radius/height core.
  --------------------------------------------------------------------

  rcases
      hilbert_XI23_radius_height_in_plane_XI
        (Geo := Geo)
        pi
        Cp Pp R1p
        Cp Pp R2p
        Cp Pp R3p
        Up Kp
        h12Plane
        h23Plane
        h31Plane
        hFourPlane
        hPC_PR1_plane
        hPC_PC_plane
        hPC_PR2_plane
        hPC_PC_plane
        hPC_PR3_plane
        hCK_CR1_plane
        hR2K_CR3_plane
        hUC_UR2_plane
        hUC_UK_plane
    with
    ⟨hRadiusPlane,
      E0p, K0p, H0p,
      hPE0C_plane,
      hPE0_UC_plane,
      _hMidE0,
      hPH0_PC_plane,
      _hK0H0_PC_plane,
      hE0PH0_plane,
      hRightPE0H0_plane⟩

  let E0 : Geo.Point :=
    E0p.1

  let H0 : Geo.Point :=
    H0p.1

  have hE0pi :
      S.OnPlane E0 pi := by
    simpa [E0] using E0p.2

  have hH0pi :
      S.OnPlane H0 pi := by
    simpa [H0] using H0p.2

  --------------------------------------------------------------------
  -- Radius non-nullity comes for free from the strict comparison.
  --------------------------------------------------------------------

  have hNonzero :=
    bookZero_48_lessThanNotEqual
      (PlaneGeo Geo pi)
      Up Cp
      Pp Cp
      hRadiusPlane

  have hUCPlane :
      Ne Up Cp :=
    hNonzero.1

  have hUC :
      Ne U C := by
    intro h
    apply hUCPlane
    exact Subtype.ext h

  have hUR2Plane :
      Ne Up R2p :=
    bookZero_nullSegment3
      (PlaneGeo Geo pi)
      Up Cp
      Up R2p
      hUCPlane
      hUC_UR2_plane

  have hUR2 :
      Ne U R2 := by
    intro h
    apply hUR2Plane
    exact Subtype.ext h

  have hUKPlane :
      Ne Up Kp :=
    bookZero_nullSegment3
      (PlaneGeo Geo pi)
      Up Cp
      Up Kp
      hUCPlane
      hUC_UK_plane

  have hUK :
      Ne U K := by
    intro h
    apply hUKPlane
    exact Subtype.ext h

  --------------------------------------------------------------------
  -- Export the auxiliary right triangle to ambient space.
  --------------------------------------------------------------------

  have hPE0C :
      Geo.Between P E0 C := by
    have h :=
      (planeGeo_between
        (Geo := Geo)
        pi
        Pp E0p Cp).mp
        hPE0C_plane
    simpa [Pp, E0, Cp] using h

  have hPE0 :
      Ne P E0 :=
    (HilbertSpaceOrder.between_incidence
      (Geo := Geo)
      P E0 C hPE0C).1

  have hPE0_UC :
      Geo.Congruent P E0 U C := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi
        Pp E0p
        Up Cp).mp
        hPE0_UC_plane
    simpa [Pp, E0, U, Cp] using h

  have hUC_PE0 :
      Geo.Congruent U C P E0 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      P E0
      U C
      hPE0
      hPE0_UC

  have hUC_E0P :
      Geo.Congruent U C E0 P :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      U C
      P E0).mp
      hUC_PE0

  have hUR2_E0P :
      Geo.Congruent U R2 E0 P :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      U C
      U R2
      E0 P
      hUC_UR2
      hUC_E0P

  have hUK_E0P :
      Geo.Congruent U K E0 P :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      U C
      U K
      E0 P
      hUC_UK
      hUC_E0P

  have hPH0_PC :
      Geo.Congruent P H0 P C := by
    have h :=
      (planeGeo_congruent
        (Geo := Geo)
        pi
        Pp H0p
        Pp Cp).mp
        hPH0_PC_plane
    simpa [Pp, H0, Cp] using h

  have hE0PH0 :
      Not (PrimCollinear Geo E0 P H0) := by
    have h :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        pi
        E0p Pp H0p
        hE0PH0_plane
    simpa [E0, Pp, H0] using h

  have hRightPE0H0 :
      HilbertRightAngle Geo P E0 H0 := by
    have h :=
      (planeGeo_rightAngle_iff_ambient
        (Geo := Geo)
        pi
        Pp E0p H0p).mp
        hRightPE0H0_plane
    simpa [Pp, E0, H0] using h

  exact
    ⟨pi,
      R1, R2, R3, K, U, E0, H0,
      hCpi,
      hPpi,
      hR1pi,
      hR2pi,
      hR3pi,
      hKpi,
      hUpi,
      hE0pi,
      hH0pi,
      hAOB_CPR1,
      hCPD_CPR2,
      hEQF_CPR3,
      hCPR1,
      hCPR2,
      hCPR3,
      hPC_PR1,
      hPC_PR2,
      hPC_PR3,
      hCK_CR1,
      hR2K_CR3,
      hCR2K,
      hUC_UR2,
      hUC_UK,
      hUC,
      hUR2,
      hUK,
      hUC_E0P,
      hUR2_E0P,
      hUK_E0P,
      hPH0_PC,
      hE0PH0,
      hRightPE0H0⟩

------------------------------------------------------------------------
-- XI.23: erect the spatial apex over the normalized chord triangle
------------------------------------------------------------------------

theorem hilbert_XI23_normalized_spatial_apex_XI
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (A O B C P D E Q F : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    exists pi : S.Plane,
    exists R1 R2 R3 K R : Geo.Point,
      S.OnPlane C pi /\
      S.OnPlane P pi /\
      S.OnPlane R1 pi /\
      S.OnPlane R2 pi /\
      S.OnPlane R3 pi /\
      S.OnPlane K pi /\
      Not (S.OnPlane R pi) /\
      Geo.AngleCongruent A O B C P R1 /\
      Geo.AngleCongruent C P D C P R2 /\
      Geo.AngleCongruent E Q F C P R3 /\
      Not (PrimCollinear Geo C P R1) /\
      Not (PrimCollinear Geo C P R2) /\
      Not (PrimCollinear Geo C P R3) /\
      Geo.Congruent P C P R1 /\
      Geo.Congruent P C P R2 /\
      Geo.Congruent P C P R3 /\
      Geo.Congruent C K C R1 /\
      Geo.Congruent R2 K C R3 /\
      Not (PrimCollinear Geo C R2 K) /\
      Geo.Congruent R C P C /\
      Geo.Congruent R R2 P C /\
      Geo.Congruent R K P C := by

  rcases
      hilbert_XI23_normalized_radius_height_XI
        (Geo := Geo)
        A O B C P D E Q F
        h12_3 h23_1 h31_2 hFour
    with
    ⟨pi,
      R1, R2, R3, K, U, E0, H0,
      hCpi,
      hPpi,
      hR1pi,
      hR2pi,
      hR3pi,
      hKpi,
      hUpi,
      _hE0pi,
      _hH0pi,
      hAOB_CPR1,
      hCPD_CPR2,
      hEQF_CPR3,
      hCPR1,
      hCPR2,
      hCPR3,
      hPC_PR1,
      hPC_PR2,
      hPC_PR3,
      hCK_CR1,
      hR2K_CR3,
      hCR2K,
      _hUC_UR2,
      _hUC_UK,
      hUC,
      hUR2,
      hUK,
      hUC_E0P,
      hUR2_E0P,
      hUK_E0P,
      hPH0_PC,
      hE0PH0,
      hRightPE0H0⟩

  --------------------------------------------------------------------
  -- Pure spatial engine: erect the normal and lay off the height.
  --------------------------------------------------------------------

  rcases
      hilbert_XI23_spatial_apex_from_right_triangle_XI
        (Geo := Geo)
        C R2 K U E0 P H0
        pi
        hCpi
        hR2pi
        hKpi
        hUpi
        hUC
        hUR2
        hUK
        hUC_E0P
        hUR2_E0P
        hUK_E0P
        hE0PH0
        hRightPE0H0
    with
    ⟨R,
      hRoff,
      hCR_PH0,
      hR2R_PH0,
      hKR_PH0⟩

  --------------------------------------------------------------------
  -- Normalize the three new lateral edges from PH0 to PC.
  --
  -- We use spatial symmetry + III.2 common-segment transitivity;
  -- no ambient HilbertCongruence instance is introduced.
  --------------------------------------------------------------------

  have hCR : Ne C R := by
    intro hEq
    subst R
    exact hRoff hCpi

  have hR2R : Ne R2 R := by
    intro hEq
    subst R
    exact hRoff hR2pi

  have hKR : Ne K R := by
    intro hEq
    subst R
    exact hRoff hKpi

  have hPH0_CR :
      Geo.Congruent P H0 C R :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      C R
      P H0
      hCR
      hCR_PH0

  have hPH0_R2R :
      Geo.Congruent P H0 R2 R :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      R2 R
      P H0
      hR2R
      hR2R_PH0

  have hPH0_KR :
      Geo.Congruent P H0 K R :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      K R
      P H0
      hKR
      hKR_PH0

  have hCR_PC :
      Geo.Congruent C R P C :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      P H0
      C R
      P C
      hPH0_CR
      hPH0_PC

  have hR2R_PC :
      Geo.Congruent R2 R P C :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      P H0
      R2 R
      P C
      hPH0_R2R
      hPH0_PC

  have hKR_PC :
      Geo.Congruent K R P C :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      P H0
      K R
      P C
      hPH0_KR
      hPH0_PC

  --------------------------------------------------------------------
  -- Put the apex first in all three lateral segments.
  --------------------------------------------------------------------

  have hRC_PC :
      Geo.Congruent R C P C :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      C R
      P C).mp
      hCR_PC

  have hRR2_PC :
      Geo.Congruent R R2 P C :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      R2 R
      P C).mp
      hR2R_PC

  have hRK_PC :
      Geo.Congruent R K P C :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      K R
      P C).mp
      hKR_PC

  exact
    ⟨pi,
      R1, R2, R3, K, R,
      hCpi,
      hPpi,
      hR1pi,
      hR2pi,
      hR3pi,
      hKpi,
      hRoff,
      hAOB_CPR1,
      hCPD_CPR2,
      hEQF_CPR3,
      hCPR1,
      hCPR2,
      hCPR3,
      hPC_PR1,
      hPC_PR2,
      hPC_PR3,
      hCK_CR1,
      hR2K_CR3,
      hCR2K,
      hRC_PC,
      hRR2_PC,
      hRK_PC⟩

------------------------------------------------------------------------
-- Euclid XI.23: final trihedral realization
------------------------------------------------------------------------

theorem euclid_proposition_11_23
    [Hinc : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := Hinc) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (A O B C P D E Q F : Geo.Point)
    (h12_3 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (h23_1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C P D
        E Q F
        A O B)
    (h31_2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E Q F
        A O B
        C P D)
    (hFour :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    HilbertThreeAnglesHaveTrihedralRealization
      Geo
      A O B
      C P D
      E Q F := by

  rcases
      hilbert_XI23_normalized_spatial_apex_XI
        (Geo := Geo)
        A O B C P D E Q F
        h12_3 h23_1 h31_2 hFour
    with
    ⟨pi,
      R1, R2, R3, K, R,
      hCpi,
      hPpi,
      hR1pi,
      hR2pi,
      hR3pi,
      hKpi,
      hRoff,
      hAOB_CPR1,
      hCPD_CPR2,
      hEQF_CPR3,
      hCPR1,
      hCPR2,
      hCPR3,
      hPC_PR1,
      hPC_PR2,
      hPC_PR3,
      hCK_CR1,
      hR2K_CR3,
      hCR2K,
      hRC_PC,
      hRR2_PC,
      hRK_PC⟩

  --------------------------------------------------------------------
  -- Basic non-nullity in the base triangle and at the apex.
  --------------------------------------------------------------------

  have hCR2 : Ne C R2 :=
    hilbert_noncollinear_ne_first
      Geo C R2 K hCR2K

  have hR2KC :
      Not (PrimCollinear Geo R2 K C) := by
    intro hCol
    apply hCR2K
    rcases hCol with
      ⟨l, hR2l, hKl, hCl⟩
    exact ⟨l, hCl, hR2l, hKl⟩

  have hR2K : Ne R2 K :=
    hilbert_noncollinear_ne_first
      Geo R2 K C hR2KC

  have hKCR2 :
      Not (PrimCollinear Geo K C R2) := by
    intro hCol
    apply hCR2K
    rcases hCol with
      ⟨l, hKl, hCl, hR2l⟩
    exact ⟨l, hCl, hR2l, hKl⟩

  have hKC : Ne K C :=
    hilbert_noncollinear_ne_first
      Geo K C R2 hKCR2

  have hRC : Ne R C := by
    intro hEq
    subst R
    exact hRoff hCpi

  have hRR2 : Ne R R2 := by
    intro hEq
    subst R
    exact hRoff hR2pi

  have hRK : Ne R K := by
    intro hEq
    subst R
    exact hRoff hKpi

  --------------------------------------------------------------------
  -- The three spatial face triangles are proper.
  --------------------------------------------------------------------

  have hRKC :
      Not (PrimCollinear Geo R K C) := by
    intro hCol
    apply hRoff

    have hKCR :
        PrimCollinear Geo K C R := by
      rcases hCol with
        ⟨l, hRl, hKl, hCl⟩
      exact ⟨l, hKl, hCl, hRl⟩

    exact
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi
        K C R
        hKC
        hKpi hCpi
        hKCR

  have hRCR2 :
      Not (PrimCollinear Geo R C R2) := by
    intro hCol
    apply hRoff

    have hCR2R :
        PrimCollinear Geo C R2 R := by
      rcases hCol with
        ⟨l, hRl, hCl, hR2l⟩
      exact ⟨l, hCl, hR2l, hRl⟩

    exact
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi
        C R2 R
        hCR2
        hCpi hR2pi
        hCR2R

  have hRR2K :
      Not (PrimCollinear Geo R R2 K) := by
    intro hCol
    apply hRoff

    have hR2KR :
        PrimCollinear Geo R2 K R := by
      rcases hCol with
        ⟨l, hRl, hR2l, hKl⟩
      exact ⟨l, hR2l, hKl, hRl⟩

    exact
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi
        R2 K R
        hR2K
        hR2pi hKpi
        hR2KR

  --------------------------------------------------------------------
  -- Plane representatives of the three normalized source triangles.
  --------------------------------------------------------------------

  let Pp : PlanePoint Geo pi :=
    ⟨P, hPpi⟩

  let Cp : PlanePoint Geo pi :=
    ⟨C, hCpi⟩

  let R1p : PlanePoint Geo pi :=
    ⟨R1, hR1pi⟩

  let R2p : PlanePoint Geo pi :=
    ⟨R2, hR2pi⟩

  let R3p : PlanePoint Geo pi :=
    ⟨R3, hR3pi⟩

  have hPCR1 :
      Not (PrimCollinear Geo P C R1) := by
    intro hCol
    apply hCPR1
    rcases hCol with
      ⟨l, hPl, hCl, hR1l⟩
    exact ⟨l, hCl, hPl, hR1l⟩

  have hPCR2 :
      Not (PrimCollinear Geo P C R2) := by
    intro hCol
    apply hCPR2
    rcases hCol with
      ⟨l, hPl, hCl, hR2l⟩
    exact ⟨l, hCl, hPl, hR2l⟩

  have hPCR3 :
      Not (PrimCollinear Geo P C R3) := by
    intro hCol
    apply hCPR3
    rcases hCol with
      ⟨l, hPl, hCl, hR3l⟩
    exact ⟨l, hCl, hPl, hR3l⟩

  have hPCR1Plane :
      Not (PrimCollinear
        (PlaneGeo Geo pi)
        Pp Cp R1p) := by
    intro hCol
    apply hPCR1
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi Pp Cp R1p hCol
    simpa [Pp, Cp, R1p] using h

  have hPCR2Plane :
      Not (PrimCollinear
        (PlaneGeo Geo pi)
        Pp Cp R2p) := by
    intro hCol
    apply hPCR2
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi Pp Cp R2p hCol
    simpa [Pp, Cp, R2p] using h

  have hPCR3Plane :
      Not (PrimCollinear
        (PlaneGeo Geo pi)
        Pp Cp R3p) := by
    intro hCol
    apply hPCR3
    have h :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi Pp Cp R3p hCol
    simpa [Pp, Cp, R3p] using h

  --------------------------------------------------------------------
  -- Normalize the second lateral side in each SSS comparison.
  --------------------------------------------------------------------

  have hPC_RC :
      Geo.Congruent P C R C :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      R C
      P C
      hRC
      hRC_PC

  have hRC_PR1 :
      Geo.Congruent R C P R1 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      P C
      R C
      P R1
      hPC_RC
      hPC_PR1

  have hPC_RR2 :
      Geo.Congruent P C R R2 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      R R2
      P C
      hRR2
      hRR2_PC

  have hRR2_PR2 :
      Geo.Congruent R R2 P R2 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      P C
      R R2
      P R2
      hPC_RR2
      hPC_PR2

  have hPC_RK :
      Geo.Congruent P C R K :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      R K
      P C
      hRK
      hRK_PC

  have hRK_PR3 :
      Geo.Congruent R K P R3 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      P C
      R K
      P R3
      hPC_RK
      hPC_PR3

  --------------------------------------------------------------------
  -- Base sides for SSS.
  --------------------------------------------------------------------

  have hKC_CR1 :
      Geo.Congruent K C C R1 :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      C K
      C R1).mp
      hCK_CR1

  have hCR2_CR2 :
      Geo.Congruent C R2 C R2 :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      C R2 hCR2

  --------------------------------------------------------------------
  -- SSS 1: angle KRC ~= angle CPR1 ~= angle AOB.
  --------------------------------------------------------------------

  have hFirstNorm :
      Geo.AngleCongruent
        K R C
        C P R1 := by
    have h :=
      hilbert_space_sss_angleA_in_plane
        (Geo := Geo)
        pi
        R K C
        Pp Cp R1p
        hRKC
        hPCR1Plane
        hRK_PC
        hKC_CR1
        hRC_PR1
    simpa [Pp, Cp, R1p] using h

  have hCPR1_AOB :
      Geo.AngleCongruent
        C P R1
        A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      C P R1
      hAOB_CPR1

  have hFirst :
      Geo.AngleCongruent
        K R C
        A O B :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K R C
      C P R1
      A O B
      hFirstNorm
      hCPR1_AOB

  --------------------------------------------------------------------
  -- SSS 2: angle CRR2 ~= angle CPR2 ~= angle CPD.
  --------------------------------------------------------------------

  have hSecondNorm :
      Geo.AngleCongruent
        C R R2
        C P R2 := by
    have h :=
      hilbert_space_sss_angleA_in_plane
        (Geo := Geo)
        pi
        R C R2
        Pp Cp R2p
        hRCR2
        hPCR2Plane
        hRC_PC
        hCR2_CR2
        hRR2_PR2
    simpa [Pp, Cp, R2p] using h

  have hCPR2_CPD :
      Geo.AngleCongruent
        C P R2
        C P D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      C P D
      C P R2
      hCPD_CPR2

  have hSecond :
      Geo.AngleCongruent
        C R R2
        C P D :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C R R2
      C P R2
      C P D
      hSecondNorm
      hCPR2_CPD

  --------------------------------------------------------------------
  -- SSS 3: angle R2RK ~= angle CPR3 ~= angle EQF.
  --------------------------------------------------------------------

  have hThirdNorm :
      Geo.AngleCongruent
        R2 R K
        C P R3 := by
    have h :=
      hilbert_space_sss_angleA_in_plane
        (Geo := Geo)
        pi
        R R2 K
        Pp Cp R3p
        hRR2K
        hPCR3Plane
        hRR2_PC
        hR2K_CR3
        hRK_PR3
    simpa [Pp, Cp, R3p] using h

  have hCPR3_EQF :
      Geo.AngleCongruent
        C P R3
        E Q F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E Q F
      C P R3
      hEQF_CPR3

  have hThird :
      Geo.AngleCongruent
        R2 R K
        E Q F :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      R2 R K
      C P R3
      E Q F
      hThirdNorm
      hCPR3_EQF

  --------------------------------------------------------------------
  -- Trihedral properness in the cyclic order R; K,C,R2.
  --------------------------------------------------------------------

  have hKRC :
      Not (PrimCollinear Geo K R C) := by
    intro hCol
    apply hRKC
    rcases hCol with
      ⟨l, hKl, hRl, hCl⟩
    exact ⟨l, hRl, hKl, hCl⟩

  have hCRR2 :
      Not (PrimCollinear Geo C R R2) := by
    intro hCol
    apply hRCR2
    rcases hCol with
      ⟨l, hCl, hRl, hR2l⟩
    exact ⟨l, hRl, hCl, hR2l⟩

  have hR2RK :
      Not (PrimCollinear Geo R2 R K) := by
    intro hCol
    apply hRR2K
    rcases hCol with
      ⟨l, hR2l, hRl, hKl⟩
    exact ⟨l, hRl, hR2l, hKl⟩

  have hNoCoplanar :
      Not
        (exists omega : S.Plane,
          S.OnPlane R omega /\
          S.OnPlane K omega /\
          S.OnPlane C omega /\
          S.OnPlane R2 omega) := by
    rintro
      ⟨omega,
       hRomega,
       hKomega,
       hComega,
       hR2omega⟩

    have homega_pi :
        omega = pi :=
      HilbertSpaceIncidence.plane_unique
        (Geo := Geo)
        C R2 K
        hCR2K
        omega pi
        hComega hR2omega hKomega
        hCpi hR2pi hKpi

    rw [homega_pi] at hRomega
    exact hRoff hRomega

  have hTri :
      HilbertTrihedralConfiguration
        Geo R K C R2 :=
    ⟨hKRC,
      hCRR2,
      hR2RK,
      hNoCoplanar⟩

  --------------------------------------------------------------------
  -- Package the neutral XI.23 target.
  --------------------------------------------------------------------

  have hRealizes :
      HilbertTrihedralRealizesThreeAngles
        Geo
        R K C R2
        A O B
        C P D
        E Q F :=
    hilbertTrihedralRealizesThreeAngles_intro
      Geo
      R K C R2
      A O B C P D E Q F
      hTri
      hFirst
      hSecond
      hThird

  exact
    hilbertThreeAnglesHaveTrihedralRealization_intro
      Geo
      A O B C P D E Q F
      R K C R2
      hRealizes

end Geometry

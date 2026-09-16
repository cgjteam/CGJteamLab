import CGJteamLab.HilbertAngleChordSum
import CGJteamLab.Proposition22

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.22 -- dimension-free Hilbert route

Given three proper plane angles such that the sum of any two is
greater than the remaining angle, and equal radial sides containing
the three angles, the three opposite chords satisfy the triangle
inequalities. Euclid I.22 then constructs a triangle having those
three chords as its sides.

This theorem is entirely planar. It uses no spatial incidence,
no trihedral-angle structure, and no dimension-specific axiom.
-/

/--
Euclid XI.22.

The three angles are

    angle AOB,
    angle CPD,
    angle EQF.

All six radial sides have one common length, represented by OA:

    OA ~= OB,
    OA ~= PC,
    OA ~= PD,
    OA ~= QE,
    OA ~= QF.

The hypotheses `h12_3`, `h23_1`, `h31_2` express respectively

    angle AOB + angle CPD > angle EQF,
    angle CPD + angle EQF > angle AOB,
    angle EQF + angle AOB > angle CPD.

The conclusion constructs a point K such that triangle CDK has
side CK congruent to chord AB and side DK congruent to chord EF.
Its third side is the given chord CD.
-/
theorem euclid_proposition_11_22
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
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
    (hOA_OB :
      Geo.Congruent O A O B)
    (hOA_PC :
      Geo.Congruent O A P C)
    (hOA_PD :
      Geo.Congruent O A P D)
    (hOA_QE :
      Geo.Congruent O A Q E)
    (hOA_QF :
      Geo.Congruent O A Q F) :
    exists K : Geo.Point,
      Geo.Congruent C K A B /\
      Geo.Congruent D K E F := by

  --------------------------------------------------------------------
  -- Properness and non-nullity of the three chords.
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

  have hAB :
      Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo
      A B O
      (by
        intro h
        exact
          hAOB
            (PrimCollinearRotate
              Geo A B O h))

  have hCD :
      Not (C = D) :=
    hilbert_noncollinear_ne_first
      Geo
      C D P
      (by
        intro h
        exact
          hCPD
            (PrimCollinearRotate
              Geo C D P h))

  have hEF :
      Not (E = F) :=
    hilbert_noncollinear_ne_first
      Geo
      E F Q
      (by
        intro h
        exact
          hEQF
            (PrimCollinearRotate
              Geo E F Q h))

  --------------------------------------------------------------------
  -- First triangle inequality:
  --
  --     AB + CD > EF.
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

  --------------------------------------------------------------------
  -- Rebase the common radius at PC for
  --
  --     CD + EF > AB.
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

  --------------------------------------------------------------------
  -- Rebase the common radius at QE for
  --
  --     EF + AB > CD.
  --------------------------------------------------------------------

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

  have hCD_lt_ABEF :
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

  --------------------------------------------------------------------
  -- Euclid I.22 applied to the three chords AB, CD, EF.
  --------------------------------------------------------------------

  exact
    euclid_proposition_22
      Geo
      A B
      C D
      E F
      hAB
      hCD
      hEF
      hAB_lt_CDEF
      hCD_lt_ABEF
      hEF_lt_ABCD

end Geometry

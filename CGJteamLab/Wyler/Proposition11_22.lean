import CGJteamLab.HilbertAngleChordSum
import CGJteamLab.Proposition22

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.22 -- Hilbert-Wyler route

This is the Wyler-side entry point for Euclid XI.22.

Unlike XI.20 and XI.21, proposition XI.22 is entirely planar.  Its proof
uses only the neutral dimension-free chord comparison developed in

    HilbertAngleChordSum.lean

together with Euclid I.22.

Accordingly, no Wyler-specific spatial axiom is required here.  In
particular this file does not use:

* `HilbertSpacePrimitive`,
* `HilbertWylerAxioms`,
* Wyler I.7,
* Smith I.5,
* any ambient dimension bound.

The proof is independent of `CGJteamLab.Proposition11_22`: both public
entry points use the same neutral planar core, but neither calls the
other.
-/

/--
Euclid XI.22 in the Hilbert-Wyler route.

The three angles are

    angle AOB,
    angle CPD,
    angle EQF.

All six radial sides have one common length represented by OA.

The three hypotheses `h12_3`, `h23_1`, `h31_2` state that the sum of
each pair of angles is greater than the remaining angle in the
synthetic relation `HilbertTwoAnglesGreaterThanAngle`.

The conclusion constructs a triangle CDK whose remaining two sides
are congruent to chords AB and EF.
-/
theorem euclid_proposition_11_22_wyler
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
  -- The three source angles are proper, hence the three chords
  -- are non-null.
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
  -- AB + CD > EF.
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
  -- Rebase the common radius at PC and obtain CD + EF > AB.
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
  -- Rebase the common radius at QE and obtain EF + AB > CD.
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
  -- Euclid I.22 constructs the triangle from the three chords.
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

import CGJteamLab.Proposition31
import CGJteamLab.Proposition34
import CGJteamLab.Proposition47

namespace Geometry

universe u
variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid II.9: permanent construction layer for the oriented case
-- A-C-D-B.  This is the source-faithful promotion of tests 01-13.
------------------------------------------------------------------------

/--
At the endpoint A of AC, erect a perpendicular AD and copy the
prescribed segment PQ onto AD.  This is the I.11 + I.3 construction
used in Euclid II.9.
-/
theorem proposition2_9_erect_perpendicular
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A C P Q : Geo.Point)
    (hAC : A ≠ C) :
    ∃ D : Geo.Point,
      Not (Collinear Geo D A C) ∧
      HilbertRightAngle Geo D A C ∧
      Geo.Congruent A D P Q := by

  have hCA : C ≠ A := hAC.symm

  rcases
      ExtendSegmentBeyond
        Geo C A hCA with
    ⟨F, hCAF, _hCongCA⟩

  rcases
      hilbert_right_angle_exists_nondegenerate
        Geo C A F hCAF with
    ⟨X, hNCCAX, hRightCAX⟩

  have hAX : A ≠ X := by
    intro hEq
    subst hEq
    rcases
        HilbertPlaneIncidence.line_through
          C A hCA with
      ⟨l, hCl, hAl⟩
    exact hNCCAX ⟨l, hCl, hAl, hAl⟩

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo) P Q A X hAX with
    ⟨D, hRayAXD, hCongAD⟩

  have hDA : D ≠ A :=
    hRayAXD.2.1

  have hADX :
      Collinear Geo A D X :=
    PrimCollinearRotate
      Geo A X D hRayAXD.2.2.1

  have hNCCAD :
      Not (Collinear Geo C A D) := by
    intro hCol
    apply hNCCAX
    exact
      hilbert_primCollinear_trans
        Geo C A D X
        hDA.symm
        hCol
        hADX

  have hNCDAC :
      Not (Collinear Geo D A C) := by
    intro hCol
    exact
      hNCCAD
        (PrimCollinearSymm Geo D A C hCol)

  have hAngleEq :
      Geo.Angle C A X = Geo.Angle C A D :=
    hilbert_angle_eq_of_sameRay_second
      Geo A C X D hRayAXD

  have hRefl :
      Geo.AngleCongruent C A X C A X :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo) C A X hNCCAX

  have hAngleCAX_CAD :
      Geo.AngleCongruent C A X C A D := by
    unfold Geometry.Geo.AngleCongruent
    rw [← hAngleEq]
    exact hRefl

  have hRightCAD :
      HilbertRightAngle Geo C A D :=
    hilbert_right_angle_transport
      Geo
      C A X
      C A D
      hNCCAX
      hNCCAD
      hRightCAX
      hAngleCAX_CAD

  have hArmSwap :
      Geo.AngleCongruent C A D D A C :=
    bookZero_56_ABCequalsCBA
      Geo C A D hNCCAD

  have hRightDAC :
      HilbertRightAngle Geo D A C :=
    hilbert_right_angle_transport
      Geo
      C A D
      D A C
      hNCCAD
      hNCDAC
      hRightCAD
      hArmSwap

  exact ⟨D, hNCDAC, hRightDAC, hCongAD⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 01.

Configuration skeleton for the standard branch

  A -- C -- D -- B

where C is the midpoint of AB and D is the unequal cut point on the
right half CB.

At this stage we only normalize the midpoint data. No perpendicular,
parallel, square, or Pythagorean content is introduced yet.
-/
theorem proposition2_9_data
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    Geo.Between A C B /\
    Geo.Between C D B /\
    Geo.Congruent A C C B /\
    Geo.Congruent C A C B := by

  have hACB : Geo.Between A C B :=
    hMidC.1

  have hAC_CB : Geo.Congruent A C C B :=
    hMidC.2

  have hCA_CB : Geo.Congruent C A C B :=
    CongruentReverseFirst
      Geo A C C B hAC_CB

  exact
    And.intro hACB
      (And.intro hCDB
        (And.intro hAC_CB hCA_CB))

------------------------------------------------------------------------

/--
Euclid II.9 -- test 02.

In the standard configuration

  A -- C -- D -- B

with C the midpoint of AB, erect at C a perpendicular to the carrier
CB and lay off on it a segment CE congruent to AC.

This packages the classical I.11 + I.3 construction needed at the
beginning of II.9.
-/
theorem proposition2_9_perpendicular_equal_half
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (_hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E : Geo.Point,
      Not (Collinear Geo E C B) /\
      HilbertRightAngle Geo E C B /\
      Geo.Congruent C E A C := by

  --------------------------------------------------------------------
  -- C and B are distinct because C-D-B.
  --------------------------------------------------------------------

  have hCDBdata :=
    HilbertOrder.between_incidence
      C D B hCDB

  have hCB : C ≠ B :=
    hCDBdata.2.2.1

  --------------------------------------------------------------------
  -- Reuse the general I.11/I.3 helper from Proposition I.48:
  --
  --   vertex        A -> C
  --   carrier point C -> B
  --   copied segment PQ -> AC.
  --------------------------------------------------------------------

  exact
    proposition2_9_erect_perpendicular
      Geo
      C B
      A C
      hCB

------------------------------------------------------------------------

/--
Euclid II.9 -- test 03.

Construct a nondegenerate perpendicular direction CX at the midpoint C,
then lay off on the ray CX a point E such that CE is congruent to CA.

At this stage we retain the SameRay data explicitly; transport of the
right angle from X to E is postponed to the next test.
-/
theorem proposition2_9_layoff_equal_half
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (_hCDB : Geo.Between C D B) :
    exists X E : Geo.Point,
      Not (Collinear Geo A C X) /\
      HilbertRightAngle Geo A C X /\
      HilbertSameRay Geo C X E /\
      Geo.Congruent C E C A := by

  have hACB : Geo.Between A C B :=
    hMidC.1

  have hACBdata :=
    HilbertOrder.between_incidence
      A C B hACB

  have hAC : A ≠ C :=
    hACBdata.1

  rcases
      hilbert_right_angle_exists_nondegenerate
        Geo A C B hACB with
    ⟨X, hACX, hRightACX⟩

  have hCX : C ≠ X := by
    intro hEq
    subst X
    rcases
        HilbertPlaneIncidence.line_through
          A C hAC with
      ⟨l, hAl, hCl⟩
    exact hACX ⟨l, hAl, hCl, hCl⟩

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        C A C X hCX with
    ⟨E, hRayCXE, hCE_CA⟩

  exact
    ⟨X, E,
      hACX,
      hRightACX,
      hRayCXE,
      hCE_CA⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 04.

Eliminate the temporary perpendicular-direction point X.

From
  * ACX right,
  * E on the same ray from C as X,
  * CE congruent CA,

deduce directly that ACE is right and retain the equal perpendicular
segment CE.
-/
theorem proposition2_9_equal_perpendicular
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E : Geo.Point,
      Not (Collinear Geo A C E) /\
      HilbertRightAngle Geo A C E /\
      Geo.Congruent C E C A := by

  rcases
      proposition2_9_layoff_equal_half
        Geo A B C D hMidC hCDB with
    ⟨X, E, hACX, hRightACX, hRayCXE, hCE_CA⟩

  have hEC : Not (E = C) :=
    hRayCXE.2.1

  have hCE : Not (C = E) :=
    Ne.symm hEC

  have hCXE :
      Collinear Geo C X E :=
    hRayCXE.2.2.1

  have hCEX :
      Collinear Geo C E X :=
    PrimCollinearRotate
      Geo C X E hCXE

  have hACE :
      Not (Collinear Geo A C E) := by
    intro hACEcol

    have hACXcol :
        Collinear Geo A C X :=
      hilbert_primCollinear_trans
        Geo A C E X
        hCE
        hACEcol
        hCEX

    exact hACX hACXcol

  have hAngleEq :
      Geo.Angle A C X =
      Geo.Angle A C E :=
    hilbert_angle_eq_of_sameRay_second
      Geo C A X E hRayCXE

  have hAngleRefl :
      Geo.AngleCongruent
        A C X
        A C X :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A C X
      hACX

  have hAngle :
      Geo.AngleCongruent
        A C X
        A C E := by

    unfold Geometry.Geo.AngleCongruent
      at hAngleRefl ⊢

    rw [← hAngleEq]

    exact hAngleRefl

  have hRightACE :
      HilbertRightAngle Geo A C E :=
    hilbert_right_angle_transport
      Geo
      A C X
      A C E
      hACX
      hACE
      hRightACX
      hAngle

  exact
    ⟨E,
      hACE,
      hRightACE,
      hCE_CA⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 05.

Normalize the constructed perpendicular segment against the right half CB.

From C being the midpoint of AB we have CA congruent CB.
Together with CE congruent CA this gives CE congruent CB.
-/
theorem proposition2_9_equal_to_right_half
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E : Geo.Point,
      Not (Collinear Geo A C E) /\
      HilbertRightAngle Geo A C E /\
      Geo.Congruent C E C B := by

  rcases
      proposition2_9_equal_perpendicular
        Geo A B C D hMidC hCDB with
    ⟨E, hACE, hRightACE, hCE_CA⟩

  have hCA_CB :
      Geo.Congruent C A C B :=
    CongruentReverseFirst
      Geo A C C B hMidC.2

  have hCE_CB :
      Geo.Congruent C E C B :=
    hilbert_congruent_transitivity
      Geo
      C E
      C A
      C B
      hCE_CA
      hCA_CB

  exact
    ⟨E,
      hACE,
      hRightACE,
      hCE_CB⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 06.

Normalize the order to A-C-D-B and transfer the perpendicularity from
the ray CA to its opposite ray CD.

Thus the constructed segment CE is perpendicular also to CD.
-/
theorem proposition2_9_right_angle_at_D_side
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E : Geo.Point,
      Geo.Between A C D /\
      Not (Collinear Geo D C E) /\
      HilbertRightAngle Geo D C E /\
      Geo.Congruent C E C B := by

  rcases
      proposition2_9_equal_to_right_half
        Geo A B C D hMidC hCDB with
    ⟨E, hACE, hRightACE, hCE_CB⟩

  have hACB : Geo.Between A C B :=
    hMidC.1

  have hBDC : Geo.Between B D C :=
    (HilbertOrder.between_incidence
      C D B hCDB).2.2.2.2

  have hBCA : Geo.Between B C A :=
    (HilbertOrder.between_incidence
      A C B hACB).2.2.2.2

  have hDCA : Geo.Between D C A :=
    (hilbert_between_inner_trans
      Geo B D C A hBDC hBCA).1

  have hACD : Geo.Between A C D :=
    (HilbertOrder.between_incidence
      D C A hDCA).2.2.2.2

  have hCD : Not (C = D) :=
    (HilbertOrder.between_incidence
      C D B hCDB).1

  have hACDcol : Collinear Geo A C D :=
    (HilbertOrder.between_incidence
      A C D hACD).2.2.2.1

  have hDCE :
      Not (Collinear Geo D C E) := by
    intro hDCEcol

    have hCDE : Collinear Geo C D E :=
      PrimCollinearSwap
        Geo D C E hDCEcol

    have hACEcol : Collinear Geo A C E :=
      hilbert_primCollinear_trans
        Geo A C D E
        hCD
        hACDcol
        hCDE

    exact hACE hACEcol

  have hACE_ECD :
      Geo.AngleCongruent A C E E C D :=
    hilbert_right_angle_opposite_extension
      Geo
      A C E D
      hACE
      hRightACE
      hACD

  have hACE_DCE :
      Geo.AngleCongruent A C E D C E :=
    (Geo.angle_congruent_reverse_second
      A C E
      E C D).mp hACE_ECD

  have hRightDCE :
      HilbertRightAngle Geo D C E :=
    hilbert_right_angle_transport
      Geo
      A C E
      D C E
      hACE
      hDCE
      hRightACE
      hACE_DCE

  exact
    ⟨E,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 07.

Through D construct the line parallel to CE.

This is exactly Euclid I.31 applied to the noncollinear triple C,E,D.
The resulting point F satisfies DF parallel CE.
-/
theorem proposition2_9_parallel_through_D
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E F : Geo.Point,
      Geo.Between A C D /\
      Not (Collinear Geo D C E) /\
      HilbertRightAngle Geo D C E /\
      Geo.Congruent C E C B /\
      Not (D = F) /\
      Geo.Parallel C E D F := by

  rcases
      proposition2_9_right_angle_at_D_side
        Geo A B C D hMidC hCDB with
    ⟨E, hACD, hDCE, hRightDCE, hCE_CB⟩

  have hCD : Not (C = D) :=
    (HilbertOrder.between_incidence
      C D B hCDB).1

  have hCED :
      Not (Collinear Geo C E D) := by
    intro hCEDcol
    have hEDC :
        Collinear Geo E D C :=
      PrimCollinearCycle
        Geo C E D hCEDcol
    have hDCEcol :
        Collinear Geo D C E :=
      PrimCollinearCycle
        Geo E D C hEDC
    exact hDCE hDCEcol

  have hCE : Not (C = E) := by
    intro hEq
    subst E
    rcases
        HilbertPlaneIncidence.line_through
          C D hCD with
      ⟨l, hCl, hDl⟩
    exact hCED
      ⟨l, hCl, hCl, hDl⟩

  rcases
      euclid_proposition_31
        C E D
        hCE
        hCED with
    ⟨F, hDF, hParCE_DF⟩

  exact
    ⟨E, F,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hDF,
      hParCE_DF⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 08.

Let DQ be the parallel through D to CE constructed in test 07.
Its carrier must meet the carrier EB.

If EB and DQ were disjoint, then EB || DQ.  Since CE || DQ as well,
Euclidean parallel transitivity would force EB || CE, impossible because
the two carriers share E.
-/
theorem proposition2_9_intersection_with_EB
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E Q F : Geo.Point,
      Geo.Between A C D /\
      Not (Collinear Geo D C E) /\
      HilbertRightAngle Geo D C E /\
      Geo.Congruent C E C B /\
      Geo.Parallel C E D Q /\
      Collinear Geo D Q F /\
      Collinear Geo E B F := by

  rcases
      proposition2_9_parallel_through_D
        Geo A B C D hMidC hCDB with
    ⟨E, Q,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hDQ,
      hParCE_DQ⟩

  have hCDBdata :=
    HilbertOrder.between_incidence
      C D B hCDB

  have hCB : Not (C = B) :=
    hCDBdata.2.2.1

  have hCDBcol :
      Collinear Geo C D B :=
    hCDBdata.2.2.2.1

  have hDCBcol :
      Collinear Geo D C B := by
    rcases hCDBcol with
      ⟨base, hCbase, hDbase, hBbase⟩
    exact
      ⟨base, hDbase, hCbase, hBbase⟩

  have hBCE :
      Not (Collinear Geo B C E) := by
    intro hBCEcol

    have hCBEcol :
        Collinear Geo C B E :=
      PrimCollinearSwap
        Geo B C E hBCEcol

    have hDCEcol :
        Collinear Geo D C E :=
      hilbert_primCollinear_trans
        Geo D C B E
        hCB
        hDCBcol
        hCBEcol

    exact hDCE hDCEcol

  have hEB : Not (E = B) := by
    intro hEq
    subst E

    have hBCB :
        Collinear Geo B C B := by
      rcases
          HilbertPlaneIncidence.line_through
            C B hCB with
        ⟨base, hCbase, hBbase⟩
      exact
        ⟨base, hBbase, hCbase, hBbase⟩

    exact hBCE hBCB

  have hCE : Not (C = E) :=
    hParCE_DQ.1

  rcases
      HilbertPlaneIncidence.line_through
        E B hEB with
    ⟨lineEB, hEeb, hBeb⟩

  rcases
      HilbertPlaneIncidence.line_through
        D Q hDQ with
    ⟨lineDQ, hDdq, hQdq⟩

  rcases
      HilbertPlaneIncidence.line_through
        C E hCE with
    ⟨lineCE, hCce, hEce⟩

  have hMeet :
      HilbertLinesMeet Geo lineEB lineDQ := by

    by_contra hDisjoint

    have hParEB_DQ :
        Geo.Parallel E B D Q :=
      intersection_test_parallel_of_lines_disjoint
        Geo
        E B D Q
        lineEB lineDQ
        hEB hDQ
        hEeb hBeb
        hDdq hQdq
        hDisjoint

    have hDistinct :
        Not
          (Geo.PointLine E B =
           Geo.PointLine C E) := by

      intro hSame

      have hB_EB :
          B ∈ Geo.PointLine E B :=
        intersection_test_right_mem
          Geo E B

      have hB_CE :
          B ∈ Geo.PointLine C E := by
        rw [← hSame]
        exact hB_EB

      have hBce :
          HilbertIncidence.OnLine B lineCE :=
        (hilbert_mem_pointLine_iff_onLine
          Geo
          C E B
          lineCE
          hCE
          hCce
          hEce).mp hB_CE

      exact hBCE
        ⟨lineCE,
          hBce,
          hCce,
          hEce⟩

    have hParEB_CE :
        Geo.Parallel E B C E :=
      hilbert_parallel_transitive_distinct
        Geo
        E B
        C E
        D Q
        hParEB_DQ
        hParCE_DQ
        hDistinct

    exact
      (intersection_test_not_parallel_of_common_point
        Geo
        E B
        C E
        E
        (intersection_test_left_mem Geo E B)
        (intersection_test_right_mem Geo C E))
        hParEB_CE

  rcases hMeet with
    ⟨F, hFeb, hFdq⟩

  have hEBF :
      Collinear Geo E B F :=
    ⟨lineEB,
      hEeb,
      hBeb,
      hFeb⟩

  have hDQF :
      Collinear Geo D Q F :=
    ⟨lineDQ,
      hDdq,
      hQdq,
      hFdq⟩

  exact
    ⟨E, Q, F,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hParCE_DQ,
      hDQF,
      hEBF⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 09.

Normalize the intersection construction from test 08.

The auxiliary point Q only served to construct the parallel through D.
Once F is known to lie on both DQ and EB, prove F != D and transport
the parallel along the common carrier to obtain the classical datum

  CE || DF

with E,B,F collinear.
-/
theorem proposition2_9_classical_DF
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E F : Geo.Point,
      Geo.Between A C D /\
      Not (Collinear Geo D C E) /\
      HilbertRightAngle Geo D C E /\
      Geo.Congruent C E C B /\
      Not (D = F) /\
      Geo.Parallel C E D F /\
      Collinear Geo E B F := by

  rcases
      proposition2_9_intersection_with_EB
        Geo A B C D hMidC hCDB with
    ⟨E, Q, F,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hParCE_DQ,
      hDQF,
      hEBF⟩

  have hCDBdata :=
    HilbertOrder.between_incidence
      C D B hCDB

  have hDB : Not (D = B) :=
    hCDBdata.2.1

  have hCDBcol :
      Collinear Geo C D B :=
    hCDBdata.2.2.2.1

  have hDF : Not (D = F) := by
    intro hEq
    subst F

    have hDBE :
        Collinear Geo D B E :=
      PrimCollinearSymm
        Geo E B D hEBF

    have hCDE :
        Collinear Geo C D E :=
      hilbert_primCollinear_trans
        Geo C D B E
        hDB
        hCDBcol
        hDBE

    have hDCEcol :
        Collinear Geo D C E :=
      PrimCollinearSwap
        Geo C D E hCDE

    exact hDCE hDCEcol

  have hDFQ :
      Collinear Geo D F Q := by
    rcases hDQF with
      ⟨lineDQ, hDdq, hQdq, hFdq⟩
    exact
      ⟨lineDQ, hDdq, hFdq, hQdq⟩

  have hDQ_CE :
      Geo.Parallel D Q C E :=
    ParallelSymmetry
      Geo C E D Q hParCE_DQ

  have hDF_CE :
      Geo.Parallel D F C E :=
    collinear_parallel_trans
      Geo
      D F Q
      C E
      hDF
      hDFQ
      hDQ_CE

  have hCE_DF :
      Geo.Parallel C E D F :=
    ParallelSymmetry
      Geo D F C E hDF_CE

  exact
    ⟨E, F,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hDF,
      hCE_DF,
      hEBF⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 10.

Complete D-F-?-C to a parallelogram D-F-G-C.

Then
  DF || GC
and
  FG || CD.

Since CE || DF already, the two carriers GC and CE are parallel to the
same line DF and both pass through C.  Euclidean uniqueness therefore
forces them to coincide, so E,C,G are collinear.

This is the formal version of drawing FG through F parallel to the base,
with G on CE.
-/
theorem proposition2_9_construct_G
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E F G : Geo.Point,
      Geo.Between A C D /\
      Not (Collinear Geo D C E) /\
      HilbertRightAngle Geo D C E /\
      Geo.Congruent C E C B /\
      Geo.Parallel C E D F /\
      Collinear Geo E B F /\
      IsParallelogram Geo D F G C /\
      Collinear Geo E C G /\
      Geo.Parallel F G C D := by

  rcases
      proposition2_9_classical_DF
        Geo A B C D hMidC hCDB with
    ⟨E, F,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hDF,
      hCE_DF,
      hEBF⟩

  have hCE : Not (C = E) :=
    hCE_DF.1

  have hDFC :
      Not (Collinear Geo D F C) := by
    intro hDFCcol

    rcases hDFCcol with
      ⟨lineDF, hDdf, hFdf, hCdf⟩

    have hC_DF :
        C ∈ Geo.PointLine D F :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D F C
        lineDF
        hDF
        hDdf
        hFdf).mpr hCdf

    exact
      (intersection_test_not_parallel_of_common_point
        Geo
        C E
        D F
        C
        (intersection_test_left_mem Geo C E)
        hC_DF)
        hCE_DF

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo D F C hDFC with
    ⟨G, hParDFGC⟩

  have hGC_DF :
      Geo.Parallel G C D F :=
    ParallelSymmetry
      Geo D F G C hParDFGC.1

  have hCarrier :
      Geo.PointLine G C =
      Geo.PointLine C E := by

    by_contra hDistinct

    have hGC_CE :
        Geo.Parallel G C C E :=
      hilbert_parallel_transitive_distinct
        Geo
        G C
        C E
        D F
        hGC_DF
        hCE_DF
        hDistinct

    exact
      (intersection_test_not_parallel_of_common_point
        Geo
        G C
        C E
        C
        (intersection_test_right_mem Geo G C)
        (intersection_test_left_mem Geo C E))
        hGC_CE

  rcases
      HilbertPlaneIncidence.line_through
        C E hCE with
    ⟨lineCE, hCce, hEce⟩

  have hG_GC :
      G ∈ Geo.PointLine G C :=
    intersection_test_left_mem
      Geo G C

  have hG_CE :
      G ∈ Geo.PointLine C E := by
    rw [← hCarrier]
    exact hG_GC

  have hGce :
      HilbertIncidence.OnLine G lineCE :=
    (hilbert_mem_pointLine_iff_onLine
      Geo
      C E G
      lineCE
      hCE
      hCce
      hEce).mp hG_CE

  have hECG :
      Collinear Geo E C G :=
    ⟨lineCE,
      hEce,
      hCce,
      hGce⟩

  have hFG_CD :
      Geo.Parallel F G C D :=
    hParDFGC.2

  exact
    ⟨E, F, G,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hCE_DF,
      hEBF,
      hParDFGC,
      hECG,
      hFG_CD⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 11.

Extract the metric content of the auxiliary parallelogram D-F-G-C.

By Euclid I.34, opposite sides of a parallelogram are congruent:

  DF ~= GC
  FG ~= CD.

These are the two segment equalities needed in the next order/subtraction
stage of the II.9 construction.
-/
theorem proposition2_9_parallelogram_sides
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E F G : Geo.Point,
      Geo.Between A C D /\
      Not (Collinear Geo D C E) /\
      HilbertRightAngle Geo D C E /\
      Geo.Congruent C E C B /\
      Geo.Parallel C E D F /\
      Collinear Geo E B F /\
      IsParallelogram Geo D F G C /\
      Collinear Geo E C G /\
      Geo.Congruent D F G C /\
      Geo.Congruent F G C D := by

  rcases
      proposition2_9_construct_G
        Geo A B C D hMidC hCDB with
    ⟨E, F, G,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hCE_DF,
      hEBF,
      hParDFGC,
      hECG,
      _hFG_CD_parallel⟩

  have h34 :=
    euclid_proposition_34
      Geo D F G C hParDFGC

  have hSides :
      OppositeSidesCongruent Geo D F G C :=
    h34.1

  have hDF_GC :
      Geo.Congruent D F G C :=
    hSides.1

  have hFG_CD :
      Geo.Congruent F G C D :=
    hSides.2

  exact
    ⟨E, F, G,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hCE_DF,
      hEBF,
      hParDFGC,
      hECG,
      hDF_GC,
      hFG_CD⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 12.

Locate the intersection point F on the open side EB.

In triangle B-C-E, the line DF enters through D on the open side BC.
Because DF is parallel to CE, it cannot meet the open side CE.
Forced Pasch therefore gives an intersection X on the open side BE.

The already constructed point F lies on both DF and EB.  Uniqueness of
the intersection of these two distinct carriers identifies X with F.
Hence E-F-B.
-/
theorem proposition2_9_F_between_EB
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E F G : Geo.Point,
      Geo.Between E F B /\
      Geo.Between A C D /\
      Not (Collinear Geo D C E) /\
      HilbertRightAngle Geo D C E /\
      Geo.Congruent C E C B /\
      Geo.Parallel C E D F /\
      IsParallelogram Geo D F G C /\
      Collinear Geo E C G /\
      Geo.Congruent D F G C /\
      Geo.Congruent F G C D := by

  rcases
      proposition2_9_parallelogram_sides
        Geo A B C D hMidC hCDB with
    ⟨E, F, G,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hCE_DF,
      hEBF,
      hParDFGC,
      hECG,
      hDF_GC,
      hFG_CD⟩

  have hCDBdata :=
    HilbertOrder.between_incidence
      C D B hCDB

  have hCD : Not (C = D) :=
    hCDBdata.1

  have hDB : Not (D = B) :=
    hCDBdata.2.1

  have hCB : Not (C = B) :=
    hCDBdata.2.2.1

  have hCDBcol :
      Collinear Geo C D B :=
    hCDBdata.2.2.2.1

  have hBDC :
      Geo.Between B D C :=
    hCDBdata.2.2.2.2

  have hDF : Not (D = F) :=
    hCE_DF.2.1

  have hCE : Not (C = E) :=
    hCE_DF.1

  --------------------------------------------------------------------
  -- Triangle B-C-E is nondegenerate.
  --------------------------------------------------------------------

  have hBCE :
      Not (Collinear Geo B C E) := by
    intro hBCEcol

    have hCBE :
        Collinear Geo C B E :=
      PrimCollinearSwap
        Geo B C E hBCEcol

    have hDCB :
        Collinear Geo D C B := by
      rcases hCDBcol with
        ⟨base, hCbase, hDbase, hBbase⟩
      exact
        ⟨base, hDbase, hCbase, hBbase⟩

    have hDCEcol :
        Collinear Geo D C E :=
      hilbert_primCollinear_trans
        Geo
        D C B E
        hCB
        hDCB
        hCBE

    exact hDCE hDCEcol

  --------------------------------------------------------------------
  -- Choose explicit carriers DF, CE, and EB.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        D F hDF with
    ⟨lineDF, hDdf, hFdf⟩

  rcases
      HilbertPlaneIncidence.line_through
        C E hCE with
    ⟨lineCE, hCce, hEce⟩

  rcases hEBF with
    ⟨lineEB, hEeb, hBeb, hFeb⟩

  --------------------------------------------------------------------
  -- The three vertices B,C,E of the triangle are off DF.
  --------------------------------------------------------------------

  have hCoff :
      Not (HilbertIncidence.OnLine C lineDF) := by
    intro hCdf

    have hC_DF :
        C ∈ Geo.PointLine D F :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D F C
        lineDF
        hDF
        hDdf
        hFdf).mpr hCdf

    exact
      Set.disjoint_left.mp hCE_DF.2.2
        (intersection_test_left_mem Geo C E)
        hC_DF

  have hEoff :
      Not (HilbertIncidence.OnLine E lineDF) := by
    intro hEdf

    have hE_DF :
        E ∈ Geo.PointLine D F :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D F E
        lineDF
        hDF
        hDdf
        hFdf).mpr hEdf

    exact
      Set.disjoint_left.mp hCE_DF.2.2
        (intersection_test_right_mem Geo C E)
        hE_DF

  have hBoff :
      Not (HilbertIncidence.OnLine B lineDF) := by
    intro hBdf

    have hDBC :
        Collinear Geo D B C :=
      PrimCollinearCycle
        Geo C D B hCDBcol

    have hCdf :
        HilbertIncidence.OnLine C lineDF :=
      hilbert_collinear_on_line
        Geo
        D B C
        lineDF
        hDB
        hDdf
        hBdf
        hDBC

    exact hCoff hCdf

  --------------------------------------------------------------------
  -- DF enters triangle B-C-E through D on BC.
  --------------------------------------------------------------------

  have hMeetsBC :
      HilbertSegmentMeetsLine Geo B C lineDF :=
    ⟨D, hBDC, hDdf⟩

  --------------------------------------------------------------------
  -- DF cannot meet the open side CE because DF || CE.
  --------------------------------------------------------------------

  have hNotMeetsCE :
      Not (HilbertSegmentMeetsLine Geo C E lineDF) := by
    rintro ⟨X, hCXE, hXdf⟩

    have hXce :
        HilbertIncidence.OnLine X lineCE :=
      hilbert_between_on_line
        Geo
        C X E
        lineCE
        hCce
        hEce
        hCXE

    have hX_CE :
        X ∈ Geo.PointLine C E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        C E X
        lineCE
        hCE
        hCce
        hEce).mpr hXce

    have hX_DF :
        X ∈ Geo.PointLine D F :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D F X
        lineDF
        hDF
        hDdf
        hFdf).mpr hXdf

    exact
      Set.disjoint_left.mp hCE_DF.2.2
        hX_CE
        hX_DF

  --------------------------------------------------------------------
  -- Forced Pasch gives an interior intersection X on BE.
  --------------------------------------------------------------------

  have hMeetsBE :
      HilbertSegmentMeetsLine Geo B E lineDF :=
    hilbert_pasch_forced
      Geo
      B C E
      lineDF
      hBCE
      hBoff
      hCoff
      hEoff
      hMeetsBC
      hNotMeetsCE

  rcases hMeetsBE with
    ⟨X, hBXE, hXdf⟩

  have hXeb :
      HilbertIncidence.OnLine X lineEB :=
    hilbert_between_on_line
      Geo
      B X E
      lineEB
      hBeb
      hEeb
      hBXE

  --------------------------------------------------------------------
  -- X is the already constructed intersection F of DF and EB.
  --------------------------------------------------------------------

  have hXF : X = F := by
    by_contra hXF

    have hLinesEq :
        lineDF = lineEB :=
      HilbertPlaneIncidence.line_unique
        X F
        hXF
        lineDF lineEB
        hXdf hFdf
        hXeb hFeb

    have hDeb :
        HilbertIncidence.OnLine D lineEB := by
      rw [← hLinesEq]
      exact hDdf

    have hDBE :
        Collinear Geo D B E :=
      ⟨lineEB,
        hDeb,
        hBeb,
        hEeb⟩

    have hCDE :
        Collinear Geo C D E :=
      hilbert_primCollinear_trans
        Geo
        C D B E
        hDB
        hCDBcol
        hDBE

    have hDCEcol :
        Collinear Geo D C E :=
      PrimCollinearSwap
        Geo C D E hCDE

    exact hDCE hDCEcol

  subst X

  have hEFB :
      Geo.Between E F B :=
    (HilbertOrder.between_incidence
      B F E hBXE).2.2.2.2

  exact
    ⟨E, F, G,
      hEFB,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hCE_DF,
      hParDFGC,
      hECG,
      hDF_GC,
      hFG_CD⟩

------------------------------------------------------------------------

/--
Euclid II.9 -- test 13.

Locate G on the open segment CE.

From the auxiliary parallelogram D-F-G-C we have FG || CD.
Since C,D,B are collinear, transport this to FG || CB.

In triangle E-B-C, the line FG enters through F on the open side EB.
It cannot meet the open side BC because FG || CB, so forced Pasch gives
an intersection X on the open side EC.  The already constructed point G
lies on both FG and EC, hence uniqueness of the two-line intersection
identifies X with G.

Therefore C-G-E.
-/
theorem proposition2_9_G_between_CE
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    exists E F G : Geo.Point,
      Geo.Between E F B /\
      Geo.Between C G E /\
      Geo.Between A C D /\
      Not (Collinear Geo D C E) /\
      HilbertRightAngle Geo D C E /\
      Geo.Congruent C E C B /\
      Geo.Parallel C E D F /\
      IsParallelogram Geo D F G C /\
      Geo.Congruent D F G C /\
      Geo.Congruent F G C D := by

  rcases
      proposition2_9_F_between_EB
        Geo A B C D hMidC hCDB with
    ⟨E, F, G,
      hEFB,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hCE_DF,
      hParDFGC,
      hECG,
      hDF_GC,
      hFG_CD⟩

  have hCDBdata :=
    HilbertOrder.between_incidence
      C D B hCDB

  have hCB : Not (C = B) :=
    hCDBdata.2.2.1

  have hCDBcol :
      Collinear Geo C D B :=
    hCDBdata.2.2.2.1

  --------------------------------------------------------------------
  -- Transport FG || CD along the base carrier C-D-B to FG || CB.
  --------------------------------------------------------------------

  have hFG_CD_parallel :
      Geo.Parallel F G C D :=
    hParDFGC.2

  have hCD_FG :
      Geo.Parallel C D F G :=
    ParallelSymmetry
      Geo F G C D hFG_CD_parallel

  have hCBDcol :
      Collinear Geo C B D :=
    PrimCollinearRotate
      Geo C D B hCDBcol

  have hCB_FG :
      Geo.Parallel C B F G :=
    collinear_parallel_trans
      Geo
      C B D
      F G
      hCB
      hCBDcol
      hCD_FG

  have hFG_CB :
      Geo.Parallel F G C B :=
    ParallelSymmetry
      Geo C B F G hCB_FG

  have hFG : Not (F = G) :=
    hFG_CB.1

  --------------------------------------------------------------------
  -- Triangle E-B-C is nondegenerate.
  --------------------------------------------------------------------

  have hBCE :
      Not (Collinear Geo B C E) := by
    intro hBCEcol

    have hCBE :
        Collinear Geo C B E :=
      PrimCollinearSwap
        Geo B C E hBCEcol

    have hDCB :
        Collinear Geo D C B := by
      rcases hCDBcol with
        ⟨base, hCbase, hDbase, hBbase⟩
      exact
        ⟨base, hDbase, hCbase, hBbase⟩

    have hDCEcol :
        Collinear Geo D C E :=
      hilbert_primCollinear_trans
        Geo
        D C B E
        hCB
        hDCB
        hCBE

    exact hDCE hDCEcol

  have hEBC :
      Not (Collinear Geo E B C) := by
    intro hEBCcol
    exact hBCE
      (PrimCollinearCycle
        Geo E B C hEBCcol)

  --------------------------------------------------------------------
  -- Explicit carriers FG, CB, and EC.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        F G hFG with
    ⟨lineFG, hFfg, hGfg⟩

  rcases
      HilbertPlaneIncidence.line_through
        C B hCB with
    ⟨lineCB, hCcb, hBcb⟩

  rcases hECG with
    ⟨lineEC, hEec, hCec, hGec⟩

  have hCE : Not (C = E) :=
    hCE_DF.1

  --------------------------------------------------------------------
  -- B and C are off FG because FG || CB.
  --------------------------------------------------------------------

  have hBoff :
      Not (HilbertIncidence.OnLine B lineFG) := by
    intro hBfg

    have hB_FG :
        B ∈ Geo.PointLine F G :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        F G B
        lineFG
        hFG
        hFfg
        hGfg).mpr hBfg

    exact
      Set.disjoint_left.mp hFG_CB.2.2
        hB_FG
        (intersection_test_right_mem Geo C B)

  have hCoff :
      Not (HilbertIncidence.OnLine C lineFG) := by
    intro hCfg

    have hC_FG :
        C ∈ Geo.PointLine F G :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        F G C
        lineFG
        hFG
        hFfg
        hGfg).mpr hCfg

    exact
      Set.disjoint_left.mp hFG_CB.2.2
        hC_FG
        (intersection_test_left_mem Geo C B)

  --------------------------------------------------------------------
  -- E is also off FG.  Otherwise E and F would put the whole carrier
  -- E-F-B onto FG, contradicting B off FG.
  --------------------------------------------------------------------

  have hEFBdata :=
    HilbertOrder.between_incidence
      E F B hEFB

  have hEF : Not (E = F) :=
    hEFBdata.1

  have hEFBcol :
      Collinear Geo E F B :=
    hEFBdata.2.2.2.1

  have hEoff :
      Not (HilbertIncidence.OnLine E lineFG) := by
    intro hEfg

    have hBfg :
        HilbertIncidence.OnLine B lineFG :=
      hilbert_collinear_on_line
        Geo
        E F B
        lineFG
        hEF
        hEfg
        hFfg
        hEFBcol

    exact hBoff hBfg

  --------------------------------------------------------------------
  -- FG enters triangle E-B-C through F on EB.
  --------------------------------------------------------------------

  have hMeetsEB :
      HilbertSegmentMeetsLine Geo E B lineFG :=
    ⟨F, hEFB, hFfg⟩

  --------------------------------------------------------------------
  -- FG cannot meet the open side BC because FG || CB.
  --------------------------------------------------------------------

  have hNotMeetsBC :
      Not (HilbertSegmentMeetsLine Geo B C lineFG) := by
    rintro ⟨X, hBXC, hXfg⟩

    have hXcb :
        HilbertIncidence.OnLine X lineCB :=
      hilbert_between_on_line
        Geo
        B X C
        lineCB
        hBcb
        hCcb
        hBXC

    have hX_FG :
        X ∈ Geo.PointLine F G :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        F G X
        lineFG
        hFG
        hFfg
        hGfg).mpr hXfg

    have hX_CB :
        X ∈ Geo.PointLine C B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        C B X
        lineCB
        hCB
        hCcb
        hBcb).mpr hXcb

    exact
      Set.disjoint_left.mp hFG_CB.2.2
        hX_FG
        hX_CB

  --------------------------------------------------------------------
  -- Forced Pasch gives an interior intersection X on EC.
  --------------------------------------------------------------------

  have hMeetsEC :
      HilbertSegmentMeetsLine Geo E C lineFG :=
    hilbert_pasch_forced
      Geo
      E B C
      lineFG
      hEBC
      hEoff
      hBoff
      hCoff
      hMeetsEB
      hNotMeetsBC

  rcases hMeetsEC with
    ⟨X, hEXC, hXfg⟩

  have hXec :
      HilbertIncidence.OnLine X lineEC :=
    hilbert_between_on_line
      Geo
      E X C
      lineEC
      hEec
      hCec
      hEXC

  --------------------------------------------------------------------
  -- X is the already constructed point G.
  --------------------------------------------------------------------

  have hXG : X = G := by
    by_contra hXG

    have hLinesEq :
        lineFG = lineEC :=
      HilbertPlaneIncidence.line_unique
        X G
        hXG
        lineFG lineEC
        hXfg hGfg
        hXec hGec

    have hCfg :
        HilbertIncidence.OnLine C lineFG := by
      rw [hLinesEq]
      exact hCec

    exact hCoff hCfg

  subst X

  have hCGE :
      Geo.Between C G E :=
    (HilbertOrder.between_incidence
      E G C hEXC).2.2.2.2

  exact
    ⟨E, F, G,
      hEFB,
      hCGE,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      hCE_DF,
      hParDFGC,
      hDF_GC,
      hFG_CD⟩

end Geometry

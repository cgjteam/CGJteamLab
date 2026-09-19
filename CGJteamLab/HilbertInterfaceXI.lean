import CGJteamLab.HilbertTrihedralAngle
import CGJteamLab.HilbertBookZero
import CGJteamLab.HilbertSegmentSum
import CGJteamLab.HilbertAngleChordSum
import CGJteamLab.HilbertThreeAnglesFourRight
import CGJteamLab.HilbertThreeAnglesFourRightCyclic
import CGJteamLab.HilbertRightAngle
import CGJteamLab.Hilbert3DAngleComparisonTransport
import CGJteamLab.Proposition08
import CGJteamLab.Proposition17
import CGJteamLab.Proposition29
import CGJteamLab.Proposition06
import CGJteamLab.Proposition25
import CGJteamLab.Proposition20

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Hilbert interface for Euclid Book XI

This module collects derived helper results used across the Book XI
formalization.

Policy:

* no new axioms are introduced here;
* proposition-independent planar and spatial helpers belong here once
  their statements and proofs are stable;
* proposition files should import this interface rather than chains of
  small workshop helper modules;
* source-faithful axiom classes remain in their existing foundational
  modules.

The first material consolidated here was developed while formalizing
Euclid XI.23.
-/

/-!
ARCHITECTURE NOTE

This file contains proposition-independent Book XI support only.

Rule:
  reusable mathematics -> HilbertInterfaceXI
  proposition logic    -> Proposition11_23

XI.23-specific case analysis, radius contradiction, and final
construction belong in `Proposition11_23.lean`.
-/



/-!
# Trihedral realization of three prescribed plane angles

Neutral target language for Euclid XI.23.

A realization consists of one proper trihedral configuration

    R; L, M, N

whose three face angles are congruent, in cyclic order, to the three
prescribed plane angles.
-/

/--
A proper trihedral configuration realizes three prescribed plane angles.

The cyclic correspondence is

    angle LRM ~= angle AOB,
    angle MRN ~= angle CPD,
    angle NRL ~= angle EQF.
-/
def HilbertTrihedralRealizesThreeAngles
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (R L M N : Geo.Point)
    (A O B C P D E Q F : Geo.Point) : Prop :=
  HilbertTrihedralConfiguration Geo R L M N /\
  Geo.AngleCongruent L R M A O B /\
  Geo.AngleCongruent M R N C P D /\
  Geo.AngleCongruent N R L E Q F

/--
Existential target of Euclid XI.23.
-/
def HilbertThreeAnglesHaveTrihedralRealization
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (A O B C P D E Q F : Geo.Point) : Prop :=
  exists R L M N : Geo.Point,
    HilbertTrihedralRealizesThreeAngles
      Geo
      R L M N
      A O B
      C P D
      E Q F

/--
Constructor for a realization.
-/
theorem hilbertTrihedralRealizesThreeAngles_intro
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (R L M N : Geo.Point)
    (A O B C P D E Q F : Geo.Point)
    (hTri :
      HilbertTrihedralConfiguration
        Geo R L M N)
    (hFirst :
      Geo.AngleCongruent
        L R M
        A O B)
    (hSecond :
      Geo.AngleCongruent
        M R N
        C P D)
    (hThird :
      Geo.AngleCongruent
        N R L
        E Q F) :
    HilbertTrihedralRealizesThreeAngles
      Geo
      R L M N
      A O B
      C P D
      E Q F := by
  exact
    And.intro hTri
      (And.intro hFirst
        (And.intro hSecond hThird))

/--
Extract the underlying proper trihedral configuration.
-/
theorem hilbertTrihedralRealizesThreeAngles_configuration
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (R L M N : Geo.Point)
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertTrihedralRealizesThreeAngles
        Geo
        R L M N
        A O B
        C P D
        E Q F) :
    HilbertTrihedralConfiguration
      Geo R L M N :=
  h.1

/--
Extract the first realized face angle.
-/
theorem hilbertTrihedralRealizesThreeAngles_first
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (R L M N : Geo.Point)
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertTrihedralRealizesThreeAngles
        Geo
        R L M N
        A O B
        C P D
        E Q F) :
    Geo.AngleCongruent
      L R M
      A O B :=
  h.2.1

/--
Extract the second realized face angle.
-/
theorem hilbertTrihedralRealizesThreeAngles_second
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (R L M N : Geo.Point)
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertTrihedralRealizesThreeAngles
        Geo
        R L M N
        A O B
        C P D
        E Q F) :
    Geo.AngleCongruent
      M R N
      C P D :=
  h.2.2.1

/--
Extract the third realized face angle.
-/
theorem hilbertTrihedralRealizesThreeAngles_third
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (R L M N : Geo.Point)
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertTrihedralRealizesThreeAngles
        Geo
        R L M N
        A O B
        C P D
        E Q F) :
    Geo.AngleCongruent
      N R L
      E Q F :=
  h.2.2.2

/--
Introduction rule for the existential XI.23 target.
-/
theorem hilbertThreeAnglesHaveTrihedralRealization_intro
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (A O B C P D E Q F : Geo.Point)
    (R L M N : Geo.Point)
    (h :
      HilbertTrihedralRealizesThreeAngles
        Geo
        R L M N
        A O B
        C P D
        E Q F) :
    HilbertThreeAnglesHaveTrihedralRealization
      Geo
      A O B
      C P D
      E Q F := by
  exact
    Exists.intro R
      (Exists.intro L
        (Exists.intro M
          (Exists.intro N h)))

/-!
# Perpendicular-bisector metric lemma

This is a proposition-independent planar helper needed for Euclid XI.23.

If M is the midpoint of AB and MP is perpendicular to AB at M, then
P is equidistant from A and B.

No circle object, continuity principle, or spatial hypothesis is used.
-/

/--
A point on a perpendicular through the midpoint of a segment is
equidistant from the endpoints.

The explicit noncollinearity assumption is intentional:
`HilbertRightAngle` itself stores the adjacent-angle relation, while
the properness of the angle is supplied separately by the construction
that produced the perpendicular.
-/
theorem hilbert_perpendicularBisector_equidistant
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A M B P : Geo.Point)
    (hMid : HilbertIsMidpoint Geo M A B)
    (hAMP : Not (PrimCollinear Geo A M P))
    (hRight : HilbertRightAngle Geo A M P) :
    Geo.Congruent P A P B := by

  have hAMB : Geo.Between A M B :=
    hMid.1

  have hAM_MB : Geo.Congruent A M M B :=
    hMid.2

  have hData :=
    HilbertOrder.between_incidence
      A M B hAMB

  have hMB : Not (M = B) :=
    hData.2.1

  have hAMBcol :
      PrimCollinear Geo A M B :=
    hData.2.2.2.1

  --------------------------------------------------------------------
  -- The right angle may be written using B as the chosen point on
  -- the ray opposite A.
  --------------------------------------------------------------------

  have hAngleAMP_PMB :
      Geo.AngleCongruent A M P P M B :=
    hilbert_right_angle_chosen_supplement
      Geo
      P M A B
      hAMB
      hAMP
      hRight

  have hAngleAMP_BMP :
      Geo.AngleCongruent A M P B M P := by
    unfold Geometry.Geo.AngleCongruent at hAngleAMP_PMB
    unfold Geometry.Geo.AngleCongruent
    rw [Geometry.Geo.angle_swap Geo P M B]
      at hAngleAMP_PMB
    exact hAngleAMP_PMB

  --------------------------------------------------------------------
  -- Both SAS triangles are proper.
  --------------------------------------------------------------------

  have hMAP :
      Not (PrimCollinear Geo M A P) := by
    intro h
    exact
      hAMP
        (PrimCollinearSwap
          Geo M A P h)

  have hMBP :
      Not (PrimCollinear Geo M B P) := by
    intro h

    have hBMP :
        PrimCollinear Geo B M P :=
      PrimCollinearSwap
        Geo M B P h

    have hMBP' :
        PrimCollinear Geo M B P :=
      PrimCollinearSwap
        Geo B M P hBMP

    have hAMPcol :
        PrimCollinear Geo A M P :=
      hilbert_primCollinear_trans
        Geo
        A M B P
        hMB
        hAMBcol
        hMBP'

    exact hAMP hAMPcol

  --------------------------------------------------------------------
  -- SAS for triangles MAP and MBP.
  --------------------------------------------------------------------

  have hMA_MB :
      Geo.Congruent M A M B :=
    CongruentReverseFirst
      Geo A M M B hAM_MB

  have hMP_MP :
      Geo.Congruent M P M P :=
    hilbert_congruent_reflexive
      Geo M P

  have hSAS :=
    SAS
      Geo
      M A P
      M B P
      hMAP
      hMBP
      hMA_MB
      hAngleAMP_BMP
      hMP_MP

  have hAP_BP :
      Geo.Congruent A P B P :=
    hSAS.sideBC

  exact
    CongruentReverseBoth
      Geo
      A P B P
      hAP_BP

/-!
# Existence data for a perpendicular bisector

For every nondegenerate segment AB we construct:

* its midpoint M,
* a point X off line AB such that MX is perpendicular to AB,
* the carrier line bis through M and X,
* the equidistance XA ~= XB.

This is still completely planar and uses no continuity axiom.
-/

/--
Existence of explicit perpendicular-bisector data for a nondegenerate
segment AB.
-/
theorem hilbert_perpendicularBisector_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : Not (A = B)) :
    exists M X : Geo.Point,
    exists bis : Geo.Line,
      HilbertIsMidpoint Geo M A B /\
      Not (PrimCollinear Geo A M X) /\
      HilbertRightAngle Geo A M X /\
      HilbertIncidence.OnLine M bis /\
      HilbertIncidence.OnLine X bis /\
      Geo.Congruent X A X B := by

  cases HilbertMidpointExists Geo A B hAB with
  | intro M hMid =>

    have hAMB :
        Geo.Between A M B :=
      hMid.1

    cases
        hilbert_right_angle_exists_nondegenerate
          Geo A M B hAMB
    with
    | intro X hX =>

      have hAMX :
          Not (PrimCollinear Geo A M X) :=
        hX.1

      have hRight :
          HilbertRightAngle Geo A M X :=
        hX.2

      have hMX :
          Not (M = X) := by
        intro hMXeq
        subst X

        have hAM :
            Not (A = M) :=
          (HilbertOrder.between_incidence
            A M B hAMB).1

        cases
            HilbertPlaneIncidence.line_through
              A M hAM
        with
        | intro lineAM hLineData =>
          have hAline :
              HilbertIncidence.OnLine A lineAM :=
            hLineData.1
          have hMline :
              HilbertIncidence.OnLine M lineAM :=
            hLineData.2

          exact
            hAMX
              (Exists.intro lineAM
                (And.intro hAline
                  (And.intro hMline hMline)))

      cases
          HilbertPlaneIncidence.line_through
            M X hMX
      with
      | intro bis hBisData =>

        have hMbis :
            HilbertIncidence.OnLine M bis :=
          hBisData.1

        have hXbis :
            HilbertIncidence.OnLine X bis :=
          hBisData.2

        have hXA_XB :
            Geo.Congruent X A X B :=
          hilbert_perpendicularBisector_equidistant
            Geo
            A M B X
            hMid
            hAMX
            hRight

        exact
          Exists.intro M
            (Exists.intro X
              (Exists.intro bis
                (And.intro hMid
                  (And.intro hAMX
                    (And.intro hRight
                      (And.intro hMbis
                        (And.intro hXbis hXA_XB)))))))

/-!
# Intersection bridge for Hilbert incidence lines

`HilbertLinesDisjoint Geo l m` is definitionally the negation of
`HilbertLinesMeet Geo l m`.  This helper only exposes the positive
intersection witness in a convenient form.
-/

/--
If two Hilbert incidence lines are not disjoint, they have a common point.
-/
theorem hilbert_commonPoint_of_not_linesDisjoint
    [HilbertIncidence Geo]
    (l m : Geo.Line)
    (hNotDisjoint :
      Not (HilbertLinesDisjoint Geo l m)) :
    exists P : Geo.Point,
      HilbertIncidence.OnLine P l /\
      HilbertIncidence.OnLine P m := by
  unfold HilbertLinesDisjoint at hNotDisjoint
  exact Classical.byContradiction hNotDisjoint

/-!
# Common-point obstruction to point-line parallelism

This file contains only representation-level facts about `Geo.Parallel`.
No Hilbert axiom is used.
-/

/--
Two extensional point-lines with a common point cannot be parallel.
-/
theorem hilbert_not_parallel_of_common_point
    (A B C D P : Geo.Point)
    (hPAB : (Geo.PointLine A B) P)
    (hPCD : (Geo.PointLine C D) P) :
    Not (Geo.Parallel A B C D) := by
  intro hParallel
  exact
    Set.disjoint_left.mp hParallel.2.2
      hPAB hPCD

/--
Two point-lines with the same first endpoint cannot be parallel.
-/
theorem hilbert_not_parallel_same_origin
    (A B C : Geo.Point) :
    Not (Geo.Parallel A B A C) := by

  have hAAB :
      (Geo.PointLine A B) A := by
    change Geometry.Geo.LineCollinear Geo A B A
    exact Or.inr (Or.inl rfl)

  have hAAC :
      (Geo.PointLine A C) A := by
    change Geometry.Geo.LineCollinear Geo A C A
    exact Or.inr (Or.inl rfl)

  exact
    hilbert_not_parallel_of_common_point
      Geo
      A B
      A C
      A
      hAAB
      hAAC

/-!
# Two right angles in one triangle are impossible

This is the neutral obstruction needed for later perpendicular-line
arguments. It is a direct corollary of Euclid I.17 together with the
Hilbert theory of right angles.
-/

/--
A nondegenerate triangle cannot have right angles at two distinct
vertices B and C.
-/
theorem hilbert_triangle_two_right_angles_impossible
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hRightB : HilbertRightAngle Geo A B C)
    (hRightC : HilbertRightAngle Geo A C B) :
    False := by

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hBCA :
      Not (PrimCollinear Geo B C A) := by
    intro h
    have hCAB :
        PrimCollinear Geo C A B :=
      PrimCollinearCycle
        Geo B C A h
    have hABC' :
        PrimCollinear Geo A B C :=
      PrimCollinearCycle
        Geo C A B hCAB
    exact hABC hABC'

  --------------------------------------------------------------------
  -- Reverse the two arms of the right angle at C.
  --------------------------------------------------------------------

  have hACBrefl :
      Geo.AngleCongruent A C B A C B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A C B
      hACB

  have hACB_BCA :
      Geo.AngleCongruent A C B B C A :=
    (Geo.angle_congruent_reverse_second
      A C B
      A C B).mp
      hACBrefl

  have hRightCRev :
      HilbertRightAngle Geo B C A :=
    hilbert_right_angle_transport
      Geo
      A C B
      B C A
      hACB
      hBCA
      hRightC
      hACB_BCA

  --------------------------------------------------------------------
  -- I.17: angle ABC + angle ACB is less than two right angles.
  --
  -- Hence there is E with B-C-E and
  --
  --     angle ABC < angle ACE.
  --------------------------------------------------------------------

  cases
      euclid_proposition_17_ABC_ACB
        Geo A B C hABC
  with
  | intro E hData =>

    have hBCE :
        Geo.Between B C E :=
      hData.1

    have hLess :
        HilbertAngleLess Geo A B C A C E :=
      hData.2

    ------------------------------------------------------------------
    -- Since BCA is right and B-C-E, its supplement ACE is also right:
    --
    --     angle BCA ~= angle ACE.
    ------------------------------------------------------------------

    have hBCA_ACE :
        Geo.AngleCongruent B C A A C E :=
      hilbert_right_angle_chosen_supplement
        Geo
        A C B E
        hBCE
        hBCA
        hRightCRev

    ------------------------------------------------------------------
    -- All right angles are congruent:
    --
    --     angle ABC ~= angle BCA ~= angle ACE.
    ------------------------------------------------------------------

    have hABC_BCA :
        Geo.AngleCongruent A B C B C A :=
      hilbert_all_right_angles_congruent
        Geo
        A B C
        B C A
        hABC
        hBCA
        hRightB
        hRightCRev

    have hABC_ACE :
        Geo.AngleCongruent A B C A C E :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        A B C
        B C A
        A C E
        hABC_BCA
        hBCA_ACE

    have hACE_ABC :
        Geo.AngleCongruent A C E A B C :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        A B C
        A C E
        hABC_ACE

    ------------------------------------------------------------------
    -- Transport the target of the strict inequality:
    --
    --     angle ABC < angle ACE ~= angle ABC,
    --
    -- contradicting irreflexivity.
    ------------------------------------------------------------------

    have hCycle :
        HilbertAngleLess Geo A B C A B C :=
      hilbert_angleLess_transport_right
        Geo
        A B C
        A C E
        A B C
        hLess
        hABC
        hACE_ABC

    exact
      (hilbert_angleLess_irrefl
        Geo A B C)
        hCycle

------------------------------------------------------------------------
-- Right-angle transport along carrier lines
------------------------------------------------------------------------

/--
Swapping the two arms of a nondegenerate right angle preserves
rightness.
-/
theorem hilbert_right_angle_swap_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo B O A := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hRefl :
      Geo.AngleCongruent B O A B O A :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      B O A
      hBOA

  have hCong :
      Geo.AngleCongruent A O B B O A := by
    unfold Geometry.Geo.AngleCongruent at hRefl
    unfold Geometry.Geo.AngleCongruent
    rw [Geometry.Geo.angle_swap Geo A O B]
    exact hRefl

  exact
    hilbert_right_angle_transport
      Geo
      A O B
      B O A
      hAOB
      hBOA
      hRight
      hCong

/--
A right angle depends on the carrier line of its second arm, not on
the particular nonvertex point chosen on that line.

Thus, if A, F, and P are collinear and P is distinct from F, then
a right angle XFA transports to XFP.
-/
theorem hilbert_right_angle_collinear_second_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (X F A P : Geo.Point)
    (hXFA : Not (PrimCollinear Geo X F A))
    (hRight : HilbertRightAngle Geo X F A)
    (hFAP : PrimCollinear Geo F A P)
    (hFP : Not (F = P)) :
    HilbertRightAngle Geo X F P := by

  have hFAX :
      Not (PrimCollinear Geo F A X) := by
    intro h
    have hAXF :
        PrimCollinear Geo A X F :=
      PrimCollinearCycle
        Geo F A X h
    have hXFA' :
        PrimCollinear Geo X F A :=
      PrimCollinearCycle
        Geo A X F hAXF
    exact hXFA hXFA'

  have hFA :
      Not (F = A) :=
    hilbert_noncollinear_ne_first
      Geo F A X hFAX

  have hXFP :
      Not (PrimCollinear Geo X F P) := by
    intro h

    have hFPA :
        PrimCollinear Geo F P A :=
      PrimCollinearRotate
        Geo F A P hFAP

    have hXFA' :
        PrimCollinear Geo X F A :=
      hilbert_primCollinear_trans
        Geo
        X F P A
        hFP
        h
        hFPA

    exact hXFA hXFA'

  by_cases hAP : A = P

  . subst P
    exact hRight

  . rcases
        hilbert_between_trichotomy
          Geo
          F A P
          hFA
          hAP
          hFP
          hFAP
    with
      hFAPbetween | hAFP | hFPA

    . have hRayAP :
          HilbertSameRay Geo F A P :=
        hilbert_sameRay_of_between
          Geo F A P hFAPbetween

      have hAngleEq :
          Geo.Angle X F A =
          Geo.Angle X F P :=
        hilbert_angle_eq_of_sameRay_second
          Geo F X A P hRayAP

      have hCong :
          Geo.AngleCongruent X F A X F P := by
        unfold Geometry.Geo.AngleCongruent
        rw [hAngleEq]
        exact
          HilbertCongruence.angle_congruence_reflexive
            (Geo := Geo)
            X F P
            hXFP

      exact
        hilbert_right_angle_transport
          Geo
          X F A
          X F P
          hXFA
          hXFP
          hRight
          hCong

    . have hAFX :
          Not (PrimCollinear Geo A F X) := by
        intro h
        exact
          hXFA
            (PrimCollinearSymm
              Geo A F X h)

      have hRightSwap :
          HilbertRightAngle Geo A F X :=
        hilbert_right_angle_swap_XI
          Geo
          X F A
          hXFA
          hRight

      have hCongOpp :
          Geo.AngleCongruent A F X X F P :=
        hilbert_right_angle_chosen_supplement
          Geo
          X F A P
          hAFP
          hAFX
          hRightSwap

      exact
        hilbert_right_angle_transport
          Geo
          A F X
          X F P
          hAFX
          hXFP
          hRightSwap
          hCongOpp

    . have hRayPA :
          HilbertSameRay Geo F P A :=
        hilbert_sameRay_of_between
          Geo F P A hFPA

      have hRayAP :
          HilbertSameRay Geo F A P :=
        hilbert_sameRay_symm
          Geo F P A hRayPA

      have hAngleEq :
          Geo.Angle X F A =
          Geo.Angle X F P :=
        hilbert_angle_eq_of_sameRay_second
          Geo F X A P hRayAP

      have hCong :
          Geo.AngleCongruent X F A X F P := by
        unfold Geometry.Geo.AngleCongruent
        rw [hAngleEq]
        exact
          HilbertCongruence.angle_congruence_reflexive
            (Geo := Geo)
            X F P
            hXFP

      exact
        hilbert_right_angle_transport
          Geo
          X F A
          X F P
          hXFA
          hXFP
          hRight
          hCong

/--
Two lines perpendicular to the same base line at distinct feet are
disjoint.

This is neutral geometry. If they met at P, triangle PFG would have
right angles at both F and G, contradicting Euclid I.17.
-/
theorem hilbert_perpendiculars_same_line_distinct_feet_disjoint_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (F G A D : Geo.Point)
    (base l m : Geo.Line)
    (hFG : Not (F = G))
    (hFbase : HilbertIncidence.OnLine F base)
    (hGbase : HilbertIncidence.OnLine G base)
    (hFl : HilbertIncidence.OnLine F l)
    (hAl : HilbertIncidence.OnLine A l)
    (hGm : HilbertIncidence.OnLine G m)
    (hDm : HilbertIncidence.OnLine D m)
    (hGFA : Not (PrimCollinear Geo G F A))
    (hFGD : Not (PrimCollinear Geo F G D))
    (hRightF : HilbertRightAngle Geo G F A)
    (hRightG : HilbertRightAngle Geo F G D) :
    HilbertLinesDisjoint Geo l m := by

  intro hMeet

  cases hMeet with
  | intro P hPdata =>

    have hPl :
        HilbertIncidence.OnLine P l :=
      hPdata.1

    have hPm :
        HilbertIncidence.OnLine P m :=
      hPdata.2

    have hPF :
        Not (P = F) := by
      intro hPF
      subst P

      have hMbase :
          m = base :=
        HilbertPlaneIncidence.line_unique
          F G hFG
          m base
          hPm hGm
          hFbase hGbase

      have hDbase :
          HilbertIncidence.OnLine D base := by
        rw [<- hMbase]
        exact hDm

      exact
        hFGD
          (Exists.intro base
            (And.intro hFbase
              (And.intro hGbase hDbase)))

    have hPG :
        Not (P = G) := by
      intro hPG
      subst P

      have hLbase :
          l = base :=
        HilbertPlaneIncidence.line_unique
          F G hFG
          l base
          hFl hPl
          hFbase hGbase

      have hAbase :
          HilbertIncidence.OnLine A base := by
        rw [<- hLbase]
        exact hAl

      exact
        hGFA
          (Exists.intro base
            (And.intro hGbase
              (And.intro hFbase hAbase)))

    have hPFG :
        Not (PrimCollinear Geo P F G) := by
      intro hPFGcol

      have hFGP :
          PrimCollinear Geo F G P :=
        PrimCollinearCycle
          Geo P F G hPFGcol

      have hPbase :
          HilbertIncidence.OnLine P base :=
        hilbert_collinear_on_line
          Geo
          F G P
          base
          hFG
          hFbase
          hGbase
          hFGP

      have hLbase :
          l = base :=
        HilbertPlaneIncidence.line_unique
          P F hPF
          l base
          hPl hFl
          hPbase hFbase

      have hAbase :
          HilbertIncidence.OnLine A base := by
        rw [<- hLbase]
        exact hAl

      exact
        hGFA
          (Exists.intro base
            (And.intro hGbase
              (And.intro hFbase hAbase)))

    have hFAP :
        PrimCollinear Geo F A P :=
      Exists.intro l
        (And.intro hFl
          (And.intro hAl hPl))

    have hGDP :
        PrimCollinear Geo G D P :=
      Exists.intro m
        (And.intro hGm
          (And.intro hDm hPm))

    have hFP :
        Not (F = P) := by
      intro h
      exact hPF h.symm

    have hGP :
        Not (G = P) := by
      intro h
      exact hPG h.symm

    have hGFP :
        HilbertRightAngle Geo G F P :=
      hilbert_right_angle_collinear_second_XI
        Geo
        G F A P
        hGFA
        hRightF
        hFAP
        hFP

    have hFGP :
        HilbertRightAngle Geo F G P :=
      hilbert_right_angle_collinear_second_XI
        Geo
        F G D P
        hFGD
        hRightG
        hGDP
        hGP

    have hGFPnc :
        Not (PrimCollinear Geo G F P) := by
      intro h
      exact
        hPFG
          (PrimCollinearSymm
            Geo G F P h)

    have hFGPnc :
        Not (PrimCollinear Geo F G P) := by
      intro h

      have hGPF :
          PrimCollinear Geo G P F :=
        PrimCollinearCycle
          Geo F G P h

      have hPFG' :
          PrimCollinear Geo P F G :=
        PrimCollinearCycle
          Geo G P F hGPF

      exact hPFG hPFG'

    have hPFGright :
        HilbertRightAngle Geo P F G :=
      hilbert_right_angle_swap_XI
        Geo
        G F P
        hGFPnc
        hGFP

    have hPGF :
        HilbertRightAngle Geo P G F :=
      hilbert_right_angle_swap_XI
        Geo
        F G P
        hFGPnc
        hFGP

    exact
      hilbert_triangle_two_right_angles_impossible
        Geo
        P F G
        hPFG
        hPFGright
        hPGF

------------------------------------------------------------------------
-- Bridge from incidence-line disjointness to Geo.Parallel
------------------------------------------------------------------------

/--
Two nondegenerate point-lines carried by disjoint Hilbert incidence
lines are parallel in the extensional `Geo.Parallel` sense.
-/
theorem hilbert_parallel_of_disjoint_carrier_lines_XI
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (l m : Geo.Line)
    (hAB : Not (A = B))
    (hCD : Not (C = D))
    (hAl : HilbertIncidence.OnLine A l)
    (hBl : HilbertIncidence.OnLine B l)
    (hCm : HilbertIncidence.OnLine C m)
    (hDm : HilbertIncidence.OnLine D m)
    (hDisjoint : HilbertLinesDisjoint Geo l m) :
    Geo.Parallel A B C D := by

  refine And.intro hAB ?_
  refine And.intro hCD ?_

  apply Set.disjoint_left.mpr
  intro P hPAB hPCD

  have hPl :
      HilbertIncidence.OnLine P l :=
    (hilbert_mem_pointLine_iff_onLine
      Geo A B P l
      hAB
      hAl hBl).mp hPAB

  have hPm :
      HilbertIncidence.OnLine P m :=
    (hilbert_mem_pointLine_iff_onLine
      Geo C D P m
      hCD
      hCm hDm).mp hPCD

  exact
    hDisjoint
      (Exists.intro P
        (And.intro hPl hPm))

/--
Point-line form of the neutral theorem on perpendiculars to the same
base line at distinct feet.
-/
theorem hilbert_perpendiculars_same_line_distinct_feet_parallel_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (F G A D : Geo.Point)
    (base l m : Geo.Line)
    (hFG : Not (F = G))
    (hFA : Not (F = A))
    (hGD : Not (G = D))
    (hFbase : HilbertIncidence.OnLine F base)
    (hGbase : HilbertIncidence.OnLine G base)
    (hFl : HilbertIncidence.OnLine F l)
    (hAl : HilbertIncidence.OnLine A l)
    (hGm : HilbertIncidence.OnLine G m)
    (hDm : HilbertIncidence.OnLine D m)
    (hGFA : Not (PrimCollinear Geo G F A))
    (hFGD : Not (PrimCollinear Geo F G D))
    (hRightF : HilbertRightAngle Geo G F A)
    (hRightG : HilbertRightAngle Geo F G D) :
    Geo.Parallel F A G D := by

  have hDisjoint :
      HilbertLinesDisjoint Geo l m :=
    hilbert_perpendiculars_same_line_distinct_feet_disjoint_XI
      Geo
      F G A D
      base l m
      hFG
      hFbase hGbase
      hFl hAl
      hGm hDm
      hGFA hFGD
      hRightF hRightG

  exact
    hilbert_parallel_of_disjoint_carrier_lines_XI
      Geo
      F A G D
      l m
      hFA hGD
      hFl hAl
      hGm hDm
      hDisjoint

------------------------------------------------------------------------
-- Euclidean transfer of perpendicularity across parallel lines
------------------------------------------------------------------------

/--
Transport a right angle when the first arm is replaced by another
nonvertex point on the same carrier line.
-/
theorem hilbert_right_angle_collinear_first_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A F X P : Geo.Point)
    (hAFX : Not (PrimCollinear Geo A F X))
    (hRight : HilbertRightAngle Geo A F X)
    (hFAP : PrimCollinear Geo F A P)
    (hFP : Not (F = P)) :
    HilbertRightAngle Geo P F X := by

  have hXFA :
      Not (PrimCollinear Geo X F A) := by
    intro h
    exact
      hAFX
        (PrimCollinearSymm
          Geo X F A h)

  have hRightSwap :
      HilbertRightAngle Geo X F A :=
    hilbert_right_angle_swap_XI
      Geo
      A F X
      hAFX
      hRight

  have hXFP :
      HilbertRightAngle Geo X F P :=
    hilbert_right_angle_collinear_second_XI
      Geo
      X F A P
      hXFA
      hRightSwap
      hFAP
      hFP

  have hPFX :
      Not (PrimCollinear Geo P F X) := by
    intro h

    have hXFPcol :
        PrimCollinear Geo X F P :=
      PrimCollinearSymm
        Geo P F X h

    have hFPA :
        PrimCollinear Geo F P A :=
      PrimCollinearRotate
        Geo F A P hFAP

    have hXFAcol :
        PrimCollinear Geo X F A :=
      hilbert_primCollinear_trans
        Geo
        X F P A
        hFP
        hXFPcol
        hFPA

    exact hXFA hXFAcol

  exact
    hilbert_right_angle_swap_XI
      Geo
      X F P
      (by
        intro h
        exact
          hPFX
            (PrimCollinearSymm
              Geo X F P h))
      hXFP

/--
Let p and q be disjoint parallel carrier lines. If a transversal base
meets p at A and q at H, and p is perpendicular to base at A, then q
is perpendicular to base at H.

The proof uses only the neutral theorem that two perpendiculars to the
same line are parallel, followed by Hilbert IV: through H there is a
unique line parallel to p.
-/
theorem hilbert_perpendicular_transfer_across_parallel_carriers_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A H X : Geo.Point)
    (base p q : Geo.Line)
    (hAH : Not (A = H))
    (hAbase : HilbertIncidence.OnLine A base)
    (hHbase : HilbertIncidence.OnLine H base)
    (hAp : HilbertIncidence.OnLine A p)
    (hXp : HilbertIncidence.OnLine X p)
    (hHq : HilbertIncidence.OnLine H q)
    (hPQ : HilbertLinesDisjoint Geo p q)
    (hHAX : Not (PrimCollinear Geo H A X))
    (hRightA : HilbertRightAngle Geo H A X) :
    exists T : Geo.Point,
      HilbertIncidence.OnLine T q /\
      Not (PrimCollinear Geo A H T) /\
      HilbertRightAngle Geo A H T := by

  --------------------------------------------------------------------
  -- Construct a perpendicular t to base through H.
  --------------------------------------------------------------------

  cases
      HilbertOrder.between_extension
        A H hAH
  with
  | intro K hAHK =>

    cases
        hilbert_right_angle_exists_nondegenerate
          Geo A H K hAHK
    with
    | intro T hTdata =>

      have hAHT :
          Not (PrimCollinear Geo A H T) :=
        hTdata.1

      have hRightH :
          HilbertRightAngle Geo A H T :=
        hTdata.2

      have hHT :
          Not (H = T) := by
        intro h
        subst T

        have hAHA :
            PrimCollinear Geo A H H := by
          cases
              HilbertPlaneIncidence.line_through
                A H hAH
          with
          | intro l hldata =>
            exact
              Exists.intro l
                (And.intro hldata.1
                  (And.intro hldata.2 hldata.2))

        exact hAHT hAHA

      cases
          HilbertPlaneIncidence.line_through
            H T hHT
      with
      | intro t htdata =>

        have hHt :
            HilbertIncidence.OnLine H t :=
          htdata.1

        have hTt :
            HilbertIncidence.OnLine T t :=
          htdata.2

        ----------------------------------------------------------------
        -- p and t are perpendicular to the same base at A and H.
        ----------------------------------------------------------------

        have hPT :
            HilbertLinesDisjoint Geo p t :=
          hilbert_perpendiculars_same_line_distinct_feet_disjoint_XI
            Geo
            A H X T
            base p t
            hAH
            hAbase hHbase
            hAp hXp
            hHt hTt
            hHAX hAHT
            hRightA hRightH

        ----------------------------------------------------------------
        -- q and t both pass through H and are parallel to p.
        -- Hilbert IV identifies them.
        ----------------------------------------------------------------

        have hHoffp :
            Not (HilbertIncidence.OnLine H p) := by
          intro hHp
          exact
            hPQ
              (Exists.intro H
                (And.intro hHp hHq))

        have hQP :
            HilbertLinesDisjoint Geo q p := by
          intro hMeet
          cases hMeet with
          | intro P hPdata =>
            exact
              hPQ
                (Exists.intro P
                  (And.intro hPdata.2 hPdata.1))

        have hTP :
            HilbertLinesDisjoint Geo t p := by
          intro hMeet
          cases hMeet with
          | intro P hPdata =>
            exact
              hPT
                (Exists.intro P
                  (And.intro hPdata.2 hPdata.1))

        have hqt :
            q = t :=
          HilbertEuclideanPlane.parallel_unique
            (Geo := Geo)
            p H
            hHoffp
            q t
            hHq hQP
            hHt hTP

        have hTq :
            HilbertIncidence.OnLine T q := by
          rw [hqt]
          exact hTt

        exact
          Exists.intro T
            (And.intro hTq
              (And.intro hAHT hRightH))

------------------------------------------------------------------------
-- Transport on both arms and transversals of parallel carriers
------------------------------------------------------------------------

/--
Noncollinearity is preserved when each arm of an angle is represented
by another nonvertex point on the same carrier line.
-/
theorem hilbert_not_collinear_collinear_arms_XI
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A F X P Q : Geo.Point)
    (hAFX : Not (PrimCollinear Geo A F X))
    (hFAP : PrimCollinear Geo F A P)
    (hFXQ : PrimCollinear Geo F X Q)
    (hFP : Not (F = P))
    (hFQ : Not (F = Q)) :
    Not (PrimCollinear Geo P F Q) := by

  intro hPFQ

  cases hFAP with
  | intro l hl =>
    cases hFXQ with
    | intro m hm =>
      cases hPFQ with
      | intro n hn =>

        have hln :
            l = n :=
          HilbertPlaneIncidence.line_unique
            F P hFP
            l n
            hl.1 hl.2.2
            hn.2.1 hn.1

        have hmn :
            m = n :=
          HilbertPlaneIncidence.line_unique
            F Q hFQ
            m n
            hm.1 hm.2.2
            hn.2.1 hn.2.2

        have hAn :
            HilbertIncidence.OnLine A n := by
          rw [<- hln]
          exact hl.2.1

        have hXn :
            HilbertIncidence.OnLine X n := by
          rw [<- hmn]
          exact hm.2.1

        exact
          hAFX
            (Exists.intro n
              (And.intro hAn
                (And.intro hn.2.1 hXn)))

/--
A right angle is unchanged when both arms are represented by other
nonvertex points on the same two carrier lines.
-/
theorem hilbert_right_angle_collinear_both_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A F X P Q : Geo.Point)
    (hAFX : Not (PrimCollinear Geo A F X))
    (hRight : HilbertRightAngle Geo A F X)
    (hFAP : PrimCollinear Geo F A P)
    (hFXQ : PrimCollinear Geo F X Q)
    (hFP : Not (F = P))
    (hFQ : Not (F = Q)) :
    HilbertRightAngle Geo P F Q := by

  have hFXA :
      Not (PrimCollinear Geo F X A) := by
    intro h
    have hXAF :
        PrimCollinear Geo X A F :=
      PrimCollinearCycle
        Geo F X A h
    have hAFX' :
        PrimCollinear Geo A F X :=
      PrimCollinearCycle
        Geo X A F hXAF
    exact hAFX hAFX'

  have hFX :
      Not (F = X) :=
    hilbert_noncollinear_ne_first
      Geo F X A hFXA

  cases
      HilbertPlaneIncidence.line_through
        F X hFX
  with
  | intro lineFX hLineFX =>

    have hFXX :
        PrimCollinear Geo F X X :=
      Exists.intro lineFX
        (And.intro hLineFX.1
          (And.intro hLineFX.2 hLineFX.2))

    have hPFX :
        Not (PrimCollinear Geo P F X) :=
      hilbert_not_collinear_collinear_arms_XI
        Geo
        A F X P X
        hAFX
        hFAP
        hFXX
        hFP
        hFX

    have hRightPFX :
        HilbertRightAngle Geo P F X :=
      hilbert_right_angle_collinear_first_XI
        Geo
        A F X P
        hAFX
        hRight
        hFAP
        hFP

    exact
      hilbert_right_angle_collinear_second_XI
        Geo
        P F X Q
        hPFX
        hRightPFX
        hFXQ
        hFQ

/--
A transversal through A that meets p cannot stay disjoint from q when
p and q are disjoint parallel carriers and the transversal is genuinely
different from p.

The Euclidean step is exactly Hilbert IV: if the transversal were also
disjoint from q, then through A there would be two distinct parallels
to q, namely p and the transversal.
-/
theorem hilbert_transversal_meets_parallel_carrier_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B X : Geo.Point)
    (base p q : Geo.Line)
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hAp : HilbertIncidence.OnLine A p)
    (hXp : HilbertIncidence.OnLine X p)
    (hPQ : HilbertLinesDisjoint Geo p q)
    (hBAX : Not (PrimCollinear Geo B A X)) :
    exists H : Geo.Point,
      HilbertIncidence.OnLine H base /\
      HilbertIncidence.OnLine H q := by

  apply
    hilbert_commonPoint_of_not_linesDisjoint
      Geo base q

  intro hBaseQ

  have hAoffq :
      Not (HilbertIncidence.OnLine A q) := by
    intro hAq
    exact
      hPQ
        (Exists.intro A
          (And.intro hAp hAq))

  have hpbase :
      p = base :=
    HilbertEuclideanPlane.parallel_unique
      (Geo := Geo)
      q A
      hAoffq
      p base
      hAp hPQ
      hAbase hBaseQ

  have hXbase :
      HilbertIncidence.OnLine X base := by
    rw [<- hpbase]
    exact hXp

  exact
    hBAX
      (Exists.intro base
        (And.intro hBbase
          (And.intro hAbase hXbase)))

------------------------------------------------------------------------
-- Intersection of two perpendicular bisectors in a triangle
------------------------------------------------------------------------

/--
For a nondegenerate triangle ABC, the perpendicular bisectors of AB
and AC meet.

The theorem returns the midpoint/right-angle construction data for
both bisectors together with one common point O.  This is the planar
existence core needed for the circumcenter construction.
-/
theorem hilbert_triangle_two_perpendicularBisectors_meet_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    exists M N X Y O : Geo.Point,
    exists bisAB bisAC : Geo.Line,
      HilbertIsMidpoint Geo M A B /\
      HilbertIsMidpoint Geo N A C /\
      Not (PrimCollinear Geo A M X) /\
      HilbertRightAngle Geo A M X /\
      HilbertIncidence.OnLine M bisAB /\
      HilbertIncidence.OnLine X bisAB /\
      Not (PrimCollinear Geo A N Y) /\
      HilbertRightAngle Geo A N Y /\
      HilbertIncidence.OnLine N bisAC /\
      HilbertIncidence.OnLine Y bisAC /\
      HilbertIncidence.OnLine O bisAB /\
      HilbertIncidence.OnLine O bisAC := by

  have hAB :
      Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hAC :
      Not (A = C) :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  cases
      hilbert_perpendicularBisector_exists
        Geo A B hAB
  with
  | intro M hMdata =>

    cases hMdata with
    | intro X hXdata =>

      cases hXdata with
      | intro bisAB hABdata =>

        have hMidAB :
            HilbertIsMidpoint Geo M A B :=
          hABdata.1

        have hAMX :
            Not (PrimCollinear Geo A M X) :=
          hABdata.2.1

        have hRightAB :
            HilbertRightAngle Geo A M X :=
          hABdata.2.2.1

        have hMbisAB :
            HilbertIncidence.OnLine M bisAB :=
          hABdata.2.2.2.1

        have hXbisAB :
            HilbertIncidence.OnLine X bisAB :=
          hABdata.2.2.2.2.1

        cases
            hilbert_perpendicularBisector_exists
              Geo A C hAC
        with
        | intro N hNdata =>

          cases hNdata with
          | intro Y hYdata =>

            cases hYdata with
            | intro bisAC hACdata =>

              have hMidAC :
                  HilbertIsMidpoint Geo N A C :=
                hACdata.1

              have hANY :
                  Not (PrimCollinear Geo A N Y) :=
                hACdata.2.1

              have hRightAC :
                  HilbertRightAngle Geo A N Y :=
                hACdata.2.2.1

              have hNbisAC :
                  HilbertIncidence.OnLine N bisAC :=
                hACdata.2.2.2.1

              have hYbisAC :
                  HilbertIncidence.OnLine Y bisAC :=
                hACdata.2.2.2.2.1

              ----------------------------------------------------------------
              -- Carrier lines AB and AC.
              ----------------------------------------------------------------

              cases
                  HilbertPlaneIncidence.line_through
                    A B hAB
              with
              | intro lineAB hLineAB =>

                have hAlineAB :
                    HilbertIncidence.OnLine A lineAB :=
                  hLineAB.1

                have hBlineAB :
                    HilbertIncidence.OnLine B lineAB :=
                  hLineAB.2

                have hMlineAB :
                    HilbertIncidence.OnLine M lineAB :=
                  hilbert_between_on_line
                    Geo
                    A M B
                    lineAB
                    hAlineAB hBlineAB
                    hMidAB.1

                cases
                    HilbertPlaneIncidence.line_through
                      A C hAC
                with
                | intro lineAC hLineAC =>

                  have hAlineAC :
                      HilbertIncidence.OnLine A lineAC :=
                    hLineAC.1

                  have hClineAC :
                      HilbertIncidence.OnLine C lineAC :=
                    hLineAC.2

                  have hNlineAC :
                      HilbertIncidence.OnLine N lineAC :=
                    hilbert_between_on_line
                      Geo
                      A N C
                      lineAC
                      hAlineAC hClineAC
                      hMidAC.1

                  ----------------------------------------------------------------
                  -- It remains to show that the two bisectors are not disjoint.
                  ----------------------------------------------------------------

                  have hNotDisjoint :
                      Not (HilbertLinesDisjoint Geo bisAB bisAC) := by

                    intro hBisDisjoint

                    --------------------------------------------------------------
                    -- AB meets the second bisector.
                    --------------------------------------------------------------

                    cases
                        hilbert_transversal_meets_parallel_carrier_XI
                          Geo
                          M A X
                          lineAB bisAB bisAC
                          hMlineAB
                          hAlineAB
                          hMbisAB
                          hXbisAB
                          hBisDisjoint
                          hAMX
                    with
                    | intro H hHdata =>

                      have hHlineAB :
                          HilbertIncidence.OnLine H lineAB :=
                        hHdata.1

                      have hHbisAC :
                          HilbertIncidence.OnLine H bisAC :=
                        hHdata.2

                      have hMH :
                          Not (M = H) := by
                        intro h
                        subst H
                        exact
                          hBisDisjoint
                            (Exists.intro M
                              (And.intro hMbisAB hHbisAC))

                      have hMAH :
                          PrimCollinear Geo M A H :=
                        Exists.intro lineAB
                          (And.intro hMlineAB
                            (And.intro hAlineAB hHlineAB))

                      have hMX :
                          Not (M = X) := by
                        intro h
                        subst X

                        exact
                          hAMX
                            (Exists.intro lineAB
                              (And.intro hAlineAB
                                (And.intro hMlineAB hMlineAB)))

                      have hMXX :
                          PrimCollinear Geo M X X :=
                        Exists.intro bisAB
                          (And.intro hMbisAB
                            (And.intro hXbisAB hXbisAB))

                      have hHMX :
                          Not (PrimCollinear Geo H M X) :=
                        hilbert_not_collinear_collinear_arms_XI
                          Geo
                          A M X H X
                          hAMX
                          hMAH
                          hMXX
                          hMH
                          hMX

                      have hRightHMX :
                          HilbertRightAngle Geo H M X :=
                        hilbert_right_angle_collinear_first_XI
                          Geo
                          A M X H
                          hAMX
                          hRightAB
                          hMAH
                          hMH

                      ------------------------------------------------------------
                      -- Since bisAB || bisAC, transfer perpendicularity from M
                      -- to H.  We obtain T on bisAC with MHT right.
                      ------------------------------------------------------------

                      cases
                          hilbert_perpendicular_transfer_across_parallel_carriers_XI
                            Geo
                            M H X
                            lineAB bisAB bisAC
                            hMH
                            hMlineAB
                            hHlineAB
                            hMbisAB
                            hXbisAB
                            hHbisAC
                            hBisDisjoint
                            hHMX
                            hRightHMX
                      with
                      | intro T hTdata =>

                        have hTbisAC :
                            HilbertIncidence.OnLine T bisAC :=
                          hTdata.1

                        have hMHT :
                            Not (PrimCollinear Geo M H T) :=
                          hTdata.2.1

                        have hRightMHT :
                            HilbertRightAngle Geo M H T :=
                          hTdata.2.2

                        ----------------------------------------------------------
                        -- H and N are distinct.  Otherwise N would lie on both
                        -- side carriers AB and AC, forcing the triangle to be
                        -- collinear.
                        ----------------------------------------------------------

                        have hAN :
                            Not (A = N) :=
                          (HilbertOrder.between_incidence
                            A N C hMidAC.1).1

                        have hHN :
                            Not (H = N) := by
                          intro h
                          subst H

                          have hNlineAB :
                              HilbertIncidence.OnLine N lineAB :=
                            hHlineAB

                          have hLinesEqual :
                              lineAB = lineAC :=
                            HilbertPlaneIncidence.line_unique
                              A N hAN
                              lineAB lineAC
                              hAlineAB hNlineAB
                              hAlineAC hNlineAC

                          have hClineAB :
                              HilbertIncidence.OnLine C lineAB := by
                            rw [hLinesEqual]
                            exact hClineAC

                          exact
                            hABC
                              (Exists.intro lineAB
                                (And.intro hAlineAB
                                  (And.intro hBlineAB hClineAB)))

                        have hNH :
                            Not (N = H) := by
                          intro h
                          exact hHN h.symm

                        ----------------------------------------------------------
                        -- At H, bisAC is perpendicular to AB:
                        -- T-H-M is right, hence N-H-M is right.
                        ----------------------------------------------------------

                        have hTHM :
                            Not (PrimCollinear Geo T H M) := by
                          intro h
                          exact
                            hMHT
                              (PrimCollinearSymm
                                Geo T H M h)

                        have hRightTHM :
                            HilbertRightAngle Geo T H M :=
                          hilbert_right_angle_swap_XI
                            Geo
                            M H T
                            hMHT
                            hRightMHT

                        have hHTN :
                            PrimCollinear Geo H T N :=
                          Exists.intro bisAC
                            (And.intro hHbisAC
                              (And.intro hTbisAC hNbisAC))

                        have hRightNHM :
                            HilbertRightAngle Geo N H M :=
                          hilbert_right_angle_collinear_first_XI
                            Geo
                            T H M N
                            hTHM
                            hRightTHM
                            hHTN
                            hHN

                        ----------------------------------------------------------
                        -- At N, bisAC is perpendicular to AC:
                        -- Y-N-A is right, hence H-N-A is right.
                        ----------------------------------------------------------

                        have hYNA :
                            Not (PrimCollinear Geo Y N A) := by
                          intro h
                          exact
                            hANY
                              (PrimCollinearSymm
                                Geo Y N A h)

                        have hRightYNA :
                            HilbertRightAngle Geo Y N A :=
                          hilbert_right_angle_swap_XI
                            Geo
                            A N Y
                            hANY
                            hRightAC

                        have hNYH :
                            PrimCollinear Geo N Y H :=
                          Exists.intro bisAC
                            (And.intro hNbisAC
                              (And.intro hYbisAC hHbisAC))

                        have hRightHNA :
                            HilbertRightAngle Geo H N A :=
                          hilbert_right_angle_collinear_first_XI
                            Geo
                            Y N A H
                            hYNA
                            hRightYNA
                            hNYH
                            hNH

                        ----------------------------------------------------------
                        -- Therefore AB and AC are two perpendiculars to bisAC
                        -- at distinct feet H and N, hence disjoint.
                        ----------------------------------------------------------

                        have hHNM :
                            Not (PrimCollinear Geo N H M) := by
                          intro h
                          exact
                            hTHM
                              (hilbert_primCollinear_trans
                                Geo
                                T H N M
                                hHN
                                (Exists.intro bisAC
                                  (And.intro hTbisAC
                                    (And.intro hHbisAC hNbisAC)))
                                (PrimCollinearSwap
                                  Geo N H M h))

                        have hHNA :
                            Not (PrimCollinear Geo H N A) := by
                          intro h
                          exact
                            hANY
                              (hilbert_primCollinear_trans
                                Geo
                                A N H Y
                                hNH
                                (PrimCollinearSymm
                                  Geo H N A h)
                                (Exists.intro bisAC
                                  (And.intro hNbisAC
                                    (And.intro hHbisAC hYbisAC))))

                        have hABACdisjoint :
                            HilbertLinesDisjoint Geo lineAB lineAC :=
                          hilbert_perpendiculars_same_line_distinct_feet_disjoint_XI
                            Geo
                            H N M A
                            bisAC lineAB lineAC
                            hHN
                            hHbisAC hNbisAC
                            hHlineAB hMlineAB
                            hNlineAC hAlineAC
                            hHNM hHNA
                            hRightNHM hRightHNA

                        exact
                          hABACdisjoint
                            (Exists.intro A
                              (And.intro hAlineAB hAlineAC))

                  cases
                      hilbert_commonPoint_of_not_linesDisjoint
                        Geo bisAB bisAC hNotDisjoint
                  with
                  | intro O hOdata =>

                    refine
                      Exists.intro M
                        (Exists.intro N
                          (Exists.intro X
                            (Exists.intro Y
                              (Exists.intro O
                                (Exists.intro bisAB
                                  (Exists.intro bisAC ?_))))))

                    constructor
                    . exact hMidAB
                    constructor
                    . exact hMidAC
                    constructor
                    . exact hAMX
                    constructor
                    . exact hRightAB
                    constructor
                    . exact hMbisAB
                    constructor
                    . exact hXbisAB
                    constructor
                    . exact hANY
                    constructor
                    . exact hRightAC
                    constructor
                    . exact hNbisAC
                    constructor
                    . exact hYbisAC
                    constructor
                    . exact hOdata.1
                    . exact hOdata.2

------------------------------------------------------------------------
-- Equidistance on a perpendicular bisector and circumcenter
------------------------------------------------------------------------

/--
Every point on the carrier of a perpendicular bisector is equidistant
from the endpoints of the bisected segment.
-/
theorem hilbert_point_on_perpendicularBisector_equidistant_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B M X P : Geo.Point)
    (bis : Geo.Line)
    (hMid : HilbertIsMidpoint Geo M A B)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X)
    (hMbis : HilbertIncidence.OnLine M bis)
    (hXbis : HilbertIncidence.OnLine X bis)
    (hPbis : HilbertIncidence.OnLine P bis) :
    Geo.Congruent P A P B := by

  by_cases hMP : M = P

  . subst P

    exact
      CongruentReverseFirst
        Geo
        A M
        M B
        hMid.2

  . have hMXP :
        PrimCollinear Geo M X P :=
      Exists.intro bis
        (And.intro hMbis
          (And.intro hXbis hPbis))

    have hMPX :
        PrimCollinear Geo M P X :=
      PrimCollinearRotate
        Geo M X P hMXP

    have hAMP :
        Not (PrimCollinear Geo A M P) := by
      intro h

      have hAMX' :
          PrimCollinear Geo A M X :=
        hilbert_primCollinear_trans
          Geo
          A M P X
          hMP
          h
          hMPX

      exact hAMX hAMX'

    have hRightP :
        HilbertRightAngle Geo A M P :=
      hilbert_right_angle_collinear_second_XI
        Geo
        A M X P
        hAMX
        hRight
        hMXP
        hMP

    exact
      hilbert_perpendicularBisector_equidistant
        Geo
        A M B P
        hMid
        hAMP
        hRightP

/--
Every nondegenerate Hilbert triangle in the Euclidean plane has a
circumcenter: a point equidistant from all three vertices.

The construction is the intersection of the perpendicular bisectors
of AB and AC.
-/
theorem hilbert_triangle_circumcenter_exists_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    exists O : Geo.Point,
      Geo.Congruent O A O B /\
      Geo.Congruent O A O C := by

  cases
      hilbert_triangle_two_perpendicularBisectors_meet_XI
        Geo A B C hABC
  with
  | intro M hMdata =>

    cases hMdata with
    | intro N hNdata =>

      cases hNdata with
      | intro X hXdata =>

        cases hXdata with
        | intro Y hYdata =>

          cases hYdata with
          | intro O hOdata =>

            cases hOdata with
            | intro bisAB hBisABdata =>

              cases hBisABdata with
              | intro bisAC hData =>

                have hMidAB :
                    HilbertIsMidpoint Geo M A B :=
                  hData.1

                have hMidAC :
                    HilbertIsMidpoint Geo N A C :=
                  hData.2.1

                have hAMX :
                    Not (PrimCollinear Geo A M X) :=
                  hData.2.2.1

                have hRightAB :
                    HilbertRightAngle Geo A M X :=
                  hData.2.2.2.1

                have hMbisAB :
                    HilbertIncidence.OnLine M bisAB :=
                  hData.2.2.2.2.1

                have hXbisAB :
                    HilbertIncidence.OnLine X bisAB :=
                  hData.2.2.2.2.2.1

                have hANY :
                    Not (PrimCollinear Geo A N Y) :=
                  hData.2.2.2.2.2.2.1

                have hRightAC :
                    HilbertRightAngle Geo A N Y :=
                  hData.2.2.2.2.2.2.2.1

                have hNbisAC :
                    HilbertIncidence.OnLine N bisAC :=
                  hData.2.2.2.2.2.2.2.2.1

                have hYbisAC :
                    HilbertIncidence.OnLine Y bisAC :=
                  hData.2.2.2.2.2.2.2.2.2.1

                have hObisAB :
                    HilbertIncidence.OnLine O bisAB :=
                  hData.2.2.2.2.2.2.2.2.2.2.1

                have hObisAC :
                    HilbertIncidence.OnLine O bisAC :=
                  hData.2.2.2.2.2.2.2.2.2.2.2

                have hOA_OB :
                    Geo.Congruent O A O B :=
                  hilbert_point_on_perpendicularBisector_equidistant_XI
                    Geo
                    A B M X O
                    bisAB
                    hMidAB
                    hAMX
                    hRightAB
                    hMbisAB
                    hXbisAB
                    hObisAB

                have hOA_OC :
                    Geo.Congruent O A O C :=
                  hilbert_point_on_perpendicularBisector_equidistant_XI
                    Geo
                    A C N Y O
                    bisAC
                    hMidAC
                    hANY
                    hRightAC
                    hNbisAC
                    hYbisAC
                    hObisAC

                exact
                  Exists.intro O
                    (And.intro hOA_OB hOA_OC)

------------------------------------------------------------------------
-- Congruence transport for the target of an angle-sum comparison
------------------------------------------------------------------------

/--
Replace the target angle in `HilbertTwoAnglesGreaterThanAngle` by a
congruent proper angle.

The decomposition case uses the permanent angle-decomposition
transport: an interior ray of the old target angle is transported to
an interior ray of the new target angle together with both component
angles.
-/
theorem hilbertTwoAnglesGreaterThanAngle_transport_target_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F E' Q' F' : Geo.Point)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hTarget' :
      Not (PrimCollinear Geo E' Q' F'))
    (hTargetCong :
      Geo.AngleCongruent
        E Q F
        E' Q' F') :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A O B
      C P D
      E' Q' F' := by

  have hFirst :
      Not (PrimCollinear Geo A O B) :=
    h.1

  have hSecond :
      Not (PrimCollinear Geo C P D) :=
    h.2.1

  have hTarget :
      Not (PrimCollinear Geo E Q F) :=
    h.2.2.1

  have hCore :=
    h.2.2.2

  refine
    And.intro hFirst
      (And.intro hSecond
        (And.intro hTarget' ?_))

  cases hCore with

  | inl hLess =>

      have hTargetCongSymm :
          Geo.AngleCongruent
            E' Q' F'
            E Q F :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          E Q F
          E' Q' F'
          hTargetCong

      have hLess' :
          HilbertAngleLess
            Geo
            E' Q' F'
            A O B :=
        hilbert_angleLess_transport_left
          Geo
          E Q F
          E' Q' F'
          A O B
          hLess
          hTarget'
          hTargetCongSymm

      exact Or.inl hLess'

  | inr hRest =>

      cases hRest with

      | inl hEq =>

          have hTargetCongSymm :
              Geo.AngleCongruent
                E' Q' F'
                E Q F :=
            Geometry.Geo.angle_congruent_symmetry
              Geo
              E Q F
              E' Q' F'
              hTargetCong

          have hEq' :
              Geo.AngleCongruent
                E' Q' F'
                A O B :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              E' Q' F'
              E Q F
              A O B
              hTargetCongSymm
              hEq

          exact Or.inr (Or.inl hEq')

      | inr hDecomp =>

          cases hDecomp with
          | intro X hXdata =>

              have hInside :
                  HilbertRayMeetsSegment
                    Geo Q X E F :=
                hXdata.1

              have hFirstPart :
                  Geo.AngleCongruent
                    A O B
                    E Q X :=
                hXdata.2.1

              have hRemainder :
                  HilbertAngleLess
                    Geo
                    X Q F
                    C P D :=
                hXdata.2.2

              cases
                  hilbert_interior_subangle_transport_both
                    Geo
                    Q E F X
                    E' Q' F'
                    hTarget
                    hTarget'
                    hInside
                    hTargetCong
              with
              | intro X' hX'data =>

                  have hInside' :
                      HilbertRayMeetsSegment
                        Geo Q' X' E' F' :=
                    hX'data.1

                  have hParts :=
                    hX'data.2

                  have hRightRaw :
                      Geo.AngleCongruent
                        F Q X
                        F' Q' X' :=
                    hParts.1

                  have hLeft :
                      Geo.AngleCongruent
                        E Q X
                        E' Q' X' :=
                    hParts.2

                  have hFirstPart' :
                      Geo.AngleCongruent
                        A O B
                        E' Q' X' :=
                    Geometry.Geo.angle_congruent_transitivity
                      Geo
                      A O B
                      E Q X
                      E' Q' X'
                      hFirstPart
                      hLeft

                  have hRight1 :
                      Geo.AngleCongruent
                        X Q F
                        F' Q' X' :=
                    (Geometry.Geo.angle_congruent_reverse_first
                      Geo
                      F Q X
                      F' Q' X').mp
                      hRightRaw

                  have hRight :
                      Geo.AngleCongruent
                        X Q F
                        X' Q' F' :=
                    (Geometry.Geo.angle_congruent_reverse_second
                      Geo
                      X Q F
                      F' Q' X').mp
                      hRight1

                  have hF'Q'E' :
                      Not (PrimCollinear Geo F' Q' E') := by
                    intro h
                    exact
                      hTarget'
                        (PrimCollinearSymm
                          Geo F' Q' E' h)

                  have hInsideRev :
                      HilbertRayMeetsSegment
                        Geo Q' X' F' E' :=
                    hilbert_angleDecomposition_ray_meets_segment_reverse
                      Geo
                      Q' X' E' F'
                      hInside'

                  have hF'Q'X' :
                      Not (PrimCollinear Geo F' Q' X') :=
                    (hilbert_interior_angle_less
                      Geo
                      Q' X' F' E'
                      hF'Q'E'
                      hInsideRev).1

                  have hX'Q'F' :
                      Not (PrimCollinear Geo X' Q' F') := by
                    intro h
                    exact
                      hF'Q'X'
                        (PrimCollinearSymm
                          Geo X' Q' F' h)

                  have hRightSymm :
                      Geo.AngleCongruent
                        X' Q' F'
                        X Q F :=
                    Geometry.Geo.angle_congruent_symmetry
                      Geo
                      X Q F
                      X' Q' F'
                      hRight

                  have hRemainder' :
                      HilbertAngleLess
                        Geo
                        X' Q' F'
                        C P D :=
                    hilbert_angleLess_transport_left
                      Geo
                      X Q F
                      X' Q' F'
                      C P D
                      hRemainder
                      hX'Q'F'
                      hRightSymm

                  exact
                    Or.inr
                      (Or.inr
                        (Exists.intro X'
                          (And.intro hInside'
                            (And.intro hFirstPart'
                              hRemainder'))))

------------------------------------------------------------------------
-- Full congruence transport for XI.23 angle data
------------------------------------------------------------------------

/--
Transport all three angles in a synthetic comparison

    first + second > target

through angle congruences.
-/
theorem hilbertTwoAnglesGreaterThanAngle_transport_all_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F
     A' O' B' C' P' D' E' Q' F' : Geo.Point)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hFirst' :
      Not (PrimCollinear Geo A' O' B'))
    (hSecond' :
      Not (PrimCollinear Geo C' P' D'))
    (hTarget' :
      Not (PrimCollinear Geo E' Q' F'))
    (hFirstCong :
      Geo.AngleCongruent
        A O B
        A' O' B')
    (hSecondCong :
      Geo.AngleCongruent
        C P D
        C' P' D')
    (hTargetCong :
      Geo.AngleCongruent
        E Q F
        E' Q' F') :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A' O' B'
      C' P' D'
      E' Q' F' := by

  have h1 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A' O' B'
        C P D
        E Q F :=
    hilbertTwoAnglesGreaterThanAngle_transport_first
      Geo
      A O B
      A' O' B'
      C P D
      E Q F
      h
      hFirst'
      hFirstCong

  have h2 :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A' O' B'
        C' P' D'
        E Q F :=
    hilbertTwoAnglesGreaterThanAngle_transport_second
      Geo
      A' O' B'
      C P D
      C' P' D'
      E Q F
      h1
      hSecond'
      hSecondCong

  exact
    hilbertTwoAnglesGreaterThanAngle_transport_target_XI
      Geo
      A' O' B'
      C' P' D'
      E Q F
      E' Q' F'
      h2
      hTarget'
      hTargetCong

/--
Transport the synthetic inequality

    first + second + third < four right angles

through congruences of all three proper angles.

The definition of the four-right-angle bound uses supplements of the
first two angles.  The new supplements are constructed by extending
the corresponding target rays, and `bookZero_43_supplements` transports
the supplement angles.
-/
theorem hilbertThreeAnglesLessThanFourRightAngles_transport_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F
     A' O' B' C' P' D' E' Q' F' : Geo.Point)
    (h :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F)
    (hFirst' :
      Not (PrimCollinear Geo A' O' B'))
    (hSecond' :
      Not (PrimCollinear Geo C' P' D'))
    (hTarget' :
      Not (PrimCollinear Geo E' Q' F'))
    (hFirstCong :
      Geo.AngleCongruent
        A O B
        A' O' B')
    (hSecondCong :
      Geo.AngleCongruent
        C P D
        C' P' D')
    (hTargetCong :
      Geo.AngleCongruent
        E Q F
        E' Q' F') :
    HilbertThreeAnglesLessThanFourRightAngles
      Geo
      A' O' B'
      C' P' D'
      E' Q' F' := by

  have hFirst :
      Not (PrimCollinear Geo A O B) :=
    h.1

  have hSecond :
      Not (PrimCollinear Geo C P D) :=
    h.2.1

  have hTarget :
      Not (PrimCollinear Geo E Q F) :=
    h.2.2.1

  cases h.2.2.2 with
  | intro X hXdata =>

    cases hXdata with
    | intro Y hXYdata =>

      have hBOX :
          Geo.Between B O X :=
        hXYdata.1

      have hDPY :
          Geo.Between D P Y :=
        hXYdata.2.1

      have hCompare :
          HilbertTwoAnglesGreaterThanAngle
            Geo
            A O X
            C P Y
            E Q F :=
        hXYdata.2.2

      ----------------------------------------------------------------
      -- Construct the two supplements in the target configuration.
      ----------------------------------------------------------------

      have hB'O'A' :
          Not (PrimCollinear Geo B' O' A') := by
        intro hcol
        exact
          hFirst'
            (PrimCollinearSymm
              Geo B' O' A' hcol)

      have hB'O' :
          Not (B' = O') :=
        hilbert_noncollinear_ne_first
          Geo B' O' A' hB'O'A'

      cases
          HilbertOrder.between_extension
            B' O' hB'O'
      with
      | intro X' hB'O'X' =>

        have hD'P'C' :
            Not (PrimCollinear Geo D' P' C') := by
          intro hcol
          exact
            hSecond'
              (PrimCollinearSymm
                Geo D' P' C' hcol)

        have hD'P' :
            Not (D' = P') :=
          hilbert_noncollinear_ne_first
            Geo D' P' C' hD'P'C'

        cases
            HilbertOrder.between_extension
              D' P' hD'P'
        with
        | intro Y' hD'P'Y' =>

          ----------------------------------------------------------------
          -- Properness of the two target supplement angles.
          ----------------------------------------------------------------

          have hB'O'X'data :=
            HilbertOrder.between_incidence
              B' O' X' hB'O'X'

          have hO'X' :
              Not (O' = X') :=
            hB'O'X'data.2.1

          have hB'O'X'col :
              PrimCollinear Geo B' O' X' :=
            hB'O'X'data.2.2.2.1

          have hO'X'B' :
              PrimCollinear Geo O' X' B' :=
            PrimCollinearCycle
              Geo B' O' X' hB'O'X'col

          have hA'O'X' :
              Not (PrimCollinear Geo A' O' X') := by
            intro hcol

            have hA'O'B' :
                PrimCollinear Geo A' O' B' :=
              hilbert_primCollinear_trans
                Geo
                A' O' X' B'
                hO'X'
                hcol
                hO'X'B'

            exact hFirst' hA'O'B'

          have hD'P'Y'data :=
            HilbertOrder.between_incidence
              D' P' Y' hD'P'Y'

          have hP'Y' :
              Not (P' = Y') :=
            hD'P'Y'data.2.1

          have hD'P'Y'col :
              PrimCollinear Geo D' P' Y' :=
            hD'P'Y'data.2.2.2.1

          have hP'Y'D' :
              PrimCollinear Geo P' Y' D' :=
            PrimCollinearCycle
              Geo D' P' Y' hD'P'Y'col

          have hC'P'Y' :
              Not (PrimCollinear Geo C' P' Y') := by
            intro hcol

            have hC'P'D' :
                PrimCollinear Geo C' P' D' :=
              hilbert_primCollinear_trans
                Geo
                C' P' Y' D'
                hP'Y'
                hcol
                hP'Y'D'

            exact hSecond' hC'P'D'

          ----------------------------------------------------------------
          -- Congruence of the first pair of supplement angles.
          ----------------------------------------------------------------

          have hBOA :
              Not (PrimCollinear Geo B O A) := by
            intro hcol
            exact
              hFirst
                (PrimCollinearSymm
                  Geo B O A hcol)

          have hAO :
              Not (A = O) :=
            hilbert_noncollinear_ne_first
              Geo A O B hFirst

          have hA'O' :
              Not (A' = O') :=
            hilbert_noncollinear_ne_first
              Geo A' O' B' hFirst'

          have hSupp1 :
              BookZeroSupplement
                Geo B O A A X :=
            And.intro
              (hilbert_sameRay_refl
                Geo O A hAO)
              hBOX

          have hSupp1' :
              BookZeroSupplement
                Geo B' O' A' A' X' :=
            And.intro
              (hilbert_sameRay_refl
                Geo O' A' hA'O')
              hB'O'X'

          have hFirstRev1 :
              Geo.AngleCongruent
                B O A
                A' O' B' :=
            (Geometry.Geo.angle_congruent_reverse_first
              Geo
              A O B
              A' O' B').mp
              hFirstCong

          have hFirstRev :
              Geo.AngleCongruent
                B O A
                B' O' A' :=
            (Geometry.Geo.angle_congruent_reverse_second
              Geo
              B O A
              A' O' B').mp
              hFirstRev1

          have hSuppCong1 :
              Geo.AngleCongruent
                A O X
                A' O' X' :=
            bookZero_43_supplements
              Geo
              B O A A X
              B' O' A' A' X'
              hFirstRev
              hSupp1
              hSupp1'
              hBOA
              hB'O'A'

          ----------------------------------------------------------------
          -- Congruence of the second pair of supplement angles.
          ----------------------------------------------------------------

          have hDPC :
              Not (PrimCollinear Geo D P C) := by
            intro hcol
            exact
              hSecond
                (PrimCollinearSymm
                  Geo D P C hcol)

          have hCP :
              Not (C = P) :=
            hilbert_noncollinear_ne_first
              Geo C P D hSecond

          have hC'P' :
              Not (C' = P') :=
            hilbert_noncollinear_ne_first
              Geo C' P' D' hSecond'

          have hSupp2 :
              BookZeroSupplement
                Geo D P C C Y :=
            And.intro
              (hilbert_sameRay_refl
                Geo P C hCP)
              hDPY

          have hSupp2' :
              BookZeroSupplement
                Geo D' P' C' C' Y' :=
            And.intro
              (hilbert_sameRay_refl
                Geo P' C' hC'P')
              hD'P'Y'

          have hSecondRev1 :
              Geo.AngleCongruent
                D P C
                C' P' D' :=
            (Geometry.Geo.angle_congruent_reverse_first
              Geo
              C P D
              C' P' D').mp
              hSecondCong

          have hSecondRev :
              Geo.AngleCongruent
                D P C
                D' P' C' :=
            (Geometry.Geo.angle_congruent_reverse_second
              Geo
              D P C
              C' P' D').mp
              hSecondRev1

          have hSuppCong2 :
              Geo.AngleCongruent
                C P Y
                C' P' Y' :=
            bookZero_43_supplements
              Geo
              D P C C Y
              D' P' C' C' Y'
              hSecondRev
              hSupp2
              hSupp2'
              hDPC
              hD'P'C'

          ----------------------------------------------------------------
          -- Transport the final comparison and rebuild the < 4R witness.
          ----------------------------------------------------------------

          have hCompare' :
              HilbertTwoAnglesGreaterThanAngle
                Geo
                A' O' X'
                C' P' Y'
                E' Q' F' :=
            hilbertTwoAnglesGreaterThanAngle_transport_all_XI
              Geo
              A O X
              C P Y
              E Q F
              A' O' X'
              C' P' Y'
              E' Q' F'
              hCompare
              hA'O'X'
              hC'P'Y'
              hTarget'
              hSuppCong1
              hSuppCong2
              hTargetCong

          exact
            And.intro hFirst'
              (And.intro hSecond'
                (And.intro hTarget'
                  (Exists.intro X'
                    (Exists.intro Y'
                      (And.intro hB'O'X'
                        (And.intro hD'P'Y'
                          hCompare'))))))

------------------------------------------------------------------------
-- Cyclic transport of the three XI.23 angle inequalities
------------------------------------------------------------------------

/--
Transport the three cyclic inequalities

    first + second > third,
    second + third > first,
    third + first > second

through congruences of the three underlying proper angles.
-/
theorem hilbertThreeAngleInequalities_transport_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F
     A' O' B' C' P' D' E' Q' F' : Geo.Point)
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
    (hFirst' :
      Not (PrimCollinear Geo A' O' B'))
    (hSecond' :
      Not (PrimCollinear Geo C' P' D'))
    (hThird' :
      Not (PrimCollinear Geo E' Q' F'))
    (hFirstCong :
      Geo.AngleCongruent
        A O B
        A' O' B')
    (hSecondCong :
      Geo.AngleCongruent
        C P D
        C' P' D')
    (hThirdCong :
      Geo.AngleCongruent
        E Q F
        E' Q' F') :
    HilbertTwoAnglesGreaterThanAngle
        Geo
        A' O' B'
        C' P' D'
        E' Q' F'
    /\
    HilbertTwoAnglesGreaterThanAngle
        Geo
        C' P' D'
        E' Q' F'
        A' O' B'
    /\
    HilbertTwoAnglesGreaterThanAngle
        Geo
        E' Q' F'
        A' O' B'
        C' P' D' := by

  have h12_3' :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A' O' B'
        C' P' D'
        E' Q' F' :=
    hilbertTwoAnglesGreaterThanAngle_transport_all_XI
      Geo
      A O B
      C P D
      E Q F
      A' O' B'
      C' P' D'
      E' Q' F'
      h12_3
      hFirst'
      hSecond'
      hThird'
      hFirstCong
      hSecondCong
      hThirdCong

  have h23_1' :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        C' P' D'
        E' Q' F'
        A' O' B' :=
    hilbertTwoAnglesGreaterThanAngle_transport_all_XI
      Geo
      C P D
      E Q F
      A O B
      C' P' D'
      E' Q' F'
      A' O' B'
      h23_1
      hSecond'
      hThird'
      hFirst'
      hSecondCong
      hThirdCong
      hFirstCong

  have h31_2' :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        E' Q' F'
        A' O' B'
        C' P' D' :=
    hilbertTwoAnglesGreaterThanAngle_transport_all_XI
      Geo
      E Q F
      A O B
      C P D
      E' Q' F'
      A' O' B'
      C' P' D'
      h31_2
      hThird'
      hFirst'
      hSecond'
      hThirdCong
      hFirstCong
      hSecondCong

  exact
    And.intro h12_3'
      (And.intro h23_1' h31_2')

------------------------------------------------------------------------
-- Segment-sum transport and triangle noncollinearity
------------------------------------------------------------------------

/--
Transport a strict two-segment sum comparison through congruent
replacements of both summands and of the target segment.

If

    AB + CD > EF

and

    AB ~= A'B',
    CD ~= C'D',
    EF ~= E'F',

then

    A'B' + C'D' > E'F'.
-/
theorem hilbertSegmentSumGreater_transport_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F
     A' B' C' D' E' F' : Geo.Point)
    (h :
      HilbertSegmentSumGreater
        Geo A B C D E F)
    (hAB :
      Geo.Congruent A B A' B')
    (hCD :
      Geo.Congruent C D C' D')
    (hEF :
      Geo.Congruent E F E' F') :
    HilbertSegmentSumGreater
      Geo A' B' C' D' E' F' := by

  cases h with
  | intro P hP =>

    have hABP :
        Geo.Between A B P :=
      hP.1

    have hBP_CD :
        Geo.Congruent B P C D :=
      hP.2.1

    have hEF_AP :
        HilbertSegmentLess Geo E F A P :=
      hP.2.2

    have hABne :
        Not (A = B) :=
      (HilbertOrder.between_incidence
        A B P hABP).1

    have hBPne :
        Not (B = P) :=
      (HilbertOrder.between_incidence
        A B P hABP).2.1

    have hCDne :
        Not (C = D) :=
      bookZero_nullSegment3
        Geo
        B P
        C D
        hBPne
        hBP_CD

    have hA'B'ne :
        Not (A' = B') :=
      bookZero_nullSegment3
        Geo
        A B
        A' B'
        hABne
        hAB

    have hC'D'ne :
        Not (C' = D') :=
      bookZero_nullSegment3
        Geo
        C D
        C' D'
        hCDne
        hCD

    cases
        hilbert_segmentSum_witness
          Geo
          A' B'
          C' D'
          hA'B'ne
          hC'D'ne
    with
    | intro P' hP' =>

      have hA'B'P' :
          Geo.Between A' B' P' :=
        hP'.1

      have hB'P'_C'D' :
          Geo.Congruent B' P' C' D' :=
        hP'.2

      have hC'D'_B'P' :
          Geo.Congruent C' D' B' P' :=
        hilbert_congruent_symmetry
          Geo
          B' P'
          C' D'
          hB'P'_C'D'

      have hBP_C'D' :
          Geo.Congruent B P C' D' :=
        hilbert_congruent_transitivity
          Geo
          B P
          C D
          C' D'
          hBP_CD
          hCD

      have hBP_B'P' :
          Geo.Congruent B P B' P' :=
        hilbert_congruent_transitivity
          Geo
          B P
          C' D'
          B' P'
          hBP_C'D'
          hC'D'_B'P'

      have hAP_A'P' :
          Geo.Congruent A P A' P' :=
        HilbertCongruence.segment_additivity
          (Geo := Geo)
          A B P
          A' B' P'
          hABP
          hA'B'P'
          hAB
          hBP_B'P'

      have hEF_A'P' :
          HilbertSegmentLess Geo E F A' P' :=
        bookZero_30_lessThanCongruence
          Geo
          E F
          A P
          A' P'
          hEF_AP
          hAP_A'P'

      have hE'F'_A'P' :
          HilbertSegmentLess Geo E' F' A' P' :=
        bookZero_32_lessThanCongruence2
          Geo
          E F
          A' P'
          E' F'
          hEF_A'P'
          hEF

      exact
        Exists.intro P'
          (And.intro hA'B'P'
            (And.intro hB'P'_C'D'
              hE'F'_A'P'))

/--
Three distinct points whose three sides satisfy the strict triangle
inequalities cannot be collinear.

The inequalities are oriented to match the three possible Hilbert
betweenness orders:

    AB + BC > AC,
    BA + AC > BC,
    AC + CB > AB.
-/
theorem hilbert_triangle_noncollinear_of_segment_sums_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hAB : Not (A = B))
    (hBC : Not (B = C))
    (hAC : Not (A = C))
    (hAB_BC_AC :
      HilbertSegmentSumGreater
        Geo A B B C A C)
    (hBA_AC_BC :
      HilbertSegmentSumGreater
        Geo B A A C B C)
    (hAC_CB_AB :
      HilbertSegmentSumGreater
        Geo A C C B A B) :
    Not (PrimCollinear Geo A B C) := by

  intro hABCcol

  cases
      hilbert_between_trichotomy
        Geo
        A B C
        hAB
        hBC
        hAC
        hABCcol
  with

  | inl hABC =>

      cases hAB_BC_AC with
      | intro P hP =>

        have hABP :
            Geo.Between A B P :=
          hP.1

        have hBP_BC :
            Geo.Congruent B P B C :=
          hP.2.1

        have hAC_AP :
            HilbertSegmentLess Geo A C A P :=
          hP.2.2

        have hPC :
            P = C :=
          bookZero_extensionUnique
            Geo
            A B
            P C
            hABP
            hABC
            hBP_BC

        subst P

        exact
          (hilbert_segmentLess_asymm
            Geo
            A C
            A C
            hAC_AP)
            hAC_AP

  | inr hRest =>

      cases hRest with

      | inl hBAC =>

          cases hBA_AC_BC with
          | intro P hP =>

            have hBAP :
                Geo.Between B A P :=
              hP.1

            have hAP_AC :
                Geo.Congruent A P A C :=
              hP.2.1

            have hBC_BP :
                HilbertSegmentLess Geo B C B P :=
              hP.2.2

            have hPC :
                P = C :=
              bookZero_extensionUnique
                Geo
                B A
                P C
                hBAP
                hBAC
                hAP_AC

            subst P

            exact
              (hilbert_segmentLess_asymm
                Geo
                B C
                B C
                hBC_BP)
                hBC_BP

      | inr hACB =>

          cases hAC_CB_AB with
          | intro P hP =>

            have hACP :
                Geo.Between A C P :=
              hP.1

            have hCP_CB :
                Geo.Congruent C P C B :=
              hP.2.1

            have hAB_AP :
                HilbertSegmentLess Geo A B A P :=
              hP.2.2

            have hPB :
                P = B :=
              bookZero_extensionUnique
                Geo
                A C
                P B
                hACP
                hACB
                hCP_CB

            subst P

            exact
              (hilbert_segmentLess_asymm
                Geo
                A B
                A B
                hAB_AP)
                hAB_AP

------------------------------------------------------------------------
-- Parallel point-lines and concrete carrier lines
------------------------------------------------------------------------

/--
If two nondegenerate point-lines are parallel and `l`, `m` are their
concrete Hilbert incidence carriers, then the carrier lines are disjoint.

This is the converse bridge to
`hilbert_parallel_of_disjoint_carrier_lines_XI`.
-/
theorem hilbert_disjoint_carrier_lines_of_parallel_XI
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (l m : Geo.Line)
    (hParallel : Geo.Parallel A B C D)
    (hAl : HilbertIncidence.OnLine A l)
    (hBl : HilbertIncidence.OnLine B l)
    (hCm : HilbertIncidence.OnLine C m)
    (hDm : HilbertIncidence.OnLine D m) :
    HilbertLinesDisjoint Geo l m := by

  intro hMeet

  cases hMeet with
  | intro X hXdata =>

      have hXl :
          HilbertIncidence.OnLine X l :=
        hXdata.1

      have hXm :
          HilbertIncidence.OnLine X m :=
        hXdata.2

      have hXAB :
          Geo.PointLine A B X :=
        (hilbert_mem_pointLine_iff_onLine
          Geo
          A B X
          l
          hParallel.1
          hAl
          hBl).mpr
          hXl

      have hXCD :
          Geo.PointLine C D X :=
        (hilbert_mem_pointLine_iff_onLine
          Geo
          C D X
          m
          hParallel.2.1
          hCm
          hDm).mpr
          hXm

      exact
        Set.disjoint_left.mp
          hParallel.2.2
          hXAB
          hXCD

------------------------------------------------------------------------
-- A parallel through an interior side point meets the opposite side
------------------------------------------------------------------------

/--
Pasch form used in XI.23.

Let P lie strictly between O and L in a nondegenerate triangle OLM.
If a line q passes through P and is disjoint from the carrier of LM,
then q meets the open side OM.

The alternative Pasch exit through LM is excluded by disjointness.
-/
theorem hilbert_inner_disjoint_line_meets_opposite_side_XI
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O L M P : Geo.Point)
    (q lineLM : Geo.Line)
    (hOLM : Not (PrimCollinear Geo O L M))
    (hOPL : Geo.Between O P L)
    (hPq : HilbertIncidence.OnLine P q)
    (hLlineLM : HilbertIncidence.OnLine L lineLM)
    (hMlineLM : HilbertIncidence.OnLine M lineLM)
    (hDisjoint : HilbertLinesDisjoint Geo q lineLM) :
    exists Q : Geo.Point,
      Geo.Between O Q M /\
      HilbertIncidence.OnLine Q q := by

  have hOq :
      Not (HilbertIncidence.OnLine O q) := by
    intro hOq

    have hOP :
        Not (O = P) :=
      (HilbertOrder.between_incidence
        O P L hOPL).1

    have hOPLcol :
        PrimCollinear Geo O P L :=
      (HilbertOrder.between_incidence
        O P L hOPL).2.2.2.1

    cases hOPLcol with
    | intro lineOL hLineOL =>

        have hOlineOL :
            HilbertIncidence.OnLine O lineOL :=
          hLineOL.1

        have hPlineOL :
            HilbertIncidence.OnLine P lineOL :=
          hLineOL.2.1

        have hLlineOL :
            HilbertIncidence.OnLine L lineOL :=
          hLineOL.2.2

        have hq_eq_lineOL :
            q = lineOL :=
          HilbertPlaneIncidence.line_unique
            O P hOP
            q lineOL
            hOq hPq
            hOlineOL hPlineOL

        have hLq :
            HilbertIncidence.OnLine L q := by
          rw [hq_eq_lineOL]
          exact hLlineOL

        exact
          hDisjoint
            (Exists.intro L
              (And.intro hLq hLlineLM))

  have hLq :
      Not (HilbertIncidence.OnLine L q) := by
    intro hLq
    exact
      hDisjoint
        (Exists.intro L
          (And.intro hLq hLlineLM))

  have hMq :
      Not (HilbertIncidence.OnLine M q) := by
    intro hMq
    exact
      hDisjoint
        (Exists.intro M
          (And.intro hMq hMlineLM))

  have hMeetOL :
      HilbertSegmentMeetsLine Geo O L q :=
    Exists.intro P
      (And.intro hOPL hPq)

  have hPasch :
      HilbertSegmentMeetsLine Geo O M q \/
      HilbertSegmentMeetsLine Geo L M q :=
    HilbertOrder.pasch
      O L M
      hOLM
      q
      hOq hLq hMq
      hMeetOL

  cases hPasch with

  | inl hMeetOM =>
      cases hMeetOM with
      | intro Q hQ =>
          exact
            Exists.intro Q
              (And.intro hQ.1 hQ.2)

  | inr hMeetLM =>
      cases hMeetLM with
      | intro X hX =>
          have hXlineLM :
              HilbertIncidence.OnLine X lineLM :=
            hilbert_between_on_line
              Geo
              L X M
              lineLM
              hLlineLM hMlineLM
              hX.1

          exact
            False.elim
              (hDisjoint
                (Exists.intro X
                  (And.intro hX.2 hXlineLM)))

/--
In a nondegenerate triangle OLM, a Euclidean parallel to LM through
an interior point P of OL meets the open side OM.

The returned point Q is already in the exact form needed later in
XI.23:

    O-P-L,
    O-Q-M,
    PQ || LM.
-/
theorem hilbert_parallel_through_inner_side_point_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O L M P : Geo.Point)
    (hOLM : Not (PrimCollinear Geo O L M))
    (hOPL : Geo.Between O P L) :
    exists Q : Geo.Point,
      Geo.Between O Q M /\
      Geo.Parallel P Q L M := by

  have hOPLdata :=
    HilbertOrder.between_incidence
      O P L hOPL

  have hOP :
      Not (O = P) :=
    hOPLdata.1

  have hPL :
      Not (P = L) :=
    hOPLdata.2.1

  have hLP :
      Not (L = P) := by
    intro hLP
    exact hPL hLP.symm

  have hOL :
      Not (O = L) :=
    hOPLdata.2.2.1

  have hOPLcol :
      PrimCollinear Geo O P L :=
    hOPLdata.2.2.2.1

  have hOLP :
      PrimCollinear Geo O L P :=
    PrimCollinearRotate
      Geo O P L hOPLcol

  have hLMO :
      Not (PrimCollinear Geo L M O) := by
    intro hLMO

    have hOML :
        PrimCollinear Geo O M L :=
      PrimCollinearSymm
        Geo L M O hLMO

    have hOLM' :
        PrimCollinear Geo O L M :=
      PrimCollinearRotate
        Geo O M L hOML

    exact hOLM hOLM'

  have hLM :
      Not (L = M) :=
    hilbert_noncollinear_ne_first
      Geo
      L M O
      hLMO

  have hLMP :
      Not (PrimCollinear Geo L M P) := by
    intro hLMP

    have hLPM :
        PrimCollinear Geo L P M :=
      PrimCollinearRotate
        Geo L M P hLMP

    have hOLM' :
        PrimCollinear Geo O L M :=
      hilbert_primCollinear_trans
        Geo
        O L P M
        hLP
        hOLP
        hLPM

    exact hOLM hOLM'

  cases
      hilbert_parallel_through_point_exists
        Geo
        L M P
        hLM
        hLMP
  with
  | intro R hR =>

      have hPR :
          Not (P = R) :=
        hR.1

      have hParallelLM_PR :
          Geo.Parallel L M P R :=
        hR.2

      cases
          HilbertPlaneIncidence.line_through
            L M hLM
      with
      | intro lineLM hLineLM =>

          have hLlineLM :
              HilbertIncidence.OnLine L lineLM :=
            hLineLM.1

          have hMlineLM :
              HilbertIncidence.OnLine M lineLM :=
            hLineLM.2

          cases
              HilbertPlaneIncidence.line_through
                P R hPR
          with
          | intro linePR hLinePR =>

              have hPlinePR :
                  HilbertIncidence.OnLine P linePR :=
                hLinePR.1

              have hRlinePR :
                  HilbertIncidence.OnLine R linePR :=
                hLinePR.2

              have hDisjoint :
                  HilbertLinesDisjoint
                    Geo linePR lineLM := by

                have hDisjointLM_PR :
                    HilbertLinesDisjoint
                      Geo lineLM linePR :=
                  hilbert_disjoint_carrier_lines_of_parallel_XI
                    Geo
                    L M P R
                    lineLM linePR
                    hParallelLM_PR
                    hLlineLM hMlineLM
                    hPlinePR hRlinePR

                intro hMeet

                cases hMeet with
                | intro X hX =>
                    exact
                      hDisjointLM_PR
                        (Exists.intro X
                          (And.intro hX.2 hX.1))

              cases
                  hilbert_inner_disjoint_line_meets_opposite_side_XI
                    Geo
                    O L M P
                    linePR lineLM
                    hOLM
                    hOPL
                    hPlinePR
                    hLlineLM hMlineLM
                    hDisjoint
              with
              | intro Q hQ =>

                  have hOQM :
                      Geo.Between O Q M :=
                    hQ.1

                  have hQlinePR :
                      HilbertIncidence.OnLine Q linePR :=
                    hQ.2

                  have hOQMdata :=
                    HilbertOrder.between_incidence
                      O Q M hOQM

                  have hOQ :
                      Not (O = Q) :=
                    hOQMdata.1

                  have hPQ :
                      Not (P = Q) := by
                    intro hPQ
                    subst Q

                    have hOPMcol :
                        PrimCollinear Geo O P M :=
                      hOQMdata.2.2.2.1

                    have hLOP :
                        PrimCollinear Geo L O P :=
                      PrimCollinearRotate
                        Geo L P O
                        (PrimCollinearSymm
                          Geo O P L hOPLcol)

                    have hLOM :
                        PrimCollinear Geo L O M :=
                      hilbert_primCollinear_trans
                        Geo
                        L O P M
                        hOP
                        hLOP
                        hOPMcol

                    exact
                      hOLM
                        (PrimCollinearSwap
                          Geo L O M hLOM)

                  have hPQR :
                      PrimCollinear Geo P Q R :=
                    Exists.intro linePR
                      (And.intro hPlinePR
                        (And.intro hQlinePR hRlinePR))

                  have hParallelPR_LM :
                      Geo.Parallel P R L M :=
                    ParallelSymmetry
                      Geo
                      L M P R
                      hParallelLM_PR

                  have hParallelPQ_LM :
                      Geo.Parallel P Q L M :=
                    collinear_parallel_trans
                      Geo
                      P Q R
                      L M
                      hPQ
                      hPQR
                      hParallelPR_LM

                  exact
                    Exists.intro Q
                      (And.intro hOQM hParallelPQ_LM)

------------------------------------------------------------------------
-- Corresponding angles for an inner parallel segment
------------------------------------------------------------------------

/--
If P and Q lie on the two sides OL and OM of a nondegenerate triangle
and PQ is parallel to LM, then the two base angles of the inner triangle
OPQ agree with the corresponding base angles of OLM.

This is a configuration wrapper around Euclid I.29.
-/
theorem hilbert_inner_parallel_corresponding_angles_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O P L Q M : Geo.Point)
    (hOLM : Not (PrimCollinear Geo O L M))
    (hOPL : Geo.Between O P L)
    (hOQM : Geo.Between O Q M)
    (hParallel : Geo.Parallel P Q L M) :
    Geo.AngleCongruent O P Q O L M /\
    Geo.AngleCongruent O Q P O M L := by

  have hOPLdata :=
    HilbertOrder.between_incidence O P L hOPL

  have hOQMdata :=
    HilbertOrder.between_incidence O Q M hOQM

  have hOP : Not (O = P) := hOPLdata.1
  have hPL : Not (P = L) := hOPLdata.2.1
  have hOL : Not (O = L) := hOPLdata.2.2.1

  have hOQ : Not (O = Q) := hOQMdata.1
  have hQM : Not (Q = M) := hOQMdata.2.1
  have hOM : Not (O = M) := hOQMdata.2.2.1

  have hPQ : Not (P = Q) :=
    hParallel.1

  have hLM : Not (L = M) :=
    hParallel.2.1

  have hOPLcol :
      PrimCollinear Geo O P L :=
    hOPLdata.2.2.2.1

  have hOQMcol :
      PrimCollinear Geo O Q M :=
    hOQMdata.2.2.2.1

  cases
      HilbertPlaneIncidence.line_through
        O L hOL
  with
  | intro lineOL hLineOL =>

      have hOlineOL :
          HilbertIncidence.OnLine O lineOL :=
        hLineOL.1

      have hLlineOL :
          HilbertIncidence.OnLine L lineOL :=
        hLineOL.2

      have hPlineOL :
          HilbertIncidence.OnLine P lineOL :=
        hilbert_between_on_line
          Geo O P L
          lineOL
          hOlineOL hLlineOL
          hOPL

      cases
          HilbertPlaneIncidence.line_through
            O M hOM
      with
      | intro lineOM hLineOM =>

          have hOlineOM :
              HilbertIncidence.OnLine O lineOM :=
            hLineOM.1

          have hMlineOM :
              HilbertIncidence.OnLine M lineOM :=
            hLineOM.2

          have hQlineOM :
              HilbertIncidence.OnLine Q lineOM :=
            hilbert_between_on_line
              Geo O Q M
              lineOM
              hOlineOM hMlineOM
              hOQM

          have hMnotOL :
              Not (HilbertIncidence.OnLine M lineOL) := by
            intro hMlineOL
            exact
              hOLM
                (Exists.intro lineOL
                  (And.intro hOlineOL
                    (And.intro hLlineOL hMlineOL)))

          have hLnotOM :
              Not (HilbertIncidence.OnLine L lineOM) := by
            intro hLlineOM
            exact
              hOLM
                (Exists.intro lineOM
                  (And.intro hOlineOM
                    (And.intro hLlineOM hMlineOM)))

          have hQnotOL :
              Not (HilbertIncidence.OnLine Q lineOL) := by
            intro hQlineOL

            have hEq :
                lineOL = lineOM :=
              HilbertPlaneIncidence.line_unique
                O Q hOQ
                lineOL lineOM
                hOlineOL hQlineOL
                hOlineOM hQlineOM

            have hMlineOL :
                HilbertIncidence.OnLine M lineOL := by
              rw [hEq]
              exact hMlineOM

            exact hMnotOL hMlineOL

          have hPnotOM :
              Not (HilbertIncidence.OnLine P lineOM) := by
            intro hPlineOM

            have hEq :
                lineOL = lineOM :=
              HilbertPlaneIncidence.line_unique
                O P hOP
                lineOL lineOM
                hOlineOL hPlineOL
                hOlineOM hPlineOM

            have hLlineOM :
                HilbertIncidence.OnLine L lineOM := by
              rw [<- hEq]
              exact hLlineOL

            exact hLnotOM hLlineOM

          ----------------------------------------------------------------
          -- First corresponding angle: OPQ ~= OLM.
          ----------------------------------------------------------------

          have hQP :
              Not (Q = P) := by
            intro hQP
            exact hPQ hQP.symm

          cases
              HilbertOrder.between_extension
                Q P hQP
          with
          | intro A hQPA =>

              have hAPQ :
                  Geo.Between A P Q :=
                (HilbertOrder.between_incidence
                  Q P A hQPA).2.2.2.2

              have hAPQdata :=
                HilbertOrder.between_incidence
                  A P Q hAPQ

              have hAP :
                  Not (A = P) :=
                hAPQdata.1

              have hAQ :
                  Not (A = Q) :=
                hAPQdata.2.2.1

              have hAPQcol :
                  PrimCollinear Geo A P Q :=
                hAPQdata.2.2.2.1

              have hML :
                  Not (M = L) := by
                intro hML
                exact hLM hML.symm

              cases
                  HilbertOrder.between_extension
                    M L hML
              with
              | intro C hMLC =>

                  have hCLM :
                      Geo.Between C L M :=
                    (HilbertOrder.between_incidence
                      M L C hMLC).2.2.2.2

                  have hCLMdata :=
                    HilbertOrder.between_incidence
                      C L M hCLM

                  have hCM :
                      Not (C = M) :=
                    hCLMdata.2.2.1

                  have hCLMcol :
                      PrimCollinear Geo C L M :=
                    hCLMdata.2.2.2.1

                  have hAQ_LM :
                      Geo.Parallel A Q L M :=
                    ParallelCollinearLeft
                      Geo
                      P Q A L M
                      hAQ
                      hParallel
                      hAPQcol

                  have hLM_AQ :
                      Geo.Parallel L M A Q :=
                    ParallelSymmetry
                      Geo A Q L M hAQ_LM

                  have hCM_AQ :
                      Geo.Parallel C M A Q :=
                    ParallelCollinearLeft
                      Geo
                      L M C A Q
                      hCM
                      hLM_AQ
                      hCLMcol

                  have hAQ_CM :
                      Geo.Parallel A Q C M :=
                    ParallelSymmetry
                      Geo C M A Q hCM_AQ

                  have hAnotOL :
                      Not (HilbertIncidence.OnLine A lineOL) := by
                    intro hAlineOL

                    cases hAPQcol with
                    | intro lineAPQ hLineAPQ =>

                        have hAlineAPQ :
                            HilbertIncidence.OnLine A lineAPQ :=
                          hLineAPQ.1

                        have hPlineAPQ :
                            HilbertIncidence.OnLine P lineAPQ :=
                          hLineAPQ.2.1

                        have hQlineAPQ :
                            HilbertIncidence.OnLine Q lineAPQ :=
                          hLineAPQ.2.2

                        have hEq :
                            lineAPQ = lineOL :=
                          HilbertPlaneIncidence.line_unique
                            A P hAP
                            lineAPQ lineOL
                            hAlineAPQ hPlineAPQ
                            hAlineOL hPlineOL

                        have hQlineOL :
                            HilbertIncidence.OnLine Q lineOL := by
                          rw [<- hEq]
                          exact hQlineAPQ

                        exact hQnotOL hQlineOL

                  have hOppositeAQ :
                      HilbertOppositeSide
                        Geo A Q lineOL :=
                    And.intro hAnotOL
                      (And.intro hQnotOL
                        (Exists.intro P
                          (And.intro hAPQ hPlineOL)))

                  have hRayOQQ :
                      HilbertSameRay Geo O Q Q :=
                    hilbert_sameRay_refl
                      Geo O Q
                      (by
                        intro hQO
                        exact hOQ hQO.symm)

                  have hRayOQM :
                      HilbertSameRay Geo O Q M :=
                    hilbert_sameRay_of_between
                      Geo O Q M hOQM

                  have hQMSame :
                      HilbertSameSide
                        Geo Q M lineOL :=
                    hilbert_sameRay_points_sameSide
                      Geo
                      O Q
                      Q M
                      L
                      lineOM lineOL
                      hOlineOM hQlineOM
                      hOlineOL hLlineOL
                      hLnotOM
                      hRayOQQ
                      hRayOQM

                  have hOppositeAM :
                      HilbertOppositeSide
                        Geo A M lineOL :=
                    hilbert_oppositeSide_transport_right
                      Geo
                      A Q M lineOL
                      hOppositeAQ
                      hQMSame

                  have hRaw1 :
                      Geo.AngleCongruent
                        O P Q
                        P L M :=
                    euclid_proposition_29_corresponding
                      (Geo := Geo)
                      A Q
                      C M
                      O P L
                      lineOL
                      hAPQ
                      hCLM
                      hOPL
                      hPL
                      hPlineOL
                      hLlineOL
                      hOppositeAM
                      hAQ_CM

                  have hLPO :
                      Geo.Between L P O :=
                    hOPLdata.2.2.2.2

                  have hRayLPO :
                      HilbertSameRay Geo L P O :=
                    hilbert_sameRay_of_between
                      Geo L P O hLPO

                  have hAtL :
                      Geo.Angle P L M =
                      Geo.Angle O L M :=
                    hilbert_angle_eq_of_sameRay_first
                      Geo
                      L P O M
                      hRayLPO

                  have hAngle1 :
                      Geo.AngleCongruent
                        O P Q
                        O L M := by
                    unfold Geometry.Geo.AngleCongruent
                      at hRaw1 |- 
                    rw [<- hAtL]
                    exact hRaw1

                  --------------------------------------------------------
                  -- Second corresponding angle: OQP ~= OML.
                  --------------------------------------------------------

                  cases
                      HilbertOrder.between_extension
                        P Q hPQ
                  with
                  | intro A2 hPQA2 =>

                      have hA2QP :
                          Geo.Between A2 Q P :=
                        (HilbertOrder.between_incidence
                          P Q A2 hPQA2).2.2.2.2

                      have hA2QPdata :=
                        HilbertOrder.between_incidence
                          A2 Q P hA2QP

                      have hA2Q :
                          Not (A2 = Q) :=
                        hA2QPdata.1

                      have hA2P :
                          Not (A2 = P) :=
                        hA2QPdata.2.2.1

                      have hA2QPcol :
                          PrimCollinear Geo A2 Q P :=
                        hA2QPdata.2.2.2.1

                      cases
                          HilbertOrder.between_extension
                            L M hLM
                      with
                      | intro C2 hLMC2 =>

                          have hC2ML :
                              Geo.Between C2 M L :=
                            (HilbertOrder.between_incidence
                              L M C2 hLMC2).2.2.2.2

                          have hC2MLdata :=
                            HilbertOrder.between_incidence
                              C2 M L hC2ML

                          have hC2L :
                              Not (C2 = L) :=
                            hC2MLdata.2.2.1

                          have hC2MLcol :
                              PrimCollinear Geo C2 M L :=
                            hC2MLdata.2.2.2.1

                          have hQP_LM :
                              Geo.Parallel Q P L M :=
                            ParallelSwapFirstLine
                              Geo P Q L M hParallel

                          have hQP_ML :
                              Geo.Parallel Q P M L :=
                            ParallelSwapSecondLine
                              Geo Q P L M hQP_LM

                          have hA2P_ML :
                              Geo.Parallel A2 P M L :=
                            ParallelCollinearLeft
                              Geo
                              Q P A2 M L
                              hA2P
                              hQP_ML
                              hA2QPcol

                          have hML_A2P :
                              Geo.Parallel M L A2 P :=
                            ParallelSymmetry
                              Geo A2 P M L hA2P_ML

                          have hC2L_A2P :
                              Geo.Parallel C2 L A2 P :=
                            ParallelCollinearLeft
                              Geo
                              M L C2 A2 P
                              hC2L
                              hML_A2P
                              hC2MLcol

                          have hA2P_C2L :
                              Geo.Parallel A2 P C2 L :=
                            ParallelSymmetry
                              Geo C2 L A2 P hC2L_A2P

                          have hA2notOM :
                              Not
                                (HilbertIncidence.OnLine
                                  A2 lineOM) := by
                            intro hA2lineOM

                            cases hA2QPcol with
                            | intro lineA2QP hLineA2QP =>

                                have hA2lineA2QP :
                                    HilbertIncidence.OnLine
                                      A2 lineA2QP :=
                                  hLineA2QP.1

                                have hQlineA2QP :
                                    HilbertIncidence.OnLine
                                      Q lineA2QP :=
                                  hLineA2QP.2.1

                                have hPlineA2QP :
                                    HilbertIncidence.OnLine
                                      P lineA2QP :=
                                  hLineA2QP.2.2

                                have hEq :
                                    lineA2QP = lineOM :=
                                  HilbertPlaneIncidence.line_unique
                                    A2 Q hA2Q
                                    lineA2QP lineOM
                                    hA2lineA2QP hQlineA2QP
                                    hA2lineOM hQlineOM

                                have hPlineOM :
                                    HilbertIncidence.OnLine
                                      P lineOM := by
                                  rw [<- hEq]
                                  exact hPlineA2QP

                                exact hPnotOM hPlineOM

                          have hOppositeA2P :
                              HilbertOppositeSide
                                Geo A2 P lineOM :=
                            And.intro hA2notOM
                              (And.intro hPnotOM
                                (Exists.intro Q
                                  (And.intro
                                    hA2QP
                                    hQlineOM)))

                          have hRayOPP :
                              HilbertSameRay Geo O P P :=
                            hilbert_sameRay_refl
                              Geo O P
                              (by
                                intro hPO
                                exact hOP hPO.symm)

                          have hRayOPL :
                              HilbertSameRay Geo O P L :=
                            hilbert_sameRay_of_between
                              Geo O P L hOPL

                          have hPLSame :
                              HilbertSameSide
                                Geo P L lineOM :=
                            hilbert_sameRay_points_sameSide
                              Geo
                              O P
                              P L
                              M
                              lineOL lineOM
                              hOlineOL hPlineOL
                              hOlineOM hMlineOM
                              hMnotOL
                              hRayOPP
                              hRayOPL

                          have hOppositeA2L :
                              HilbertOppositeSide
                                Geo A2 L lineOM :=
                            hilbert_oppositeSide_transport_right
                              Geo
                              A2 P L lineOM
                              hOppositeA2P
                              hPLSame

                          have hRaw2 :
                              Geo.AngleCongruent
                                O Q P
                                Q M L :=
                            euclid_proposition_29_corresponding
                              (Geo := Geo)
                              A2 P
                              C2 L
                              O Q M
                              lineOM
                              hA2QP
                              hC2ML
                              hOQM
                              hQM
                              hQlineOM
                              hMlineOM
                              hOppositeA2L
                              hA2P_C2L

                          have hMQO :
                              Geo.Between M Q O :=
                            hOQMdata.2.2.2.2

                          have hRayMQO :
                              HilbertSameRay Geo M Q O :=
                            hilbert_sameRay_of_between
                              Geo M Q O hMQO

                          have hAtM :
                              Geo.Angle Q M L =
                              Geo.Angle O M L :=
                            hilbert_angle_eq_of_sameRay_first
                              Geo
                              M Q O L
                              hRayMQO

                          have hAngle2 :
                              Geo.AngleCongruent
                                O Q P
                                O M L := by
                            unfold Geometry.Geo.AngleCongruent
                              at hRaw2 |-
                            rw [<- hAtM]
                            exact hRaw2

                          exact
                            And.intro hAngle1 hAngle2

------------------------------------------------------------------------
-- Equal cuts on equal sides give an inner parallel
------------------------------------------------------------------------

/--
Let P and Q lie strictly inside the equal sides OL and OM of the
nondegenerate isosceles triangle OLM. If the initial cuts are equal,

    OP ~= OQ,

then the joining segment is parallel to the base:

    PQ || LM.

The proof is synthetic and avoids Book VI. Construct the parallel to
LM through P; Pasch gives its intersection Q' with OM. I.29 transports
the base angles of the large isosceles triangle to OPQ'. I.6 then gives
OP ~= OQ'. Uniqueness of segment construction on ray OM yields Q'=Q.
-/
theorem hilbert_equal_cuts_on_equal_sides_parallel_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O P L Q M : Geo.Point)
    (hOLM : Not (PrimCollinear Geo O L M))
    (hOPL : Geo.Between O P L)
    (hOQM : Geo.Between O Q M)
    (hOL_OM : Geo.Congruent O L O M)
    (hOP_OQ : Geo.Congruent O P O Q) :
    Geo.Parallel P Q L M := by

  cases
      hilbert_parallel_through_inner_side_point_XI
        Geo
        O L M P
        hOLM
        hOPL
  with
  | intro Q' hQ' =>

      have hOQ'M :
          Geo.Between O Q' M :=
        hQ'.1

      have hPQ'_LM :
          Geo.Parallel P Q' L M :=
        hQ'.2

      have hAngles :=
        hilbert_inner_parallel_corresponding_angles_XI
          Geo
          O P L Q' M
          hOLM
          hOPL
          hOQ'M
          hPQ'_LM

      have hOPQ'_OLM :
          Geo.AngleCongruent O P Q' O L M :=
        hAngles.1

      have hOQ'P_OML :
          Geo.AngleCongruent O Q' P O M L :=
        hAngles.2

      have hLOM :
          Not (PrimCollinear Geo L O M) := by
        intro h
        cases h with
        | intro l hl =>
            exact
              hOLM
                (Exists.intro l
                  (And.intro hl.2.1
                    (And.intro hl.1 hl.2.2)))

      have hBase :
          Geo.AngleCongruent O L M O M L :=
        hilbert_isosceles_base_angles
          Geo
          O L M
          hOLM
          hOL_OM

      have hOML_OQ'P :
          Geo.AngleCongruent O M L O Q' P :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          O Q' P
          O M L
          hOQ'P_OML

      have hOPQ'_OML :
          Geo.AngleCongruent O P Q' O M L :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          O P Q'
          O L M
          O M L
          hOPQ'_OLM
          hBase

      have hSmallBase :
          Geo.AngleCongruent O P Q' O Q' P :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          O P Q'
          O M L
          O Q' P
          hOPQ'_OML
          hOML_OQ'P

      have hOPLdata :=
        HilbertOrder.between_incidence
          O P L hOPL

      have hOQ'Mdata :=
        HilbertOrder.between_incidence
          O Q' M hOQ'M

      have hOP :
          Not (O = P) :=
        hOPLdata.1

      have hOQ' :
          Not (O = Q') :=
        hOQ'Mdata.1

      have hOLP :
          PrimCollinear Geo O L P :=
        PrimCollinearRotate
          Geo O P L
          hOPLdata.2.2.2.1

      have hOMQ' :
          PrimCollinear Geo O M Q' :=
        PrimCollinearRotate
          Geo O Q' M
          hOQ'Mdata.2.2.2.1

      have hPOQ' :
          Not (PrimCollinear Geo P O Q') :=
        hilbert_not_collinear_collinear_arms_XI
          Geo
          L O M P Q'
          hLOM
          hOLP
          hOMQ'
          hOP
          hOQ'

      have hOPQ' :
          Not (PrimCollinear Geo O P Q') := by
        intro h

        cases h with
        | intro line hLine =>

            have hPOQ'col :
                PrimCollinear Geo P O Q' :=
              Exists.intro line
                (And.intro hLine.2.1
                  (And.intro hLine.1 hLine.2.2))

            exact hPOQ' hPOQ'col

      have hOP_OQ' :
          Geo.Congruent O P O Q' :=
        euclid_proposition_6
          Geo
          O P Q'
          hOPQ'
          hSmallBase

      have hRayOQ'M :
          HilbertSameRay Geo O Q' M :=
        hilbert_sameRay_of_between
          Geo O Q' M hOQ'M

      have hRayOMQ' :
          HilbertSameRay Geo O M Q' :=
        hilbert_sameRay_symm
          Geo O Q' M hRayOQ'M

      have hRayOQM :
          HilbertSameRay Geo O Q M :=
        hilbert_sameRay_of_between
          Geo O Q M hOQM

      have hRayOMQ :
          HilbertSameRay Geo O M Q :=
        hilbert_sameRay_symm
          Geo O Q M hRayOQM

      have hOQ'_OP :
          Geo.Congruent O Q' O P :=
        hilbert_congruent_symmetry
          Geo
          O P
          O Q'
          hOP_OQ'

      have hOQ_OP :
          Geo.Congruent O Q O P :=
        hilbert_congruent_symmetry
          Geo
          O P
          O Q
          hOP_OQ

      have hQ'eqQ :
          Q' = Q :=
        hilbert_segment_construction_unique
          Geo
          O P
          O M
          Q' Q
          hRayOMQ'
          hRayOMQ
          hOQ'_OP
          hOQ_OP

      subst Q'

      exact hPQ'_LM

------------------------------------------------------------------------
-- An inner parallel segment is shorter than the opposite side
------------------------------------------------------------------------

/--
Let P and Q lie strictly inside the two sides OL and OM of a
nondegenerate triangle OLM. If PQ is parallel to LM, then PQ is
strictly shorter than LM.

The proof uses a second inner parallel. Through P draw PR parallel to
OM, with R on the open side LM. Then PQMR is a parallelogram, hence

    PQ ~= MR.

Since R lies strictly between L and M, MR is strictly shorter than ML,
and therefore PQ is strictly shorter than LM.
-/
theorem hilbert_inner_parallel_segment_less_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O P L Q M : Geo.Point)
    (hOLM : Not (PrimCollinear Geo O L M))
    (hOPL : Geo.Between O P L)
    (hOQM : Geo.Between O Q M)
    (hParallel : Geo.Parallel P Q L M) :
    HilbertSegmentLess Geo P Q L M := by

  have hLPO :
      Geo.Between L P O :=
    (HilbertOrder.between_incidence
      O P L hOPL).2.2.2.2

  have hLOM :
      Not (PrimCollinear Geo L O M) := by
    intro h

    cases h with
    | intro line hLine =>
        exact
          hOLM
            (Exists.intro line
              (And.intro hLine.2.1
                (And.intro hLine.1 hLine.2.2)))

  cases
      hilbert_parallel_through_inner_side_point_XI
        Geo
        L O M P
        hLOM
        hLPO
  with
  | intro R hR =>

      have hLRM :
          Geo.Between L R M :=
        hR.1

      have hPR_OM :
          Geo.Parallel P R O M :=
        hR.2

      have hLRMdata :=
        HilbertOrder.between_incidence
          L R M hLRM

      have hRM :
          Not (R = M) :=
        hLRMdata.2.1

      have hMR :
          Not (M = R) := by
        intro hMR
        exact hRM hMR.symm

      have hRLM :
          PrimCollinear Geo R L M := by
        cases hLRMdata.2.2.2.1 with
        | intro line hLine =>
            exact
              Exists.intro line
                (And.intro hLine.2.1
                  (And.intro hLine.1 hLine.2.2))

      have hOQMdata :=
        HilbertOrder.between_incidence
          O Q M hOQM

      have hQM :
          Not (Q = M) :=
        hOQMdata.2.1

      have hQOM :
          PrimCollinear Geo Q O M := by
        cases hOQMdata.2.2.2.1 with
        | intro line hLine =>
            exact
              Exists.intro line
                (And.intro hLine.2.1
                  (And.intro hLine.1 hLine.2.2))

      --------------------------------------------------------------
      -- First opposite pair: PQ || MR.
      --------------------------------------------------------------

      have hLM_PQ :
          Geo.Parallel L M P Q :=
        ParallelSymmetry
          Geo P Q L M hParallel

      have hRM_PQ :
          Geo.Parallel R M P Q :=
        ParallelCollinearLeft
          Geo
          L M R
          P Q
          hRM
          hLM_PQ
          hRLM

      have hMR_PQ :
          Geo.Parallel M R P Q :=
        ParallelSwapFirstLine
          Geo R M P Q hRM_PQ

      have hPQ_MR :
          Geo.Parallel P Q M R :=
        ParallelSymmetry
          Geo M R P Q hMR_PQ

      --------------------------------------------------------------
      -- Second opposite pair: QM || RP.
      --------------------------------------------------------------

      have hOM_PR :
          Geo.Parallel O M P R :=
        ParallelSymmetry
          Geo P R O M hPR_OM

      have hQM_PR :
          Geo.Parallel Q M P R :=
        ParallelCollinearLeft
          Geo
          O M Q
          P R
          hQM
          hOM_PR
          hQOM

      have hQM_RP :
          Geo.Parallel Q M R P :=
        ParallelSwapSecondLine
          Geo Q M P R hQM_PR

      have hParallelogram :
          IsParallelogram Geo P Q M R :=
        And.intro hPQ_MR hQM_RP

      have hOppositeSides :
          OppositeSidesCongruent Geo P Q M R :=
        ParallelogramOppositeSidesCongruent
          Geo
          P Q M R
          hParallelogram

      have hPQ_MR_cong :
          Geo.Congruent P Q M R :=
        hOppositeSides.1

      --------------------------------------------------------------
      -- MR < ML because M-R-L.
      --------------------------------------------------------------

      have hMRL :
          Geo.Between M R L :=
        hLRMdata.2.2.2.2

      have hMR_lt_ML :
          HilbertSegmentLess Geo M R M L :=
        hilbert_segmentLess_of_between
          Geo
          M R L
          hMRL

      --------------------------------------------------------------
      -- Transport MR < ML through PQ ~= MR and ML ~= LM.
      --------------------------------------------------------------

      have hPQ_lt_ML :
          HilbertSegmentLess Geo P Q M L :=
        hilbert_segmentLess_congruent_left
          Geo
          M R
          P Q
          M L
          hMR_lt_ML
          hPQ_MR_cong

      have hML_LM :
          Geo.Congruent M L L M :=
        CongruentReverseFirst
          Geo
          L M
          L M
          (hilbert_congruent_reflexive
            Geo L M)

      exact
        hilbert_segmentLess_congruent_right
          Geo
          P Q
          M L
          L M
          hPQ_lt_ML
          hML_LM

------------------------------------------------------------------------
-- Equal inner cuts on equal sides are shorter than the base
------------------------------------------------------------------------

/--
Synthetic replacement for the VI.2 + VI.4 + V.16 chain used in the
classical proof of Euclid XI.23.

In a nondegenerate isosceles triangle OLM, let P and Q be interior
points of OL and OM. If the initial cuts are equal,

    OP ~= OQ,

then

    PQ < LM.

The proof first obtains PQ || LM from equal cuts on equal sides, and
then uses the general inner-parallel-segment comparison theorem.
No segment ratios or Book VI propositions are used.
-/
theorem hilbert_equal_cuts_on_equal_sides_less_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O P L Q M : Geo.Point)
    (hOLM : Not (PrimCollinear Geo O L M))
    (hOPL : Geo.Between O P L)
    (hOQM : Geo.Between O Q M)
    (hOL_OM : Geo.Congruent O L O M)
    (hOP_OQ : Geo.Congruent O P O Q) :
    HilbertSegmentLess Geo P Q L M := by

  have hParallel :
      Geo.Parallel P Q L M :=
    hilbert_equal_cuts_on_equal_sides_parallel_XI
      Geo
      O P L Q M
      hOLM
      hOPL
      hOQM
      hOL_OM
      hOP_OQ

  exact
    hilbert_inner_parallel_segment_less_XI
      Geo
      O P L Q M
      hOLM
      hOPL
      hOQM
      hParallel

------------------------------------------------------------------------
-- XI.23: comparison of a source angle with a larger-radius central angle
------------------------------------------------------------------------

/--
Equal-radius chord comparison used in the radius-smaller branch of
Euclid XI.23.

Suppose AOB and CUK are nondegenerate angles. Assume

    OA ~= OB,
    UC ~= UK,
    CK ~= AB,

and the source radius OA is strictly smaller than the target radius UC.

Then the target central angle is strictly smaller than the source angle:

    angle CUK < angle AOB.

Proof. Cut UP and UQ on UC and UK with length OA. The previous XI
helper gives PQ < CK, hence PQ < AB. The two triangles OAB and UPQ
have two corresponding sides congruent, so Euclid I.25 gives

    angle PUQ < angle AOB.

Finally P and Q lie on the rays UC and UK, so angle PUQ is the same
angle as CUK.
-/
theorem hilbert_equalRadiusChord_angleLess_of_radiusLess_XI
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A O B C U K : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCUK : Not (PrimCollinear Geo C U K))
    (hOA_OB : Geo.Congruent O A O B)
    (hUC_UK : Geo.Congruent U C U K)
    (hCK_AB : Geo.Congruent C K A B)
    (hRadiusLess : HilbertSegmentLess Geo O A U C) :
    HilbertAngleLess Geo C U K A O B := by

  have hRadiusLessUK :
      HilbertSegmentLess Geo O A U K :=
    hilbert_segmentLess_congruent_right
      Geo
      O A
      U C
      U K
      hRadiusLess
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

          have hOA_UQ :
              Geo.Congruent O A U Q :=
            hQ.2

          have hUP_OA :
              Geo.Congruent U P O A :=
            hilbert_congruent_symmetry
              Geo
              O A
              U P
              hOA_UP

          have hUP_UQ :
              Geo.Congruent U P U Q :=
            hilbert_congruent_transitivity
              Geo
              U P
              O A
              U Q
              hUP_OA
              hOA_UQ

          have hUCK :
              Not (PrimCollinear Geo U C K) := by
            intro h
            exact
              hCUK
                (PrimCollinearSwap
                  Geo U C K h)

          have hPQ_CK :
              HilbertSegmentLess Geo P Q C K :=
            hilbert_equal_cuts_on_equal_sides_less_XI
              Geo
              U P C Q K
              hUCK
              hUPC
              hUQK
              hUC_UK
              hUP_UQ

          have hPQ_AB :
              HilbertSegmentLess Geo P Q A B :=
            hilbert_segmentLess_congruent_right
              Geo
              P Q
              C K
              A B
              hPQ_CK
              hCK_AB

          have hOB_OA :
              Geo.Congruent O B O A :=
            hilbert_congruent_symmetry
              Geo
              O A
              O B
              hOA_OB

          have hOB_UQ :
              Geo.Congruent O B U Q :=
            hilbert_congruent_transitivity
              Geo
              O B
              O A
              U Q
              hOB_OA
              hOA_UQ

          have hUPCdata :=
            HilbertOrder.between_incidence
              U P C hUPC

          have hUQKdata :=
            HilbertOrder.between_incidence
              U Q K hUQK

          have hUP :
              Not (U = P) :=
            hUPCdata.1

          have hUQ :
              Not (U = Q) :=
            hUQKdata.1

          have hUCP :
              PrimCollinear Geo U C P :=
            PrimCollinearRotate
              Geo
              U P C
              hUPCdata.2.2.2.1

          have hUKQ :
              PrimCollinear Geo U K Q :=
            PrimCollinearRotate
              Geo
              U Q K
              hUQKdata.2.2.2.1

          have hPUQ :
              Not (PrimCollinear Geo P U Q) :=
            hilbert_not_collinear_collinear_arms_XI
              Geo
              C U K P Q
              hCUK
              hUCP
              hUKQ
              hUP
              hUQ

          have hUPQ :
              Not (PrimCollinear Geo U P Q) := by
            intro h

            cases h with
            | intro line hLine =>

                have hPUQcol :
                    PrimCollinear Geo P U Q :=
                  Exists.intro line
                    (And.intro hLine.2.1
                      (And.intro hLine.1 hLine.2.2))

                exact hPUQ hPUQcol

          have hOAB :
              Not (PrimCollinear Geo O A B) := by
            intro h
            exact
              hAOB
                (PrimCollinearSwap
                  Geo O A B h)

          have hSmallAngle :
              HilbertAngleLess Geo P U Q A O B :=
            euclid_proposition_25
              (Geo := Geo)
              O A B
              U P Q
              hOAB
              hUPQ
              hOA_UP
              hOB_UQ
              hPQ_AB

          have hRayUPC :
              HilbertSameRay Geo U P C :=
            hilbert_sameRay_of_between
              Geo U P C hUPC

          have hRayUQK :
              HilbertSameRay Geo U Q K :=
            hilbert_sameRay_of_between
              Geo U Q K hUQK

          have hFirstRay :
              Geo.Angle P U Q =
              Geo.Angle C U Q :=
            hilbert_angle_eq_of_sameRay_first
              Geo
              U P C Q
              hRayUPC

          have hSecondRay :
              Geo.Angle C U Q =
              Geo.Angle C U K :=
            hilbert_angle_eq_of_sameRay_second
              Geo
              U C Q K
              hRayUQK

          have hPUQ_CUK :
              Geo.AngleCongruent P U Q C U K := by
            unfold Geometry.Geo.AngleCongruent
            rw [hFirstRay, hSecondRay]
            exact
              Geometry.Geo.angle_congruent_reflexive
                Geo C U K

          have hCUK_PUQ :
              Geo.AngleCongruent C U K P U Q :=
            Geometry.Geo.angle_congruent_symmetry
              Geo
              P U Q
              C U K
              hPUQ_CUK

          exact
            hilbert_angleLess_transport_left
              Geo
              P U Q
              C U K
              A O B
              hSmallAngle
              hCUK
              hCUK_PUQ


------------------------------------------------------------------------
-- XI.23: automatic properness of the three central angles
------------------------------------------------------------------------

/--
If two distinct points X,Y are equidistant from O and O does not lie
between X and Y, then X,O,Y are noncollinear.

Indeed, if they were collinear, order trichotomy leaves three cases.
The case X-O-Y is excluded by hypothesis.  In either remaining case
one of OX, OY is a proper subsegment of the other, contradicting
OX ~= OY.
-/
theorem hilbert_equal_radii_noncollinear_of_not_between_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (X O Y : Geo.Point)
    (hXY : Not (X = Y))
    (hOX_OY : Geo.Congruent O X O Y)
    (hNotBetween : Not (Geo.Between X O Y)) :
    Not (PrimCollinear Geo X O Y) := by

  intro hXOY

  have hOX : Not (O = X) := by
    intro hOXeq
    subst X

    have hOY_OO :
        Geo.Congruent O Y O O :=
      hilbert_congruent_symmetry
        Geo
        O O
        O Y
        hOX_OY

    have hOY : O = Y :=
      bookZero_nullSegment1
        Geo
        O Y O
        hOY_OO

    exact hXY hOY

  have hOY : Not (O = Y) := by
    intro hOYeq
    subst Y

    have hOX : O = X :=
      bookZero_nullSegment1
        Geo
        O X O
        hOX_OY

    exact hXY hOX.symm

  have hXO : Not (X = O) := by
    intro hXOeq
    exact hOX hXOeq.symm

  rcases
      hilbert_between_trichotomy
        Geo
        X O Y
        hXO
        hOY
        hXY
        hXOY
    with
    hXOYbetween | hOXY | hXYO

  exact hNotBetween hXOYbetween

  have hOX_lt_OY :
      HilbertSegmentLess Geo O X O Y :=
    hilbert_segmentLess_of_between
      Geo
      O X Y
      hOXY

  exact
    (hilbert_segmentLess_not_congruent
      Geo
      O X
      O Y
      hOX_lt_OY)
      hOX_OY

  have hOYX :
      Geo.Between O Y X :=
    (HilbertOrder.between_incidence
      X Y O hXYO).2.2.2.2

  have hOY_lt_OX :
      HilbertSegmentLess Geo O Y O X :=
    hilbert_segmentLess_of_between
      Geo
      O Y X
      hOYX

  have hOY_OX :
      Geo.Congruent O Y O X :=
    hilbert_congruent_symmetry
      Geo
      O X
      O Y
      hOX_OY

  exact
    (hilbert_segmentLess_not_congruent
      Geo
      O Y
      O X
      hOY_lt_OX)
      hOY_OX


------------------------------------------------------------------------
-- XI.23: equal-radius chord/angle order equivalence
------------------------------------------------------------------------

/--
Converse equal-radius chord comparison.

For two proper angles whose corresponding radial sides are congruent,
a strictly shorter opposite chord determines a strictly smaller included
angle.

This is the converse of `hilbert_equalRadiusChord_less`.  The proof uses
angle trichotomy.  Equality of the angles would give congruent chords by
SAS, while the opposite strict angle inequality would give the reverse
strict chord inequality by Euclid I.24.
-/
theorem hilbert_equalRadiusChord_angleLess_of_chordLess_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A B P C D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCPD : Not (PrimCollinear Geo C P D))
    (hOA_PC : Geo.Congruent O A P C)
    (hOB_PD : Geo.Congruent O B P D)
    (hAB_CD : HilbertSegmentLess Geo A B C D) :
    HilbertAngleLess Geo A O B C P D := by

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  have hPCD :
      Not (PrimCollinear Geo P C D) := by
    intro h
    exact
      hCPD
        (PrimCollinearSwap
          Geo P C D h)

  rcases
      angle_trichotomy
        Geo
        A O B
        C P D
        hAOB
        hCPD
    with
    hEq | hLess | hGreater

  · have hAB_CD_cong :
        Geo.Congruent A B C D :=
      hilbert_equalRadiusChord_congruent
        Geo
        O A B
        P C D
        hOAB
        hPCD
        hOA_PC
        hOB_PD
        hEq

    exact
      False.elim
        ((hilbert_segmentLess_not_congruent
          Geo
          A B
          C D
          hAB_CD)
          hAB_CD_cong)

  · exact hLess

  · have hPC_OA :
        Geo.Congruent P C O A :=
      hilbert_congruent_symmetry
        Geo
        O A
        P C
        hOA_PC

    have hPD_OB :
        Geo.Congruent P D O B :=
      hilbert_congruent_symmetry
        Geo
        O B
        P D
        hOB_PD

    have hCD_AB :
        HilbertSegmentLess Geo C D A B :=
      hilbert_equalRadiusChord_less
        Geo
        P C D
        O A B
        hPCD
        hOAB
        hPC_OA
        hPD_OB
        hGreater

    exact
      False.elim
        ((hilbert_segmentLess_asymm
          Geo
          A B
          C D
          hAB_CD)
          hCD_AB)


/--
For proper equal-radius angles, congruent opposite chords determine
congruent included angles.

Together with `hilbert_equalRadiusChord_congruent`, this gives the
synthetic equal-radius chord/angle equality correspondence needed in
XI.23.
-/
theorem hilbert_equalRadiusChord_angleCongruent_of_chordCongruent_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A B P C D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCPD : Not (PrimCollinear Geo C P D))
    (hOA_PC : Geo.Congruent O A P C)
    (hOB_PD : Geo.Congruent O B P D)
    (hAB_CD : Geo.Congruent A B C D) :
    Geo.AngleCongruent A O B C P D := by

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  have hPCD :
      Not (PrimCollinear Geo P C D) := by
    intro h
    exact
      hCPD
        (PrimCollinearSwap
          Geo P C D h)

  rcases
      angle_trichotomy
        Geo
        A O B
        C P D
        hAOB
        hCPD
    with
    hEq | hLess | hGreater

  · exact hEq

  · have hAB_CD_less :
        HilbertSegmentLess Geo A B C D :=
      hilbert_equalRadiusChord_less
        Geo
        O A B
        P C D
        hOAB
        hPCD
        hOA_PC
        hOB_PD
        hLess

    exact
      False.elim
        ((hilbert_segmentLess_not_congruent
          Geo
          A B
          C D
          hAB_CD_less)
          hAB_CD)

  · have hPC_OA :
        Geo.Congruent P C O A :=
      hilbert_congruent_symmetry
        Geo
        O A
        P C
        hOA_PC

    have hPD_OB :
        Geo.Congruent P D O B :=
      hilbert_congruent_symmetry
        Geo
        O B
        P D
        hOB_PD

    have hCD_AB_less :
        HilbertSegmentLess Geo C D A B :=
      hilbert_equalRadiusChord_less
        Geo
        P C D
        O A B
        hPCD
        hOAB
        hPC_OA
        hPD_OB
        hGreater

    have hCD_AB :
        Geo.Congruent C D A B :=
      hilbert_congruent_symmetry
        Geo
        A B
        C D
        hAB_CD

    exact
      False.elim
        ((hilbert_segmentLess_not_congruent
          Geo
          C D
          A B
          hCD_AB_less)
          hCD_AB)


/--
Strict order equivalence for opposite chords and included angles at
equal radii.
-/
theorem hilbert_equalRadiusChord_angleLess_iff_chordLess_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A B P C D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCPD : Not (PrimCollinear Geo C P D))
    (hOA_PC : Geo.Congruent O A P C)
    (hOB_PD : Geo.Congruent O B P D) :
    HilbertAngleLess Geo A O B C P D <->
    HilbertSegmentLess Geo A B C D := by

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  have hPCD :
      Not (PrimCollinear Geo P C D) := by
    intro h
    exact
      hCPD
        (PrimCollinearSwap
          Geo P C D h)

  constructor

  · intro hAngleLess
    exact
      hilbert_equalRadiusChord_less
        Geo
        O A B
        P C D
        hOAB
        hPCD
        hOA_PC
        hOB_PD
        hAngleLess

  · intro hChordLess
    exact
      hilbert_equalRadiusChord_angleLess_of_chordLess_XI
        Geo
        O A B
        P C D
        hAOB
        hCPD
        hOA_PC
        hOB_PD
        hChordLess


/--
Equality equivalence for opposite chords and included angles at equal
radii.
-/
theorem hilbert_equalRadiusChord_angleCongruent_iff_chordCongruent_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A B P C D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCPD : Not (PrimCollinear Geo C P D))
    (hOA_PC : Geo.Congruent O A P C)
    (hOB_PD : Geo.Congruent O B P D) :
    Geo.AngleCongruent A O B C P D <->
    Geo.Congruent A B C D := by

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  have hPCD :
      Not (PrimCollinear Geo P C D) := by
    intro h
    exact
      hCPD
        (PrimCollinearSwap
          Geo P C D h)

  constructor

  · intro hAngleCong
    exact
      hilbert_equalRadiusChord_congruent
        Geo
        O A B
        P C D
        hOAB
        hPCD
        hOA_PC
        hOB_PD
        hAngleCong

  · intro hChordCong
    exact
      hilbert_equalRadiusChord_angleCongruent_of_chordCongruent_XI
        Geo
        O A B
        P C D
        hAOB
        hCPD
        hOA_PC
        hOB_PD
        hChordCong


------------------------------------------------------------------------
-- XI.23: an interior central ray determines the longest opposite chord
------------------------------------------------------------------------

/--
If UD is an interior ray of the proper angle CUK and UC = UD = UK,
then both chords cut off by D are strictly shorter than CK.

This is the chord-order form of the elementary ray-order fact needed
for the exterior-circumcenter branch of XI.23.  No circle arcs or angle
measure are used: the two component angles are proper subangles of CUK,
and v39 converts their strict angle inequalities into strict chord
inequalities at equal radius.
-/
theorem hilbert_equalRadius_interiorRay_two_chords_less_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (U C D K : Geo.Point)
    (hCUK : Not (PrimCollinear Geo C U K))
    (hInside : HilbertRayMeetsSegment Geo U D C K)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K) :
    HilbertSegmentLess Geo C D C K /\
    HilbertSegmentLess Geo D K C K := by

  have hCUD_less :
      HilbertAngleLess Geo C U D C U K :=
    hilbert_interior_angle_less
      Geo
      U D C K
      hCUK
      hInside

  have hCUD :
      Not (PrimCollinear Geo C U D) :=
    hCUD_less.1

  have hKUC :
      Not (PrimCollinear Geo K U C) := by
    intro h
    exact
      hCUK
        (PrimCollinearSymm Geo K U C h)

  rcases hInside with
    ⟨H, hCHK, hRayUDH⟩

  have hKHC :
      Geo.Between K H C :=
    (HilbertOrder.between_incidence
      C H K hCHK).2.2.2.2

  have hInsideRev :
      HilbertRayMeetsSegment Geo U D K C :=
    ⟨H, hKHC, hRayUDH⟩

  have hKUD_less :
      HilbertAngleLess Geo K U D K U C :=
    hilbert_interior_angle_less
      Geo
      U D K C
      hKUC
      hInsideRev

  have hKUD :
      Not (PrimCollinear Geo K U D) :=
    hKUD_less.1

  have hUCD :
      Not (PrimCollinear Geo U C D) := by
    intro h
    exact
      hCUD
        (PrimCollinearSwap Geo U C D h)

  have hUCK :
      Not (PrimCollinear Geo U C K) := by
    intro h
    exact
      hCUK
        (PrimCollinearSwap Geo U C K h)

  have hUD_UK :
      Geo.Congruent U D U K :=
    hilbert_congruent_transitivity
      Geo
      U D
      U C
      U K
      (hilbert_congruent_symmetry
        Geo U C U D hUC_UD)
      hUC_UK

  have hCD_CK :
      HilbertSegmentLess Geo C D C K :=
    hilbert_equalRadiusChord_less
      Geo
      U C D
      U C K
      hUCD
      hUCK
      (hilbert_congruent_reflexive Geo U C)
      hUD_UK
      hCUD_less

  have hUK_UD :
      Geo.Congruent U K U D :=
    hilbert_congruent_symmetry
      Geo U D U K hUD_UK

  have hUK_UC :
      Geo.Congruent U K U C :=
    hilbert_congruent_symmetry
      Geo U C U K hUC_UK

  have hUKD :
      Not (PrimCollinear Geo U K D) := by
    intro h
    exact
      hKUD
        (PrimCollinearSwap Geo U K D h)

  have hUKC :
      Not (PrimCollinear Geo U K C) := by
    intro h
    exact
      hKUC
        (PrimCollinearSwap Geo U K C h)

  have hKD_KC :
      HilbertSegmentLess Geo K D K C :=
    hilbert_equalRadiusChord_less
      Geo
      U K D
      U K C
      hUKD
      hUKC
      (hilbert_congruent_reflexive Geo U K)
      (hilbert_congruent_transitivity
        Geo
        U D
        U K
        U C
        hUD_UK
        hUK_UC)
      hKUD_less

  have hKD_DK :
      Geo.Congruent K D D K :=
    CongruentReverseFirst
      Geo
      D K
      D K
      (hilbert_congruent_reflexive Geo D K)

  have hKC_CK :
      Geo.Congruent K C C K :=
    CongruentReverseFirst
      Geo
      C K
      C K
      (hilbert_congruent_reflexive Geo C K)

  have hDK_KC :
      HilbertSegmentLess Geo D K K C :=
    bookZero_32_lessThanCongruence2
      Geo
      K D
      K C
      D K
      hKD_KC
      hKD_DK

  have hDK_CK :
      HilbertSegmentLess Geo D K C K :=
    bookZero_30_lessThanCongruence
      Geo
      D K
      K C
      C K
      hDK_KC
      hKC_CK

  exact ⟨hCD_CK, hDK_CK⟩


------------------------------------------------------------------------
-- XI.23: an interior central ray forces the decomposition branch
------------------------------------------------------------------------

/--
If the target chord is strictly longer than the chord of the first
summand, then a proof of `HilbertTwoAnglesGreaterThanAngle` cannot use
its first two branches.

Indeed, at equal radii:

* `target < first` would imply `targetChord < firstChord`, contradicting
  `firstChord < targetChord`;
* `target ~= first` would imply congruent chords, again contradicting
  strict chord inequality.

Hence only the genuine angle-decomposition branch remains.
-/
theorem hilbert_twoAnglesGreater_decomposition_forced_of_firstChord_less_targetChord_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (hSum :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOB_QF : Geo.Congruent O B Q F)
    (hAB_EF : HilbertSegmentLess Geo A B E F) :
    exists X : Geo.Point,
      HilbertRayMeetsSegment Geo Q X E F /\
      Geo.AngleCongruent A O B E Q X /\
      HilbertAngleLess Geo X Q F C P D := by

  rcases hSum with
    ⟨hFirst, hSecond, hTarget, hCases⟩

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hFirst
        (PrimCollinearSwap Geo O A B h)

  have hQEF :
      Not (PrimCollinear Geo Q E F) := by
    intro h
    exact
      hTarget
        (PrimCollinearSwap Geo Q E F h)

  rcases hCases with hTargetLess | hRest

  · have hQE_OA :
        Geo.Congruent Q E O A :=
      hilbert_congruent_symmetry
        Geo O A Q E hOA_QE

    have hQF_OB :
        Geo.Congruent Q F O B :=
      hilbert_congruent_symmetry
        Geo O B Q F hOB_QF

    have hEF_AB :
        HilbertSegmentLess Geo E F A B :=
      hilbert_equalRadiusChord_less
        Geo
        Q E F
        O A B
        hQEF
        hOAB
        hQE_OA
        hQF_OB
        hTargetLess

    exact
      False.elim
        ((hilbert_segmentLess_asymm
          Geo
          A B
          E F
          hAB_EF)
          hEF_AB)

  · rcases hRest with hTargetEq | hDecomp

    · have hEF_AB :
          Geo.Congruent E F A B :=
        hilbert_equalRadiusChord_congruent
          Geo
          Q E F
          O A B
          hQEF
          hOAB
          (hilbert_congruent_symmetry
            Geo O A Q E hOA_QE)
          (hilbert_congruent_symmetry
            Geo O B Q F hOB_QF)
          hTargetEq

      have hAB_EF_cong :
          Geo.Congruent A B E F :=
        hilbert_congruent_symmetry
          Geo E F A B hEF_AB

      exact
        False.elim
          ((hilbert_segmentLess_not_congruent
            Geo
            A B
            E F
            hAB_EF)
            hAB_EF_cong)

    · exact hDecomp

------------------------------------------------------------------------
-- XI.23 v42: realize a forced angle decomposition by source-radius
-- chords.
------------------------------------------------------------------------

/--
Realize the decomposition branch of `HilbertTwoAnglesGreaterThanAngle`
on the common source circle.

Assume X is an interior ray of angle AOB, the first component AOX is
congruent to CPD, and the remainder XOB is strictly smaller than EQF.
All three source angles are represented by the same radius OA.

Lay off R on ray OX with OR congruent OA.  Then the first component
chord AR is congruent to CD, while the remainder chord RB is strictly
shorter than EF.

This is the chord-level form of the genuine decomposition branch needed
in the outside-circumcenter analysis of Euclid XI.23.
-/
theorem hilbert_angleDecomposition_sourceRadius_chord_witness_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F X : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCPD : Not (PrimCollinear Geo C P D))
    (hEQF : Not (PrimCollinear Geo E Q F))
    (hInside : HilbertRayMeetsSegment Geo O X A B)
    (hFirstPart : Geo.AngleCongruent C P D A O X)
    (hRemainder : HilbertAngleLess Geo X O B E Q F)
    (hOA_OB : Geo.Congruent O A O B)
    (hOA_PC : Geo.Congruent O A P C)
    (hOA_PD : Geo.Congruent O A P D)
    (hOA_QE : Geo.Congruent O A Q E)
    (hOA_QF : Geo.Congruent O A Q F) :
    exists R : Geo.Point,
      HilbertSameRay Geo O X R /\
      Geo.Congruent O R O A /\
      Geo.Congruent A R C D /\
      HilbertSegmentLess Geo R B E F := by

  have hAOX_less :
      HilbertAngleLess Geo A O X A O B :=
    hilbert_interior_angle_less
      Geo
      O X A B
      hAOB
      hInside

  have hAOX :
      Not (PrimCollinear Geo A O X) :=
    hAOX_less.1

  have hXOB :
      Not (PrimCollinear Geo X O B) :=
    hRemainder.1

  rcases hInside with
    ⟨H, hAHB, hRayOXH⟩

  have hXO :
      Not (X = O) :=
    hRayOXH.1

  have hOX :
      Not (O = X) := by
    intro h
    exact hXO h.symm

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  have hOA :
      Not (O = A) :=
    hilbert_noncollinear_ne_first
      Geo O A B hOAB

  cases
      bookZero_49_layoff
        Geo
        O X
        O A
        hOX
        hOA with
  | intro R hR =>

      have hRayOXR :
          HilbertSameRay Geo O X R :=
        hR.1

      have hOR_OA :
          Geo.Congruent O R O A :=
        hR.2

      have hRO :
          Not (R = O) :=
        hRayOXR.2.1

      have hOR :
          Not (O = R) := by
        intro h
        exact hRO h.symm

      have hOXR :
          PrimCollinear Geo O X R :=
        hRayOXR.2.2.1

      have hORX :
          PrimCollinear Geo O R X :=
        PrimCollinearRotate
          Geo O X R hOXR

      have hAOR :
          Not (PrimCollinear Geo A O R) := by
        intro hAORcol

        have hAOXcol :
            PrimCollinear Geo A O X :=
          hilbert_primCollinear_trans
            Geo
            A O R X
            hOR
            hAORcol
            hORX

        exact hAOX hAOXcol

      have hOAR :
          Not (PrimCollinear Geo O A R) := by
        intro h
        exact
          hAOR
            (PrimCollinearSwap
              Geo O A R h)

      have hPCD :
          Not (PrimCollinear Geo P C D) := by
        intro h
        exact
          hCPD
            (PrimCollinearSwap
              Geo P C D h)

      have hAOX_eq_AOR :
          Geo.Angle A O X =
          Geo.Angle A O R :=
        hilbert_angle_eq_of_sameRay_second
          Geo
          O A X R
          hRayOXR

      have hCPD_AOR :
          Geo.AngleCongruent C P D A O R := by
        unfold Geometry.Geo.AngleCongruent
          at hFirstPart |-
        rw [<- hAOX_eq_AOR]
        exact hFirstPart

      have hAOR_CPD :
          Geo.AngleCongruent A O R C P D :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          C P D
          A O R
          hCPD_AOR

      have hOR_PD :
          Geo.Congruent O R P D :=
        hilbert_congruent_transitivity
          Geo
          O R
          O A
          P D
          hOR_OA
          hOA_PD

      have hAR_CD :
          Geo.Congruent A R C D :=
        hilbert_equalRadiusChord_congruent
          Geo
          O A R
          P C D
          hOAR
          hPCD
          hOA_PC
          hOR_PD
          hAOR_CPD

      have hXOR :
          PrimCollinear Geo X O R :=
        PrimCollinearSwap
          Geo O X R hOXR

      have hROB :
          Not (PrimCollinear Geo R O B) := by
        intro hROBcol

        have hXOBcol :
            PrimCollinear Geo X O B :=
          hilbert_primCollinear_trans
            Geo
            X O R B
            hOR
            hXOR
            (PrimCollinearSwap
              Geo R O B hROBcol)

        exact hXOB hXOBcol

      have hORB :
          Not (PrimCollinear Geo O R B) := by
        intro h
        exact
          hROB
            (PrimCollinearSwap
              Geo O R B h)

      have hQEF :
          Not (PrimCollinear Geo Q E F) := by
        intro h
        exact
          hEQF
            (PrimCollinearSwap
              Geo Q E F h)

      have hXOB_eq_ROB :
          Geo.Angle X O B =
          Geo.Angle R O B :=
        hilbert_angle_eq_of_sameRay_first
          Geo
          O X R B
          hRayOXR

      have hROB_XOB :
          Geo.AngleCongruent R O B X O B := by
        have hRefl :
            Geo.AngleCongruent X O B X O B :=
          Geometry.Geo.angle_congruent_reflexive
            Geo X O B

        unfold Geometry.Geo.AngleCongruent
          at hRefl |-
        rw [<- hXOB_eq_ROB]
        exact hRefl

      have hRemainderR :
          HilbertAngleLess Geo R O B E Q F :=
        hilbert_angleLess_transport_left
          Geo
          X O B
          R O B
          E Q F
          hRemainder
          hROB
          hROB_XOB

      have hOR_QE :
          Geo.Congruent O R Q E :=
        hilbert_congruent_transitivity
          Geo
          O R
          O A
          Q E
          hOR_OA
          hOA_QE

      have hOB_OA :
          Geo.Congruent O B O A :=
        hilbert_congruent_symmetry
          Geo
          O A
          O B
          hOA_OB

      have hOB_QF :
          Geo.Congruent O B Q F :=
        hilbert_congruent_transitivity
          Geo
          O B
          O A
          Q F
          hOB_OA
          hOA_QF

      have hRB_EF :
          HilbertSegmentLess Geo R B E F :=
        hilbert_equalRadiusChord_less
          Geo
          O R B
          Q E F
          hORB
          hQEF
          hOR_QE
          hOB_QF
          hRemainderR

      exact
        ⟨R,
          hRayOXR,
          hOR_OA,
          hAR_CD,
          hRB_EF⟩



------------------------------------------------------------------------
-- Angle decomposition: strict order reverses on the complementary part
------------------------------------------------------------------------

/--
For two interior rays of the same proper angle, strict order of the
left components forces the opposite strict order of the right
components.

This packages the Pasch core
`hilbert_angleDecomposition_two_component_less_impossible` together
with angle trichotomy and angle subtraction.  It is deliberately
independent of XI.23.
-/
theorem hilbert_angleDecomposition_complement_order_reverse_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D E : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hInsideD : HilbertRayMeetsSegment Geo O D X C)
    (hInsideE : HilbertRayMeetsSegment Geo O E X C)
    (hLessFirst : HilbertAngleLess Geo X O D X O E) :
    HilbertAngleLess Geo C O E C O D := by

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm
          Geo C O X h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O D X C
      hInsideD

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E X C
      hInsideE

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    (hilbert_interior_angle_less
      Geo
      O D C X
      hCOX
      hInsideDrev).1

  have hCOE :
      Not (PrimCollinear Geo C O E) :=
    (hilbert_interior_angle_less
      Geo
      O E C X
      hCOX
      hInsideErev).1

  rcases
      angle_trichotomy
        Geo
        C O E
        C O D
        hCOE
        hCOD
    with hEq | hOrder

  · have hRight :
        Geo.AngleCongruent C O D C O E :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        C O E
        C O D
        hEq

    have hWhole :
        Geo.AngleCongruent X O C X O C :=
      Geometry.Geo.angle_congruent_reflexive
        Geo X O C

    have hLeftEq :
        Geo.AngleCongruent X O D X O E :=
      hilbert_angleDecomposition_angle_subtraction
        Geo
        O X C D
        X O C E
        hXOC
        hXOC
        hInsideD
        hInsideE
        hWhole
        hRight

    have hLeftEqSymm :
        Geo.AngleCongruent X O E X O D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O D
        X O E
        hLeftEq

    have hCycle :
        HilbertAngleLess Geo X O D X O D :=
      hilbert_angleLess_transport_right
        Geo
        X O D
        X O E
        X O D
        hLessFirst
        hLessFirst.1
        hLeftEqSymm

    exact
      False.elim
        ((hilbert_angleLess_irrefl
          Geo X O D)
          hCycle)

  · rcases hOrder with hWanted | hForbidden

    · exact hWanted

    · exact
        False.elim
          (hilbert_angleDecomposition_two_component_less_impossible
            Geo
            O X C D E
            hXOC
            hInsideD
            hInsideE
            hLessFirst
            hForbidden)


------------------------------------------------------------------------
-- Nested transport of an interior-angle decomposition
------------------------------------------------------------------------

/--
If a proper angle PUQ is strictly smaller than a proper angle AOB,
and US is an interior ray of PUQ, then the whole decomposition

    PUQ = PUS + SUQ

can be realized inside AOB.  Thus there are rays OE and OT such that
OE is interior to AOB, OT is interior to AOE, and the two component
angles are transported separately:

    PUQ ~= AOE,
    PUS ~= AOT,
    QUS ~= EOT.

This is a pure angle-decomposition lemma; no radial or XI.23 data are
used.
-/
theorem hilbert_angleDecomposition_nested_transport_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P U Q S A O B : Geo.Point)
    (hPUQ : Not (PrimCollinear Geo P U Q))
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideS : HilbertRayMeetsSegment Geo U S P Q)
    (hWholeLess : HilbertAngleLess Geo P U Q A O B) :
    exists E T : Geo.Point,
      HilbertRayMeetsSegment Geo O E A B /\
      HilbertRayMeetsSegment Geo O T A E /\
      Geo.AngleCongruent P U Q A O E /\
      Geo.AngleCongruent P U S A O T /\
      Geo.AngleCongruent Q U S E O T := by

  rcases hWholeLess with
    ⟨_hPUQ, _hAOB, E, hInsideE, hWhole⟩

  have hAOE_less :
      HilbertAngleLess Geo A O E A O B :=
    hilbert_interior_angle_less
      Geo
      O E A B
      hAOB
      hInsideE

  have hAOE :
      Not (PrimCollinear Geo A O E) :=
    hAOE_less.1

  rcases
      hilbert_interior_subangle_transport_both
        Geo
        U P Q S
        A O E
        hPUQ
        hAOE
        hInsideS
        hWhole
    with
    ⟨T, hInsideT, hParts⟩

  exact
    ⟨E, T,
      hInsideE,
      hInsideT,
      hWhole,
      hParts.2,
      hParts.1⟩


/--
Specialization of nested transport to the angular output of the
radial reduction.  Besides transporting the decomposition, it records
that the transported first component is still strictly smaller than
AOR.
-/
theorem hilbert_radial_remainder_nested_transport_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P U Q S A O B R : Geo.Point)
    (hPUQ : Not (PrimCollinear Geo P U Q))
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideS : HilbertRayMeetsSegment Geo U S P Q)
    (hPUS_AOR : HilbertAngleLess Geo P U S A O R)
    (hPUQ_AOB : HilbertAngleLess Geo P U Q A O B) :
    exists E T : Geo.Point,
      HilbertRayMeetsSegment Geo O E A B /\
      HilbertRayMeetsSegment Geo O T A E /\
      Geo.AngleCongruent P U Q A O E /\
      Geo.AngleCongruent P U S A O T /\
      Geo.AngleCongruent Q U S E O T /\
      HilbertAngleLess Geo A O T A O R := by

  rcases
      hilbert_angleDecomposition_nested_transport_XI
        Geo
        P U Q S A O B
        hPUQ
        hAOB
        hInsideS
        hPUQ_AOB
    with
    ⟨E, T,
      hInsideE,
      hInsideT,
      hPUQ_AOE,
      hPUS_AOT,
      hQUS_EOT⟩

  have hAOE_less :
      HilbertAngleLess Geo A O E A O B :=
    hilbert_interior_angle_less
      Geo
      O E A B
      hAOB
      hInsideE

  have hAOE :
      Not (PrimCollinear Geo A O E) :=
    hAOE_less.1

  have hAOT_less_AOE :
      HilbertAngleLess Geo A O T A O E :=
    hilbert_interior_angle_less
      Geo
      O T A E
      hAOE
      hInsideT

  have hAOT :
      Not (PrimCollinear Geo A O T) :=
    hAOT_less_AOE.1

  have hAOT_PUS :
      Geo.AngleCongruent A O T P U S :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      P U S
      A O T
      hPUS_AOT

  have hAOT_AOR :
      HilbertAngleLess Geo A O T A O R :=
    hilbert_angleLess_transport_left
      Geo
      P U S
      A O T
      A O R
      hPUS_AOR
      hAOT
      hAOT_PUS

  exact
    ⟨E, T,
      hInsideE,
      hInsideT,
      hPUQ_AOE,
      hPUS_AOT,
      hQUS_EOT,
      hAOT_AOR⟩




------------------------------------------------------------------------
-- Nested interior ray promoted to the whole angle
------------------------------------------------------------------------

/--
If OE is interior to AOB and OT is interior to AOE, then OT is also
interior to AOB.  Consequently, if AOT < AOR and OR is another
interior ray of AOB, the complementary parts are ordered in the
opposite direction:

    angle BOR < angle BOT.

This is the exact form needed after the nested radial transport.
-/
theorem hilbert_nested_interior_complement_order_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B E T R : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideE : HilbertRayMeetsSegment Geo O E A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T A E)
    (hInsideR : HilbertRayMeetsSegment Geo O R A B)
    (hAOT_AOR : HilbertAngleLess Geo A O T A O R) :
    HilbertAngleLess Geo B O R B O T := by

  have hAOE_AOB :
      HilbertAngleLess Geo A O E A O B :=
    hilbert_interior_angle_less
      Geo
      O E A B
      hAOB
      hInsideE

  have hAOE :
      Not (PrimCollinear Geo A O E) :=
    hAOE_AOB.1

  have hAOT_AOE :
      HilbertAngleLess Geo A O T A O E :=
    hilbert_interior_angle_less
      Geo
      O T A E
      hAOE
      hInsideT

  have hAOT_AOB :
      HilbertAngleLess Geo A O T A O B :=
    hilbert_angleLess_trans
      Geo
      A O T
      A O E
      A O B
      hAOT_AOE
      hAOE_AOB

  --------------------------------------------------------------------
  -- Put T and B on the same side of OA.
  --------------------------------------------------------------------

  have hAO : O ≠ A :=
    hilbert_noncollinear_ne_first
      Geo O A B
      (by
        intro h
        exact hAOB
          (PrimCollinearSwap Geo O A B h))

  rcases
      HilbertPlaneIncidence.line_through
        O A hAO
    with
    ⟨lineOA, hOlineOA, hAlineOA⟩

  have hEOA :
      Not (PrimCollinear Geo E O A) := by
    intro h
    exact hAOE
      (PrimCollinearSymm Geo E O A h)

  have hInsideTrev :
      HilbertRayMeetsSegment Geo O T E A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A E
      hInsideT

  have hTESameOA :
      HilbertSameSide Geo T E lineOA :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O T E A
      lineOA
      hOlineOA
      hAlineOA
      hEOA
      hInsideTrev

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact hAOB
      (PrimCollinearSymm Geo B O A h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A B
      hInsideE

  have hEBSameOA :
      HilbertSameSide Geo E B lineOA :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O E B A
      lineOA
      hOlineOA
      hAlineOA
      hBOA
      hInsideErev

  have hTBSameOA :
      HilbertSameSide Geo T B lineOA :=
    hilbert_sameSide_trans
      Geo
      T E B
      lineOA
      hTESameOA
      hEBSameOA

  have hInsideTWhole :
      HilbertRayMeetsSegment Geo O T A B :=
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      T B O A
      lineOA
      hOlineOA
      hAlineOA
      hAO
      hTBSameOA
      hAOT_AOB

  exact
    hilbert_angleDecomposition_complement_order_reverse_XI
      Geo
      O A B T R
      hAOB
      hInsideTWhole
      hInsideR
      hAOT_AOR


/--
Apply the preceding complement-order lemma directly to the output of
`hilbert_radial_remainder_nested_transport_XI`.

The resulting inequality is the angular comparison of the two
remainders inside the common source angle AOB.
-/
theorem hilbert_radial_remainder_source_complement_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P U Q S A O B R : Geo.Point)
    (hPUQ : Not (PrimCollinear Geo P U Q))
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideS : HilbertRayMeetsSegment Geo U S P Q)
    (hInsideR : HilbertRayMeetsSegment Geo O R A B)
    (hPUS_AOR : HilbertAngleLess Geo P U S A O R)
    (hPUQ_AOB : HilbertAngleLess Geo P U Q A O B) :
    exists E T : Geo.Point,
      HilbertRayMeetsSegment Geo O E A B /\
      HilbertRayMeetsSegment Geo O T A E /\
      Geo.AngleCongruent Q U S E O T /\
      HilbertAngleLess Geo B O R B O T := by

  rcases
      hilbert_radial_remainder_nested_transport_XI
        Geo
        P U Q S A O B R
        hPUQ
        hAOB
        hInsideS
        hPUS_AOR
        hPUQ_AOB
    with
    ⟨E, T,
      hInsideE,
      hInsideT,
      _hPUQ_AOE,
      _hPUS_AOT,
      hQUS_EOT,
      hAOT_AOR⟩

  have hComplement :
      HilbertAngleLess Geo B O R B O T :=
    hilbert_nested_interior_complement_order_XI
      Geo
      A O B E T R
      hAOB
      hInsideE
      hInsideT
      hInsideR
      hAOT_AOR

  exact
    ⟨E, T,
      hInsideE,
      hInsideT,
      hQUS_EOT,
      hComplement⟩

------------------------------------------------------------------------
-- XI.23 v52: I.24/I.25 reduction of the radial remainder problem
------------------------------------------------------------------------

/--
With two corresponding sides fixed, strict comparison of the third
sides is equivalent to strict comparison of the included angles.

This packages Euclid I.24 and I.25 in the exact bidirectional form
needed for the radial-remainder problem.  No circle theorem is used
here; this is only the hinge reduction.
-/
theorem hilbert_twoSides_fixed_thirdSide_less_iff_includedAngle_less_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hDEF : Not (PrimCollinear Geo D E F))
    (hAB_DE : Geo.Congruent A B D E)
    (hAC_DF : Geo.Congruent A C D F) :
    HilbertSegmentLess Geo E F B C <->
      HilbertAngleLess Geo E D F B A C := by

  constructor

  · intro hEF_BC
    exact
      euclid_proposition_25
        (Geo := Geo)
        A B C
        D E F
        hABC
        hDEF
        hAB_DE
        hAC_DF
        hEF_BC

  · intro hEDF_BAC
    exact
      euclid_proposition_24
        (Geo := Geo)
        A B C
        D E F
        hABC
        hDEF
        hAB_DE
        hAC_DF
        hEDF_BAC


/--
Radial-remainder specialization of the preceding hinge equivalence.

The two triangles are

    A-R-B
    C-D-K.

If AR ~= CD and AB ~= CK, then

    DK < RB

is equivalent to

    angle DCK < angle RAB.

Thus the remaining exterior-circumcenter difficulty of XI.23 can be
studied as a circle/circumradius comparison of the two included angles,
rather than as a direct third-side comparison.
-/
theorem hilbert_radial_remainder_side_angle_iff_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A R B C D K : Geo.Point)
    (hARB : Not (PrimCollinear Geo A R B))
    (hCDK : Not (PrimCollinear Geo C D K))
    (hAR_CD : Geo.Congruent A R C D)
    (hCK_AB : Geo.Congruent C K A B) :
    HilbertSegmentLess Geo D K R B <->
      HilbertAngleLess Geo D C K R A B := by

  have hAB_CK :
      Geo.Congruent A B C K :=
    hilbert_congruent_symmetry
      Geo
      C K
      A B
      hCK_AB

  exact
    hilbert_twoSides_fixed_thirdSide_less_iff_includedAngle_less_XI
      Geo
      A R B
      C D K
      hARB
      hCDK
      hAR_CD
      hAB_CK


------------------------------------------------------------------------
-- XI.23 v55: oriented base angles in the four isosceles triangles
------------------------------------------------------------------------

/--
Oriented form of the isosceles-base-angle theorem.

If `AB ~= AC`, then the base angles are congruent in the orientation
used by the XI.23 outside-circumcenter argument:

    angle ABC ~= angle BCA.

The underlying theorem is Euclid I.5; this wrapper only reverses the
second angle, which is representational because Hilbert angles are
unoriented pairs of rays.
-/
theorem hilbert_isosceles_base_angles_oriented_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hAB_AC : Geo.Congruent A B A C) :
    Geo.AngleCongruent A B C B C A := by

  have hBase :
      Geo.AngleCongruent A B C A C B :=
    hilbert_isosceles_base_angles
      Geo
      A B C
      hABC
      hAB_AC

  exact
    (Geo.angle_congruent_reverse_second
      A B C
      A C B).mp
      hBase


------------------------------------------------------------------------
-- XI.23 v56: smaller equal sides force smaller base angle
------------------------------------------------------------------------

/--
A comparison theorem for two isosceles triangles with congruent bases.

Assume

    PA ~= PB,
    UC ~= UD,
    AB ~= CD,
    PA < UC.

Then the base angle of the smaller isosceles triangle is smaller:

    angle PAB < angle UCD.

The proof is synthetic and avoids angle measures and angle-sum
arithmetic.  Cut CX ~= PA on ray CU.  Since CX < CU, X lies between
C and U.  Euclid I.20 in triangle UXD shows that XD is longer than
CX.  Hence BP < DX.  Euclid I.25 applied to triangles CDX and ABP
then gives the required angle comparison.
-/
theorem hilbert_isosceles_base_angle_less_of_smaller_equal_sides_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P A B U C D : Geo.Point)
    (hPAB : Not (PrimCollinear Geo P A B))
    (hUCD : Not (PrimCollinear Geo U C D))
    (hPA_PB : Geo.Congruent P A P B)
    (hUC_UD : Geo.Congruent U C U D)
    (hAB_CD : Geo.Congruent A B C D)
    (hRadiusLess : HilbertSegmentLess Geo P A U C) :
    HilbertAngleLess Geo P A B U C D := by

  --------------------------------------------------------------------
  -- Cut the smaller radius PA from C along ray CU.
  --------------------------------------------------------------------

  have hUC : Not (U = C) :=
    hilbert_noncollinear_ne_first
      Geo U C D hUCD

  have hCU : Not (C = U) := by
    intro h
    exact hUC h.symm

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        P A
        C U
        hCU with
    ⟨X, hRayCUX, hCX_PA⟩

  have hPA_CX :
      Geo.Congruent P A C X :=
    hilbert_congruent_symmetry
      Geo C X P A hCX_PA

  have hCX_UC :
      HilbertSegmentLess Geo C X U C :=
    bookZero_32_lessThanCongruence2
      Geo
      P A
      U C
      C X
      hRadiusLess
      hPA_CX

  have hUC_CU :
      Geo.Congruent U C C U :=
    CongruentSwapSecond
      Geo
      U C
      U C
      (hilbert_congruent_reflexive Geo U C)

  have hCX_CU :
      HilbertSegmentLess Geo C X C U :=
    bookZero_30_lessThanCongruence
      Geo
      C X
      U C
      C U
      hCX_UC
      hUC_CU

  have hRayCXU :
      HilbertSameRay Geo C X U :=
    hilbert_sameRay_symm
      Geo C U X hRayCUX

  have hCXU :
      Geo.Between C X U :=
    bookZero_51_lessThanBetween
      Geo C X U
      hCX_CU
      hRayCXU

  have hUXC :
      Geo.Between U X C :=
    (HilbertOrder.between_incidence
      C X U hCXU).2.2.2.2

  have hUX : Not (U = X) :=
    (HilbertOrder.between_incidence
      U X C hUXC).1

  have hCX : Not (C = X) :=
    (HilbertOrder.between_incidence
      C X U hCXU).1

  have hUXCcol :
      PrimCollinear Geo U X C :=
    (HilbertOrder.between_incidence
      U X C hUXC).2.2.2.1

  --------------------------------------------------------------------
  -- Triangle UXD is nondegenerate.
  --------------------------------------------------------------------

  have hUXD :
      Not (PrimCollinear Geo U X D) := by
    intro hUXDcol

    have hCUX :
        PrimCollinear Geo C U X :=
      PrimCollinearCycle
        Geo
        X C U
        (PrimCollinearCycle
          Geo U X C hUXCcol)

    have hCUD :
        PrimCollinear Geo C U D :=
      hilbert_primCollinear_trans
        Geo
        C U X D
        hUX
        hCUX
        hUXDcol

    exact
      hUCD
        (PrimCollinearSwap
          Geo C U D hCUD)

  have hXUD :
      Not (PrimCollinear Geo X U D) := by
    intro h
    exact
      hUXD
        (PrimCollinearSwap Geo X U D h)

  --------------------------------------------------------------------
  -- I.20 in triangle UXD.
  --
  -- It produces Y with U-X-Y, XY ~= XD, and UD < UY.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_20
        Geo
        X U D
        hXUD with
    ⟨Y, hUXY, hXY_XD, hUD_UY⟩

  --------------------------------------------------------------------
  -- Since UC ~= UD, also UC < UY.  Both C and Y lie on ray UX,
  -- hence U-C-Y.  Together with U-X-C this gives X-C-Y.
  --------------------------------------------------------------------

  have hUD_UC :
      Geo.Congruent U D U C :=
    hilbert_congruent_symmetry
      Geo U C U D hUC_UD

  have hUC_UY :
      HilbertSegmentLess Geo U C U Y :=
    bookZero_32_lessThanCongruence2
      Geo
      U D
      U Y
      U C
      hUD_UY
      hUD_UC

  have hRayUXC :
      HilbertSameRay Geo U X C :=
    hilbert_sameRay_of_between
      Geo U X C hUXC

  have hRayUXY :
      HilbertSameRay Geo U X Y :=
    hilbert_sameRay_of_between
      Geo U X Y hUXY

  have hRayUCY :
      HilbertSameRay Geo U C Y :=
    hilbert_sameRay_of_common
      Geo
      U X C Y
      hRayUXC
      hRayUXY

  have hUCY :
      Geo.Between U C Y :=
    bookZero_51_lessThanBetween
      Geo U C Y
      hUC_UY
      hRayUCY

  have hXCY :
      Geo.Between X C Y :=
    bookZero_3_6a
      Geo
      U X C Y
      hUXC
      hUCY

  --------------------------------------------------------------------
  -- Therefore XC < XY ~= XD, so XC < XD.
  --------------------------------------------------------------------

  have hXC_XY :
      HilbertSegmentLess Geo X C X Y :=
    ⟨C,
      hXCY,
      hilbert_congruent_reflexive Geo X C⟩

  have hXC_XD :
      HilbertSegmentLess Geo X C X D :=
    bookZero_30_lessThanCongruence
      Geo
      X C
      X Y
      X D
      hXC_XY
      hXY_XD

  --------------------------------------------------------------------
  -- Replace XC by the congruent source side PB.
  --------------------------------------------------------------------

  have hXC_PA :
      Geo.Congruent X C P A :=
    CongruentReverseFirst
      Geo
      C X
      P A
      hCX_PA

  have hXC_PB :
      Geo.Congruent X C P B :=
    hilbert_congruent_transitivity
      Geo
      X C
      P A
      P B
      hXC_PA
      hPA_PB

  have hPB_XD :
      HilbertSegmentLess Geo P B X D :=
    bookZero_32_lessThanCongruence2
      Geo
      X C
      X D
      P B
      hXC_XD
      hXC_PB

  have hPB_BP :
      Geo.Congruent P B B P :=
    CongruentSwapSecond
      Geo
      P B
      P B
      (hilbert_congruent_reflexive Geo P B)

  have hBP_XD :
      HilbertSegmentLess Geo B P X D :=
    bookZero_32_lessThanCongruence2
      Geo
      P B
      X D
      B P
      hPB_XD
      hPB_BP

  have hXD_DX :
      Geo.Congruent X D D X :=
    CongruentSwapSecond
      Geo
      X D
      X D
      (hilbert_congruent_reflexive Geo X D)

  have hBP_DX :
      HilbertSegmentLess Geo B P D X :=
    bookZero_30_lessThanCongruence
      Geo
      B P
      X D
      D X
      hBP_XD
      hXD_DX

  --------------------------------------------------------------------
  -- Prepare the two triangles CDX and ABP for I.25.
  --------------------------------------------------------------------

  have hCDX :
      Not (PrimCollinear Geo C D X) := by
    intro hCDXcol

    have hCXD :
        PrimCollinear Geo C X D :=
      PrimCollinearRotate
        Geo C D X hCDXcol

    have hUCX :
        PrimCollinear Geo U C X :=
      PrimCollinearRotate
        Geo
        U X C
        hUXCcol

    have hUCDcol :
        PrimCollinear Geo U C D :=
      hilbert_primCollinear_trans
        Geo
        U C X D
        hCX
        hUCX
        hCXD

    exact hUCD hUCDcol

  have hABP :
      Not (PrimCollinear Geo A B P) := by
    intro hABPcol

    have hBPA :
        PrimCollinear Geo B P A :=
      PrimCollinearCycle
        Geo A B P hABPcol

    have hPABcol :
        PrimCollinear Geo P A B :=
      PrimCollinearCycle
        Geo B P A hBPA

    exact hPAB hPABcol

  have hCD_AB :
      Geo.Congruent C D A B :=
    hilbert_congruent_symmetry
      Geo A B C D hAB_CD

  have hCX_AP :
      Geo.Congruent C X A P :=
    CongruentSwapSecond
      Geo
      C X
      P A
      hCX_PA

  --------------------------------------------------------------------
  -- I.25:
  --
  --   CD ~= AB,
  --   CX ~= AP,
  --   BP < DX,
  --
  -- hence angle BAP < angle DCX.
  --------------------------------------------------------------------

  have hBAP_DCX :
      HilbertAngleLess Geo B A P D C X :=
    euclid_proposition_25
      (Geo := Geo)
      C D X
      A B P
      hCDX
      hABP
      hCD_AB
      hCX_AP
      hBP_DX

  --------------------------------------------------------------------
  -- Reverse the arms of the source angle.
  --------------------------------------------------------------------

  have hBAPrefl :
      Geo.AngleCongruent B A P B A P :=
    Geometry.Geo.angle_congruent_reflexive
      Geo B A P

  have hPAB_BAP :
      Geo.AngleCongruent P A B B A P :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      B A P
      B A P).mp
      hBAPrefl

  have hPAB_DCX :
      HilbertAngleLess Geo P A B D C X :=
    hilbert_angleLess_transport_left
      Geo
      B A P
      P A B
      D C X
      hBAP_DCX
      hPAB
      hPAB_BAP

  --------------------------------------------------------------------
  -- Since X lies on ray CU, angle DCX is angle DCU, hence angle UCD.
  --------------------------------------------------------------------

  have hDCX_DCU_eq :
      Geo.Angle D C X = Geo.Angle D C U :=
    hilbert_angle_eq_of_sameRay_second
      Geo C D X U hRayCXU

  have hDCX_DCU :
      Geo.AngleCongruent D C X D C U := by
    have hRefl :
        Geo.AngleCongruent D C U D C U :=
      Geometry.Geo.angle_congruent_reflexive
        Geo D C U

    unfold Geometry.Geo.AngleCongruent at hRefl ⊢
    rw [hDCX_DCU_eq]
    exact hRefl

  have hDCX_UCD :
      Geo.AngleCongruent D C X U C D :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      D C X
      D C U).mp
      hDCX_DCU

  exact
    hilbert_angleLess_transport_right
      Geo
      P A B
      D C X
      U C D
      hPAB_DCX
      hUCD
      hDCX_UCD


------------------------------------------------------------------------
-- XI.23 v57: reversing the interior radius across an equal-radius chord
------------------------------------------------------------------------

/--
An interior point of the base of an isosceles triangle is strictly
closer to the apex than either endpoint of the base.

If C-H-K and UC ~= UK, then UH < UC.  The proof is purely Book I:
I.5 identifies the base angles of UCK; I.16 says that the exterior
angle UHC of triangle UKH is greater than the remote angle UKH;
after transporting along the base this gives

    angle UCH < angle UHC,

and I.19 gives UH < UC.
-/
theorem hilbert_isosceles_base_inner_point_closer_to_apex_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (U C H K : Geo.Point)
    (hUCK : Not (PrimCollinear Geo U C K))
    (hCHK : Geo.Between C H K)
    (hUC_UK : Geo.Congruent U C U K) :
    HilbertSegmentLess Geo U H U C := by

  have hCHKdata :=
    HilbertOrder.between_incidence
      C H K hCHK

  have hCH : C ≠ H :=
    hCHKdata.1

  have hHK : H ≠ K :=
    hCHKdata.2.1

  have hKH : K ≠ H := by
    intro h
    exact hHK h.symm

  have hKHC :
      Geo.Between K H C :=
    hCHKdata.2.2.2.2

  have hCHKcol :
      PrimCollinear Geo C H K :=
    hCHKdata.2.2.2.1

  have hKHCcol :
      PrimCollinear Geo K H C :=
    PrimCollinearSymm
      Geo C H K hCHKcol

  --------------------------------------------------------------------
  -- Triangles UKH and UCH are nondegenerate.
  --------------------------------------------------------------------

  have hUKH :
      Not (PrimCollinear Geo U K H) := by
    intro hUKHcol

    have hUKC :
        PrimCollinear Geo U K C :=
      hilbert_primCollinear_trans
        Geo
        U K H C
        hKH
        hUKHcol
        hKHCcol

    exact hUCK
      (PrimCollinearRotate
        Geo U K C hUKC)

  have hUCH :
      Not (PrimCollinear Geo U C H) := by
    intro hUCHcol

    have hCHKcol2 :
        PrimCollinear Geo C H K :=
      hCHKcol

    have hUCKcol :
        PrimCollinear Geo U C K :=
      hilbert_primCollinear_trans
        Geo
        U C H K
        hCH
        hUCHcol
        hCHKcol2

    exact hUCK hUCKcol

  have hUHC :
      Not (PrimCollinear Geo U H C) := by
    intro h
    exact hUCH
      (PrimCollinearRotate
        Geo U H C h)

  --------------------------------------------------------------------
  -- I.16 in triangle UKH, with KH extended through H to C.
  --------------------------------------------------------------------

  have hUKH_UHC :
      HilbertAngleLess Geo U K H U H C :=
    euclid_proposition_16_second
      Geo
      U K H C
      hUKH
      hKHC

  --------------------------------------------------------------------
  -- I.5 in UCK and transport H along the base CK.
  --------------------------------------------------------------------

  have hBase :
      Geo.AngleCongruent U C K U K C :=
    hilbert_isosceles_base_angles
      Geo
      U C K
      hUCK
      hUC_UK

  have hBaseSymm :
      Geo.AngleCongruent U K C U C K :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      U C K
      U K C
      hBase

  have hRayKHC :
      HilbertSameRay Geo K H C :=
    hilbert_sameRay_of_between
      Geo K H C hKHC

  have hRayCHK :
      HilbertSameRay Geo C H K :=
    hilbert_sameRay_of_between
      Geo C H K hCHK

  have hUKH_eq_UKC :
      Geo.Angle U K H = Geo.Angle U K C :=
    hilbert_angle_eq_of_sameRay_second
      Geo K U H C hRayKHC

  have hUCH_eq_UCK :
      Geo.Angle U C H = Geo.Angle U C K :=
    hilbert_angle_eq_of_sameRay_second
      Geo C U H K hRayCHK

  have hUCH_UKH :
      Geo.AngleCongruent U C H U K H := by
    have hUKH_UCH :
        Geo.AngleCongruent U K H U C H := by
      unfold Geometry.Geo.AngleCongruent
        at hBaseSymm ⊢
      rw [hUKH_eq_UKC, hUCH_eq_UCK]
      exact hBaseSymm

    exact
      Geometry.Geo.angle_congruent_symmetry
        Geo
        U K H
        U C H
        hUKH_UCH

  have hUCH_UHC :
      HilbertAngleLess Geo U C H U H C :=
    hilbert_angleLess_transport_left
      Geo
      U K H
      U C H
      U H C
      hUKH_UHC
      hUCH
      hUCH_UKH

  --------------------------------------------------------------------
  -- I.19 in triangle UHC.
  --------------------------------------------------------------------

  exact
    euclid_proposition_19
      Geo
      U H C
      hUHC
      hUCH_UHC


/--
Equal-radius reversal of an interior central ray.

Assume UD is an interior ray of angle CUK, so ray UD meets the open
chord CK.  If C, D and K all have the same distance from U, then the
intersection point lies strictly inside the radius UD.  Consequently
the opposite view from D has U on an interior ray of angle CDK:

    ray DU meets the open segment CK.

This is the local orientation fact needed in the outside-circumcenter
branch of XI.23.
-/
theorem hilbert_equalRadius_interiorRay_reverse_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (U C D K : Geo.Point)
    (hCUK : Not (PrimCollinear Geo C U K))
    (hInsideD : HilbertRayMeetsSegment Geo U D C K)
    (hUC_UD : Geo.Congruent U C U D)
    (hUC_UK : Geo.Congruent U C U K) :
    HilbertRayMeetsSegment Geo D U C K := by

  rcases hInsideD with
    ⟨H, hCHK, hRayUDH⟩

  have hUCK :
      Not (PrimCollinear Geo U C K) := by
    intro h
    exact hCUK
      (PrimCollinearSwap
        Geo U C K h)

  have hUH_UC :
      HilbertSegmentLess Geo U H U C :=
    hilbert_isosceles_base_inner_point_closer_to_apex_XI
      Geo
      U C H K
      hUCK
      hCHK
      hUC_UK

  have hUH_UD :
      HilbertSegmentLess Geo U H U D :=
    bookZero_30_lessThanCongruence
      Geo
      U H
      U C
      U D
      hUH_UC
      hUC_UD

  have hRayUHD :
      HilbertSameRay Geo U H D :=
    hilbert_sameRay_symm
      Geo U D H hRayUDH

  have hUHD :
      Geo.Between U H D :=
    bookZero_51_lessThanBetween
      Geo
      U H D
      hUH_UD
      hRayUHD

  have hDHU :
      Geo.Between D H U :=
    (HilbertOrder.between_incidence
      U H D hUHD).2.2.2.2

  have hRayDHU :
      HilbertSameRay Geo D H U :=
    hilbert_sameRay_of_between
      Geo D H U hDHU

  have hRayDUH :
      HilbertSameRay Geo D U H :=
    hilbert_sameRay_symm
      Geo D H U hRayDHU

  exact ⟨H, hCHK, hRayDUH⟩


------------------------------------------------------------------------
-- XI.23 v58: the auxiliary radius is an interior divider at D
------------------------------------------------------------------------

/--
Opposite-side chord crossing for an equal-radius configuration.

Assume P,C,D,T are arranged so that C and T lie on opposite sides of
line PD and

    PC ~= PD,
    PC ~= PT.

Let H be the crossing of CT with line PD.  If H = P, the conclusion is
immediate.  Otherwise H is an interior point of chord CT in the
isosceles triangle PCT, so v57 gives

    PH < PC ~= PD.

Hence H cannot lie beyond D on the ray PD.  Order trichotomy on line
PD leaves exactly the two cases in which H lies on ray DP.  Therefore
ray DP meets the open segment CT.
-/
theorem hilbert_equalRadius_oppositeSides_reverse_divider_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P C D T : Geo.Point)
    (base : Geo.Line)
    (hPbase : HilbertIncidence.OnLine P base)
    (hDbase : HilbertIncidence.OnLine D base)
    (hOppCT : HilbertOppositeSide Geo C T base)
    (hCPD : Not (PrimCollinear Geo C P D))
    (hPC_PD : Geo.Congruent P C P D)
    (hPC_PT : Geo.Congruent P C P T) :
    HilbertRayMeetsSegment Geo D P C T := by

  rcases hOppCT with
    ⟨hCoff, hToff, H, hCHT, hHbase⟩

  have hPDC :
      Not (PrimCollinear Geo P D C) := by
    intro h
    exact hCPD
      (PrimCollinearRotate
        Geo
        C D P
        (PrimCollinearSymm Geo P D C h))

  have hPD : P ≠ D :=
    hilbert_noncollinear_ne_first
      Geo P D C hPDC

  --------------------------------------------------------------------
  -- If the chord CT crosses line PD exactly at P, we are done.
  --------------------------------------------------------------------

  by_cases hHP : H = P

  · subst H

    have hRayDPP :
        HilbertSameRay Geo D P P :=
      hilbert_sameRay_refl
        Geo D P hPD

    exact ⟨P, hCHT, hRayDPP⟩

  --------------------------------------------------------------------
  -- Otherwise triangle PCT is nondegenerate.
  --------------------------------------------------------------------

  · have hPH : P ≠ H := by
      intro h
      exact hHP h.symm

    have hCHTdata :=
      HilbertOrder.between_incidence
        C H T hCHT

    have hCT : C ≠ T :=
      hCHTdata.2.2.1

    have hCHTcol :
        PrimCollinear Geo C H T :=
      hCHTdata.2.2.2.1

    have hCTHcol :
        PrimCollinear Geo C T H :=
      PrimCollinearRotate
        Geo C H T hCHTcol

    have hPCT :
        Not (PrimCollinear Geo P C T) := by
      intro hPCTcol

      have hPCH :
          PrimCollinear Geo P C H :=
        hilbert_primCollinear_trans
          Geo
          P C T H
          hCT
          hPCTcol
          hCTHcol

      have hPHC :
          PrimCollinear Geo P H C :=
        PrimCollinearRotate
          Geo P C H hPCH

      have hCbase :
          HilbertIncidence.OnLine C base :=
        hilbert_collinear_on_line
          Geo
          P H C
          base
          hPH
          hPbase
          hHbase
          hPHC

      exact hCoff hCbase

    ------------------------------------------------------------------
    -- H is an inner point of chord CT, so PH < PC ~= PD.
    ------------------------------------------------------------------

    have hPH_PC :
        HilbertSegmentLess Geo P H P C :=
      hilbert_isosceles_base_inner_point_closer_to_apex_XI
        Geo
        P C H T
        hPCT
        hCHT
        hPC_PT

    have hPH_PD :
        HilbertSegmentLess Geo P H P D :=
      bookZero_30_lessThanCongruence
        Geo
        P H
        P C
        P D
        hPH_PC
        hPC_PD

    have hHD : H ≠ D := by
      intro hHD
      subst H

      exact
        (hilbert_segmentLess_not_congruent
          Geo
          P D
          P D
          hPH_PD)
          (hilbert_congruent_reflexive Geo P D)

    have hPHDcol :
        PrimCollinear Geo P H D :=
      ⟨base, hPbase, hHbase, hDbase⟩

    ------------------------------------------------------------------
    -- Order trichotomy on P,H,D.
    ------------------------------------------------------------------

    rcases
        hilbert_between_trichotomy
          Geo
          P H D
          hPH
          hHD
          hPD
          hPHDcol
      with
      hPHD | hHPD | hPDH

    · have hDHP :
          Geo.Between D H P :=
        (HilbertOrder.between_incidence
          P H D hPHD).2.2.2.2

      have hRayDHP :
          HilbertSameRay Geo D H P :=
        hilbert_sameRay_of_between
          Geo D H P hDHP

      have hRayDPH :
          HilbertSameRay Geo D P H :=
        hilbert_sameRay_symm
          Geo D H P hRayDHP

      exact ⟨H, hCHT, hRayDPH⟩

    · have hDPH :
          Geo.Between D P H :=
        (HilbertOrder.between_incidence
          H P D hHPD).2.2.2.2

      have hRayDPH :
          HilbertSameRay Geo D P H :=
        hilbert_sameRay_of_between
          Geo D P H hDPH

      exact ⟨H, hCHT, hRayDPH⟩

    · have hPD_PH :
          HilbertSegmentLess Geo P D P H :=
        ⟨D,
          hPDH,
          hilbert_congruent_reflexive Geo P D⟩

      exact
        False.elim
          ((hilbert_segmentLess_asymm
              Geo P H P D hPH_PD)
            hPD_PH)




------------------------------------------------------------------------
-- XI.23 v59: strict addition for interior angle decompositions
------------------------------------------------------------------------

/--
Strict componentwise comparison of two interior angle decompositions
implies strict comparison of the whole angles.

If OD divides angle XOC and O'D' divides angle X'O'C', and

    angle XOD < angle X'O'D',
    angle COD < angle C'O'D',

then

    angle XOC < angle X'O'C'.

The proof uses trichotomy of the whole angles.  Equality is excluded by
transporting one divider to the other whole angle and applying the
"two components cannot both be smaller" lemma.  If the whole-angle
order were reversed, the smaller whole angle would embed inside the
larger one.  Transporting its divider into that embedded copy and using
complement-order reversal twice forces its second component to be
smaller than the corresponding source component, contradicting the
assumed second strict inequality.
-/
theorem hilbert_angleDecomposition_componentwise_less_whole_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hX'O'C' : Not (PrimCollinear Geo X' O' C'))
    (hInsideD : HilbertRayMeetsSegment Geo O D X C)
    (hInsideD' : HilbertRayMeetsSegment Geo O' D' X' C')
    (hLeft : HilbertAngleLess Geo X O D X' O' D')
    (hRight : HilbertAngleLess Geo C O D C' O' D') :
    HilbertAngleLess Geo X O C X' O' C' := by

  --------------------------------------------------------------------
  -- Proper component angles used below.
  --------------------------------------------------------------------

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact hXOC
      (PrimCollinearSymm Geo C O X h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo O D X C hInsideD

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    (hilbert_interior_angle_less
      Geo O D C X hCOX hInsideDrev).1

  have hC'O'X' :
      Not (PrimCollinear Geo C' O' X') := by
    intro h
    exact hX'O'C'
      (PrimCollinearSymm Geo C' O' X' h)

  have hInsideD'rev :
      HilbertRayMeetsSegment Geo O' D' C' X' :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo O' D' X' C' hInsideD'

  have hC'O'D' :
      Not (PrimCollinear Geo C' O' D') :=
    (hilbert_interior_angle_less
      Geo O' D' C' X' hC'O'X' hInsideD'rev).1

  --------------------------------------------------------------------
  -- Trichotomy of the whole angles.
  --------------------------------------------------------------------

  rcases
      angle_trichotomy
        Geo
        X O C
        X' O' C'
        hXOC
        hX'O'C'
    with hWholeEq | hWholeOrder

  --------------------------------------------------------------------
  -- Case 1: the whole angles are congruent.
  --------------------------------------------------------------------

  · rcases
        hilbert_interior_subangle_transport_both
          Geo
          O X C D
          X' O' C'
          hXOC
          hX'O'C'
          hInsideD
          hWholeEq
      with
      ⟨E, hInsideE, hParts⟩

    have hX'O'E :
        Not (PrimCollinear Geo X' O' E) :=
      (hilbert_interior_angle_less
        Geo O' E X' C' hX'O'C' hInsideE).1

    have hInsideErev :
        HilbertRayMeetsSegment Geo O' E C' X' :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo O' E X' C' hInsideE

    have hC'O'E :
        Not (PrimCollinear Geo C' O' E) :=
      (hilbert_interior_angle_less
        Geo O' E C' X' hC'O'X' hInsideErev).1

    have hX'O'E_X'O'D' :
        HilbertAngleLess Geo X' O' E X' O' D' :=
      hilbert_angleLess_transport_left
        Geo
        X O D
        X' O' E
        X' O' D'
        hLeft
        hX'O'E
        (Geometry.Geo.angle_congruent_symmetry
          Geo X O D X' O' E hParts.2)

    have hC'O'E_C'O'D' :
        HilbertAngleLess Geo C' O' E C' O' D' :=
      hilbert_angleLess_transport_left
        Geo
        C O D
        C' O' E
        C' O' D'
        hRight
        hC'O'E
        (Geometry.Geo.angle_congruent_symmetry
          Geo C O D C' O' E hParts.1)

    exact
      False.elim
        (hilbert_angleDecomposition_two_component_less_impossible
          Geo
          O' X' C' E D'
          hX'O'C'
          hInsideE
          hInsideD'
          hX'O'E_X'O'D'
          hC'O'E_C'O'D')

  --------------------------------------------------------------------
  -- Case 2: one whole angle is strictly smaller than the other.
  --------------------------------------------------------------------

  · rcases hWholeOrder with hWanted | hReverse

    · exact hWanted

    ------------------------------------------------------------------
    -- Assume, for contradiction, that the target whole is smaller.
    ------------------------------------------------------------------

    · rcases hReverse with
        ⟨_hX'O'C', _hXOC, E, hInsideE, hWholeTarget⟩

      have hXOE_less_XOC :
          HilbertAngleLess Geo X O E X O C :=
        hilbert_interior_angle_less
          Geo O E X C hXOC hInsideE

      have hXOE :
          Not (PrimCollinear Geo X O E) :=
        hXOE_less_XOC.1

      rcases
          hilbert_interior_subangle_transport_both
            Geo
            O' X' C' D'
            X O E
            hX'O'C'
            hXOE
            hInsideD'
            hWholeTarget
        with
        ⟨F, hInsideF, hTargetParts⟩

      have hXOF_less_XOE :
          HilbertAngleLess Geo X O F X O E :=
        hilbert_interior_angle_less
          Geo O F X E hXOE hInsideF

      have hXOF :
          Not (PrimCollinear Geo X O F) :=
        hXOF_less_XOE.1

      have hXOD_XOF :
          HilbertAngleLess Geo X O D X O F :=
        hilbert_angleLess_transport_right
          Geo
          X O D
          X' O' D'
          X O F
          hLeft
          hXOF
          hTargetParts.2

      have hXOD_XOE :
          HilbertAngleLess Geo X O D X O E :=
        hilbert_angleLess_trans
          Geo
          X O D
          X O F
          X O E
          hXOD_XOF
          hXOF_less_XOE

      ----------------------------------------------------------------
      -- Promote D from the whole XOC to the embedded whole XOE.
      ----------------------------------------------------------------

      have hOX : O ≠ X :=
        hilbert_noncollinear_ne_first
          Geo O X C
          (by
            intro h
            exact hXOC
              (PrimCollinearSwap Geo O X C h))

      rcases
          HilbertPlaneIncidence.line_through
            O X hOX
        with
        ⟨lineOX, hOlineOX, hXlineOX⟩

      have hDCSameOX :
          HilbertSameSide Geo D C lineOX :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O D C X
          lineOX
          hOlineOX
          hXlineOX
          hCOX
          hInsideDrev

      have hInsideErevWhole :
          HilbertRayMeetsSegment Geo O E C X :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo O E X C hInsideE

      have hECSameOX :
          HilbertSameSide Geo E C lineOX :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O E C X
          lineOX
          hOlineOX
          hXlineOX
          hCOX
          hInsideErevWhole

      have hCESameOX :
          HilbertSameSide Geo C E lineOX :=
        hilbert_sameSide_symm
          Geo E C lineOX hECSameOX

      have hDESameOX :
          HilbertSameSide Geo D E lineOX :=
        hilbert_sameSide_trans
          Geo D C E lineOX hDCSameOX hCESameOX

      have hInsideD_XE :
          HilbertRayMeetsSegment Geo O D X E :=
        hilbert_angleDecomposition_angle_less_ray_inside
          Geo
          D E O X
          lineOX
          hOlineOX
          hXlineOX
          hOX
          hDESameOX
          hXOD_XOE

      ----------------------------------------------------------------
      -- Inside XOE, D precedes F, so EOF < EOD.
      ----------------------------------------------------------------

      have hEOF_EOD :
          HilbertAngleLess Geo E O F E O D :=
        hilbert_angleDecomposition_complement_order_reverse_XI
          Geo
          O X E D F
          hXOE
          hInsideD_XE
          hInsideF
          hXOD_XOF

      ----------------------------------------------------------------
      -- Inside XOC, D precedes E.  Therefore E lies inside DOC.
      ----------------------------------------------------------------

      have hCOE_COD :
          HilbertAngleLess Geo C O E C O D :=
        hilbert_angleDecomposition_complement_order_reverse_XI
          Geo
          O X C D E
          hXOC
          hInsideD
          hInsideE
          hXOD_XOE

      have hOC : O ≠ C :=
        hilbert_noncollinear_ne_first
          Geo O C X
          (by
            intro h
            exact hXOC
              (PrimCollinearRotate
                Geo X C O
                (PrimCollinearSymm Geo O C X h)))

      rcases
          HilbertPlaneIncidence.line_through
            O C hOC
        with
        ⟨lineOC, hOlineOC, hClineOC⟩

      have hDXSameOC :
          HilbertSameSide Geo D X lineOC :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O D X C
          lineOC
          hOlineOC
          hClineOC
          hXOC
          hInsideD

      have hEXSameOC :
          HilbertSameSide Geo E X lineOC :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O E X C
          lineOC
          hOlineOC
          hClineOC
          hXOC
          hInsideE

      have hXDSameOC :
          HilbertSameSide Geo X D lineOC :=
        hilbert_sameSide_symm
          Geo D X lineOC hDXSameOC

      have hEDSameOC :
          HilbertSameSide Geo E D lineOC :=
        hilbert_sameSide_trans
          Geo E X D lineOC hEXSameOC hXDSameOC

      have hInsideE_CD :
          HilbertRayMeetsSegment Geo O E C D :=
        hilbert_angleDecomposition_angle_less_ray_inside
          Geo
          E D O C
          lineOC
          hOlineOC
          hClineOC
          hOC
          hEDSameOC
          hCOE_COD

      have hInsideE_DC :
          HilbertRayMeetsSegment Geo O E D C :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo O E C D hInsideE_CD

      have hDOC :
          Not (PrimCollinear Geo D O C) := by
        intro h
        exact hCOD
          (PrimCollinearSymm Geo D O C h)

      have hDOE_DOC :
          HilbertAngleLess Geo D O E D O C :=
        hilbert_interior_angle_less
          Geo O E D C hDOC hInsideE_DC

      have hDOE :
          Not (PrimCollinear Geo D O E) :=
        hDOE_DOC.1

      have hEOD :
          Not (PrimCollinear Geo E O D) := by
        intro h
        exact hDOE
          (PrimCollinearSymm Geo E O D h)

      have hReflDOE :
          Geo.AngleCongruent D O E D O E :=
        Geometry.Geo.angle_congruent_reflexive
          Geo D O E

      have hEOD_DOE :
          Geo.AngleCongruent E O D D O E :=
        (Geometry.Geo.angle_congruent_reverse_first
          Geo D O E D O E).mp hReflDOE

      have hEOD_DOC :
          HilbertAngleLess Geo E O D D O C :=
        hilbert_angleLess_transport_left
          Geo
          D O E
          E O D
          D O C
          hDOE_DOC
          hEOD
          hEOD_DOE

      have hReflDOC :
          Geo.AngleCongruent D O C D O C :=
        Geometry.Geo.angle_congruent_reflexive
          Geo D O C

      have hDOC_COD :
          Geo.AngleCongruent D O C C O D :=
        (Geometry.Geo.angle_congruent_reverse_second
          Geo D O C D O C).mp hReflDOC

      have hEOD_COD :
          HilbertAngleLess Geo E O D C O D :=
        hilbert_angleLess_transport_right
          Geo
          E O D
          D O C
          C O D
          hEOD_DOC
          hCOD
          hDOC_COD

      have hEOF_COD :
          HilbertAngleLess Geo E O F C O D :=
        hilbert_angleLess_trans
          Geo
          E O F
          E O D
          C O D
          hEOF_EOD
          hEOD_COD

      ----------------------------------------------------------------
      -- But the assumed second component inequality says COD < EOF.
      ----------------------------------------------------------------

      have hEOX :
          Not (PrimCollinear Geo E O X) := by
        intro h
        exact hXOE
          (PrimCollinearSymm Geo E O X h)

      have hInsideFrev :
          HilbertRayMeetsSegment Geo O F E X :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo O F X E hInsideF

      have hEOF :
          Not (PrimCollinear Geo E O F) :=
        (hilbert_interior_angle_less
          Geo O F E X hEOX hInsideFrev).1

      have hCOD_EOF :
          HilbertAngleLess Geo C O D E O F :=
        hilbert_angleLess_transport_right
          Geo
          C O D
          C' O' D'
          E O F
          hRight
          hEOF
          hTargetParts.1

      have hCycle :
          HilbertAngleLess Geo C O D C O D :=
        hilbert_angleLess_trans
          Geo
          C O D
          E O F
          C O D
          hCOD_EOF
          hEOF_COD

      exact
        False.elim
          ((hilbert_angleLess_irrefl
              Geo C O D)
            hCycle)

------------------------------------------------------------------------
-- XI.23 v60: assemble the two strict component inequalities
------------------------------------------------------------------------

/--
If an interior divider cuts a nondegenerate left component, then the
whole angle is nondegenerate.

Indeed, if X,O,C were collinear, the crossing point H of ray OD with
segment XC would lie on the same line XOC.  Since O,D,H are collinear
and O != H, this would force X,O,D to be collinear as well.
-/
theorem hilbert_angleDecomposition_whole_noncollinear_of_left_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D : Geo.Point)
    (hInside : HilbertRayMeetsSegment Geo O D X C)
    (hXOD : Not (PrimCollinear Geo X O D)) :
    Not (PrimCollinear Geo X O C) := by

  intro hXOC

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  rcases hXOC with
    ⟨lineXC, hXline, hOline, hCline⟩

  have hHline :
      HilbertIncidence.OnLine H lineXC :=
    hilbert_between_on_line
      Geo X H C lineXC hXline hCline hXHC

  have hOH : O ≠ H := by
    intro hOH
    exact hRayODH.2.1 hOH.symm

  rcases hRayODH.2.2.1 with
    ⟨lineOD, hOlineOD, hDlineOD, hHlineOD⟩

  have hLines : lineXC = lineOD :=
    HilbertPlaneIncidence.line_unique
      O H hOH
      lineXC lineOD
      hOline hHline
      hOlineOD hHlineOD

  subst lineOD

  exact hXOD
    ⟨lineXC, hXline, hOline, hDlineOD⟩



------------------------------------------------------------------------
-- XI.23 v63: reusable nesting of interior angle rays
------------------------------------------------------------------------

/--
If OE is interior to angle AOB and OT is interior to angle AOE, then
OT is interior to angle AOB.

This is the reusable nesting step that was already proved internally in
v51.  It is now exposed as a standalone API lemma.
-/
theorem hilbert_angleDecomposition_nested_inside_left_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B E T : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideE : HilbertRayMeetsSegment Geo O E A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T A E) :
    HilbertRayMeetsSegment Geo O T A B := by

  have hAOE_AOB :
      HilbertAngleLess Geo A O E A O B :=
    hilbert_interior_angle_less
      Geo
      O E A B
      hAOB
      hInsideE

  have hAOE :
      Not (PrimCollinear Geo A O E) :=
    hAOE_AOB.1

  have hAOT_AOE :
      HilbertAngleLess Geo A O T A O E :=
    hilbert_interior_angle_less
      Geo
      O T A E
      hAOE
      hInsideT

  have hAOT_AOB :
      HilbertAngleLess Geo A O T A O B :=
    hilbert_angleLess_trans
      Geo
      A O T
      A O E
      A O B
      hAOT_AOE
      hAOE_AOB

  have hAO : O ≠ A :=
    hilbert_noncollinear_ne_first
      Geo O A B
      (by
        intro h
        exact hAOB
          (PrimCollinearSwap Geo O A B h))

  rcases
      HilbertPlaneIncidence.line_through
        O A hAO
    with
    ⟨lineOA, hOlineOA, hAlineOA⟩

  have hEOA :
      Not (PrimCollinear Geo E O A) := by
    intro h
    exact hAOE
      (PrimCollinearSymm Geo E O A h)

  have hInsideTrev :
      HilbertRayMeetsSegment Geo O T E A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A E
      hInsideT

  have hTESameOA :
      HilbertSameSide Geo T E lineOA :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O T E A
      lineOA
      hOlineOA
      hAlineOA
      hEOA
      hInsideTrev

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact hAOB
      (PrimCollinearSymm Geo B O A h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A B
      hInsideE

  have hEBSameOA :
      HilbertSameSide Geo E B lineOA :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O E B A
      lineOA
      hOlineOA
      hAlineOA
      hBOA
      hInsideErev

  have hTBSameOA :
      HilbertSameSide Geo T B lineOA :=
    hilbert_sameSide_trans
      Geo
      T E B
      lineOA
      hTESameOA
      hEBSameOA

  exact
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      T B O A
      lineOA
      hOlineOA
      hAlineOA
      hAO
      hTBSameOA
      hAOT_AOB


/--
Right-hand nesting form.

If OE is interior to angle AOB and OT is interior to angle EOB, then
OT is also interior to angle AOB.
-/
theorem hilbert_angleDecomposition_nested_inside_right_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B E T : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideE : HilbertRayMeetsSegment Geo O E A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T E B) :
    HilbertRayMeetsSegment Geo O T A B := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact hAOB
      (PrimCollinearSymm Geo B O A h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A B
      hInsideE

  have hInsideTrev :
      HilbertRayMeetsSegment Geo O T B E :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T E B
      hInsideT

  have hNestedRev :
      HilbertRayMeetsSegment Geo O T B A :=
    hilbert_angleDecomposition_nested_inside_left_XI
      Geo
      B O A E T
      hBOA
      hInsideErev
      hInsideTrev

  exact
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T B A
      hNestedRev



------------------------------------------------------------------------
-- XI.23 v64: a synthetic angle sum realized by an interior divider
------------------------------------------------------------------------

/--
Nested-divider converse.

If OE is interior to angle XOC and OZ is interior to angle EOC, then
OE is interior to angle XOZ.

Together with the two nesting lemmas from v63 this gives the exact
incidence data needed to assemble a smaller angle from two component
angles.
-/
theorem hilbert_angleDecomposition_nested_parent_divider_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (X O C E Z : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hInsideE : HilbertRayMeetsSegment Geo O E X C)
    (hInsideZ : HilbertRayMeetsSegment Geo O Z E C) :
    HilbertRayMeetsSegment Geo O E X Z := by

  have hInsideZwhole :
      HilbertRayMeetsSegment Geo O Z X C :=
    hilbert_angleDecomposition_nested_inside_right_XI
      Geo
      X O C E Z
      hXOC
      hInsideE
      hInsideZ

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact hXOC
      (PrimCollinearSymm Geo C O X h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E X C
      hInsideE

  have hInsideZrev :
      HilbertRayMeetsSegment Geo O Z C E :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O Z E C
      hInsideZ

  have hCOE :
      Not (PrimCollinear Geo C O E) :=
    (hilbert_interior_angle_less
      Geo
      O E C X
      hCOX
      hInsideErev).1

  have hCOZ_COE :
      HilbertAngleLess Geo C O Z C O E :=
    hilbert_interior_angle_less
      Geo
      O Z C E
      hCOE
      hInsideZrev

  have hInsideZwholeRev :
      HilbertRayMeetsSegment Geo O Z C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O Z X C
      hInsideZwhole

  have hXOE_XOZ :
      HilbertAngleLess Geo X O E X O Z :=
    hilbert_angleDecomposition_complement_order_reverse_XI
      Geo
      O C X Z E
      hCOX
      hInsideZwholeRev
      hInsideErev
      hCOZ_COE

  have hOX :
      O ≠ X :=
    hilbert_noncollinear_ne_first
      Geo
      O X C
      (by
        intro h
        exact hXOC
          (PrimCollinearSwap Geo O X C h))

  rcases
      HilbertPlaneIncidence.line_through
        O X hOX
    with
    ⟨lineOX, hOlineOX, hXlineOX⟩

  have hEDSame :
      HilbertSameSide Geo E C lineOX :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O E C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideErev

  have hZCSame :
      HilbertSameSide Geo Z C lineOX :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O Z C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideZwholeRev

  have hCZSame :
      HilbertSameSide Geo C Z lineOX :=
    hilbert_sameSide_symm
      Geo
      Z C
      lineOX
      hZCSame

  have hEZSame :
      HilbertSameSide Geo E Z lineOX :=
    hilbert_sameSide_trans
      Geo
      E C Z
      lineOX
      hEDSame
      hCZSame

  exact
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      E Z O X
      lineOX
      hOlineOX
      hXlineOX
      hOX
      hEZSame
      hXOE_XOZ


/--
If an interior ray OE decomposes angle XOC, and the two component
angles synthetically have sum greater than a proper target angle APB,
then the target angle is strictly smaller than the whole angle XOC.

This is the realization theorem corresponding directly to
`HilbertTwoAnglesGreaterThanAngle`.
-/
theorem hilbert_twoAnglesGreaterThanAngle_of_interior_split_gives_whole_greater_XI
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (X O C E A P B : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hInsideE : HilbertRayMeetsSegment Geo O E X C)
    (hSum :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        X O E
        E O C
        A P B) :
    HilbertAngleLess Geo A P B X O C := by

  have hXOE_XOC :
      HilbertAngleLess Geo X O E X O C :=
    hilbert_interior_angle_less
      Geo
      O E X C
      hXOC
      hInsideE

  have hXOE :
      Not (PrimCollinear Geo X O E) :=
    hXOE_XOC.1

  have hEOC :
      Not (PrimCollinear Geo E O C) :=
    hSum.2.1

  have hAPB :
      Not (PrimCollinear Geo A P B) :=
    hSum.2.2.1

  rcases hSum.2.2.2 with
    hTargetLessFirst | hRest

  · exact
      hilbert_angleLess_trans
        Geo
        A P B
        X O E
        X O C
        hTargetLessFirst
        hXOE_XOC

  · rcases hRest with hTargetEqFirst | hDecomp

    · exact
        hilbert_angleLess_intro
          Geo
          A P B
          X O C
          E
          hAPB
          hXOC
          hInsideE
          hTargetEqFirst

    · rcases hDecomp with
        ⟨Y,
          hInsideY,
          hFirstPart,
          hRemainder⟩

      rcases hRemainder with
        ⟨hYPB,
          _hEOC,
          Z,
          hInsideZ,
          hYPB_EOZ⟩

      have hInsideZwhole :
          HilbertRayMeetsSegment Geo O Z X C :=
        hilbert_angleDecomposition_nested_inside_right_XI
          Geo
          X O C E Z
          hXOC
          hInsideE
          hInsideZ

      have hXOZ :
          Not (PrimCollinear Geo X O Z) :=
        (hilbert_interior_angle_less
          Geo
          O Z X C
          hXOC
          hInsideZwhole).1

      have hInsideE_XZ :
          HilbertRayMeetsSegment Geo O E X Z :=
        hilbert_angleDecomposition_nested_parent_divider_XI
          Geo
          X O C E Z
          hXOC
          hInsideE
          hInsideZ

      have hAPY_XOE :
          Geo.AngleCongruent A P Y X O E :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          X O E
          A P Y
          hFirstPart

      have hWholeCong :
          Geo.AngleCongruent A P B X O Z :=
        hilbert_angleDecomposition_angle_addition_interior
          Geo
          P A B Y
          O X Z E
          hAPB
          hXOZ
          hInsideY
          hInsideE_XZ
          hAPY_XOE
          hYPB_EOZ

      exact
        hilbert_angleLess_intro
          Geo
          A P B
          X O C
          Z
          hAPB
          hXOC
          hInsideZwhole
          hWholeCong

end Geometry

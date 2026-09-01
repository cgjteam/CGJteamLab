import CGJteamLab.Proposition2_12
import CGJteamLab.Proposition2_7
import CGJteamLab.Proposition47
import CGJteamLab.Proposition46
import CGJteamLab.Proposition16

namespace Geometry

universe u

variable (Geo : Geometry.Geo)
/--
Euclid II.13, first geometric helper.

If B-D-C and ADB is a right angle, then ADC is also a right angle.

This is the formal version of the classical fact that AD is
perpendicular to the whole carrier BC, not only to the ray DB.
-/
theorem proposition2_13_right_angle_other_side
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hBDC : Geo.Between B D C)
    (hADB : Not (PrimCollinear Geo A D B))
    (hRightADB : HilbertRightAngle Geo A D B) :
    HilbertRightAngle Geo A D C := by

  have hBDCdata :=
    HilbertOrder.between_incidence
      B D C hBDC

  have hBD : Ne B D :=
    hBDCdata.1

  have hDC : Ne D C :=
    hBDCdata.2.1

  have hBDCcol :
      PrimCollinear Geo B D C :=
    hBDCdata.2.2.2.1

  --------------------------------------------------------------------
  -- Reverse the right angle:
  --
  --   A-D-B right  ->  B-D-A right.
  --------------------------------------------------------------------

  have hBDA :
      Not (PrimCollinear Geo B D A) := by
    intro h
    exact
      hADB
        (PrimCollinearSymm
          Geo B D A h)

  have hRightBDA :
      HilbertRightAngle Geo B D A :=
    proposition2_12_right_angle_swap
      Geo
      A D B
      hADB
      hRightADB

  --------------------------------------------------------------------
  -- Transport the first arm along the carrier B-D-C:
  --
  --   B-D-A right  ->  C-D-A right.
  --------------------------------------------------------------------

  have hRightCDA :
      HilbertRightAngle Geo C D A :=
    proposition2_12_right_angle_collinear_transport
      Geo
      B D C A
      hBD
      hDC.symm
      hBDCcol
      hBDA
      hRightBDA

  --------------------------------------------------------------------
  -- We also need noncollinearity C-D-A in order to swap the arms.
  --------------------------------------------------------------------

  have hCDA :
      Not (PrimCollinear Geo C D A) := by
    intro hCDAcol

    have hDCA :
        PrimCollinear Geo D C A :=
      PrimCollinearSwap
        Geo C D A hCDAcol

    have hBDAcol :
        PrimCollinear Geo B D A :=
      hilbert_primCollinear_trans
        Geo
        B D C A
        hDC
        hBDCcol
        hDCA

    exact hBDA hBDAcol

  --------------------------------------------------------------------
  -- Swap the arms once more:
  --
  --   C-D-A right  ->  A-D-C right.
  --------------------------------------------------------------------

  exact
    proposition2_12_right_angle_swap
      Geo
      C D A
      hCDA
      hRightCDA

/--
Euclid II.13, second incremental package.

For the internal perpendicular-foot configuration B-D-C with ADB right,
apply Euclid I.47 to the two right triangles ADB and ADC.

The result deliberately preserves all square representatives. In the
next stages the two independently constructed squares on AD will be
identified by square transport.
-/
theorem proposition2_13_two_pythagoras
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hBDC : Geo.Between B D C)
    (hADB : Not (PrimCollinear Geo A D B))
    (hRightADB : HilbertRightAngle Geo A D B) :
    exists AB0 AB1 DA10 DA11 DB0 DB1 : Geo.Point,
    exists AC0 AC1 DA20 DA21 DC0 DC1 : Geo.Point,

      IsSquare Geo A B AB1 AB0 /\
      IsSquare Geo D A DA10 DA11 /\
      IsSquare Geo D B DB1 DB0 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B AB1 AB0)
        (hilbertParallelogramTerm Geo D A DA10 DA11 +
         hilbertParallelogramTerm Geo D B DB1 DB0) /\

      IsSquare Geo A C AC1 AC0 /\
      IsSquare Geo D A DA20 DA21 /\
      IsSquare Geo D C DC1 DC0 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A C AC1 AC0)
        (hilbertParallelogramTerm Geo D A DA20 DA21 +
         hilbertParallelogramTerm Geo D C DC1 DC0) := by

  have hRightADC :
      HilbertRightAngle Geo A D C :=
    proposition2_13_right_angle_other_side
      Geo
      A B C D
      hBDC
      hADB
      hRightADB

  --------------------------------------------------------------------
  -- Noncollinearity of D,A,B.
  --------------------------------------------------------------------

  have hDAB :
      Not (PrimCollinear Geo D A B) := by
    intro hDABcol
    exact
      hADB
        (PrimCollinearSwap
          Geo D A B hDABcol)

  --------------------------------------------------------------------
  -- Noncollinearity of A,D,C.
  --------------------------------------------------------------------

  have hBDCdata :=
    HilbertOrder.between_incidence
      B D C hBDC

  have hDC : Ne D C :=
    hBDCdata.2.1

  have hBDCcol :
      PrimCollinear Geo B D C :=
    hBDCdata.2.2.2.1

  have hADC :
      Not (PrimCollinear Geo A D C) := by
    intro hADCcol

    have hDCA :
        PrimCollinear Geo D C A :=
      PrimCollinearCycle
        Geo A D C hADCcol

    have hBDA :
        PrimCollinear Geo B D A :=
      hilbert_primCollinear_trans
        Geo
        B D C A
        hDC
        hBDCcol
        hDCA

    exact
      hADB
        (PrimCollinearSymm
          Geo B D A hBDA)

  have hDAC :
      Not (PrimCollinear Geo D A C) := by
    intro hDACcol
    exact
      hADC
        (PrimCollinearSwap
          Geo D A C hDACcol)

  --------------------------------------------------------------------
  -- I.47 on triangle D-A-B, right-angled at D:
  --
  --   Sq(AB) ~ Sq(DA) + Sq(DB).
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        D A B
        hDAB
        hRightADB with
    ⟨AB0, AB1,
      DA10, DA11,
      DB0, DB1,
      hSqAB,
      hSqDA1,
      hSqDB,
      h47AB⟩

  --------------------------------------------------------------------
  -- I.47 on triangle D-A-C, right-angled at D:
  --
  --   Sq(AC) ~ Sq(DA) + Sq(DC).
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        D A C
        hDAC
        hRightADC with
    ⟨AC0, AC1,
      DA20, DA21,
      DC0, DC1,
      hSqAC,
      hSqDA2,
      hSqDC,
      h47AC⟩

  exact
    ⟨AB0, AB1,
      DA10, DA11,
      DB0, DB1,
      AC0, AC1,
      DA20, DA21,
      DC0, DC1,
      hSqAB,
      hSqDA1,
      hSqDB,
      h47AB,
      hSqAC,
      hSqDA2,
      hSqDC,
      h47AC⟩

/--
Euclid II.13, third incremental package.

Normalize the two independently constructed squares on DA so that both
Pythagorean decompositions use the same concrete square representative.
-/
theorem proposition2_13_pythagorean_package_common_DA
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hBDC : Geo.Between B D C)
    (hADB : Not (PrimCollinear Geo A D B))
    (hRightADB : HilbertRightAngle Geo A D B) :
    exists AB0 AB1 DA0 DA1 DB0 DB1 : Geo.Point,
    exists AC0 AC1 DC0 DC1 : Geo.Point,

      IsSquare Geo A B AB1 AB0 /\
      IsSquare Geo D A DA0 DA1 /\
      IsSquare Geo D B DB1 DB0 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B AB1 AB0)
        (hilbertParallelogramTerm Geo D A DA0 DA1 +
         hilbertParallelogramTerm Geo D B DB1 DB0) /\

      IsSquare Geo A C AC1 AC0 /\
      IsSquare Geo D C DC1 DC0 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A C AC1 AC0)
        (hilbertParallelogramTerm Geo D A DA0 DA1 +
         hilbertParallelogramTerm Geo D C DC1 DC0) := by

  rcases
      proposition2_13_two_pythagoras
        Geo
        A B C D
        hBDC
        hADB
        hRightADB with
    ⟨AB0, AB1,
      DA10, DA11,
      DB0, DB1,
      AC0, AC1,
      DA20, DA21,
      DC0, DC1,
      hSqAB,
      hSqDA1,
      hSqDB,
      h47AB,
      hSqAC,
      hSqDA2,
      hSqDC,
      h47AC⟩

  --------------------------------------------------------------------
  -- The two squares on the same segment DA are equicomplementable.
  --
  -- We orient the transport from the second I.47 square to the first.
  --------------------------------------------------------------------

  have hDA2_DA1 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D A DA20 DA21)
        (hilbertParallelogramTerm Geo D A DA10 DA11) :=
    proposition2_12_same_base_squares_equicomplementable
      Geo
      D A
      DA20 DA21
      DA10 DA11
      hSqDA2
      hSqDA1

  --------------------------------------------------------------------
  -- Keep the DC square fixed while replacing only the DA square.
  --------------------------------------------------------------------

  have hDCrefl :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D C DC1 DC0)
        (hilbertParallelogramTerm Geo D C DC1 DC0) :=
    equicomplementable_refl
      Geo
      (hilbertParallelogramTerm Geo D C DC1 DC0)

  have hSum :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D A DA20 DA21 +
         hilbertParallelogramTerm Geo D C DC1 DC0)
        (hilbertParallelogramTerm Geo D A DA10 DA11 +
         hilbertParallelogramTerm Geo D C DC1 DC0) :=
    i47_aux_equicomplementable_add
      Geo
      hDA2_DA1
      hDCrefl

  have h47AC_common :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A C AC1 AC0)
        (hilbertParallelogramTerm Geo D A DA10 DA11 +
         hilbertParallelogramTerm Geo D C DC1 DC0) :=
    equicomplementable_trans
      Geo
      h47AC
      hSum

  exact
    ⟨AB0, AB1,
      DA10, DA11,
      DB0, DB1,
      AC0, AC1,
      DC0, DC1,
      hSqAB,
      hSqDA1,
      hSqDB,
      h47AB,
      hSqAC,
      hSqDC,
      h47AC_common⟩

/--
Euclid II.13, fourth incremental package.

Specialized adapter for Euclid II.7 in the internal cut configuration

  B-D-C.

With (A,B,C) of II.7 instantiated as (B,C,D), the theorem reads

  Sq(BC) + Sq(DB)
    =
  2 * Rect(BC,BD) + Sq(DC).

The large construction interface is kept local to this adapter so that
later stages of II.13 can use only the resulting scissors identity.
-/
theorem proposition2_13_ii7_internal_cut
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (B C D : Geo.Point)

    --------------------------------------------------------------------
    -- II.7 outer square on BC, cut at D.
    --------------------------------------------------------------------

    (D0 E0 L0 X0 : Geo.Point)
    (hSquareBC : IsSquare Geo B C E0 D0)

    (hBDC : Geo.Between B D C)
    (hD0L0E0 : Geo.Between D0 L0 E0)
    (hD0X0C : Geo.Between D0 X0 C)
    (hDX0L0 : Geo.Between D X0 L0)

    (hII7LeftPar :
      IsParallelogram Geo L0 D0 B D)

    (hII7RightPar :
      IsParallelogram Geo C E0 L0 D)

    --------------------------------------------------------------------
    -- Rect(BC,BD) and Rect(BC,DC).
    --------------------------------------------------------------------

    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)

    (hBC_BD :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 B C B D)

    (hBC_DC :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 B C D C)

    --------------------------------------------------------------------
    -- Left II.3 branch: the square on DB.
    --------------------------------------------------------------------

    (D1 E1 L1 X1 : Geo.Point)

    (hRectLeft :
      IsRectangle Geo C B E1 D1)

    (hBE1_DB :
      Geo.Congruent B E1 D B)

    (hD1L1E1 : Geo.Between D1 L1 E1)
    (hD1X1B : Geo.Between D1 X1 B)
    (hDX1L1 : Geo.Between D X1 L1)

    (hLeftLeftPar :
      IsParallelogram Geo L1 D1 C D)

    (hLeftRightPar :
      IsParallelogram Geo B E1 L1 D)

    (F G : Geo.Point)
    (hSquareDB : IsSquare Geo D B F G)

    --------------------------------------------------------------------
    -- Right II.3 branch: the square on DC.
    --------------------------------------------------------------------

    (D2 E2 L2 X2 : Geo.Point)

    (hRectRight :
      IsRectangle Geo B C E2 D2)

    (hCE2_DC :
      Geo.Congruent C E2 D C)

    (hD2L2E2 : Geo.Between D2 L2 E2)
    (hD2X2C : Geo.Between D2 X2 C)
    (hDX2L2 : Geo.Between D X2 L2)

    (hRightLeftPar :
      IsParallelogram Geo L2 D2 B D)

    (hRightRightPar :
      IsParallelogram Geo C E2 L2 D)

    (H K : Geo.Point)
    (hSquareDC : IsSquare Geo D C H K)

    --------------------------------------------------------------------
    -- Cross rectangle Rect(BD,DC).
    --------------------------------------------------------------------

    (T0 T1 T2 T3 : Geo.Point)

    (hCross :
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 B D D C) :

    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo B C E0 D0 +
       hilbertParallelogramTerm Geo D B F G)
      ((hilbertParallelogramTerm Geo U0 U1 U2 U3 +
        hilbertParallelogramTerm Geo U0 U1 U2 U3) +
       hilbertParallelogramTerm Geo D C H K) := by

  exact
    euclid_proposition_2_7
      Geo
      B C D
      D0 E0 L0 X0
      hSquareBC
      hBDC
      hD0L0E0
      hD0X0C
      hDX0L0
      hII7LeftPar
      hII7RightPar
      U0 U1 U2 U3
      V0 V1 V2 V3
      hBC_BD
      hBC_DC
      D1 E1 L1 X1
      hRectLeft
      hBE1_DB
      hD1L1E1
      hD1X1B
      hDX1L1
      hLeftLeftPar
      hLeftRightPar
      F G
      hSquareDB
      D2 E2 L2 X2
      hRectRight
      hCE2_DC
      hD2L2E2
      hD2X2C
      hDX2L2
      hRightLeftPar
      hRightRightPar
      H K
      hSquareDC
      T0 T1 T2 T3
      hCross

/--
Euclid II.13, fifth incremental package.

Pure scissors bridge.

Assume

  AB ~ DA + DB,
  AC ~ DA + DC,
  BC + DB = (R + R) + DC.

Then

  BC + AB ~ AC + (R + R).

This is precisely the formal Common-Notions step in Euclid II.13:
add the same square DA, substitute the two Pythagorean identities,
and regroup the scissors sums.  No cancellation is used.
-/
theorem proposition2_13_scissors_bridge
    (AB AC BC DA DB DC R : HilbertScissorsTerm Geo)
    (hAB :
      HilbertScissorsEquicomplementable Geo
        AB
        (DA + DB))
    (hAC :
      HilbertScissorsEquicomplementable Geo
        AC
        (DA + DC))
    (hII7 :
      HilbertScissorsEq Geo
        (BC + DB)
        ((R + R) + DC)) :
    HilbertScissorsEquicomplementable Geo
      (BC + AB)
      (AC + (R + R)) := by

  --------------------------------------------------------------------
  -- Add BC to the first Pythagorean identity:
  --
  --   BC + AB ~ BC + (DA + DB).
  --------------------------------------------------------------------

  have hBCrefl :
      HilbertScissorsEquicomplementable Geo BC BC :=
    equicomplementable_refl
      Geo BC

  have hStep1raw :
      HilbertScissorsEquicomplementable Geo
        (BC + AB)
        (BC + (DA + DB)) :=
    equicomplementable_add
      Geo
      hBCrefl
      hAB

  have hReorder1 :
      BC + (DA + DB) =
      DA + (BC + DB) := by
    ac_rfl

  have hStep1 :
      HilbertScissorsEquicomplementable Geo
        (BC + AB)
        (DA + (BC + DB)) := by
    rw [← hReorder1]
    exact hStep1raw

  --------------------------------------------------------------------
  -- Lift II.7 from scissors equality to equicomplementability,
  -- then add the common square DA:
  --
  --   DA + (BC + DB)
  --       ~
  --   DA + ((R + R) + DC).
  --------------------------------------------------------------------

  have hII7eqc :
      HilbertScissorsEquicomplementable Geo
        (BC + DB)
        ((R + R) + DC) :=
    equicomplementable_of_scissorsEq
      Geo
      hII7

  have hDArefl :
      HilbertScissorsEquicomplementable Geo DA DA :=
    equicomplementable_refl
      Geo DA

  have hStep2raw :
      HilbertScissorsEquicomplementable Geo
        (DA + (BC + DB))
        (DA + ((R + R) + DC)) :=
    equicomplementable_add
      Geo
      hDArefl
      hII7eqc

  have hReorder2 :
      DA + ((R + R) + DC) =
      (DA + DC) + (R + R) := by
    ac_rfl

  have hStep2 :
      HilbertScissorsEquicomplementable Geo
        (DA + (BC + DB))
        ((DA + DC) + (R + R)) := by
    rw [← hReorder2]
    exact hStep2raw

  --------------------------------------------------------------------
  -- Replace DA + DC by AC using the second Pythagorean identity:
  --
  --   (DA + DC) + (R + R)
  --       ~
  --   AC + (R + R).
  --------------------------------------------------------------------

  have hACback :
      HilbertScissorsEquicomplementable Geo
        (DA + DC)
        AC :=
    equicomplementable_symm
      Geo
      hAC

  have hRRrefl :
      HilbertScissorsEquicomplementable Geo
        (R + R)
        (R + R) :=
    equicomplementable_refl
      Geo
      (R + R)

  have hStep3 :
      HilbertScissorsEquicomplementable Geo
        ((DA + DC) + (R + R))
        (AC + (R + R)) :=
    equicomplementable_add
      Geo
      hACback
      hRRrefl

  --------------------------------------------------------------------
  -- Chain the three Common-Notions steps.
  --------------------------------------------------------------------

  exact
    equicomplementable_trans
      Geo
      (equicomplementable_trans
        Geo
        hStep1
        hStep2)
      hStep3

/--
An angle AOB is acute when it is strictly smaller than a right angle
with the same first arm OA.
-/
def HilbertAcuteAngle
    [HilbertIncidence Geo]
    (A O B : Geo.Point) : Prop :=
  Exists fun X : Geo.Point =>
    And
      (HilbertRightAngle Geo A O X)
      (HilbertAngleLess Geo A O B A O X)

/--
A source-faithful acute triangle: a nondegenerate triangle whose three
interior angles are acute.
-/
def HilbertAcuteTriangle
    [HilbertIncidence Geo]
    (A B C : Geo.Point) : Prop :=
  Not (PrimCollinear Geo A B C) /\
  HilbertAcuteAngle Geo B A C /\
  HilbertAcuteAngle Geo A B C /\
  HilbertAcuteAngle Geo A C B

/--
An acute angle cannot be a right angle.
-/
theorem proposition2_13_acute_not_right
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B : Geo.Point)
    (hAcute : HilbertAcuteAngle Geo A O B) :
    Not (HilbertRightAngle Geo A O B) := by

  intro hRightAOB

  rcases hAcute with
    ⟨X, hRightAOX, hLessAOB_AOX⟩

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    hLessAOB_AOX.1

  have hAOX :
      Not (PrimCollinear Geo A O X) :=
    hLessAOB_AOX.2.1

  have hRightCong :
      Geo.AngleCongruent
        A O X
        A O B :=
    hilbert_all_right_angles_congruent
      Geo
      A O X
      A O B
      hAOX
      hAOB
      hRightAOX
      hRightAOB

  have hCycle :
      HilbertAngleLess Geo
        A O B
        A O B :=
    hilbert_angleLess_transport_right
      Geo
      A O B
      A O X
      A O B
      hLessAOB_AOX
      hAOB
      hRightCong

  exact
    hilbert_angleLess_irrefl
      Geo
      A O B
      hCycle

/--
Semantic core of Euclid II.13.

If the angles ABC and ACB are acute, then the perpendicular from A to
the carrier BC meets the segment BC internally.

The exclusion of the two external-foot cases is exactly Euclid I.16:

* if D-B-C, then the exterior angle ABC is greater than the right
  angle ADB;
* if B-C-D, then the exterior angle ACB is greater than the right
  angle ADC.

Both conclusions contradict the corresponding acute-angle hypothesis.
-/
theorem proposition2_13_acute_perpendicular_foot_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hAcuteB : HilbertAcuteAngle Geo A B C)
    (hAcuteC : HilbertAcuteAngle Geo A C B) :
    exists D : Geo.Point,
      Geo.Between B D C /\
      HilbertRightAngle Geo A D B := by

  --------------------------------------------------------------------
  -- Basic nondegeneracy permutations.
  --------------------------------------------------------------------

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap
          Geo B A C h)

  have hBCA :
      Not (PrimCollinear Geo B C A) := by
    intro hBCAcol

    have hCAB :
        PrimCollinear Geo C A B :=
      PrimCollinearCycle
        Geo B C A hBCAcol

    have hABCcol :
        PrimCollinear Geo A B C :=
      PrimCollinearCycle
        Geo C A B hCAB

    exact hABC hABCcol

  have hCBA :
      Not (PrimCollinear Geo C B A) := by
    intro hCBAcol
    exact
      hABC
        (PrimCollinearSymm
          Geo C B A hCBAcol)

  have hBC : Ne B C :=
    hilbert_noncollinear_ne_first
      Geo
      B C A
      hBCA

  --------------------------------------------------------------------
  -- I.12: drop the perpendicular from A to the carrier BC.
  --
  -- proposition2_12_perpendicular_foot_exists_full applied to
  -- (B,A,C) gives:
  --
  --   B,D,C collinear,
  --   R,D,B collinear,
  --   R,B,C collinear,
  --   RDA right.
  --------------------------------------------------------------------

  rcases
      proposition2_12_perpendicular_foot_exists_full
        Geo
        B A C
        hBAC with
    ⟨D, R,
      hBDCcol,
      hRDBcol,
      hRBCcol,
      hRD,
      hRDA,
      hRightRDA⟩

  --------------------------------------------------------------------
  -- D cannot coincide with B.
  --
  -- Otherwise the perpendicular at D=B would make ABC a right angle,
  -- contradicting acute ABC.
  --------------------------------------------------------------------

  have hDB : Ne D B := by
    intro hDB_eq
    subst D

    have hRightCBA :
        HilbertRightAngle Geo C B A :=
      proposition2_12_right_angle_collinear_transport
        Geo
        R B C A
        hRD
        hBC.symm
        hRBCcol
        hRDA
        hRightRDA

    have hRightABC :
        HilbertRightAngle Geo A B C :=
      proposition2_12_right_angle_swap
        Geo
        C B A
        hCBA
        hRightCBA

    exact
      (proposition2_13_acute_not_right
        Geo
        A B C
        hAcuteB)
        hRightABC

  --------------------------------------------------------------------
  -- D cannot coincide with C.
  --------------------------------------------------------------------

  have hDC : Ne D C := by
    intro hDC_eq
    subst D

    have hRightBCA :
        HilbertRightAngle Geo B C A :=
      proposition2_12_right_angle_collinear_transport
        Geo
        R C B A
        hRD
        hBC
        hRDBcol
        hRDA
        hRightRDA

    have hRightACB :
        HilbertRightAngle Geo A C B :=
      proposition2_12_right_angle_swap
        Geo
        B C A
        hBCA
        hRightBCA

    exact
      (proposition2_13_acute_not_right
        Geo
        A C B
        hAcuteC)
        hRightACB

  have hBD : Ne B D :=
    hDB.symm

  --------------------------------------------------------------------
  -- Transport RDA along the carrier BC to obtain BDA.
  --------------------------------------------------------------------

  have hBDA :
      Not (PrimCollinear Geo B D A) := by
    intro hBDAcol

    have hRDAcol :
        PrimCollinear Geo R D A :=
      hilbert_primCollinear_trans
        Geo
        R D B A
        hDB
        hRDBcol
        (PrimCollinearSwap
          Geo B D A hBDAcol)

    exact hRDA hRDAcol

  have hRightBDA :
      HilbertRightAngle Geo B D A :=
    proposition2_12_right_angle_collinear_transport
      Geo
      R D B A
      hRD
      hBD
      hRDBcol
      hRDA
      hRightRDA

  have hADB :
      Not (PrimCollinear Geo A D B) := by
    intro hADBcol
    exact
      hBDA
        (PrimCollinearSymm
          Geo A D B hADBcol)

  have hRightADB :
      HilbertRightAngle Geo A D B :=
    proposition2_12_right_angle_swap
      Geo
      B D A
      hBDA
      hRightBDA

  --------------------------------------------------------------------
  -- The same perpendicular gives ADC as a right angle.
  --------------------------------------------------------------------

  have hDBCcol :
      PrimCollinear Geo D B C :=
    PrimCollinearSwap
      Geo B D C hBDCcol

  have hRDCcol :
      PrimCollinear Geo R D C :=
    hilbert_primCollinear_trans
      Geo
      R D B C
      hDB
      hRDBcol
      hDBCcol

  have hCDA :
      Not (PrimCollinear Geo C D A) := by
    intro hCDAcol

    have hDCA :
        PrimCollinear Geo D C A :=
      PrimCollinearSwap
        Geo C D A hCDAcol

    have hRDAcol :
        PrimCollinear Geo R D A :=
      hilbert_primCollinear_trans
        Geo
        R D C A
        hDC
        hRDCcol
        hDCA

    exact hRDA hRDAcol

  have hRightCDA :
      HilbertRightAngle Geo C D A :=
    proposition2_12_right_angle_collinear_transport
      Geo
      R D C A
      hRD
      hDC.symm
      hRDCcol
      hRDA
      hRightRDA

  have hADC :
      Not (PrimCollinear Geo A D C) := by
    intro hADCcol
    exact
      hCDA
        (PrimCollinearSymm
          Geo A D C hADCcol)

  have hRightADC :
      HilbertRightAngle Geo A D C :=
    proposition2_12_right_angle_swap
      Geo
      C D A
      hCDA
      hRightCDA

  --------------------------------------------------------------------
  -- Trichotomy on the collinear triple B,D,C.
  --------------------------------------------------------------------

  rcases
      hilbert_between_trichotomy
        Geo
        B D C
        hBD
        hDC
        hBC
        hBDCcol with
    hBDC | hRest

  --------------------------------------------------------------------
  -- Desired internal-foot case.
  --------------------------------------------------------------------

  · exact
      ⟨D,
        hBDC,
        hRightADB⟩

  rcases hRest with hDBC | hBCD

  --------------------------------------------------------------------
  -- External case D-B-C.
  --
  -- In triangle A-D-B, extend DB through B to C.
  -- I.16 gives
  --
  --   angle ADB < angle ABC.
  --
  -- But ABC is acute, so
  --
  --   angle ABC < a right angle.
  --
  -- Since ADB itself is right, this is impossible.
  --------------------------------------------------------------------

  · have hLessADB_ABC :
        HilbertAngleLess Geo
          A D B
          A B C :=
      euclid_proposition_16_second
        Geo
        A D B C
        hADB
        hDBC

    rcases hAcuteB with
      ⟨XB, hRightABX, hLessABC_ABX⟩

    have hABX :
        Not (PrimCollinear Geo A B XB) :=
      hLessABC_ABX.2.1

    have hCongABX_ADB :
        Geo.AngleCongruent
          A B XB
          A D B :=
      hilbert_all_right_angles_congruent
        Geo
        A B XB
        A D B
        hABX
        hADB
        hRightABX
        hRightADB

    have hLessABC_ADB :
        HilbertAngleLess Geo
          A B C
          A D B :=
      hilbert_angleLess_transport_right
        Geo
        A B C
        A B XB
        A D B
        hLessABC_ABX
        hADB
        hCongABX_ADB

    have hCycle :
        HilbertAngleLess Geo
          A D B
          A D B :=
      hilbert_angleLess_trans
        Geo
        A D B
        A B C
        A D B
        hLessADB_ABC
        hLessABC_ADB

    exact
      False.elim
        (hilbert_angleLess_irrefl
          Geo
          A D B
          hCycle)

  --------------------------------------------------------------------
  -- External case B-C-D.
  --
  -- Reverse it to D-C-B.  In triangle A-D-C, extend DC through C
  -- to B. I.16 gives
  --
  --   angle ADC < angle ACB,
  --
  -- contradicting acute ACB because ADC is right.
  --------------------------------------------------------------------

  · have hDCB :
        Geo.Between D C B :=
      (HilbertOrder.between_incidence
        B C D hBCD).2.2.2.2

    have hLessADC_ACB :
        HilbertAngleLess Geo
          A D C
          A C B :=
      euclid_proposition_16_second
        Geo
        A D C B
        hADC
        hDCB

    rcases hAcuteC with
      ⟨XC, hRightACX, hLessACB_ACX⟩

    have hACX :
        Not (PrimCollinear Geo A C XC) :=
      hLessACB_ACX.2.1

    have hCongACX_ADC :
        Geo.AngleCongruent
          A C XC
          A D C :=
      hilbert_all_right_angles_congruent
        Geo
        A C XC
        A D C
        hACX
        hADC
        hRightACX
        hRightADC

    have hLessACB_ADC :
        HilbertAngleLess Geo
          A C B
          A D C :=
      hilbert_angleLess_transport_right
        Geo
        A C B
        A C XC
        A D C
        hLessACB_ACX
        hADC
        hCongACX_ADC

    have hCycle :
        HilbertAngleLess Geo
          A D C
          A D C :=
      hilbert_angleLess_trans
        Geo
        A D C
        A C B
        A D C
        hLessADC_ACB
        hLessACB_ADC

    exact
      False.elim
        (hilbert_angleLess_irrefl
          Geo
          A D C
          hCycle)

/--
Source-level wrapper: an acute triangle has an internal perpendicular
foot from A to BC.
-/
theorem proposition2_13_acute_triangle_perpendicular_foot_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hAcuteTriangle : HilbertAcuteTriangle Geo A B C) :
    exists D : Geo.Point,
      Geo.Between B D C /\
      HilbertRightAngle Geo A D B := by

  exact
    proposition2_13_acute_perpendicular_foot_between
      Geo
      A B C
      hAcuteTriangle.1
      hAcuteTriangle.2.2.1
      hAcuteTriangle.2.2.2

/--
Existential II.7 block for the internal cut B-D-C.

The square representatives on DB and DC are supplied from outside.
This lets Euclid II.13 reuse exactly the same concrete DB and DC squares
that occur in the two Pythagorean identities.

Everything else required by II.7 is constructed internally:
  * the square on BC,
  * the cut of that square at D,
  * the two contained rectangles,
  * the two II.3 rectangles and their cuts,
  * the cross rectangle Rect(BD,DC).

The result is

  Sq(BC) + Sq(DB)
    =
  2 Rect(BC,BD) + Sq(DC)

at the exact scissors level.
-/
theorem proposition2_13_ii7_exists_with_squares
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (B C D : Geo.Point)
    (hBDC : Geo.Between B D C)

    (DB0 DB1 DC0 DC1 : Geo.Point)
    (hSquareDB : IsSquare Geo D B DB1 DB0)
    (hSquareDC : IsSquare Geo D C DC1 DC0) :

    exists BC0 BC1 : Geo.Point,
    exists T0 T1 T2 T3 : Geo.Point,
      IsSquare Geo B C BC1 BC0 /\
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 B C B D /\
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C BC1 BC0 +
         hilbertParallelogramTerm Geo D B DB1 DB0)
        ((hilbertParallelogramTerm Geo T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo T0 T1 T2 T3) +
         hilbertParallelogramTerm Geo D C DC1 DC0) := by

  --------------------------------------------------------------------
  -- Order data.
  --------------------------------------------------------------------

  have hBDCdata :=
    HilbertOrder.between_incidence
      B D C hBDC

  have hBD : B ≠ D :=
    hBDCdata.1

  have hDC : D ≠ C :=
    hBDCdata.2.1

  have hBC : B ≠ C :=
    hBDCdata.2.2.1

  have hCB : C ≠ B :=
    hBC.symm

  have hDB : D ≠ B :=
    hBD.symm

  have hCDB :
      Geo.Between C D B :=
    hBDCdata.2.2.2.2

  --------------------------------------------------------------------
  -- Square on BC.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_46
        Geo B C hBC with
    ⟨E0, D0, hSquareBC⟩

  --------------------------------------------------------------------
  -- Cut the square on BC at D.
  --------------------------------------------------------------------

  rcases
      proposition2_12_parallelogram_cut_exists
        Geo
        B C D0 E0 D
        hSquareBC.1
        hBDC with
    ⟨L0, X0,
      hD0L0E0,
      hD0X0C,
      hDX0L0,
      hII7LeftPar,
      hII7RightPar⟩

  --------------------------------------------------------------------
  -- Representatives Rect(BC,BD) and Rect(BC,DC).
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        B C
        B D
        hBC with
    ⟨U2, U3, hBC_BD⟩

  rcases
      rectangle_contained_by_exists
        Geo
        B C
        D C
        hBC with
    ⟨V2, V3, hBC_DC⟩

  --------------------------------------------------------------------
  -- Left II.3 rectangle.
  --
  -- Whole side C-B, fixed side D-B, cut at D in C-D-B.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        C B
        D B
        hCB with
    ⟨E1, D1, hLeftContained⟩

  have hRectLeft :
      IsRectangle Geo C B E1 D1 :=
    hLeftContained.1

  have hBE1_DB :
      Geo.Congruent B E1 D B :=
    hLeftContained.2.2

  rcases
      proposition2_12_parallelogram_cut_exists
        Geo
        C B D1 E1 D
        hRectLeft.1
        hCDB with
    ⟨L1, X1,
      hD1L1E1,
      hD1X1B,
      hDX1L1,
      hLeftLeftPar,
      hLeftRightPar⟩

  --------------------------------------------------------------------
  -- Right II.3 rectangle.
  --
  -- Whole side B-C, fixed side D-C, cut at D in B-D-C.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        B C
        D C
        hBC with
    ⟨E2, D2, hRightContained⟩

  have hRectRight :
      IsRectangle Geo B C E2 D2 :=
    hRightContained.1

  have hCE2_DC :
      Geo.Congruent C E2 D C :=
    hRightContained.2.2

  rcases
      proposition2_12_parallelogram_cut_exists
        Geo
        B C D2 E2 D
        hRectRight.1
        hBDC with
    ⟨L2, X2,
      hD2L2E2,
      hD2X2C,
      hDX2L2,
      hRightLeftPar,
      hRightRightPar⟩

  --------------------------------------------------------------------
  -- Cross rectangle Rect(BD,DC).
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        B D
        D C
        hBD with
    ⟨T2, T3, hCross⟩

  --------------------------------------------------------------------
  -- Apply the specialized II.7 adapter.
  --------------------------------------------------------------------

  have hII7 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C E0 D0 +
         hilbertParallelogramTerm Geo D B DB1 DB0)
        ((hilbertParallelogramTerm Geo B C U2 U3 +
          hilbertParallelogramTerm Geo B C U2 U3) +
         hilbertParallelogramTerm Geo D C DC1 DC0) :=
    proposition2_13_ii7_internal_cut
      Geo
      B C D
      D0 E0 L0 X0
      hSquareBC
      hBDC
      hD0L0E0
      hD0X0C
      hDX0L0
      hII7LeftPar
      hII7RightPar
      B C U2 U3
      B C V2 V3
      hBC_BD
      hBC_DC
      D1 E1 L1 X1
      hRectLeft
      hBE1_DB
      hD1L1E1
      hD1X1B
      hDX1L1
      hLeftLeftPar
      hLeftRightPar
      DB1 DB0
      hSquareDB
      D2 E2 L2 X2
      hRectRight
      hCE2_DC
      hD2L2E2
      hD2X2C
      hDX2L2
      hRightLeftPar
      hRightRightPar
      DC1 DC0
      hSquareDC
      B D T2 T3
      hCross

  exact
    ⟨D0, E0,
      B, C, U2, U3,
      hSquareBC,
      hBC_BD,
      hII7⟩


/--
Euclid II.13, source-faithful acute-triangle form.

For an acute triangle ABC, construct the perpendicular AD to BC.
Its foot D lies internally on BC.  Then construct the square on BC and
a representative R of the rectangle contained by BC and BD.

The conclusion is the Euclidean II.13 identity

  Sq(BC) + Sq(BA)
    ~ec
  Sq(AC) + 2 Rect(BC,BD).

The proof is entirely synthetic:
  * I.12 + I.16 for the internal perpendicular foot,
  * I.47 twice,
  * II.7 on B-D-C,
  * Common-Notions substitution in the scissors calculus.
-/
theorem euclid_proposition_2_13
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C : Geo.Point)
    (hAcuteTriangle : HilbertAcuteTriangle Geo A B C) :

    exists D : Geo.Point,
    exists AB0 AB1 AC0 AC1 BC0 BC1 : Geo.Point,
    exists T0 T1 T2 T3 : Geo.Point,

      Geo.Between B D C /\
      HilbertRightAngle Geo A D B /\

      IsSquare Geo A B AB1 AB0 /\
      IsSquare Geo A C AC1 AC0 /\
      IsSquare Geo B C BC1 BC0 /\

      IsRectangleContainedBy Geo
        T0 T1 T2 T3 B C B D /\

      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C BC1 BC0 +
         hilbertParallelogramTerm Geo A B AB1 AB0)
        (hilbertParallelogramTerm Geo A C AC1 AC0 +
         (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo T0 T1 T2 T3)) := by

  --------------------------------------------------------------------
  -- Source geometry: the perpendicular foot is internal.
  --------------------------------------------------------------------

  rcases
      proposition2_13_acute_triangle_perpendicular_foot_between
        Geo
        A B C
        hAcuteTriangle with
    ⟨D, hBDC, hRightADB⟩

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hAcuteTriangle.1

  have hBDCdata :=
    HilbertOrder.between_incidence
      B D C hBDC

  have hBD : B ≠ D :=
    hBDCdata.1

  have hDC : D ≠ C :=
    hBDCdata.2.1

  have hBDCcol :
      PrimCollinear Geo B D C :=
    hBDCdata.2.2.2.1

  --------------------------------------------------------------------
  -- A,D,B is noncollinear because otherwise A,B,C would be collinear.
  --------------------------------------------------------------------

  have hADB :
      Not (PrimCollinear Geo A D B) := by
    intro hADBcol

    have hDAB :
        PrimCollinear Geo D A B :=
      PrimCollinearSwap
        Geo A D B hADBcol

    have hABD :
        PrimCollinear Geo A B D :=
      PrimCollinearCycle
        Geo D A B hDAB

    have hABCcol :
        PrimCollinear Geo A B C :=
      hilbert_primCollinear_trans
        Geo
        A B D C
        hBD
        hABD
        hBDCcol

    exact hABC hABCcol

  --------------------------------------------------------------------
  -- I.47 twice, normalized to one common square on DA.
  --------------------------------------------------------------------

  rcases
      proposition2_13_pythagorean_package_common_DA
        Geo
        A B C D
        hBDC
        hADB
        hRightADB with
    ⟨AB0, AB1,
      DA0, DA1,
      DB0, DB1,
      AC0, AC1,
      DC0, DC1,
      hSqAB,
      hSqDA,
      hSqDB,
      h47AB,
      hSqAC,
      hSqDC,
      h47AC⟩

  --------------------------------------------------------------------
  -- Construct the complete II.7 block, reusing the I.47 squares on
  -- DB and DC literally.
  --------------------------------------------------------------------

  rcases
      proposition2_13_ii7_exists_with_squares
        Geo
        B C D
        hBDC
        DB0 DB1
        DC0 DC1
        hSqDB
        hSqDC with
    ⟨BC0, BC1,
      T0, T1, T2, T3,
      hSqBC,
      hRect,
      hII7⟩

  --------------------------------------------------------------------
  -- Final Euclidean substitution.
  --------------------------------------------------------------------

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C BC1 BC0 +
         hilbertParallelogramTerm Geo A B AB1 AB0)
        (hilbertParallelogramTerm Geo A C AC1 AC0 +
         (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo T0 T1 T2 T3)) :=
    proposition2_13_scissors_bridge
      Geo
      (hilbertParallelogramTerm Geo A B AB1 AB0)
      (hilbertParallelogramTerm Geo A C AC1 AC0)
      (hilbertParallelogramTerm Geo B C BC1 BC0)
      (hilbertParallelogramTerm Geo D A DA0 DA1)
      (hilbertParallelogramTerm Geo D B DB1 DB0)
      (hilbertParallelogramTerm Geo D C DC1 DC0)
      (hilbertParallelogramTerm Geo T0 T1 T2 T3)
      h47AB
      h47AC
      hII7

  exact
    ⟨D,
      AB0, AB1,
      AC0, AC1,
      BC0, BC1,
      T0, T1, T2, T3,
      hBDC,
      hRightADB,
      hSqAB,
      hSqAC,
      hSqBC,
      hRect,
      hFinal⟩

end Geometry

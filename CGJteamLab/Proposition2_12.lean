import CGJteamLab.HilbertRightAngle
import CGJteamLab.Proposition12
import CGJteamLab.Proposition16
import CGJteamLab.Proposition47
import CGJteamLab.HilbertSquareTransport
import CGJteamLab.Proposition2_4

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
A Hilbert angle AOB is obtuse when a right angle with the same
first arm AO is strictly smaller than AOB.
-/
def HilbertObtuseAngle
    [HilbertIncidence Geo]
    (A O B : Geo.Point) : Prop :=
  Exists fun X : Geo.Point =>
    And
      (HilbertRightAngle Geo A O X)
      (HilbertAngleLess Geo A O X A O B)

/--
An obtuse angle cannot be a right angle.
-/
theorem proposition2_12_obtuse_not_right
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B : Geo.Point)
    (hObtuse : HilbertObtuseAngle Geo A O B) :
    Not (HilbertRightAngle Geo A O B) := by

  intro hRightAOB

  cases hObtuse with
  | intro X hData =>

    have hRightAOX :
        HilbertRightAngle Geo A O X :=
      hData.1

    have hLess :
        HilbertAngleLess Geo
          A O X
          A O B :=
      hData.2

    have hAOX :
        Not (PrimCollinear Geo A O X) :=
      hLess.1

    have hAOB :
        Not (PrimCollinear Geo A O B) :=
      hLess.2.1

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

    have hRightCongSymm :
        Geo.AngleCongruent
          A O B
          A O X :=
      Geo.angle_congruent_symmetry
        A O X
        A O B
        hRightCong

    have hCycle :
        HilbertAngleLess Geo
          A O X
          A O X :=
      hilbert_angleLess_transport_right
        Geo
        A O X
        A O B
        A O X
        hLess
        hAOX
        hRightCongSymm

    exact
      hilbert_angleLess_irrefl
        Geo
        A O X
        hCycle

/--
Transport a right angle along its carrier line.

If R,D,A are collinear, R and A are distinct from D, and RDB is a
nondegenerate right angle, then ADB is also a right angle.
-/
theorem proposition2_12_right_angle_collinear_transport
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (R D A B : Geo.Point)
    (hRD : Ne R D)
    (hAD : Ne A D)
    (hRDA : PrimCollinear Geo R D A)
    (hRDB : Not (PrimCollinear Geo R D B))
    (hRight : HilbertRightAngle Geo R D B) :
    HilbertRightAngle Geo A D B := by

  have hADB :
      Not (PrimCollinear Geo A D B) := by
    intro hADBcol

    have hDAB :
        PrimCollinear Geo D A B :=
      PrimCollinearSwap
        Geo A D B hADBcol

    have hRDBcol :
        PrimCollinear Geo R D B :=
      hilbert_primCollinear_trans
        Geo
        R D A B
        hAD.symm
        hRDA
        hDAB

    exact hRDB hRDBcol

  by_cases hRA : R = A

  · subst A
    exact hRight

  have hSameRayCase :
      HilbertSameRay Geo D R A ->
      HilbertRightAngle Geo A D B := by
    intro hRay

    have hAngle :
        Geo.Angle R D B =
        Geo.Angle A D B :=
      hilbert_angle_eq_of_sameRay_first
        Geo D R A B hRay

    have hRefl :
        Geo.AngleCongruent
          R D B
          R D B :=
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo)
        R D B
        hRDB

    have hCong :
        Geo.AngleCongruent
          R D B
          A D B := by
      unfold Geometry.Geo.AngleCongruent
        at hRefl
      unfold Geometry.Geo.AngleCongruent
      rw [← hAngle]
      exact hRefl

    exact
      hilbert_right_angle_transport
        Geo
        R D B
        A D B
        hRDB
        hADB
        hRight
        hCong

  rcases
      hilbert_between_trichotomy
        Geo
        R D A
        hRD
        hAD.symm
        hRA
        hRDA with
    hRDA_between | hRest

  · have hCong0 :
        Geo.AngleCongruent
          R D B
          B D A :=
      hilbert_right_angle_opposite_extension
        Geo
        R D B A
        hRDB
        hRight
        hRDA_between

    have hCong :
        Geo.AngleCongruent
          R D B
          A D B := by
      unfold Geometry.Geo.AngleCongruent
        at hCong0
      unfold Geometry.Geo.AngleCongruent
      rw [Geometry.Geo.angle_swap Geo B D A]
        at hCong0
      exact hCong0

    exact
      hilbert_right_angle_transport
        Geo
        R D B
        A D B
        hRDB
        hADB
        hRight
        hCong

  · rcases hRest with hDRA | hRAD

    · have hRay :
          HilbertSameRay Geo D R A :=
        hilbert_sameRay_of_between
          Geo D R A hDRA

      exact hSameRayCase hRay

    · have hDAR :
          Geo.Between D A R :=
        (HilbertOrder.between_incidence
          R A D hRAD).2.2.2.2

      have hRayAR :
          HilbertSameRay Geo D A R :=
        hilbert_sameRay_of_between
          Geo D A R hDAR

      have hRayRA :
          HilbertSameRay Geo D R A :=
        hilbert_sameRay_symm
          Geo D A R hRayAR

      exact hSameRayCase hRayRA

/--
Usable perpendicular-foot form of Euclid I.12.

For a nondegenerate triangle ABC, construct the foot D from B to the
carrier of AC, together with a carrier point R witnessing the right
angle RDB.
-/
theorem proposition2_12_perpendicular_foot_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    exists D R : Geo.Point,
      PrimCollinear Geo A D C /\
      PrimCollinear Geo R D A /\
      Ne R D /\
      Not (PrimCollinear Geo R D B) /\
      HilbertRightAngle Geo R D B := by

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact hABC
      (PrimCollinearRotate Geo A C B h)

  have hAC : Ne A C :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  rcases
      HilbertPlaneIncidence.line_through
        A C hAC with
    ⟨base, hAbase, hCbase⟩

  have hBbase :
      Not (HilbertIncidence.OnLine B base) := by
    intro hBbase
    exact hABC
      ⟨base, hAbase, hBbase, hCbase⟩

  rcases
      euclid_proposition_12
        Geo
        A C B
        base
        hAC
        hAbase
        hCbase
        hBbase with
    ⟨D, R, hDbase, hRbase, hRight⟩

  have hRD : Ne R D := by
    rcases hRight with
      ⟨X, hRDX, hCong⟩
    exact
      (HilbertOrder.between_incidence
        R D X hRDX).1

  have hRDB :
      Not (PrimCollinear Geo R D B) :=
    hilbert_not_collinear_of_off_line
      Geo
      R D B
      base
      hRD
      hRbase
      hDbase
      hBbase

  have hADC :
      PrimCollinear Geo A D C :=
    ⟨base, hAbase, hDbase, hCbase⟩

  have hRDA :
      PrimCollinear Geo R D A :=
    ⟨base, hRbase, hDbase, hAbase⟩

  exact
    ⟨D, R,
      hADC,
      hRDA,
      hRD,
      hRDB,
      hRight⟩


/--
Swap the arms of a nondegenerate right angle.
-/
theorem proposition2_12_right_angle_swap
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo B O A := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact hAOB
      (PrimCollinearSymm Geo B O A h)

  have hRefl :
      Geo.AngleCongruent
        A O B
        A O B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A O B
      hAOB

  have hCong :
      Geo.AngleCongruent
        A O B
        B O A := by
    unfold Geometry.Geo.AngleCongruent at hRefl
    unfold Geometry.Geo.AngleCongruent
    rw [Geometry.Geo.angle_swap Geo B O A]
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
Full incidence form of the perpendicular foot construction.
-/
theorem proposition2_12_perpendicular_foot_exists_full
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    exists D R : Geo.Point,
      PrimCollinear Geo A D C /\
      PrimCollinear Geo R D A /\
      PrimCollinear Geo R A C /\
      Ne R D /\
      Not (PrimCollinear Geo R D B) /\
      HilbertRightAngle Geo R D B := by

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact hABC
      (PrimCollinearRotate Geo A C B h)

  have hAC : Ne A C :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  rcases
      HilbertPlaneIncidence.line_through
        A C hAC with
    ⟨base, hAbase, hCbase⟩

  have hBbase :
      Not (HilbertIncidence.OnLine B base) := by
    intro hBbase
    exact hABC
      ⟨base, hAbase, hBbase, hCbase⟩

  rcases
      euclid_proposition_12
        Geo
        A C B
        base
        hAC
        hAbase
        hCbase
        hBbase with
    ⟨D, R, hDbase, hRbase, hRight⟩

  have hRD : Ne R D := by
    rcases hRight with
      ⟨X, hRDX, hCong⟩
    exact
      (HilbertOrder.between_incidence
        R D X hRDX).1

  have hRDB :
      Not (PrimCollinear Geo R D B) :=
    hilbert_not_collinear_of_off_line
      Geo
      R D B
      base
      hRD
      hRbase
      hDbase
      hBbase

  have hADC :
      PrimCollinear Geo A D C :=
    ⟨base, hAbase, hDbase, hCbase⟩

  have hRDA :
      PrimCollinear Geo R D A :=
    ⟨base, hRbase, hDbase, hAbase⟩

  have hRAC :
      PrimCollinear Geo R A C :=
    ⟨base, hRbase, hAbase, hCbase⟩

  exact
    ⟨D, R,
      hADC,
      hRDA,
      hRAC,
      hRD,
      hRDB,
      hRight⟩

/--
The geometric core of Euclid II.12.

If BAC is obtuse and D is the perpendicular foot from B to the carrier
of AC, then D lies beyond A, i.e. D-A-C.
-/
theorem proposition2_12_obtuse_perpendicular_foot_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hObtuse : HilbertObtuseAngle Geo B A C) :
    exists D : Geo.Point,
      Geo.Between D A C /\
      HilbertRightAngle Geo A D B := by

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact hABC
      (PrimCollinearSwap Geo B A C h)

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact hABC
      (PrimCollinearRotate Geo A C B h)

  have hAC : Ne A C :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  rcases hObtuse with
    ⟨X, hRightBAX, hLessBAX_BAC⟩

  have hBAX :
      Not (PrimCollinear Geo B A X) :=
    hLessBAX_BAC.1

  rcases
      proposition2_12_perpendicular_foot_exists_full
        Geo A B C hABC with
    ⟨D, R,
      hADC,
      hRDA,
      hRAC,
      hRD,
      hRDB,
      hRightRDB⟩

  have hAD : Ne A D := by
    intro hAD_eq
    subst D

    have hCAB :
        Not (PrimCollinear Geo C A B) := by
      intro h
      exact hABC
        (PrimCollinearCycle Geo C A B h)

    have hRightCAB :
        HilbertRightAngle Geo C A B :=
      proposition2_12_right_angle_collinear_transport
        Geo
        R A C B
        hRD
        hAC.symm
        hRAC
        hRDB
        hRightRDB

    have hRightBAC :
        HilbertRightAngle Geo B A C :=
      proposition2_12_right_angle_swap
        Geo
        C A B
        hCAB
        hRightCAB

    exact
      (proposition2_12_obtuse_not_right
        Geo
        B A C
        ⟨X, hRightBAX, hLessBAX_BAC⟩)
        hRightBAC

  have hRightADB :
      HilbertRightAngle Geo A D B :=
    proposition2_12_right_angle_collinear_transport
      Geo
      R D A B
      hRD
      hAD
      hRDA
      hRDB
      hRightRDB

  have hNoSameRay :
      Not (HilbertSameRay Geo A D C) := by
    intro hRayADC

    have hADCcol :
        PrimCollinear Geo A D C :=
      hRayADC.2.2.1

    have hBAD :
        Not (PrimCollinear Geo B A D) := by
      intro hBADcol

      have hDCA :
          PrimCollinear Geo D C A :=
        PrimCollinearCycle
          Geo A D C hADCcol

      have hCAD :
          PrimCollinear Geo C A D :=
        PrimCollinearCycle
          Geo D C A hDCA

      have hADBcol :
          PrimCollinear Geo A D B :=
        PrimCollinearCycle
          Geo B A D hBADcol

      have hCABcol :
          PrimCollinear Geo C A B :=
        hilbert_primCollinear_trans
          Geo
          C A D B
          hAD
          hCAD
          hADBcol

      exact hABC
        (PrimCollinearCycle Geo C A B hCABcol)

    have hADB :
        Not (PrimCollinear Geo A D B) := by
      intro h
      have hDBA :
          PrimCollinear Geo D B A :=
        PrimCollinearCycle
          Geo A D B h

      have hBAD' :
          PrimCollinear Geo B A D :=
        PrimCollinearCycle
          Geo D B A hDBA

      exact hBAD hBAD'

    rcases
        HilbertOrder.between_extension
          A D hAD with
      ⟨E, hADE⟩

    have hLessBAD_BDE :
        HilbertAngleLess Geo
          B A D
          B D E :=
      euclid_proposition_16_second
        Geo
        B A D E
        hBAD
        hADE

    have hBDE :
        Not (PrimCollinear Geo B D E) :=
      hLessBAD_BDE.2.1

    have hAngleBAD_BAC :
        Geo.Angle B A D =
        Geo.Angle B A C :=
      hilbert_angle_eq_of_sameRay_second
        Geo
        A B D C
        hRayADC

    have hReflBAC :
        Geo.AngleCongruent
          B A C
          B A C :=
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo)
        B A C
        hBAC

    have hCongBAC_BAD :
        Geo.AngleCongruent
          B A C
          B A D := by
      unfold Geometry.Geo.AngleCongruent
        at hReflBAC
      unfold Geometry.Geo.AngleCongruent
      rw [hAngleBAD_BAC]
      exact hReflBAC

    have hLessBAC_BDE :
        HilbertAngleLess Geo
          B A C
          B D E :=
      hilbert_angleLess_transport_left
        Geo
        B A D
        B A C
        B D E
        hLessBAD_BDE
        hBAC
        hCongBAC_BAD

    have hAngleADB_BDE :
        Geo.AngleCongruent
          A D B
          B D E :=
      hilbert_right_angle_opposite_extension
        Geo
        A D B E
        hADB
        hRightADB
        hADE

    have hRightBDE :
        HilbertRightAngle Geo B D E :=
      hilbert_right_angle_transport
        Geo
        A D B
        B D E
        hADB
        hBDE
        hRightADB
        hAngleADB_BDE

    have hCongBDE_BAX :
        Geo.AngleCongruent
          B D E
          B A X :=
      hilbert_all_right_angles_congruent
        Geo
        B D E
        B A X
        hBDE
        hBAX
        hRightBDE
        hRightBAX

    have hLessBAC_BAX :
        HilbertAngleLess Geo
          B A C
          B A X :=
      hilbert_angleLess_transport_right
        Geo
        B A C
        B D E
        B A X
        hLessBAC_BDE
        hBAX
        hCongBDE_BAX

    have hCycle :
        HilbertAngleLess Geo
          B A X
          B A X :=
      hilbert_angleLess_trans
        Geo
        B A X
        B A C
        B A X
        hLessBAX_BAC
        hLessBAC_BAX

    exact
      hilbert_angleLess_irrefl
        Geo
        B A X
        hCycle

  have hDC : Ne D C := by
    intro hDC_eq
    subst D

    have hRayACC :
        HilbertSameRay Geo A C C :=
      hilbert_sameRay_refl
        Geo A C hAC.symm

    exact hNoSameRay hRayACC

  rcases
      hilbert_between_trichotomy
        Geo
        A D C
        hAD
        hDC
        hAC
        hADC with
    hADC_between | hRest

  · have hRayADC :
        HilbertSameRay Geo A D C :=
      hilbert_sameRay_of_between
        Geo A D C hADC_between

    exact False.elim
      (hNoSameRay hRayADC)

  · rcases hRest with hDAC | hACD

    · exact
        ⟨D,
          hDAC,
          hRightADB⟩

    · have hRayACD :
          HilbertSameRay Geo A C D :=
        hilbert_sameRay_of_between
          Geo A C D hACD

      have hRayADC :
          HilbertSameRay Geo A D C :=
        hilbert_sameRay_symm
          Geo A C D hRayACD

      exact False.elim
        (hNoSameRay hRayADC)

/--
Pythagorean package for Euclid II.12.

For an obtuse triangle ABC, choose the perpendicular foot D on the
extension of AC beyond A. Then both triangles DAB and DCB are right at D,
and Euclid I.47 supplies the two identities

  Square(AB) ~ec Square(DA) + Square(DB),
  Square(CB) ~ec Square(DC) + Square(DB).

The two occurrences of Square(DB) are independent representatives and
will be identified later by square transport.
-/
theorem proposition2_12_pythagorean_package
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hObtuse : HilbertObtuseAngle Geo B A C) :
    exists D : Geo.Point,
    exists AB0 AB1 DA0 DA1 DB10 DB11 : Geo.Point,
    exists CB0 CB1 DC0 DC1 DB20 DB21 : Geo.Point,
      Geo.Between D A C /\
      HilbertRightAngle Geo A D B /\
      HilbertRightAngle Geo C D B /\

      IsSquare Geo A B AB1 AB0 /\
      IsSquare Geo D A DA0 DA1 /\
      IsSquare Geo D B DB11 DB10 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B AB1 AB0)
        (hilbertParallelogramTerm Geo D A DA0 DA1 +
         hilbertParallelogramTerm Geo D B DB11 DB10) /\

      IsSquare Geo C B CB1 CB0 /\
      IsSquare Geo D C DC0 DC1 /\
      IsSquare Geo D B DB21 DB20 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo C B CB1 CB0)
        (hilbertParallelogramTerm Geo D C DC0 DC1 +
         hilbertParallelogramTerm Geo D B DB21 DB20) := by

  --------------------------------------------------------------------
  -- Geometric core: the perpendicular foot lies beyond A.
  --------------------------------------------------------------------

  rcases
      proposition2_12_obtuse_perpendicular_foot_between
        Geo
        A B C
        hABC
        hObtuse with
    ⟨D, hDAC, hRightADB⟩

  have hDACdata :=
    HilbertOrder.between_incidence
      D A C hDAC

  have hDA : Ne D A :=
    hDACdata.1

  have hAC : Ne A C :=
    hDACdata.2.1

  have hDC : Ne D C :=
    hDACdata.2.2.1

  have hDACcol :
      PrimCollinear Geo D A C :=
    hDACdata.2.2.2.1

  --------------------------------------------------------------------
  -- Triangle DAB is nondegenerate.
  --------------------------------------------------------------------

  have hDAB :
      Not (PrimCollinear Geo D A B) := by
    intro hDABcol

    have hCAD :
        PrimCollinear Geo C A D :=
      PrimCollinearSymm
        Geo D A C hDACcol

    have hADB :
        PrimCollinear Geo A D B :=
      PrimCollinearSwap
        Geo D A B hDABcol

    have hCAB :
        PrimCollinear Geo C A B :=
      hilbert_primCollinear_trans
        Geo
        C A D B
        hDA.symm
        hCAD
        hADB

    exact hABC
      (PrimCollinearCycle
        Geo C A B hCAB)

  --------------------------------------------------------------------
  -- Triangle DCB is nondegenerate.
  --------------------------------------------------------------------

  have hDCB :
      Not (PrimCollinear Geo D C B) := by
    intro hDCBcol

    have hADC :
        PrimCollinear Geo A D C := by
      rcases hDACcol with
        ⟨base, hDbase, hAbase, hCbase⟩
      exact
        ⟨base, hAbase, hDbase, hCbase⟩

    have hADB :
        PrimCollinear Geo A D B :=
      hilbert_primCollinear_trans
        Geo
        A D C B
        hDC
        hADC
        hDCBcol

    have hBAD :
        PrimCollinear Geo B A D :=
      PrimCollinearSymm
        Geo D A B
        (PrimCollinearSwap
          Geo A D B hADB)

    have hBAC :
        PrimCollinear Geo B A C :=
      hilbert_primCollinear_trans
        Geo
        B A D C
        hDA.symm
        hBAD
        hADC

    exact hABC
      (PrimCollinearSwap
        Geo B A C hBAC)

  --------------------------------------------------------------------
  -- Transport the right angle from ADB to CDB.
  --
  -- D-A-C means rays DA and DC coincide.
  --------------------------------------------------------------------

  have hRayDAC :
      HilbertSameRay Geo D A C :=
    hilbert_sameRay_of_between
      Geo D A C hDAC

  have hADBnc :
      Not (PrimCollinear Geo A D B) := by
    intro h
    exact hDAB
      (PrimCollinearSwap
        Geo A D B h)

  have hCDBnc :
      Not (PrimCollinear Geo C D B) := by
    intro h
    exact hDCB
      (PrimCollinearSwap
        Geo C D B h)

  have hAngleADB_CDB :
      Geo.Angle A D B =
      Geo.Angle C D B :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      D A C B
      hRayDAC

  have hReflADB :
      Geo.AngleCongruent
        A D B
        A D B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A D B
      hADBnc

  have hCongADB_CDB :
      Geo.AngleCongruent
        A D B
        C D B := by
    unfold Geometry.Geo.AngleCongruent
      at hReflADB
    unfold Geometry.Geo.AngleCongruent
    rw [← hAngleADB_CDB]
    exact hReflADB

  have hRightCDB :
      HilbertRightAngle Geo C D B :=
    hilbert_right_angle_transport
      Geo
      A D B
      C D B
      hADBnc
      hCDBnc
      hRightADB
      hCongADB_CDB

  --------------------------------------------------------------------
  -- I.47 in triangle DAB:
  --
  --   Square(AB) ~ec Square(DA) + Square(DB).
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        D A B
        hDAB
        hRightADB with
    ⟨AB0, AB1,
      DA0, DA1,
      DB10, DB11,
      hSqAB,
      hSqDA,
      hSqDB1,
      h47AB⟩

  --------------------------------------------------------------------
  -- I.47 in triangle DCB:
  --
  --   Square(CB) ~ec Square(DC) + Square(DB).
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        D C B
        hDCB
        hRightCDB with
    ⟨CB0, CB1,
      DC0, DC1,
      DB20, DB21,
      hSqCB,
      hSqDC,
      hSqDB2,
      h47CB⟩

  exact
    ⟨D,
      AB0, AB1,
      DA0, DA1,
      DB10, DB11,
      CB0, CB1,
      DC0, DC1,
      DB20, DB21,
      hDAC,
      hRightADB,
      hRightCDB,
      hSqAB,
      hSqDA,
      hSqDB1,
      h47AB,
      hSqCB,
      hSqDC,
      hSqDB2,
      h47CB⟩

/--
Two square representatives erected on the same segment DB are
equicomplementable.
-/
theorem proposition2_12_same_base_squares_equicomplementable
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (D B X0 X1 Y0 Y1 : Geo.Point)
    (hSquareX : IsSquare Geo D B X0 X1)
    (hSquareY : IsSquare Geo D B Y0 Y1) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo D B X0 X1)
      (hilbertParallelogramTerm Geo D B Y0 Y1) := by

  have hDB_BX0 :
      Geo.Congruent D B B X0 :=
    hSquareX.2.1

  have hBX0_DB :
      Geo.Congruent B X0 D B :=
    hilbert_congruent_symmetry
      Geo D B B X0 hDB_BX0

  have hDB_DB :
      Geo.Congruent D B D B :=
    hilbert_congruent_transitivity
      Geo
      D B
      B X0
      D B
      hDB_BX0
      hBX0_DB

  exact
    hilbert_square_transport
      Geo
      D B X0 X1
      D B Y0 Y1
      hSquareX
      hSquareY
      hDB_DB

/--
Normalize the second Pythagorean identity so that both I.47 identities
use the same concrete square representative on DB.
-/
theorem proposition2_12_normalize_second_pythagoras_DB
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (D C B : Geo.Point)
    (DC0 DC1 DB10 DB11 DB20 DB21 CB0 CB1 : Geo.Point)
    (hSqDB1 : IsSquare Geo D B DB11 DB10)
    (hSqDB2 : IsSquare Geo D B DB21 DB20)
    (h47CB :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo C B CB1 CB0)
        (hilbertParallelogramTerm Geo D C DC0 DC1 +
         hilbertParallelogramTerm Geo D B DB21 DB20)) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo C B CB1 CB0)
      (hilbertParallelogramTerm Geo D C DC0 DC1 +
       hilbertParallelogramTerm Geo D B DB11 DB10) := by

  have hDB2_DB1 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D B DB21 DB20)
        (hilbertParallelogramTerm Geo D B DB11 DB10) :=
    proposition2_12_same_base_squares_equicomplementable
      Geo
      D B
      DB21 DB20
      DB11 DB10
      hSqDB2
      hSqDB1

  have hDC_refl :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D C DC0 DC1)
        (hilbertParallelogramTerm Geo D C DC0 DC1) :=
    equicomplementable_refl
      Geo
      (hilbertParallelogramTerm Geo D C DC0 DC1)

  have hSum :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D C DC0 DC1 +
         hilbertParallelogramTerm Geo D B DB21 DB20)
        (hilbertParallelogramTerm Geo D C DC0 DC1 +
         hilbertParallelogramTerm Geo D B DB11 DB10) :=
    i47_aux_equicomplementable_add
      Geo
      hDC_refl
      hDB2_DB1

  exact
    equicomplementable_trans
      Geo
      h47CB
      hSum

/--
Pythagorean package for II.12 with one common concrete square on DB.

The output now has exactly the form needed for the final Euclid-II
substitution step:

  Square(AB) ~ec Square(DA) + Square(DB),
  Square(CB) ~ec Square(DC) + Square(DB),

with the same DB term in both formulas.
-/
theorem proposition2_12_pythagorean_package_common_DB
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hObtuse : HilbertObtuseAngle Geo B A C) :
    exists D : Geo.Point,
    exists AB0 AB1 DA0 DA1 DB0 DB1 : Geo.Point,
    exists CB0 CB1 DC0 DC1 : Geo.Point,
      Geo.Between D A C /\
      HilbertRightAngle Geo A D B /\
      HilbertRightAngle Geo C D B /\

      IsSquare Geo A B AB1 AB0 /\
      IsSquare Geo D A DA0 DA1 /\
      IsSquare Geo D B DB1 DB0 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B AB1 AB0)
        (hilbertParallelogramTerm Geo D A DA0 DA1 +
         hilbertParallelogramTerm Geo D B DB1 DB0) /\

      IsSquare Geo C B CB1 CB0 /\
      IsSquare Geo D C DC0 DC1 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo C B CB1 CB0)
        (hilbertParallelogramTerm Geo D C DC0 DC1 +
         hilbertParallelogramTerm Geo D B DB1 DB0) := by

  rcases
      proposition2_12_pythagorean_package
        Geo
        A B C
        hABC
        hObtuse with
    ⟨D,
      AB0, AB1,
      DA0, DA1,
      DB10, DB11,
      CB0, CB1,
      DC0, DC1,
      DB20, DB21,
      hDAC,
      hRightADB,
      hRightCDB,
      hSqAB,
      hSqDA,
      hSqDB1,
      h47AB,
      hSqCB,
      hSqDC,
      hSqDB2,
      h47CB⟩

  have h47CB_common :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo C B CB1 CB0)
        (hilbertParallelogramTerm Geo D C DC0 DC1 +
         hilbertParallelogramTerm Geo D B DB11 DB10) :=
    proposition2_12_normalize_second_pythagoras_DB
      Geo
      D C B
      DC0 DC1
      DB10 DB11
      DB20 DB21
      CB0 CB1
      hSqDB1
      hSqDB2
      h47CB

  exact
    ⟨D,
      AB0, AB1,
      DA0, DA1,
      DB10, DB11,
      CB0, CB1,
      DC0, DC1,
      hDAC,
      hRightADB,
      hRightCDB,
      hSqAB,
      hSqDA,
      hSqDB1,
      h47AB,
      hSqCB,
      hSqDC,
      h47CB_common⟩

/--
Euclid II.4 specialized to the II.12 carrier D-A-C.

The same concrete representative of Rect(DA,AC) is used for both
cross terms. The result is immediately regrouped into the form

  Square(DC) ~ec Square(AD) + Square(AC) + 2 Rect(DA,AC).

No cancellation is used.
-/
theorem proposition2_12_ii4_DAC
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (D A C : Geo.Point)

    --------------------------------------------------------------------
    -- II.2 / II.4 diagram: square on DC cut at A.
    --------------------------------------------------------------------

    (D0 E0 L0 X0 : Geo.Point)
    (hSquareDC : IsSquare Geo D C E0 D0)

    (hDAC : Geo.Between D A C)
    (hD0L0E0 : Geo.Between D0 L0 E0)
    (hD0X0C : Geo.Between D0 X0 C)
    (hAX0L0 : Geo.Between A X0 L0)

    (hII2LeftPar :
      IsParallelogram Geo L0 D0 D A)
    (hII2RightPar :
      IsParallelogram Geo C E0 L0 A)

    -- Representatives of Rect(DC,DA) and Rect(DC,AC).
    (U0 U1 U2 U3 : Geo.Point)
    (V0 V1 V2 V3 : Geo.Point)

    (hDC_DA :
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 D C D A)

    (hDC_AC :
      IsRectangleContainedBy Geo
        V0 V1 V2 V3 D C A C)

    --------------------------------------------------------------------
    -- Left II.3 diagram, read on C-A-D.
    --------------------------------------------------------------------

    (D1 E1 L1 X1 : Geo.Point)

    (hRectLeft :
      IsRectangle Geo C D E1 D1)

    (hDE1_AD :
      Geo.Congruent D E1 A D)

    (hD1L1E1 : Geo.Between D1 L1 E1)
    (hD1X1D : Geo.Between D1 X1 D)
    (hAX1L1 : Geo.Between A X1 L1)

    (hLeftLeftPar :
      IsParallelogram Geo L1 D1 C A)
    (hLeftRightPar :
      IsParallelogram Geo D E1 L1 A)

    -- Square on AD.
    (F G : Geo.Point)
    (hSquareAD : IsSquare Geo A D F G)

    --------------------------------------------------------------------
    -- Right II.3 diagram.
    --------------------------------------------------------------------

    (D2 E2 L2 X2 : Geo.Point)

    (hRectRight :
      IsRectangle Geo D C E2 D2)

    (hCE2_AC :
      Geo.Congruent C E2 A C)

    (hD2L2E2 : Geo.Between D2 L2 E2)
    (hD2X2C : Geo.Between D2 X2 C)
    (hAX2L2 : Geo.Between A X2 L2)

    (hRightLeftPar :
      IsParallelogram Geo L2 D2 D A)
    (hRightRightPar :
      IsParallelogram Geo C E2 L2 A)

    -- Square on AC.
    (H K : Geo.Point)
    (hSquareAC : IsSquare Geo A C H K)

    --------------------------------------------------------------------
    -- One representative of Rect(DA,AC), used twice.
    --------------------------------------------------------------------

    (T0 T1 T2 T3 : Geo.Point)

    (hCross :
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 D A A C) :

    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo D C E0 D0)
      ((hilbertParallelogramTerm Geo A D F G +
        hilbertParallelogramTerm Geo A C H K) +
       (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
        hilbertParallelogramTerm Geo T0 T1 T2 T3)) := by

  --------------------------------------------------------------------
  -- Raw II.4:
  --
  --   DC^2 = (R + AD^2) + (R + AC^2).
  --------------------------------------------------------------------

  have hRaw :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo D C E0 D0)
        ((hilbertParallelogramTerm Geo T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo A D F G) +
         (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo A C H K)) :=
    euclid_proposition_2_4
      Geo
      D C A
      D0 E0 L0 X0
      hSquareDC
      hDAC
      hD0L0E0
      hD0X0C
      hAX0L0
      hII2LeftPar
      hII2RightPar
      U0 U1 U2 U3
      V0 V1 V2 V3
      hDC_DA
      hDC_AC
      D1 E1 L1 X1
      hRectLeft
      hDE1_AD
      hD1L1E1
      hD1X1D
      hAX1L1
      hLeftLeftPar
      hLeftRightPar
      F G
      hSquareAD
      D2 E2 L2 X2
      hRectRight
      hCE2_AC
      hD2L2E2
      hD2X2C
      hAX2L2
      hRightLeftPar
      hRightRightPar
      H K
      hSquareAC
      T0 T1 T2 T3
      T0 T1 T2 T3
      hCross
      hCross

  --------------------------------------------------------------------
  -- Pure commutative bookkeeping.
  --------------------------------------------------------------------

  have hRegroup :
      ((hilbertParallelogramTerm Geo T0 T1 T2 T3 +
        hilbertParallelogramTerm Geo A D F G) +
       (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
        hilbertParallelogramTerm Geo A C H K))
        =
      ((hilbertParallelogramTerm Geo A D F G +
        hilbertParallelogramTerm Geo A C H K) +
       (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
        hilbertParallelogramTerm Geo T0 T1 T2 T3)) := by
    ac_rfl

  have hTarget :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo D C E0 D0)
        ((hilbertParallelogramTerm Geo A D F G +
          hilbertParallelogramTerm Geo A C H K) +
         (hilbertParallelogramTerm Geo T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo T0 T1 T2 T3)) := by
    rw [hRegroup] at hRaw
    exact hRaw

  exact
    equicomplementable_of_scissorsEq
      Geo hTarget

/--
Pure scissors-calculus bridge for Euclid II.12.

Assume

  AB^2 ~ DA^2 + DB^2
  CB^2 ~ DC^2 + DB^2
  DC^2 ~ DA^2 + AC^2 + 2R

with literally the same representatives DA^2, DB^2, DC^2
in the three identities. Then

  CB^2 ~ AB^2 + AC^2 + 2R.

This is only substitution and commutative regrouping.
-/
theorem proposition2_12_scissors_final_bridge
    (SqAB SqDA SqDB SqCB SqDC SqAC R :
      HilbertScissorsTerm Geo)

    (hAB :
      HilbertScissorsEquicomplementable Geo
        SqAB
        (SqDA + SqDB))

    (hCB :
      HilbertScissorsEquicomplementable Geo
        SqCB
        (SqDC + SqDB))

    (hII4 :
      HilbertScissorsEquicomplementable Geo
        SqDC
        ((SqDA + SqAC) + (R + R))) :

    HilbertScissorsEquicomplementable Geo
      SqCB
      ((SqAB + SqAC) + (R + R)) := by

  --------------------------------------------------------------------
  -- Substitute II.4 into the second Pythagorean identity:
  --
  --   CB^2
  --     ~ DC^2 + DB^2
  --     ~ (DA^2 + AC^2 + 2R) + DB^2.
  --------------------------------------------------------------------

  have hDBrefl :
      HilbertScissorsEquicomplementable Geo
        SqDB SqDB :=
    equicomplementable_refl
      Geo SqDB

  have hII4plusDB :
      HilbertScissorsEquicomplementable Geo
        (SqDC + SqDB)
        (((SqDA + SqAC) + (R + R)) + SqDB) :=
    i47_aux_equicomplementable_add
      Geo
      hII4
      hDBrefl

  have hCBexpanded :
      HilbertScissorsEquicomplementable Geo
        SqCB
        (((SqDA + SqAC) + (R + R)) + SqDB) :=
    equicomplementable_trans
      Geo
      hCB
      hII4plusDB

  --------------------------------------------------------------------
  -- Regroup to expose the first Pythagorean block DA^2 + DB^2.
  --------------------------------------------------------------------

  have hRegroup :
      (((SqDA + SqAC) + (R + R)) + SqDB)
        =
      ((SqDA + SqDB) + (SqAC + (R + R))) := by
    ac_rfl

  have hCBregrouped :
      HilbertScissorsEquicomplementable Geo
        SqCB
        ((SqDA + SqDB) + (SqAC + (R + R))) := by
    rw [hRegroup] at hCBexpanded
    exact hCBexpanded

  --------------------------------------------------------------------
  -- Replace DA^2 + DB^2 by AB^2.
  --------------------------------------------------------------------

  have hTailRefl :
      HilbertScissorsEquicomplementable Geo
        (SqAC + (R + R))
        (SqAC + (R + R)) :=
    equicomplementable_refl
      Geo
      (SqAC + (R + R))

  have hReplaceAB :
      HilbertScissorsEquicomplementable Geo
        ((SqDA + SqDB) + (SqAC + (R + R)))
        (SqAB + (SqAC + (R + R))) :=
    i47_aux_equicomplementable_add
      Geo
      (equicomplementable_symm
        Geo hAB)
      hTailRefl

  have hAlmost :
      HilbertScissorsEquicomplementable Geo
        SqCB
        (SqAB + (SqAC + (R + R))) :=
    equicomplementable_trans
      Geo
      hCBregrouped
      hReplaceAB

  --------------------------------------------------------------------
  -- Euclid's displayed order:
  --
  --   AB^2 + AC^2 + 2R.
  --------------------------------------------------------------------

  simpa only [Multiset.add_assoc]
    using hAlmost


/--
Point-level normalized form of the final II.12 substitution.

All geometry has already been discharged before this lemma. The three
input relations are exactly the two I.47 identities and the specialized
II.4 identity, sharing concrete representatives.
-/
theorem proposition2_12_final_from_normalized_blocks
    (A B C D : Geo.Point)
    (AB0 AB1 DA0 DA1 DB0 DB1 : Geo.Point)
    (CB0 CB1 DC0 DC1 AC0 AC1 : Geo.Point)
    (T0 T1 T2 T3 : Geo.Point)

    (h47AB :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          A B AB1 AB0)
        (hilbertParallelogramTerm Geo
          D A DA0 DA1 +
         hilbertParallelogramTerm Geo
          D B DB1 DB0))

    (h47CB :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          C B CB1 CB0)
        (hilbertParallelogramTerm Geo
          D C DC0 DC1 +
         hilbertParallelogramTerm Geo
          D B DB1 DB0))

    (hII4 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          D C DC0 DC1)
        ((hilbertParallelogramTerm Geo
            D A DA0 DA1 +
          hilbertParallelogramTerm Geo
            A C AC0 AC1) +
         (hilbertParallelogramTerm Geo
            T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo
            T0 T1 T2 T3))) :

    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo
        C B CB1 CB0)
      ((hilbertParallelogramTerm Geo
          A B AB1 AB0 +
        hilbertParallelogramTerm Geo
          A C AC0 AC1) +
       (hilbertParallelogramTerm Geo
          T0 T1 T2 T3 +
        hilbertParallelogramTerm Geo
          T0 T1 T2 T3)) := by

  exact
    proposition2_12_scissors_final_bridge
      Geo
      (hilbertParallelogramTerm Geo
        A B AB1 AB0)
      (hilbertParallelogramTerm Geo
        D A DA0 DA1)
      (hilbertParallelogramTerm Geo
        D B DB1 DB0)
      (hilbertParallelogramTerm Geo
        C B CB1 CB0)
      (hilbertParallelogramTerm Geo
        D C DC0 DC1)
      (hilbertParallelogramTerm Geo
        A C AC0 AC1)
      (hilbertParallelogramTerm Geo
        T0 T1 T2 T3)
      h47AB
      h47CB
      hII4

/--
Normalize the square representatives occurring in the II.4 block.

The I.47 package uses a square on DA and a square on DC.  A separate
application of II.4 may use different concrete squares, and its AD
square has the opposite endpoint orientation.  Square transport removes
both differences.
-/
theorem proposition2_12_normalize_ii4_squares
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (D A C : Geo.Point)

    -- Normalized representatives used by the two I.47 blocks.
    (DA0 DA1 DC0 DC1 : Geo.Point)
    (hSqDA :
      IsSquare Geo D A DA0 DA1)
    (hSqDC :
      IsSquare Geo D C DC0 DC1)

    -- Representatives supplied by II.4.
    (AD0 AD1 DC20 DC21 AC0 AC1 : Geo.Point)
    (hSqAD2 :
      IsSquare Geo A D AD0 AD1)
    (hSqDC2 :
      IsSquare Geo D C DC20 DC21)

    -- Repeated rectangle term.
    (T0 T1 T2 T3 : Geo.Point)

    (hII4 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          D C DC20 DC21)
        ((hilbertParallelogramTerm Geo
            A D AD0 AD1 +
          hilbertParallelogramTerm Geo
            A C AC0 AC1) +
         (hilbertParallelogramTerm Geo
            T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo
            T0 T1 T2 T3))) :

    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo
        D C DC0 DC1)
      ((hilbertParallelogramTerm Geo
          D A DA0 DA1 +
        hilbertParallelogramTerm Geo
          A C AC0 AC1) +
       (hilbertParallelogramTerm Geo
          T0 T1 T2 T3 +
        hilbertParallelogramTerm Geo
          T0 T1 T2 T3)) := by

  --------------------------------------------------------------------
  -- DC square: same oriented base DC.
  --------------------------------------------------------------------

  have hDC_DC :
      Geo.Congruent D C D C :=
    hilbert_congruent_reflexive
      Geo D C

  have hDCtransport :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          D C DC0 DC1)
        (hilbertParallelogramTerm Geo
          D C DC20 DC21) :=
    hilbert_square_transport
      Geo
      D C DC0 DC1
      D C DC20 DC21
      hSqDC
      hSqDC2
      hDC_DC

  --------------------------------------------------------------------
  -- DA square versus AD square: reverse the second segment.
  --------------------------------------------------------------------

  have hDA_DA :
      Geo.Congruent D A D A :=
    hilbert_congruent_reflexive
      Geo D A

  have hDA_AD :
      Geo.Congruent D A A D :=
    CongruentSwapSecond
      Geo D A D A hDA_DA

  have hDAtransport :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          D A DA0 DA1)
        (hilbertParallelogramTerm Geo
          A D AD0 AD1) :=
    hilbert_square_transport
      Geo
      D A DA0 DA1
      A D AD0 AD1
      hSqDA
      hSqAD2
      hDA_AD

  --------------------------------------------------------------------
  -- Replace the AD-square in the right-hand side by the normalized
  -- DA-square.  AC and the repeated rectangle remain unchanged.
  --------------------------------------------------------------------

  have hACrefl :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          A C AC0 AC1)
        (hilbertParallelogramTerm Geo
          A C AC0 AC1) :=
    equicomplementable_refl
      Geo
      (hilbertParallelogramTerm Geo
        A C AC0 AC1)

  have hPair :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          A D AD0 AD1 +
         hilbertParallelogramTerm Geo
          A C AC0 AC1)
        (hilbertParallelogramTerm Geo
          D A DA0 DA1 +
         hilbertParallelogramTerm Geo
          A C AC0 AC1) :=
    i47_aux_equicomplementable_add
      Geo
      (equicomplementable_symm
        Geo hDAtransport)
      hACrefl

  have hRrefl :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          T0 T1 T2 T3 +
         hilbertParallelogramTerm Geo
          T0 T1 T2 T3)
        (hilbertParallelogramTerm Geo
          T0 T1 T2 T3 +
         hilbertParallelogramTerm Geo
          T0 T1 T2 T3) :=
    equicomplementable_refl
      Geo
      (hilbertParallelogramTerm Geo
        T0 T1 T2 T3 +
       hilbertParallelogramTerm Geo
        T0 T1 T2 T3)

  have hRightNormalize :
      HilbertScissorsEquicomplementable Geo
        ((hilbertParallelogramTerm Geo
            A D AD0 AD1 +
          hilbertParallelogramTerm Geo
            A C AC0 AC1) +
         (hilbertParallelogramTerm Geo
            T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo
            T0 T1 T2 T3))
        ((hilbertParallelogramTerm Geo
            D A DA0 DA1 +
          hilbertParallelogramTerm Geo
            A C AC0 AC1) +
         (hilbertParallelogramTerm Geo
            T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo
            T0 T1 T2 T3)) :=
    i47_aux_equicomplementable_add
      Geo
      hPair
      hRrefl

  exact
    equicomplementable_trans
      Geo
      hDCtransport
      (equicomplementable_trans
        Geo
        hII4
        hRightNormalize)


/--
Final II.12 substitution allowing II.4 to use its own square
representatives.

The two I.47 identities are already normalized to one common DB square.
This lemma normalizes only the DA and DC squares coming from II.4 and
then invokes the final scissors bridge.
-/
theorem proposition2_12_final_with_independent_ii4_squares
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D : Geo.Point)

    -- I.47 representatives.
    (AB0 AB1 DA0 DA1 DB0 DB1 : Geo.Point)
    (CB0 CB1 DC0 DC1 : Geo.Point)

    (hSqDA :
      IsSquare Geo D A DA0 DA1)
    (hSqDC :
      IsSquare Geo D C DC0 DC1)

    (h47AB :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          A B AB1 AB0)
        (hilbertParallelogramTerm Geo
          D A DA0 DA1 +
         hilbertParallelogramTerm Geo
          D B DB1 DB0))

    (h47CB :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          C B CB1 CB0)
        (hilbertParallelogramTerm Geo
          D C DC0 DC1 +
         hilbertParallelogramTerm Geo
          D B DB1 DB0))

    -- Independent II.4 square representatives.
    (AD0 AD1 DC20 DC21 AC0 AC1 : Geo.Point)

    (hSqAD2 :
      IsSquare Geo A D AD0 AD1)
    (hSqDC2 :
      IsSquare Geo D C DC20 DC21)

    (T0 T1 T2 T3 : Geo.Point)

    (hII4 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          D C DC20 DC21)
        ((hilbertParallelogramTerm Geo
            A D AD0 AD1 +
          hilbertParallelogramTerm Geo
            A C AC0 AC1) +
         (hilbertParallelogramTerm Geo
            T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo
            T0 T1 T2 T3))) :

    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo
        C B CB1 CB0)
      ((hilbertParallelogramTerm Geo
          A B AB1 AB0 +
        hilbertParallelogramTerm Geo
          A C AC0 AC1) +
       (hilbertParallelogramTerm Geo
          T0 T1 T2 T3 +
        hilbertParallelogramTerm Geo
          T0 T1 T2 T3)) := by

  have hII4normalized :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          D C DC0 DC1)
        ((hilbertParallelogramTerm Geo
            D A DA0 DA1 +
          hilbertParallelogramTerm Geo
            A C AC0 AC1) +
         (hilbertParallelogramTerm Geo
            T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo
            T0 T1 T2 T3)) :=
    proposition2_12_normalize_ii4_squares
      Geo
      D A C
      DA0 DA1
      DC0 DC1
      hSqDA
      hSqDC
      AD0 AD1
      DC20 DC21
      AC0 AC1
      hSqAD2
      hSqDC2
      T0 T1 T2 T3
      hII4

  exact
    proposition2_12_final_from_normalized_blocks
      Geo
      A B C D
      AB0 AB1
      DA0 DA1
      DB0 DB1
      CB0 CB1
      DC0 DC1
      AC0 AC1
      T0 T1 T2 T3
      h47AB
      h47CB
      hII4normalized

------------------------------------------------------------------------
-- Generic internal cut of a parallelogram.
--
-- This is the construction layer missing from the diagrammatic Book II
-- interfaces.  It is extracted from the I.47 cut machinery, but none of
-- the following lemmas uses the equal-side clauses of a square.
------------------------------------------------------------------------

/--
If B-M-C and C-E-L-M is a parallelogram inside B-C-E-D, then L lies
on the opposite carrier DE.
-/
theorem proposition2_12_parallelogram_L_on_DE
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M L : Geo.Point)
    (hBMC : Geo.Between B M C)
    (hWhole : IsParallelogram Geo B C E D)
    (hPar : IsParallelogram Geo C E L M) :
    Collinear Geo D L E := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hBC : B ≠ C :=
    hBMCdata.2.2.1

  have hCM : C ≠ M :=
    hBMCdata.2.1.symm

  have hEL_MC :
      Geo.Parallel E L M C :=
    hPar.2

  have hMC_EL :
      Geo.Parallel M C E L :=
    ParallelSymmetry
      Geo E L M C hEL_MC

  have hCM_EL :
      Geo.Parallel C M E L :=
    ParallelSwapFirstLine
      Geo M C E L hMC_EL

  have hCBMcol :
      Collinear Geo C B M := by
    have hBMCcol :
        Collinear Geo B M C :=
      hBMCdata.2.2.2.1

    have hMCB :
        Collinear Geo M C B :=
      PrimCollinearCycle
        Geo B M C hBMCcol

    exact
      PrimCollinearCycle
        Geo M C B hMCB

  have hCB_EL :
      Geo.Parallel C B E L :=
    collinear_parallel_trans
      Geo
      C B M
      E L
      hBC.symm
      hCBMcol
      hCM_EL

  have hEL_CB :
      Geo.Parallel E L C B :=
    ParallelSymmetry
      Geo C B E L hCB_EL

  have hBC_ED :
      Geo.Parallel B C E D :=
    hWhole.1

  have hCB_ED :
      Geo.Parallel C B E D :=
    ParallelSwapFirstLine
      Geo B C E D hBC_ED

  have hED_CB :
      Geo.Parallel E D C B :=
    ParallelSymmetry
      Geo C B E D hCB_ED

  have hCarrier :
      Geo.PointLine E L =
      Geo.PointLine E D := by

    by_contra hDistinct

    have hEL_ED :
        Geo.Parallel E L E D :=
      hilbert_parallel_transitive_distinct
        Geo
        E L
        E D
        C B
        hEL_CB
        hED_CB
        hDistinct

    exact
      (intersection_test_not_parallel_of_common_point
        Geo
        E L
        E D
        E
        (intersection_test_left_mem Geo E L)
        (intersection_test_left_mem Geo E D))
        hEL_ED

  have hEL : E ≠ L :=
    hEL_CB.1

  rcases
      HilbertPlaneIncidence.line_through
        E L hEL with
    ⟨lineEL, hEel, hLel⟩

  have hD_ED :
      D ∈ Geo.PointLine E D :=
    intersection_test_right_mem
      Geo E D

  have hD_EL :
      D ∈ Geo.PointLine E L := by
    rw [hCarrier]
    exact hD_ED

  have hDel :
      HilbertIncidence.OnLine D lineEL :=
    (hilbert_mem_pointLine_iff_onLine
      Geo
      E L D
      lineEL
      hEL
      hEel
      hLel).mp hD_EL

  exact
    ⟨lineEL,
      hDel,
      hLel,
      hEel⟩


/--
The complementary piece of a parallelogram cut at an interior point
is again a parallelogram.
-/
theorem proposition2_12_left_cut_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M L : Geo.Point)
    (hBMC : Geo.Between B M C)
    (hDLE : Collinear Geo D L E)
    (hWhole : IsParallelogram Geo B C E D)
    (hPar : IsParallelogram Geo C E L M) :
    IsParallelogram Geo L D B M := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hBM : B ≠ M :=
    hBMCdata.1

  have hMC : M ≠ C :=
    hBMCdata.2.1

  have hBMCcol :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  have hCMB :
      Geo.Between C M B :=
    hBMCdata.2.2.2.2

  have hCMltCB :
      HilbertSegmentLess Geo C M C B :=
    hilbert_segmentLess_of_between
      Geo C M B hCMB

  have hParSides :
      OppositeSidesCongruent Geo C E L M :=
    ParallelogramOppositeSidesCongruent
      Geo C E L M hPar

  have hEL_MC :
      Geo.Congruent E L M C :=
    hParSides.2

  have hEL_CM :
      Geo.Congruent E L C M :=
    CongruentSwapSecond
      Geo E L M C hEL_MC

  have hELltCB :
      HilbertSegmentLess Geo E L C B :=
    hilbert_segmentLess_congruent_left
      Geo
      C M
      E L
      C B
      hCMltCB
      hEL_CM

  have hWholeSides :
      OppositeSidesCongruent Geo B C E D :=
    ParallelogramOppositeSidesCongruent
      Geo B C E D hWhole

  have hBC_ED :
      Geo.Congruent B C E D :=
    hWholeSides.1

  have hCB_ED :
      Geo.Congruent C B E D :=
    CongruentReverseFirst
      Geo B C E D hBC_ED

  have hELltED :
      HilbertSegmentLess Geo E L E D :=
    hilbert_segmentLess_congruent_right
      Geo
      E L
      C B
      E D
      hELltCB
      hCB_ED

  have hLD : L ≠ D := by
    intro hEq
    subst D

    exact
      (hilbert_segmentLess_not_congruent
        Geo E L E L hELltED)
        (hilbert_congruent_reflexive
          Geo E L)

  have hBM_ED :
      Geo.Parallel B M E D :=
    collinear_parallel_trans
      Geo
      B M C
      E D
      hBM
      hBMCcol
      hWhole.1

  have hED_BM :
      Geo.Parallel E D B M :=
    ParallelSymmetry
      Geo B M E D hBM_ED

  have hLED :
      Collinear Geo L E D :=
    PrimCollinearCycle
      Geo D L E hDLE

  have hLD_BM :
      Geo.Parallel L D B M :=
    ParallelCollinearLeft
      Geo
      E D L
      B M
      hLD
      hED_BM
      hLED

  have hDB_CE :
      Geo.Parallel D B C E :=
    ParallelSymmetry
      Geo
      C E D B
      hWhole.2

  have hLM_CE :
      Geo.Parallel L M C E :=
    ParallelSymmetry
      Geo
      C E L M
      hPar.1

  have hML_CE :
      Geo.Parallel M L C E :=
    ParallelSwapFirstLine
      Geo
      L M C E
      hLM_CE

  have hDistinct :
      Geo.PointLine D B ≠
      Geo.PointLine M L := by

    intro hEq

    have hML : M ≠ L :=
      hML_CE.1

    rcases
        HilbertPlaneIncidence.line_through
          M L hML with
      ⟨lineML, hMml, hLml⟩

    have hB_DB :
        B ∈ Geo.PointLine D B :=
      intersection_test_right_mem
        Geo D B

    have hB_ML :
        B ∈ Geo.PointLine M L := by
      rw [← hEq]
      exact hB_DB

    have hBml :
        HilbertIncidence.OnLine B lineML :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        M L B
        lineML
        hML
        hMml
        hLml).mp hB_ML

    have hBML :
        Collinear Geo B M L :=
      ⟨lineML,
        hBml,
        hMml,
        hLml⟩

    have hLMB :
        Collinear Geo L M B :=
      PrimCollinearSymm
        Geo B M L hBML

    have hBCM :
        Collinear Geo B C M :=
      PrimCollinearRotate
        Geo B M C hBMCcol

    have hLMC :
        Collinear Geo L M C :=
      CollinearTrans
        Geo
        L M B C
        hBM.symm
        hLMB
        hBCM

    have hNC :=
      parallelogram_vertices_noncollinear
        Geo C E L M hPar

    exact
      hNC.2.2.2 hLMC

  have hDB_ML :
      Geo.Parallel D B M L :=
    hilbert_parallel_transitive_distinct
      Geo
      D B
      M L
      C E
      hDB_CE
      hML_CE
      hDistinct

  exact
    ⟨hLD_BM,
      hDB_ML⟩


/--
Strict order on one side of a parallelogram transfers to the opposite
side under the internal cut.
-/
theorem proposition2_12_upper_cut_between
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M L : Geo.Point)
    (hBMC : Geo.Between B M C)
    (hWhole : IsParallelogram Geo B C E D)
    (hRightPar : IsParallelogram Geo C E L M)
    (hLeftPar : IsParallelogram Geo L D B M) :
    Geo.Between D L E := by

  have hDL : D ≠ L :=
    hLeftPar.1.1.symm

  have hLE : L ≠ E :=
    hRightPar.2.1.symm

  have hDE : D ≠ E :=
    hWhole.1.2.1.symm

  have hLeftSides :
      OppositeSidesCongruent Geo L D B M :=
    ParallelogramOppositeSidesCongruent
      Geo L D B M hLeftPar

  have hLD_BM :
      Geo.Congruent L D B M :=
    hLeftSides.1

  have hBM_LD :
      Geo.Congruent B M L D :=
    hilbert_congruent_symmetry
      Geo L D B M hLD_BM

  have hBM_DL :
      Geo.Congruent B M D L :=
    CongruentSwapSecond
      Geo B M L D hBM_LD

  have hWholeSides :
      OppositeSidesCongruent Geo B C E D :=
    ParallelogramOppositeSidesCongruent
      Geo B C E D hWhole

  have hBC_ED :
      Geo.Congruent B C E D :=
    hWholeSides.1

  have hBC_DE :
      Geo.Congruent B C D E :=
    CongruentSwapSecond
      Geo B C E D hBC_ED

  have hRightSides :
      OppositeSidesCongruent Geo C E L M :=
    ParallelogramOppositeSidesCongruent
      Geo C E L M hRightPar

  have hEL_MC :
      Geo.Congruent E L M C :=
    hRightSides.2

  have hMC_EL :
      Geo.Congruent M C E L :=
    hilbert_congruent_symmetry
      Geo E L M C hEL_MC

  have hMC_LE :
      Geo.Congruent M C L E :=
    CongruentSwapSecond
      Geo M C E L hMC_EL

  exact
    hilbert_theorem27_three_points
      Geo
      B M C
      D L E
      hBMC
      hDL
      hLE
      hDE
      hBM_DL
      hBC_DE
      hMC_LE


/--
The internal cut meets the diagonal, with the crossing point lying
strictly inside both segments.
-/
theorem proposition2_12_diagonal_cut_intersection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M L : Geo.Point)
    (hBMC : Geo.Between B M C)
    (hWhole : IsParallelogram Geo B C E D)
    (hLeftPar : IsParallelogram Geo L D B M) :
    exists N : Geo.Point,
      Geo.Between D N C /\
      Geo.Between M N L := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have _hBM : B ≠ M :=
    hBMCdata.1

  have hMC : M ≠ C :=
    hBMCdata.2.1

  have _hBC : B ≠ C :=
    hBMCdata.2.2.1

  have hBMCcol :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  have hCMB :
      Geo.Between C M B :=
    hBMCdata.2.2.2.2

  have hCMBcol :
      Collinear Geo C M B :=
    (HilbertOrder.between_incidence
      C M B hCMB).2.2.2.1

  have hDB_ML :
      Geo.Parallel D B M L :=
    hLeftPar.2

  have hDB : D ≠ B :=
    hDB_ML.1

  have hML : M ≠ L :=
    hDB_ML.2.1

  rcases
      HilbertPlaneIncidence.line_through
        D B hDB with
    ⟨lineDB, hDdb, hBdb⟩

  rcases
      HilbertPlaneIncidence.line_through
        M L hML with
    ⟨lineML, hMml, hLml⟩

  have hLinesDB_ML :
      HilbertLinesDisjoint Geo lineDB lineML := by

    rintro ⟨X, hXdb, hXml⟩

    have hX_DB :
        X ∈ Geo.PointLine D B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D B X
        lineDB
        hDB
        hDdb
        hBdb).mpr hXdb

    have hX_ML :
        X ∈ Geo.PointLine M L :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        M L X
        lineML
        hML
        hMml
        hLml).mpr hXml

    exact
      Set.disjoint_left.mp
        hDB_ML.2.2
        hX_DB
        hX_ML

  have hBoff :
      Not (HilbertIncidence.OnLine B lineML) := by
    intro hBml
    exact
      hLinesDB_ML
        ⟨B, hBdb, hBml⟩

  have hDoff :
      Not (HilbertIncidence.OnLine D lineML) := by
    intro hDml
    exact
      hLinesDB_ML
        ⟨D, hDdb, hDml⟩

  have hCoff :
      Not (HilbertIncidence.OnLine C lineML) := by
    intro hCml

    have hBml :
        HilbertIncidence.OnLine B lineML :=
      hilbert_collinear_on_line
        Geo
        C M B
        lineML
        hMC.symm
        hCml
        hMml
        hCMBcol

    exact hBoff hBml

  have hWholeNC :=
    parallelogram_vertices_noncollinear
      Geo B C E D hWhole

  have hDBC :
      Not (Collinear Geo D B C) :=
    hWholeNC.1

  have hCBD :
      Not (Collinear Geo C B D) := by
    intro h
    exact
      hDBC
        (PrimCollinearSymm
          Geo C B D h)

  have hMeetsCB :
      HilbertSegmentMeetsLine Geo C B lineML :=
    ⟨M, hCMB, hMml⟩

  have hNotMeetsBD :
      Not (HilbertSegmentMeetsLine Geo B D lineML) := by

    rintro ⟨X, hBXD, hXml⟩

    have hXdb :
        HilbertIncidence.OnLine X lineDB :=
      hilbert_between_on_line
        Geo
        B X D
        lineDB
        hBdb
        hDdb
        hBXD

    exact
      hLinesDB_ML
        ⟨X, hXdb, hXml⟩

  have hMeetsCD :
      HilbertSegmentMeetsLine Geo C D lineML :=
    hilbert_pasch_forced
      Geo
      C B D
      lineML
      hCBD
      hCoff
      hBoff
      hDoff
      hMeetsCB
      hNotMeetsBD

  rcases hMeetsCD with
    ⟨N, hCND, hNml⟩

  have hDNC :
      Geo.Between D N C :=
    (HilbertOrder.between_incidence
      C N D hCND).2.2.2.2

  have hLMN :
      Collinear Geo L M N :=
    ⟨lineML,
      hLml,
      hMml,
      hNml⟩

  have hDL_BM :
      Geo.Parallel D L B M :=
    ParallelSwapFirstLine
      Geo
      L D B M
      hLeftPar.1

  have hBM_DL :
      Geo.Parallel B M D L :=
    ParallelSymmetry
      Geo
      D L B M
      hDL_BM

  have hMB_DL :
      Geo.Parallel M B D L :=
    ParallelSwapFirstLine
      Geo
      B M D L
      hBM_DL

  have hMCBcol :
      Collinear Geo M C B :=
    PrimCollinearCycle
      Geo B M C hBMCcol

  have hMC_DL :
      Geo.Parallel M C D L :=
    collinear_parallel_trans
      Geo
      M C B
      D L
      hMC
      hMCBcol
      hMB_DL

  have hDL_MC :
      Geo.Parallel D L M C :=
    ParallelSymmetry
      Geo M C D L hMC_DL

  have hLNM :
      Geo.Between L N M :=
    hilbert_collinear_between_of_parallel
      Geo
      D L M C N
      hDL_MC
      hDNC
      hLMN

  have hMNL :
      Geo.Between M N L :=
    (HilbertOrder.between_incidence
      L N M hLNM).2.2.2.2

  exact
    ⟨N,
      hDNC,
      hMNL⟩


/--
Existence of the complete Book-II cut diagram for an arbitrary
parallelogram B-C-E-D and an interior point M of BC.

This is the reusable construction needed by II.2 and II.3.
-/
theorem proposition2_12_parallelogram_cut_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M : Geo.Point)
    (hWhole : IsParallelogram Geo B C E D)
    (hBMC : Geo.Between B M C) :
    exists L X : Geo.Point,
      Geo.Between D L E /\
      Geo.Between D X C /\
      Geo.Between M X L /\
      IsParallelogram Geo L D B M /\
      IsParallelogram Geo C E L M := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hBC : B ≠ C :=
    hBMCdata.2.2.1

  have hMC : M ≠ C :=
    hBMCdata.2.1

  have hMbaseLater : M ≠ C :=
    hMC

  rcases
      HilbertPlaneIncidence.line_through
        B C hBC with
    ⟨base, hBbase, hCbase⟩

  have hMbase :
      HilbertIncidence.OnLine M base :=
    hilbert_between_on_line
      Geo
      B M C
      base
      hBbase
      hCbase
      hBMC

  have hWholeNC :=
    parallelogram_vertices_noncollinear
      Geo B C E D hWhole

  have hBCE :
      Not (Collinear Geo B C E) :=
    hWholeNC.2.1

  have hEoff :
      Not (HilbertIncidence.OnLine E base) := by
    intro hEbase
    exact
      hBCE
        ⟨base,
          hBbase,
          hCbase,
          hEbase⟩

  rcases
      i47_aux_construct_L_parallelogram
        Geo
        C E M
        base
        hCbase
        hMbase
        hEoff
        hMbaseLater with
    ⟨L, hRightPar⟩

  have hDLEcol :
      Collinear Geo D L E :=
    proposition2_12_parallelogram_L_on_DE
      Geo
      B C D E M L
      hBMC
      hWhole
      hRightPar

  have hLeftPar :
      IsParallelogram Geo L D B M :=
    proposition2_12_left_cut_parallelogram
      Geo
      B C D E M L
      hBMC
      hDLEcol
      hWhole
      hRightPar

  have hDLE :
      Geo.Between D L E :=
    proposition2_12_upper_cut_between
      Geo
      B C D E M L
      hBMC
      hWhole
      hRightPar
      hLeftPar

  rcases
      proposition2_12_diagonal_cut_intersection
        Geo
        B C D E M L
        hBMC
        hWhole
        hLeftPar with
    ⟨X, hDXC, hMXL⟩

  exact
    ⟨L, X,
      hDLE,
      hDXC,
      hMXL,
      hLeftPar,
      hRightPar⟩

/--
Existential II.4 block for the II.12 order D-A-C.

Starting only from D-A-C, construct:
  * a square on DC,
  * the II.2 cut of that square at A,
  * the two rectangles used by the two II.3 applications,
  * their internal cuts at A,
  * squares on AD and AC,
  * one concrete representative of Rect(DA,AC),
and conclude

  DC^2 ~ec AD^2 + AC^2 + 2 Rect(DA,AC).

All auxiliary Book-II diagram points are hidden existentially.
-/
theorem proposition2_12_ii4_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (D A C : Geo.Point)
    (hDAC : Geo.Between D A C) :
    exists DC20 DC21 AD0 AD1 AC0 AC1 : Geo.Point,
    exists T0 T1 T2 T3 : Geo.Point,
      IsSquare Geo D C DC20 DC21 /\
      IsSquare Geo A D AD0 AD1 /\
      IsSquare Geo A C AC0 AC1 /\
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 D A A C /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          D C DC20 DC21)
        ((hilbertParallelogramTerm Geo
            A D AD0 AD1 +
          hilbertParallelogramTerm Geo
            A C AC0 AC1) +
         (hilbertParallelogramTerm Geo
            T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo
            T0 T1 T2 T3)) := by

  --------------------------------------------------------------------
  -- Order data.
  --------------------------------------------------------------------

  have hDACdata :=
    HilbertOrder.between_incidence
      D A C hDAC

  have hDA : D ≠ A :=
    hDACdata.1

  have hAC : A ≠ C :=
    hDACdata.2.1

  have hDC : D ≠ C :=
    hDACdata.2.2.1

  have hAD : A ≠ D :=
    hDA.symm

  have hCD : C ≠ D :=
    hDC.symm

  have hCAD :
      Geo.Between C A D :=
    hDACdata.2.2.2.2

  --------------------------------------------------------------------
  -- Square on DC.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_46
        Geo D C hDC with
    ⟨E0, D0, hSquareDC⟩

  --------------------------------------------------------------------
  -- II.2 cut of the square on DC at A.
  --------------------------------------------------------------------

  rcases
      proposition2_12_parallelogram_cut_exists
        Geo
        D C D0 E0 A
        hSquareDC.1
        hDAC with
    ⟨L0, X0,
      hD0L0E0,
      hD0X0C,
      hAX0L0,
      hII2LeftPar,
      hII2RightPar⟩

  --------------------------------------------------------------------
  -- Representatives Rect(DC,DA) and Rect(DC,AC).
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        D C
        D A
        hDC with
    ⟨U2, U3, hDC_DA⟩

  rcases
      rectangle_contained_by_exists
        Geo
        D C
        A C
        hDC with
    ⟨V2, V3, hDC_AC⟩

  --------------------------------------------------------------------
  -- Left II.3 rectangle:
  --
  --   whole side C-D, fixed side A-D,
  --   cut at A in C-A-D.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        C D
        A D
        hCD with
    ⟨E1, D1, hLeftContained⟩

  have hRectLeft :
      IsRectangle Geo C D E1 D1 :=
    hLeftContained.1

  have hDE1_AD :
      Geo.Congruent D E1 A D :=
    hLeftContained.2.2

  rcases
      proposition2_12_parallelogram_cut_exists
        Geo
        C D D1 E1 A
        hRectLeft.1
        hCAD with
    ⟨L1, X1,
      hD1L1E1,
      hD1X1D,
      hAX1L1,
      hLeftLeftPar,
      hLeftRightPar⟩

  --------------------------------------------------------------------
  -- Square on AD.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_46
        Geo A D hAD with
    ⟨F, G, hSquareAD⟩

  --------------------------------------------------------------------
  -- Right II.3 rectangle:
  --
  --   whole side D-C, fixed side A-C,
  --   cut at A in D-A-C.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        D C
        A C
        hDC with
    ⟨E2, D2, hRightContained⟩

  have hRectRight :
      IsRectangle Geo D C E2 D2 :=
    hRightContained.1

  have hCE2_AC :
      Geo.Congruent C E2 A C :=
    hRightContained.2.2

  rcases
      proposition2_12_parallelogram_cut_exists
        Geo
        D C D2 E2 A
        hRectRight.1
        hDAC with
    ⟨L2, X2,
      hD2L2E2,
      hD2X2C,
      hAX2L2,
      hRightLeftPar,
      hRightRightPar⟩

  --------------------------------------------------------------------
  -- Square on AC.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_46
        Geo A C hAC with
    ⟨H, K, hSquareAC⟩

  --------------------------------------------------------------------
  -- One representative of Rect(DA,AC).
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        D A
        A C
        hDA with
    ⟨T2, T3, hCross⟩

  --------------------------------------------------------------------
  -- Apply the specialized II.4 wrapper.
  --------------------------------------------------------------------

  have hII4 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          D C E0 D0)
        ((hilbertParallelogramTerm Geo
            A D F G +
          hilbertParallelogramTerm Geo
            A C H K) +
         (hilbertParallelogramTerm Geo
            D A T2 T3 +
          hilbertParallelogramTerm Geo
            D A T2 T3)) :=
    proposition2_12_ii4_DAC
      Geo
      D A C
      D0 E0 L0 X0
      hSquareDC
      hDAC
      hD0L0E0
      hD0X0C
      hAX0L0
      hII2LeftPar
      hII2RightPar
      D C U2 U3
      D C V2 V3
      hDC_DA
      hDC_AC
      D1 E1 L1 X1
      hRectLeft
      hDE1_AD
      hD1L1E1
      hD1X1D
      hAX1L1
      hLeftLeftPar
      hLeftRightPar
      F G
      hSquareAD
      D2 E2 L2 X2
      hRectRight
      hCE2_AC
      hD2L2E2
      hD2X2C
      hAX2L2
      hRightLeftPar
      hRightRightPar
      H K
      hSquareAC
      D A T2 T3
      hCross

  exact
    ⟨E0, D0,
      F, G,
      H, K,
      D, A, T2, T3,
      hSquareDC,
      hSquareAD,
      hSquareAC,
      hCross,
      hII4⟩

/--
Euclid II.12.

For an obtuse triangle ABC, with the obtuse angle at A, there exists
a perpendicular foot D on the extension of AC beyond A and concrete
representatives of the relevant squares and rectangle such that

  Square(CB)
    ~ec
  Square(AB) + Square(AC) + 2 Rect(DA,AC).

Everything is constructed internally:
  * D and the two right triangles,
  * both I.47 decompositions,
  * the complete II.4 diagram on D-A-C,
  * all square transports and final scissors substitutions.
-/
theorem euclid_proposition_2_12
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hObtuse : HilbertObtuseAngle Geo B A C) :
    exists D : Geo.Point,
    exists AB0 AB1 AC0 AC1 CB0 CB1 : Geo.Point,
    exists T0 T1 T2 T3 : Geo.Point,
      Geo.Between D A C /\
      HilbertRightAngle Geo A D B /\
      HilbertRightAngle Geo C D B /\
      IsSquare Geo A B AB1 AB0 /\
      IsSquare Geo A C AC0 AC1 /\
      IsSquare Geo C B CB1 CB0 /\
      IsRectangleContainedBy Geo
        T0 T1 T2 T3 D A A C /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          C B CB1 CB0)
        ((hilbertParallelogramTerm Geo
            A B AB1 AB0 +
          hilbertParallelogramTerm Geo
            A C AC0 AC1) +
         (hilbertParallelogramTerm Geo
            T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo
            T0 T1 T2 T3)) := by

  --------------------------------------------------------------------
  -- Geometry + both Pythagorean blocks, already normalized to one
  -- common square on DB.
  --------------------------------------------------------------------

  rcases
      proposition2_12_pythagorean_package_common_DB
        Geo
        A B C
        hABC
        hObtuse with
    ⟨D,
      AB0, AB1,
      DA0, DA1,
      DB0, DB1,
      CB0, CB1,
      DC0, DC1,
      hDAC,
      hRightADB,
      hRightCDB,
      hSqAB,
      hSqDA,
      hSqDB,
      h47AB,
      hSqCB,
      hSqDC,
      h47CB⟩

  --------------------------------------------------------------------
  -- Construct the complete II.4 block on the collinear order D-A-C.
  --------------------------------------------------------------------

  rcases
      proposition2_12_ii4_exists
        Geo
        D A C
        hDAC with
    ⟨DC20, DC21,
      AD0, AD1,
      AC0, AC1,
      T0, T1, T2, T3,
      hSqDC2,
      hSqAD2,
      hSqAC,
      hCross,
      hII4⟩

  --------------------------------------------------------------------
  -- Normalize the independent II.4 square representatives against
  -- the two I.47 blocks and perform the final Euclidean substitution.
  --------------------------------------------------------------------

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo
          C B CB1 CB0)
        ((hilbertParallelogramTerm Geo
            A B AB1 AB0 +
          hilbertParallelogramTerm Geo
            A C AC0 AC1) +
         (hilbertParallelogramTerm Geo
            T0 T1 T2 T3 +
          hilbertParallelogramTerm Geo
            T0 T1 T2 T3)) :=
    proposition2_12_final_with_independent_ii4_squares
      Geo
      A B C D
      AB0 AB1
      DA0 DA1
      DB0 DB1
      CB0 CB1
      DC0 DC1
      hSqDA
      hSqDC
      h47AB
      h47CB
      AD0 AD1
      DC20 DC21
      AC0 AC1
      hSqAD2
      hSqDC2
      T0 T1 T2 T3
      hII4

  exact
    ⟨D,
      AB0, AB1,
      AC0, AC1,
      CB0, CB1,
      T0, T1, T2, T3,
      hDAC,
      hRightADB,
      hRightCDB,
      hSqAB,
      hSqAC,
      hSqCB,
      hCross,
      hFinal⟩

end Geometry

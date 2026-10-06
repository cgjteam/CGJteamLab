import CGJteamLab.HilbertInterfaceIV

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid/Forder IV.13

Production module for Book IV proposition 13 and its local proof support.
Stage-labelled declarations below are private implementation details; the public
entry points use production names.
-/

private theorem hilbert_forder_IV13_diameter_right_angle_stage17
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV13DiameterRightAngle
      (Geo := Geo) := by

  intro K R A B C chord
    hAB hAchord hBchord hKchord
    hAcircle hBcircle hCcircle hCoff

  --------------------------------------------------------------------
  -- K is the strict midpoint of the diameter AB.
  --------------------------------------------------------------------

  have hMidK :
      HilbertIsMidpoint Geo K A B :=
    hilbert_circle_center_midpoint_of_chord
      Geo
      K R A B
      chord
      hAB
      hAchord
      hBchord
      hKchord
      hAcircle
      hBcircle

  have hAKB :
      Geo.Between A K B :=
    hMidK.1

  have hAKBdata :=
    HilbertOrder.between_incidence
      A K B hAKB

  have hAK :
      Ne A K :=
    hAKBdata.1

  have hKB :
      Ne K B :=
    hAKBdata.2.1

  have hKA :
      Ne K A :=
    hAK.symm

  have hBK :
      Ne B K :=
    hKB.symm

  have hABcol :
      PrimCollinear Geo A K B :=
    hAKBdata.2.2.2.1

  --------------------------------------------------------------------
  -- C is off the diameter, so all triangles below are genuine.
  --------------------------------------------------------------------

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    have hABC :
        Not (PrimCollinear Geo A B C) :=
      hilbert_not_collinear_of_off_line
        Geo
        A B C
        chord
        hAB
        hAchord
        hBchord
        hCoff
    intro h
    exact
      hABC
        (PrimCollinearRotate
          Geo A C B h)

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact
      hACB
        (PrimCollinearCycle
          Geo B A C h)

  have hAC :
      Ne A C :=
    hilbert_noncollinear_ne_first
      Geo
      A C B
      hACB

  have hCA :
      Ne C A :=
    hAC.symm

  have hBC :
      Ne B C :=
    hilbert_noncollinear_ne_first
      Geo
      B C A
      (by
        intro h
        exact
          hBAC
            (PrimCollinearRotate
              Geo B C A h))

  have hCB :
      Ne C B :=
    hBC.symm

  --------------------------------------------------------------------
  -- The two radius triangles KAC and KBC are isosceles.
  --------------------------------------------------------------------

  have hKA_KC :
      Geo.Congruent K A K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      A C
      hAcircle
      hCcircle

  have hKB_KC :
      Geo.Congruent K B K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      B C
      hBcircle
      hCcircle

  have hAKC :
      Not (PrimCollinear Geo K A C) :=
    hilbert_not_collinear_of_off_line
      Geo
      K A C
      chord
      hKA
      hKchord
      hAchord
      hCoff

  have hBKC :
      Not (PrimCollinear Geo K B C) :=
    hilbert_not_collinear_of_off_line
      Geo
      K B C
      chord
      hKB
      hKchord
      hBchord
      hCoff


  have hIsoA :
      Geo.AngleCongruent
        K A C
        K C A :=
    hilbert_isosceles_base_angles
      Geo
      K A C
      hAKC
      hKA_KC

  have hIsoB :
      Geo.AngleCongruent
        K B C
        K C B :=
    hilbert_isosceles_base_angles
      Geo
      K B C
      hBKC
      hKB_KC

  --------------------------------------------------------------------
  -- K and B determine the same ray from A; K and A determine the
  -- same ray from B.
  --------------------------------------------------------------------

  have hRayAKB :
      HilbertSameRay Geo A K B :=
    hilbert_sameRay_of_between
      Geo A K B hAKB

  have hBKA :
      Geo.Between B K A :=
    hAKBdata.2.2.2.2

  have hRayBKA :
      HilbertSameRay Geo B K A :=
    hilbert_sameRay_of_between
      Geo B K A hBKA

  have hKAC_BAC :
      Geo.Angle K A C =
      Geo.Angle B A C :=
    hilbert_angle_eq_of_sameRay_first
      Geo A K B C hRayAKB

  have hKBC_ABC :
      Geo.Angle K B C =
      Geo.Angle A B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B K A C hRayBKA

  have hBAC_KCA :
      Geo.AngleCongruent
        B A C
        K C A := by
    unfold Geometry.Geo.AngleCongruent at hIsoA ⊢
    rw [← hKAC_BAC]
    exact hIsoA

  have hABC_KCB :
      Geo.AngleCongruent
        A B C
        K C B := by
    unfold Geometry.Geo.AngleCongruent at hIsoB ⊢
    rw [← hKBC_ABC]
    exact hIsoB

  --------------------------------------------------------------------
  -- Extend AC through C to X.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        A C hAC
    with
    ⟨X, hACX⟩

  have hACXdata :=
    HilbertOrder.between_incidence
      A C X hACX

  have hCX :
      Ne C X :=
    hACXdata.2.1

  have hAX :
      Ne A X :=
    hACXdata.2.2.1

  have hACXcol :
      PrimCollinear Geo A C X :=
    hACXdata.2.2.2.1

  --------------------------------------------------------------------
  -- The carrier AC will also be used to show B,C,X noncollinear.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A C hAC
    with
    ⟨lineAC, hAlineAC, hClineAC⟩

  have hXlineAC :
      H.OnLine X lineAC :=
    hilbert_collinear_on_line
      Geo
      A C X
      lineAC
      hAC
      hAlineAC
      hClineAC
      hACXcol

  have hBoffAC :
      Not (H.OnLine B lineAC) := by
    intro hBlineAC
    exact
      hBAC
        ⟨lineAC,
          hBlineAC,
          hAlineAC,
          hClineAC⟩

  have hBCX :
      Not (PrimCollinear Geo B C X) := by
    intro h
    have hBlineAC :
        H.OnLine B lineAC :=
      hilbert_collinear_on_line
        Geo
        C X B
        lineAC
        hCX
        hClineAC
        hXlineAC
        (PrimCollinearCycle
          Geo B C X h)
    exact hBoffAC hBlineAC

  have hXCB :
      Not (PrimCollinear Geo X C B) := by
    intro h
    exact
      hBCX
        (PrimCollinearSymm
          Geo X C B h)

  --------------------------------------------------------------------
  -- Euclid I.32 for triangle BAC with AC produced through C to X.
  --
  -- It supplies P on BX such that
  --
  --   angle ABC ~= angle BCP
  --   angle BAC ~= angle PCX.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        B A C X
        hBAC
        hACX
    with
    ⟨P, hBPX, hABC_BCP, hBAC_PCX⟩

  have hBPXdata :=
    HilbertOrder.between_incidence
      B P X hBPX

  have hBP :
      Ne B P :=
    hBPXdata.1

  have hPX :
      Ne P X :=
    hBPXdata.2.1

  have hBX :
      Ne B X :=
    hBPXdata.2.2.1

  have hBPXcol :
      PrimCollinear Geo B P X :=
    hBPXdata.2.2.2.1

  --------------------------------------------------------------------
  -- P is distinct from C.
  --------------------------------------------------------------------

  have hCP :
      Ne C P := by
    intro hCP
    subst P

    have hBCXbetween :
        Geo.Between B C X :=
      hBPX

    have hBlineAC :
        H.OnLine B lineAC :=
      hilbert_collinear_on_line
        Geo
        C X B
        lineAC
        hCX
        hClineAC
        hXlineAC
        (PrimCollinearCycle
          Geo
          B C X
          (HilbertOrder.between_incidence
            B C X hBCXbetween).2.2.2.1)

    exact hBoffAC hBlineAC

  --------------------------------------------------------------------
  -- Construct the two splitting carriers CK and CP.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        C K
        (hilbert_circle_center_ne_point_of_two_distinct
          Geo
          K R A B C
          hAB
          hAcircle
          hBcircle
          hCcircle).symm
    with
    ⟨lineCK, hClineCK, hKlineCK⟩

  rcases
      HilbertPlaneIncidence.line_through
        C P hCP
    with
    ⟨lineCP, hClineCP, hPlineCP⟩

  --------------------------------------------------------------------
  -- A and B are off CK.
  --------------------------------------------------------------------

  have hAoffCK :
      Not (H.OnLine A lineCK) := by
    intro hAlineCK

    have hEq :
        lineCK = chord :=
      HilbertPlaneIncidence.line_unique
        K A
        hKA
        lineCK chord
        hKlineCK
        hAlineCK
        hKchord
        hAchord

    have hCchord :
        H.OnLine C chord := by
      rw [← hEq]
      exact hClineCK

    exact hCoff hCchord

  have hBoffCK :
      Not (H.OnLine B lineCK) := by
    intro hBlineCK

    have hEq :
        lineCK = chord :=
      HilbertPlaneIncidence.line_unique
        K B
        hKB
        lineCK chord
        hKlineCK
        hBlineCK
        hKchord
        hBchord

    have hCchord :
        H.OnLine C chord := by
      rw [← hEq]
      exact hClineCK

    exact hCoff hCchord

  have hOppAB_CK :
      HilbertOppositeSide Geo A B lineCK :=
    ⟨hAoffCK,
      hBoffCK,
      ⟨K, hAKB, hKlineCK⟩⟩

  have hNotSameAB_CK :
      Not (HilbertSameSide Geo A B lineCK) :=
    hilbert_oppositeSide_not_sameSide
      Geo
      A B
      lineCK
      hOppAB_CK

  --------------------------------------------------------------------
  -- B and X are off CP.  Since B-P-X, they are opposite sides of CP.
  --------------------------------------------------------------------

  have hBoffCP :
      Not (H.OnLine B lineCP) := by
    intro hBlineCP

    have hXlineCP :
        H.OnLine X lineCP :=
      hilbert_collinear_on_line
        Geo
        B P X
        lineCP
        hBP
        hBlineCP
        hPlineCP
        hBPXcol

    exact
      hBCX
        ⟨lineCP,
          hBlineCP,
          hClineCP,
          hXlineCP⟩

  have hXoffCP :
      Not (H.OnLine X lineCP) := by
    intro hXlineCP

    have hPXcol :
        PrimCollinear Geo P X B :=
      PrimCollinearCycle
        Geo B P X hBPXcol

    have hBlineCP :
        H.OnLine B lineCP :=
      hilbert_collinear_on_line
        Geo
        P X B
        lineCP
        hPX
        hPlineCP
        hXlineCP
        hPXcol

    exact hBoffCP hBlineCP

  have hXPB :
      Geo.Between X P B :=
    hBPXdata.2.2.2.2

  have hOppXB_CP :
      HilbertOppositeSide Geo X B lineCP :=
    ⟨hXoffCP,
      hBoffCP,
      ⟨P, hXPB, hPlineCP⟩⟩

  have hNotSameXB_CP :
      Not (HilbertSameSide Geo X B lineCP) :=
    hilbert_oppositeSide_not_sameSide
      Geo
      X B
      lineCP
      hOppXB_CP

  have hSideConfiguration :
      HilbertSameSide Geo A B lineCK ↔
      HilbertSameSide Geo X B lineCP := by
    constructor
    · intro hSame
      exact False.elim (hNotSameAB_CK hSame)
    · intro hSame
      exact False.elim (hNotSameXB_CP hSame)

  --------------------------------------------------------------------
  -- Match the two component angles.
  --
  -- First component:
  --
  --   ACK ~= XCP.
  --------------------------------------------------------------------

  have hKCA_PCX :
      Geo.AngleCongruent
        K C A
        P C X :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K C A
      B A C
      P C X
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        B A C
        K C A
        hBAC_KCA)
      hBAC_PCX

  have hACK_XCP :
      Geo.AngleCongruent
        A C K
        X C P :=
    (Geo.angle_congruent_reverse_second
      A C K
      P C X).mp
      ((Geo.angle_congruent_reverse_first
        K C A
        P C X).mp
        hKCA_PCX)

  --------------------------------------------------------------------
  -- Second component:
  --
  --   KCB ~= PCB.
  --------------------------------------------------------------------

  have hKCB_BCP :
      Geo.AngleCongruent
        K C B
        B C P :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      K C B
      A B C
      B C P
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        A B C
        K C B
        hABC_KCB)
      hABC_BCP

  have hKCB_PCB :
      Geo.AngleCongruent
        K C B
        P C B :=
    (Geo.angle_congruent_reverse_second
      K C B
      B C P).mp
      hKCB_BCP

  --------------------------------------------------------------------
  -- Add corresponding angle parts.
  --------------------------------------------------------------------

  have hACB_XCB :
      Geo.AngleCongruent
        A C B
        X C B :=
    hilbert_angle_addition
      Geo
      A C K B
      X C P B
      lineCK lineCP
      (hilbert_circle_center_ne_point_of_two_distinct
        Geo
        K R A B C
        hAB
        hAcircle
        hBcircle
        hCcircle).symm
      hCP
      hClineCK
      hKlineCK
      hClineCP
      hPlineCP
      hAoffCK
      hBoffCK
      hXoffCP
      hBoffCP
      hSideConfiguration
      hACB
      hXCB
      hACK_XCP
      hKCB_PCB

  have hACB_BCX :
      Geo.AngleCongruent
        A C B
        B C X :=
    (Geo.angle_congruent_reverse_second
      A C B
      X C B).mp
      hACB_XCB

  exact
    ⟨X, hACX, hACB_BCX⟩

theorem hilbert_IV13_diameter_right_angle
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV13DiameterRightAngle (Geo := Geo) :=
  hilbert_forder_IV13_diameter_right_angle_stage17 Geo

end Geometry

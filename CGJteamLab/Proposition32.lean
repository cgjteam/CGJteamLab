import CGJteamLab.Proposition31
import CGJteamLab.Proposition29

namespace Geometry

universe u

variable {Geo : Geometry.Geo.{u}}

def HilbertExteriorAngleEqualsRemoteAngles
    [HilbertIncidence Geo]
    (A B C D : Geo.Point) : Prop :=
  exists R : Geo.Point,
    Geo.Between A R D /\
    Geo.AngleCongruent B A C A C R /\
    Geo.AngleCongruent A B C R C D

def HilbertTriangleAnglesEqualTwoRightAngles
    [HilbertIncidence Geo]
    (A B C : Geo.Point) : Prop :=
  exists D : Geo.Point,
    Geo.Between B C D /\
    HilbertExteriorAngleEqualsRemoteAngles
      A B C D

/--
Euclid I.32, exterior-angle part.

If ABC is a nondegenerate triangle and BC is extended through C
to D, then the exterior angle ACD is equal to the two remote
interior angles BAC and ABC taken together.

The equality is represented synthetically by a point R inside AD
whose ray CR decomposes the exterior angle.
-/
theorem euclid_proposition_32_exterior
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hBCD : Geo.Between B C D) :
    HilbertExteriorAngleEqualsRemoteAngles
      A B C D := by

  have hAB : Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hACBnc :
      Not (PrimCollinear Geo A C B) := by
    intro h
    exact hABC
      (PrimCollinearRotate Geo A C B h)

  have hAC : Not (A = C) :=
    hilbert_noncollinear_ne_first
      Geo A C B hACBnc

  have hBCAnc :
      Not (PrimCollinear Geo B C A) := by
    intro h
    have hACB :
        PrimCollinear Geo A C B :=
      PrimCollinearSymm Geo B C A h
    exact hABC
      (PrimCollinearRotate Geo A C B hACB)

  have hBC : Not (B = C) :=
    hilbert_noncollinear_ne_first
      Geo B C A hBCAnc

  ------------------------------------------------------------
  -- Use the established exterior-angle auxiliary configuration.
  --
  -- A-M-C
  -- B-M-E
  -- angle BAC ~= angle MCE
  ------------------------------------------------------------

  rcases
      hilbert_exterior_angle_aux
        Geo A B C hABC with
    ⟨M, E,
      hAMC,
      hAMMC,
      hBME,
      hBMME,
      hBAC_MCE⟩

  ------------------------------------------------------------
  -- The auxiliary construction gives AB || CE.
  ------------------------------------------------------------

  have hParallel :
      Geo.Parallel A B C E :=
    hilbert_exterior_angle_aux_parallel
      Geo
      A B C M E
      hABC
      hAMC
      hBME
      hBAC_MCE

  ------------------------------------------------------------
  -- The correctly oriented ray CE meets the open segment AD.
  ------------------------------------------------------------

  have hInside :
      HilbertRayMeetsSegment Geo C E A D :=
    hilbert_exterior_angle_inside
      Geo
      A B C D M E
      hABC
      hAMC
      hBME
      hBCD
      hParallel

  rcases hInside with
    ⟨R, hARD, hRayCER⟩

  ------------------------------------------------------------
  -- From A-M-C, M and A determine the same ray from C.
  ------------------------------------------------------------

  have hCMA :
      Geo.Between C M A :=
    (HilbertOrder.between_incidence
      A M C hAMC).2.2.2.2

  have hRayCMA :
      HilbertSameRay Geo C M A :=
    hilbert_sameRay_of_between
      Geo C M A hCMA

  ------------------------------------------------------------
  -- Replace M by A and E by R in the first angle congruence.
  ------------------------------------------------------------

  have hMCE_ACE :
      Geo.Angle M C E =
      Geo.Angle A C E :=
    hilbert_angle_eq_of_sameRay_first
      Geo C M A E hRayCMA

  have hACE_ACR :
      Geo.Angle A C E =
      Geo.Angle A C R :=
    hilbert_angle_eq_of_sameRay_second
      Geo C A E R hRayCER

  have hFirst :
      Geo.AngleCongruent B A C A C R := by
    unfold Geometry.Geo.AngleCongruent at hBAC_MCE ⊢
    rw [hMCE_ACE, hACE_ACR] at hBAC_MCE
    exact hBAC_MCE

  ------------------------------------------------------------
  -- Prepare the transversal BD.
  ------------------------------------------------------------

  have hBCDdata :=
    HilbertOrder.between_incidence
      B C D hBCD

  have hBD :
      Not (B = D) :=
    hBCDdata.2.2.1

  have hBCDcol :
      PrimCollinear Geo B C D :=
    hBCDdata.2.2.2.1

  have hADBnc :
      Not (PrimCollinear Geo A D B) := by
    intro hADB

    have hABD :
        PrimCollinear Geo A B D :=
      PrimCollinearRotate
        Geo A D B hADB

    have hBDC :
        PrimCollinear Geo B D C :=
      PrimCollinearRotate
        Geo B C D hBCDcol

    have hABC' :
        PrimCollinear Geo A B C :=
      hilbert_primCollinear_trans
        Geo
        A B D C
        hBD
        hABD
        hBDC

    exact hABC hABC'

  ------------------------------------------------------------
  -- Since A-R-D, A and R lie on the same side of BD.
  ------------------------------------------------------------

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        A R B D
        hARD
        hADBnc with
    ⟨lineBD,
      hBlineBD,
      hDlineBD,
      hSameAR⟩

  ------------------------------------------------------------
  -- Extend AB beyond B:
  --
  --   A - B - X
  ------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        A B hAB with
    ⟨X, hABX⟩

  have hABXdata :=
    HilbertOrder.between_incidence
      A B X hABX

  have hAX :
      Not (A = X) :=
    hABXdata.2.2.1

  have hABXcol :
      PrimCollinear Geo A B X :=
    hABXdata.2.2.2.1

  have hAXBcol :
      PrimCollinear Geo A X B :=
    PrimCollinearRotate
      Geo A B X hABXcol

  ------------------------------------------------------------
  -- Extend EC beyond C:
  --
  --   E - C - F
  ------------------------------------------------------------

  have hEC :
      Not (E = C) :=
    hParallel.2.1.symm

  rcases
      HilbertOrder.between_extension
        E C hEC with
    ⟨F, hECF⟩

  have hECFdata :=
    HilbertOrder.between_incidence
      E C F hECF

  have hCF :
      Not (C = F) :=
    hECFdata.2.1

  have hEF :
      Not (E = F) :=
    hECFdata.2.2.1

  have hECFcol :
      PrimCollinear Geo E C F :=
    hECFdata.2.2.2.1

  have hEFCcol :
      PrimCollinear Geo E F C :=
    PrimCollinearRotate
      Geo E C F hECFcol

  have hCFEcol :
      PrimCollinear Geo C F E :=
    PrimCollinearSymm
      Geo E F C hEFCcol

  have hECFcol' :
      PrimCollinear Geo E C F :=
    hECFcol

  ------------------------------------------------------------
  -- Transport AB || CE to AX || EF.
  ------------------------------------------------------------

  have hAX_CE :
      Geo.Parallel A X C E :=
    collinear_parallel_trans
      Geo
      A X B C E
      hAX
      hAXBcol
      hParallel

  have hCE_AX :
      Geo.Parallel C E A X :=
    ParallelSymmetry
      Geo A X C E hAX_CE

  have hCF_AX :
      Geo.Parallel C F A X :=
    collinear_parallel_trans
      Geo
      C F E A X
      hCF
      hCFEcol
      hCE_AX

  have hEF_AX :
      Geo.Parallel E F A X :=
    ParallelCollinearLeft
      Geo
      C F E A X
      hEF
      hCF_AX
      hECFcol'

  have hAX_EF :
      Geo.Parallel A X E F :=
    ParallelSymmetry
      Geo E F A X hEF_AX

  ------------------------------------------------------------
  -- Since R is on the same ray from C as E, and E-C-F,
  -- we obtain R-C-F.
  ------------------------------------------------------------

  have hCFF :
      HilbertSameRay Geo C F F :=
    hilbert_sameRay_refl
      Geo C F (Ne.symm hCF)

  have hRCF :
      Geo.Between R C F :=
    hilbert_between_transport_sameRays
      Geo
      E C F
      R F
      hECF
      hRayCER
      hCFF

  have hClineBD :
      HilbertIncidence.OnLine C lineBD :=
    hilbert_between_on_line
      Geo B C D lineBD
      hBlineBD
      hDlineBD
      hBCD

  have hRoff :
      Not (HilbertIncidence.OnLine R lineBD) :=
    hSameAR.2.1

  have hFoff :
      Not (HilbertIncidence.OnLine F lineBD) := by
    intro hFline

    have hRCFdata :=
      HilbertOrder.between_incidence
        R C F hRCF

    have hRCFcol :
        PrimCollinear Geo R C F :=
      hRCFdata.2.2.2.1

    have hCFR :
        PrimCollinear Geo C F R :=
      PrimCollinearCycle
        Geo R C F hRCFcol

    have hRline :
        HilbertIncidence.OnLine R lineBD :=
      hilbert_collinear_on_line
        Geo C F R lineBD
        hCF
        hClineBD
        hFline
        hCFR

    exact hRoff hRline

  have hOppRF :
      HilbertOppositeSide Geo R F lineBD :=
    ⟨hRoff,
      hFoff,
      ⟨C, hRCF, hClineBD⟩⟩

  ------------------------------------------------------------
  -- Transport the opposite-side relation from R to A.
  ------------------------------------------------------------

  have hOppFR :
      HilbertOppositeSide Geo F R lineBD :=
    hilbert_oppositeSide_symm
      Geo R F lineBD hOppRF

  have hSameRA :
      HilbertSameSide Geo R A lineBD :=
    hilbert_sameSide_symm
      Geo A R lineBD hSameAR

  have hOppFA :
      HilbertOppositeSide Geo F A lineBD :=
    hilbert_oppositeSide_transport_right
      Geo
      F R A
      lineBD
      hOppFR
      hSameRA

  have hOppAF :
      HilbertOppositeSide Geo A F lineBD :=
    hilbert_oppositeSide_symm
      Geo F A lineBD hOppFA

  ------------------------------------------------------------
  -- Ready for Proposition I.29.
  ------------------------------------------------------------

  ------------------------------------------------------------
  -- Proposition I.29:
  --
  --   A-B-X
  --   E-C-F
  --   AX || EF
  --
  -- with BD as transversal.
  ------------------------------------------------------------

  have hABC_BCF :
      Geo.AngleCongruent A B C B C F :=
    euclid_proposition_29_transversal
      (Geo := Geo)
      A X E F B C
      lineBD
      hABX
      hECF
      hBC
      hBlineBD
      hClineBD
      hOppAF
      hAX_EF

  ------------------------------------------------------------
  -- B-C-D and E-C-F give vertical angles at C.
  ------------------------------------------------------------

  have hFCE :
      Geo.Between F C E :=
    (HilbertOrder.between_incidence
      E C F hECF).2.2.2.2

  have hBCFnc :
      Not (Collinear Geo B C F) := by
    intro hBCF

    have hFlineBD :
        HilbertIncidence.OnLine F lineBD :=
      hilbert_collinear_on_line
        Geo
        B C F
        lineBD
        hBC
        hBlineBD
        hClineBD
        hBCF

    exact hFoff hFlineBD

  have hVerticalRaw :
      Geo.AngleCongruent B C F D C E :=
    VerticalAngles
      Geo
      B C F
      D E
      hBCD
      hFCE
      hBCFnc

  have hBCF_ECD :
      Geo.AngleCongruent B C F E C D :=
    (Geo.angle_congruent_reverse_second
      B C F D C E).mp
      hVerticalRaw

  ------------------------------------------------------------
  -- Combine I.29 with the vertical-angle theorem.
  ------------------------------------------------------------

  have hABC_ECD :
      Geo.AngleCongruent A B C E C D :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A B C
      B C F
      E C D
      hABC_BCF
      hBCF_ECD

  ------------------------------------------------------------
  -- E and R lie on the same ray from C.
  ------------------------------------------------------------

  have hECD_RCD :
      Geo.Angle E C D =
      Geo.Angle R C D :=
    hilbert_angle_eq_of_sameRay_first
      Geo C E R D hRayCER

  have hSecond :
      Geo.AngleCongruent A B C R C D := by
    unfold Geometry.Geo.AngleCongruent at hABC_ECD ⊢
    rw [hECD_RCD] at hABC_ECD
    exact hABC_ECD

  ------------------------------------------------------------
  -- Exterior-angle part of I.32 complete.
  ------------------------------------------------------------

  exact
    ⟨R, hARD, hFirst, hSecond⟩


/--
Euclid I.32, triangle-angle-sum part.

The three interior angles of a nondegenerate triangle are together
equal to two right angles.

Synthetically, extend BC through C to D.  The exterior angle ACD is
decomposed into the two remote interior angles BAC and ABC, while
ACD is supplementary to ACB.
-/
theorem euclid_proposition_32
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    HilbertTriangleAnglesEqualTwoRightAngles
      A B C := by

  have hBCAnc :
      Not (PrimCollinear Geo B C A) := by
    intro h

    have hACB :
        PrimCollinear Geo A C B :=
      PrimCollinearSymm
        Geo B C A h

    exact hABC
      (PrimCollinearRotate
        Geo A C B hACB)

  have hBC :
      Not (B = C) :=
    hilbert_noncollinear_ne_first
      Geo B C A hBCAnc

  rcases
      HilbertOrder.between_extension
        B C hBC with
    ⟨D, hBCD⟩

  have hExterior :
      HilbertExteriorAngleEqualsRemoteAngles
        A B C D :=
    euclid_proposition_32_exterior
      (Geo := Geo)
      A B C D
      hABC
      hBCD

  exact
    ⟨D, hBCD, hExterior⟩






end Geometry

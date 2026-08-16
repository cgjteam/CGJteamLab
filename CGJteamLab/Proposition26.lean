import CGJteamLab.HilbertBookZero
import CGJteamLab.Proposition16

namespace Geometry

variable (Geo : Geometry.Geo)

variable [HilbertIncidence Geo]
variable [HilbertCongruence Geo]

theorem euclid_proposition_26_asa
    (A B C D E F : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hDEF : ¬ PrimCollinear Geo D E F)
    (hAngleB : Geo.AngleCongruent A B C D E F)
    (hAngleC : Geo.AngleCongruent B C A E F D)
    (hBC : Geo.Congruent B C E F) :
    Geo.Congruent A B D E ∧
    Geo.Congruent A C D F ∧
    Geo.AngleCongruent B A C E D F := by

  have hBCA : ¬ PrimCollinear Geo B C A := by
    intro h
    have hCAB : PrimCollinear Geo C A B :=
      PrimCollinearCycle Geo B C A h
    have hABC' : PrimCollinear Geo A B C :=
      PrimCollinearCycle Geo C A B hCAB
    exact hABC hABC'

  have hEFD : ¬ PrimCollinear Geo E F D := by
    intro h
    have hFDE : PrimCollinear Geo F D E :=
      PrimCollinearCycle Geo E F D h
    have hDEF' : PrimCollinear Geo D E F :=
      PrimCollinearCycle Geo F D E hFDE
    exact hDEF hDEF'

  have hAngleB' :
      Geo.AngleCongruent C B A F E D :=
    (Geo.angle_congruent_reverse_second
      C B A D E F).mp
      ((Geo.angle_congruent_reverse_first
        A B C D E F).mp hAngleB)

  have hASA :=
    hilbert_asa_sides
      Geo
      B C A
      E F D
      hBCA
      hEFD
      hBC
      hAngleB'
      hAngleC

  have hAB :
      Geo.Congruent A B D E :=
    (Geo.congruent_reverse_second
      A B E D).mp
      ((Geo.congruent_reverse_first
        B A E D).mp hASA.1)

  have hAC :
      Geo.Congruent A C D F :=
    (Geo.congruent_reverse_second
      A C F D).mp
      ((Geo.congruent_reverse_first
        C A F D).mp hASA.2)

  have hSSS :=
    HilbertSSS
      Geo
      A B C
      D E F
      hABC
      hAB
      hBC
      hAC

  exact
    ⟨hAB, hAC, hSSS.2.angleA⟩


theorem euclid_proposition_26_saa_not_less
    (A B C D E F : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hDEF : ¬ PrimCollinear Geo D E F)
    (hAngleB : Geo.AngleCongruent A B C D E F)
    (hAngleC : Geo.AngleCongruent B C A E F D)
    (hAB : Geo.Congruent A B D E) :
    ¬ HilbertSegmentLess Geo E F B C := by

  intro hEF_BC

  rcases hEF_BC with
    ⟨H, hBHC, hEF_BH⟩

  have hBHCdata :=
    HilbertOrder.between_incidence
      B H C hBHC

  have hBH : B ≠ H :=
    hBHCdata.1

  have hHC : H ≠ C :=
    hBHCdata.2.1

  have hBHCcol :
      PrimCollinear Geo B H C :=
    hBHCdata.2.2.2.1

  --------------------------------------------------------------------
  -- Since B-H-C, rays BH and BC coincide.
  --------------------------------------------------------------------

  have hRayBHC :
      HilbertSameRay Geo B H C :=
    hilbert_sameRay_of_between
      Geo B H C hBHC

  have hAngleABH_eq_ABC :
      Geo.Angle A B H =
      Geo.Angle A B C :=
    hilbert_angle_eq_of_sameRay_second
      Geo B A H C hRayBHC

  have hAngleABH :
      Geo.AngleCongruent A B H D E F := by
    unfold Geometry.Geo.AngleCongruent at hAngleB ⊢
    rw [hAngleABH_eq_ABC]
    exact hAngleB

  --------------------------------------------------------------------
  -- Triangle BAH is noncollinear.
  --------------------------------------------------------------------

  have hBAH :
      ¬ PrimCollinear Geo B A H := by
    intro hBAHcol

    have hABH :
        PrimCollinear Geo A B H :=
      PrimCollinearSwap
        Geo B A H hBAHcol

    have hABC' :
        PrimCollinear Geo A B C :=
      hilbert_primCollinear_trans
        Geo
        A B H C
        hBH
        hABH
        hBHCcol

    exact hABC hABC'

  have hEDF :
      ¬ PrimCollinear Geo E D F := by
    intro h
    exact hDEF
      (PrimCollinearSwap Geo E D F h)

  --------------------------------------------------------------------
  -- Corresponding sides for SAS:
  --
  -- BA ~= ED
  -- BH ~= EF
  --------------------------------------------------------------------

  have hBA :
      Geo.Congruent B A E D :=
    (Geo.congruent_reverse_second
      B A D E).mp
      ((Geo.congruent_reverse_first
        A B D E).mp hAB)

  have hBH_EF :
      Geo.Congruent B H E F :=
    hilbert_congruent_symmetry
      Geo E F B H hEF_BH

  --------------------------------------------------------------------
  -- SAS on BAH and EDF.
  --------------------------------------------------------------------

  have hSAS :=
    SAS
      Geo
      B A H
      E D F
      hBAH
      hEDF
      hBA
      hAngleABH
      hBH_EF

  have hBHA_EFD :
      Geo.AngleCongruent B H A E F D :=
    hSAS.angleC

  --------------------------------------------------------------------
  -- Hence angle BHA ~= angle BCA.
  --------------------------------------------------------------------

  have hEFD_BCA :
      Geo.AngleCongruent E F D B C A :=
    Geo.angle_congruent_symmetry
      B C A
      E F D
      hAngleC

  have hBHA_BCA :
      Geo.AngleCongruent B H A B C A :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B H A
      E F D
      B C A
      hBHA_EFD
      hEFD_BCA

  --------------------------------------------------------------------
  -- For triangle ACH, C-H-B is an extension.
  --------------------------------------------------------------------

  have hCHB :
      Geo.Between C H B :=
    hBHCdata.2.2.2.2

  have hCHBcol :
      PrimCollinear Geo C H B :=
    PrimCollinearSymm
      Geo B H C hBHCcol

  have hACH :
      ¬ PrimCollinear Geo A C H := by
    intro hACHcol

    have hACB :
        PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo
        A C H B
        hHC.symm
        hACHcol
        hCHBcol

    exact hABC
      (PrimCollinearRotate Geo A C B hACB)

  --------------------------------------------------------------------
  -- I.16:
  --
  -- angle ACH < angle AHB.
  --------------------------------------------------------------------

  have hLess :
      HilbertAngleLess Geo A C H A H B :=
    euclid_proposition_16_second
      Geo
      A C H B
      hACH
      hCHB

  --------------------------------------------------------------------
  -- Since C-H-B, rays CH and CB coincide.
  -- Thus angle ACH is the same angle as ACB.
  --------------------------------------------------------------------

  have hRayCHB :
      HilbertSameRay Geo C H B :=
    hilbert_sameRay_of_between
      Geo C H B hCHB

  have hACH_eq_ACB :
      Geo.Angle A C H =
      Geo.Angle A C B :=
    hilbert_angle_eq_of_sameRay_second
      Geo C A H B hRayCHB

  --------------------------------------------------------------------
  -- Required noncollinear orientations.
  --------------------------------------------------------------------

  have hBCA :
      ¬ PrimCollinear Geo B C A := by
    intro h
    have hCAB :
        PrimCollinear Geo C A B :=
      PrimCollinearCycle Geo B C A h
    have hABC' :
        PrimCollinear Geo A B C :=
      PrimCollinearCycle Geo C A B hCAB
    exact hABC hABC'

  have hBHA :
      ¬ PrimCollinear Geo B H A := by
    intro h
    exact hBAH
      (PrimCollinearRotate Geo B H A h)

  --------------------------------------------------------------------
  -- BCA ~= ACH.
  --------------------------------------------------------------------

  have hReflACB :
      Geo.AngleCongruent A C B A C B :=
    Geometry.Geo.angle_congruent_reflexive
      Geo A C B

  have hBCA_ACB :
      Geo.AngleCongruent B C A A C B :=
    (Geo.angle_congruent_reverse_first
      A C B A C B).mp
      hReflACB

  have hBCA_ACH :
      Geo.AngleCongruent B C A A C H := by
    unfold Geometry.Geo.AngleCongruent at hBCA_ACB ⊢
    rw [hACH_eq_ACB]
    exact hBCA_ACB

  --------------------------------------------------------------------
  -- Transport I.16 from ACH to BCA:
  --
  -- angle BCA < angle AHB.
  --------------------------------------------------------------------

  have hLessBCA :
      HilbertAngleLess Geo B C A A H B :=
    hilbert_angleLess_transport_left
      Geo
      A C H
      B C A
      A H B
      hLess
      hBCA
      hBCA_ACH

  --------------------------------------------------------------------
  -- Since BHA ~= BCA:
  --
  -- angle BHA < angle AHB.
  --------------------------------------------------------------------

  have hLessBHA :
      HilbertAngleLess Geo B H A A H B :=
    hilbert_angleLess_transport_left
      Geo
      B C A
      B H A
      A H B
      hLessBCA
      hBHA
      hBHA_BCA

  --------------------------------------------------------------------
  -- But AHB and BHA are the same unoriented angle.
  --------------------------------------------------------------------

  have hReflAHB :
      Geo.AngleCongruent A H B A H B :=
    Geometry.Geo.angle_congruent_reflexive
      Geo A H B

  have hBHA_AHB :
      Geo.AngleCongruent B H A A H B :=
    (Geo.angle_congruent_reverse_first
      A H B A H B).mp
      hReflAHB

  have hAHB_BHA :
      Geo.AngleCongruent A H B B H A :=
    Geo.angle_congruent_symmetry
      B H A
      A H B
      hBHA_AHB

  have hLessFinal :
      HilbertAngleLess Geo B H A B H A :=
    hilbert_angleLess_transport_right
      Geo
      B H A
      A H B
      B H A
      hLessBHA
      hBHA
      hAHB_BHA

  exact
    (hilbert_angleLess_irrefl
      Geo B H A)
      hLessFinal

theorem euclid_proposition_26_saa
    (A B C D E F : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hDEF : ¬ PrimCollinear Geo D E F)
    (hAngleB : Geo.AngleCongruent A B C D E F)
    (hAngleC : Geo.AngleCongruent B C A E F D)
    (hAB : Geo.Congruent A B D E) :
    Geo.Congruent B C E F ∧
    Geo.Congruent A C D F ∧
    Geo.AngleCongruent B A C E D F := by

  --------------------------------------------------------------------
  -- First direction:
  --
  -- EF is not shorter than BC.
  --------------------------------------------------------------------

  have hNotEF_BC :
      ¬ HilbertSegmentLess Geo E F B C :=
    euclid_proposition_26_saa_not_less
      Geo
      A B C
      D E F
      hABC
      hDEF
      hAngleB
      hAngleC
      hAB

  --------------------------------------------------------------------
  -- Reverse the two triangles and apply the same helper:
  --
  -- BC is not shorter than EF.
  --------------------------------------------------------------------

  have hAngleB' :
      Geo.AngleCongruent D E F A B C :=
    Geo.angle_congruent_symmetry
      A B C
      D E F
      hAngleB

  have hAngleC' :
      Geo.AngleCongruent E F D B C A :=
    Geo.angle_congruent_symmetry
      B C A
      E F D
      hAngleC

  have hDE_AB :
      Geo.Congruent D E A B :=
    hilbert_congruent_symmetry
      Geo A B D E hAB

  have hNotBC_EF :
      ¬ HilbertSegmentLess Geo B C E F :=
    euclid_proposition_26_saa_not_less
      Geo
      D E F
      A B C
      hDEF
      hABC
      hAngleB'
      hAngleC'
      hDE_AB

  --------------------------------------------------------------------
  -- Both segments are non-null.
  --------------------------------------------------------------------

  have hBCne : B ≠ C :=
    (bookZero_26_NCdistinct
      Geo A B C hABC).2.1

  have hEFne : E ≠ F :=
    (bookZero_26_NCdistinct
      Geo D E F hDEF).2.1

  --------------------------------------------------------------------
  -- Book Zero trichotomy:
  --
  -- if neither segment is shorter than the other,
  -- they are congruent.
  --------------------------------------------------------------------

  have hBC :
      Geo.Congruent B C E F :=
    bookZero_31_trichotomy1
      Geo
      B C
      E F
      hNotBC_EF
      hNotEF_BC
      hBCne
      hEFne

  --------------------------------------------------------------------
  -- Once BC ~= EF is known, the situation is exactly the ASA case
  -- already proved above.
  --------------------------------------------------------------------

  have hASA :=
    euclid_proposition_26_asa
      Geo
      A B C
      D E F
      hABC
      hDEF
      hAngleB
      hAngleC
      hBC

  exact
    ⟨hBC, hASA.2.1, hASA.2.2⟩

end Geometry

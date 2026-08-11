import CGJteamLab.Proposition19

namespace Geometry

variable (Geo : Geometry.Geo)

theorem euclid_proposition_20
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C) :
    ∃ D : Geo.Point,
      Geo.Between B A D ∧
      Geo.Congruent A D A C ∧
      HilbertSegmentLess Geo B C B D := by

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hBA : B ≠ A :=
    hAB.symm

  rcases
      HilbertOrder.between_extension
        B A hBA with
    ⟨R, hBAR⟩

  have hAR : A ≠ R :=
    (HilbertOrder.between_incidence
      B A R hBAR).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        A C
        A R
        hAR with
    ⟨D, hRayARD, hAD_AC⟩

  have hRayABA :
      HilbertSameRay Geo A B B :=
    hilbert_sameRay_refl
      Geo A B hBA

  have hBAD :
      Geo.Between B A D :=
    hilbert_between_transport_sameRays
      Geo
      B A R
      B D
      hBAR
      hRayABA
      hRayARD

  refine ⟨D, hBAD, hAD_AC, ?_⟩

  have hBADdata :=
    HilbertOrder.between_incidence
      B A D hBAD

  have hAD : A ≠ D :=
    hBADdata.2.1

  have hBD : B ≠ D :=
    hBADdata.2.2.1

  have hBADcol :
      PrimCollinear Geo B A D :=
    hBADdata.2.2.2.1

  ------------------------------------------------------------
  -- A-B-D
  ------------------------------------------------------------

  have hADB :
      PrimCollinear Geo A D B :=
    PrimCollinearCycle
      Geo B A D hBADcol

  have hABD :
      PrimCollinear Geo A B D :=
    PrimCollinearRotate
      Geo A D B hADB

  ------------------------------------------------------------
  -- Triangle BCD is noncollinear.
  ------------------------------------------------------------

  have hBCD :
      ¬ PrimCollinear Geo B C D := by
    intro hBCDcol

    have hBDC :
        PrimCollinear Geo B D C :=
      PrimCollinearRotate
        Geo B C D hBCDcol

    have hABCcol :
        PrimCollinear Geo A B C :=
      hilbert_primCollinear_trans
        Geo
        A B D C
        hBD
        hABD
        hBDC

    exact hABC hABCcol

  ------------------------------------------------------------
  -- Triangle ACD is noncollinear.
  ------------------------------------------------------------

  have hACD :
      ¬ PrimCollinear Geo A C D := by
    intro hACDcol

    have hADC :
        PrimCollinear Geo A D C :=
      PrimCollinearRotate
        Geo A C D hACDcol

    have hBAC :
        PrimCollinear Geo B A C :=
      hilbert_primCollinear_trans
        Geo
        B A D C
        hAD
        hBADcol
        hADC

    have hCAB :
        PrimCollinear Geo C A B :=
      PrimCollinearSymm
        Geo B A C hBAC

    have hABCcol :
        PrimCollinear Geo A B C :=
      PrimCollinearCycle
        Geo C A B hCAB

    exact hABC hABCcol

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (by
        intro h
        exact hABC
          (PrimCollinearRotate Geo A C B h))

  have hDCB :
      ¬ PrimCollinear Geo D C B := by
    intro h
    exact hBCD
      (PrimCollinearSymm Geo D C B h)

  have hDAB :
      Geo.Between D A B :=
    (HilbertOrder.between_incidence
      B A D hBAD).2.2.2.2

  have hRayCAA :
      HilbertSameRay Geo C A A :=
    hilbert_sameRay_refl
      Geo C A hAC

  have hInside :
      HilbertRayMeetsSegment Geo C A D B :=
    ⟨A, hDAB, hRayCAA⟩

  have hAngleRefl :
      Geo.AngleCongruent A C D A C D :=
    Geometry.Geo.angle_congruent_reflexive
      Geo A C D

  have hAngleSwap :
      Geo.AngleCongruent A C D D C A :=
    (Geo.angle_congruent_reverse_second
      A C D
      A C D).mp
      hAngleRefl

  have hLessACD_DCB :
      HilbertAngleLess Geo A C D D C B :=
    hilbert_angleLess_intro
      Geo
      A C D
      D C B
      A
      hACD
      hDCB
      hInside
      hAngleSwap

  have hADC :
      ¬ PrimCollinear Geo A D C := by
    intro h
    exact hACD
      (PrimCollinearRotate Geo A D C h)

  have hIso :
      Geo.AngleCongruent A D C A C D :=
    hilbert_isosceles_base_angles
      Geo
      A D C
      hADC
      hAD_AC

  have hLessADC_DCB :
      HilbertAngleLess Geo A D C D C B :=
    hilbert_angleLess_transport_left
      Geo
      A C D
      A D C
      D C B
      hLessACD_DCB
      hADC
      hIso

  have hDAB :
      Geo.Between D A B :=
    (HilbertOrder.between_incidence
      B A D hBAD).2.2.2.2

  have hRayDAB :
      HilbertSameRay Geo D A B :=
    hilbert_sameRay_of_between
      Geo D A B hDAB

  have hRayDBA :
      HilbertSameRay Geo D B A :=
    hilbert_sameRay_symm
      Geo D A B hRayDAB

  have hBDC :
      ¬ PrimCollinear Geo B D C := by
    intro h
    exact hBCD
      (PrimCollinearRotate Geo B D C h)

  have hBDC_ACD :
      Geo.AngleCongruent B D C A C D := by
    unfold Geometry.Geo.AngleCongruent at hIso ⊢
    rw [hilbert_angle_eq_of_sameRay_first
      Geo D B A C hRayDBA]
    exact hIso

  have hLessBDC_DCB :
      HilbertAngleLess Geo B D C D C B :=
    hilbert_angleLess_transport_left
      Geo
      A C D
      B D C
      D C B
      hLessACD_DCB
      hBDC
      hBDC_ACD

  have hAngleReflDCB :
      Geo.AngleCongruent D C B D C B :=
    Geometry.Geo.angle_congruent_reflexive
      Geo D C B

  have hDCB_BCD :
      Geo.AngleCongruent D C B B C D :=
    (Geo.angle_congruent_reverse_second
      D C B
      D C B).mp
      hAngleReflDCB

  have hLessBDC_BCD :
      HilbertAngleLess Geo B D C B C D :=
    hilbert_angleLess_transport_right
      Geo
      B D C
      D C B
      B C D
      hLessBDC_DCB
      hBCD
      hDCB_BCD

  exact
    euclid_proposition_19
      Geo
      B C D
      hBCD
      hLessBDC_BCD


end Geometry

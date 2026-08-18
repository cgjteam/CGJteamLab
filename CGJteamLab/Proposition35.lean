import CGJteamLab.HilbertInterface


namespace Geometry

universe u

variable (Geo : Geometry.Geo)
variable [HilbertIncidence Geo]



theorem test_prop35_order_helper
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADF : Geo.Between A D F)
    (hAEF : Collinear Geo A E F) :
    ∃ Q : Geo.Point,
      Geo.Between B Q F ∧
      Geo.Between A Q C ∧
      Geo.Between A E F := by

  have hSides1 :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hABCD

  have hSides2 :
      OppositeSidesCongruent Geo E B C F :=
    ParallelogramOppositeSidesCongruent
      Geo E B C F hEBCF

  have hBC_DA :
      Geo.Congruent B C D A :=
    hSides1.2

  have hBC_FE :
      Geo.Congruent B C F E :=
    hSides2.2

  have hAD_BC :
      Geo.Congruent A D B C := by
    have hDA_BC :
        Geo.Congruent D A B C :=
      CongruentSymmetry
        Geo B C D A hBC_DA
    exact
      CongruentReverseFirst
        Geo D A B C hDA_BC

  have hEF_BC :
      Geo.Congruent E F B C := by
    have hFE_BC :
        Geo.Congruent F E B C :=
      CongruentSymmetry
        Geo B C F E hBC_FE
    exact
      CongruentReverseFirst
        Geo F E B C hFE_BC

  have hAD_EF :
      Geo.Congruent A D E F := by
    exact
      hilbert_congruent_transitivity
        Geo
        A D
        B C
        E F
        hAD_BC
        (CongruentSymmetry
          Geo E F B C hEF_BC)

  have hAB_CD :
      Geo.Parallel A B C D :=
    hABCD.1

  have hBC_DA :
      Geo.Parallel B C D A :=
    hABCD.2

  have hEB_CF :
      Geo.Parallel E B C F :=
    hEBCF.1

  have hBC_FE :
      Geo.Parallel B C F E :=
    hEBCF.2

  rcases
      ParallelogramDiagonalIntersectionExists
        Geo A B C D hABCD
    with
    ⟨M, hAMC, hBMD⟩
  rcases
      ParallelogramDiagonalIntersectionExists
        Geo E B C F hEBCF
    with
    ⟨N, hENC, hBNF⟩
  have hADB :
      ¬ Collinear Geo A D B := by
    intro hCol

    rcases hCol with
      ⟨lineAD, hAline, hDline, hBline⟩

    have hB_DA :
        B ∈ Geo.PointLine D A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D A B
        lineAD
        hBC_DA.2.1
        hDline
        hAline).mpr hBline

    have hB_BC :
        B ∈ Geo.PointLine B C := by
      change Geometry.Geo.LineCollinear Geo B C B
      exact Or.inr (Or.inl rfl)

    exact
      Set.disjoint_left.mp
        hBC_DA.2.2
        hB_BC
        hB_DA
  have hAF :
      A ≠ F :=
    (HilbertOrder.between_incidence
      A D F hADF).2.2.1

  have hDAF :
      Collinear Geo D A F :=
    PrimCollinearSwap
      Geo A D F
      (HilbertOrder.between_incidence
        A D F hADF).2.2.2.1

  have hAFB :
      ¬ Collinear Geo A F B := by
    intro hCol

    have hDAB :
        Collinear Geo D A B :=
      hilbert_primCollinear_trans
        Geo
        D A F B
        hAF
        hDAF
        hCol

    have hADB' :
        Collinear Geo A D B :=
      PrimCollinearSwap
        Geo D A B hDAB

    exact hADB hADB'

  rcases
      hilbert_outer_pasch
        Geo A B D F M
        hAFB hADF hBMD
    with
    ⟨Q, hBQF, hAMQ⟩

  have hAM :
      A ≠ M :=
    (HilbertOrder.between_incidence
      A M C hAMC).1

  have hAMQcol :
      Collinear Geo A M Q :=
    (HilbertOrder.between_incidence
      A M Q hAMQ).2.2.2.1

  have hAMCcol :
      Collinear Geo A M C :=
    (HilbertOrder.between_incidence
      A M C hAMC).2.2.2.1

  have hQAM :
      Collinear Geo Q A M :=
    PrimCollinearCycle
      Geo M Q A
      (PrimCollinearCycle
        Geo A M Q hAMQcol)

  have hQAC :
      Collinear Geo Q A C :=
    hilbert_primCollinear_trans
      Geo
      Q A M C
      hAM
      hQAM
      hAMCcol

  have hAQC :
      Collinear Geo A Q C :=
    PrimCollinearSwap
      Geo Q A C hQAC

  have hDA_BC :
      Geo.Parallel D A B C :=
    ParallelSymmetry
      Geo B C D A hBC_DA

  have hFA :
      F ≠ A :=
    (HilbertOrder.between_incidence
      A D F hADF).2.2.1.symm

  have hFDA :
      Collinear Geo F D A :=
    PrimCollinearSymm
      Geo A D F
      (HilbertOrder.between_incidence
        A D F hADF).2.2.2.1

  have hFA_BC :
      Geo.Parallel F A B C :=
    ParallelCollinearLeft
      Geo
      D A F B C
      hFA
      hDA_BC
      hFDA

  have hFA_CB :
      Geo.Parallel F A C B :=
    ParallelSwapSecondLine
      Geo F A B C hFA_BC

  have hFQB :
      Geo.Between F Q B :=
    (HilbertOrder.between_incidence
      B Q F hBQF).2.2.2.2

  have hACQ :
      Collinear Geo A C Q :=
    PrimCollinearRotate
      Geo A Q C hAQC

  have hAQCbetween :
      Geo.Between A Q C :=
    hilbert_collinear_between_of_parallel
      Geo
      F A C B Q
      hFA_CB
      hFQB
      hACQ

  have hCQA :
      Geo.Between C Q A :=
    (HilbertOrder.between_incidence
      A Q C hAQCbetween).2.2.2.2

  have hAE :
      A ≠ E := by
    intro hAEeq
    subst E

    have hAD_AF :
        Geo.Congruent A D A F := by
      simpa using hAD_EF

    exact
      (hilbert_part_not_congruent_whole
        Geo A D F hADF)
      hAD_AF

  have hNotAFE :
      ¬ Geo.Between A F E := by
    intro hAFE

    have hEFA :
        Geo.Between E F A :=
      (HilbertOrder.between_incidence
        A F E hAFE).2.2.2.2

    have hEAQ :
        ¬ Collinear Geo E A Q := by
      intro hEAQcol

      have hEAF :
          Collinear Geo E A F :=
        PrimCollinearSwap
          Geo A E F hAEF

      have hFAE :
          Collinear Geo F A E :=
        PrimCollinearSymm
          Geo E A F hEAF

      have hAEQ :
          Collinear Geo A E Q :=
        PrimCollinearSwap
          Geo E A Q hEAQcol

      have hFAQ :
          Collinear Geo F A Q :=
        hilbert_primCollinear_trans
          Geo
          F A E Q
          hAE
          hFAE
          hAEQ

      have hAQ :
          A ≠ Q :=
        (HilbertOrder.between_incidence
          A Q C hAQCbetween).1

      have hFAC :
          Collinear Geo F A C :=
        hilbert_primCollinear_trans
          Geo
          F A Q C
          hAQ
          hFAQ
          hAQC

      rcases hFAC with
        ⟨lineFAC, hFlineFAC, hAlineFAC, hClineFAC⟩

      have hC_FA :
          C ∈ Geo.PointLine F A :=
        (hilbert_mem_pointLine_iff_onLine
          Geo F A C lineFAC
          hFA
          hFlineFAC
          hAlineFAC).mpr hClineFAC

      have hCB :
          C ≠ B :=
        hFA_CB.2.1

      rcases
          HilbertPlaneIncidence.line_through
            C B hCB
        with
        ⟨lineCB, hClineCB, hBlineCB⟩

      have hC_CB :
          C ∈ Geo.PointLine C B :=
        (hilbert_mem_pointLine_iff_onLine
          Geo C B C lineCB
          hCB
          hClineCB
          hBlineCB).mpr hClineCB

      exact
        Set.disjoint_left.mp
          hFA_CB.2.2
          hC_FA
          hC_CB

    rcases
        hilbert_inner_pasch_strong
          Geo
          E A Q C F
          hEAQ
          hAQCbetween
          hEFA
      with
      ⟨r, hCrF, hErQ⟩

    have hFBE :
        ¬ Collinear Geo F B E := by
      intro hFBEcol

      have hEB :
          E ≠ B :=
        hEB_CF.1

      rcases
          HilbertPlaneIncidence.line_through
            E B hEB
        with
        ⟨lineEB, hElineEB, hBlineEB⟩

      have hEBF :
          Collinear Geo E B F :=
        PrimCollinearSwap
          Geo B E F
          (PrimCollinearCycle
            Geo F B E hFBEcol)

      have hFlineEB :
          HilbertIncidence.OnLine F lineEB :=
        hilbert_collinear_on_line
          Geo
          E B F
          lineEB
          hEB
          hElineEB
          hBlineEB
          hEBF

      have hCF :
          C ≠ F :=
        hEB_CF.2.1

      rcases
          HilbertPlaneIncidence.line_through
            C F hCF
        with
        ⟨lineCF, hClineCF, hFlineCF⟩

      have hF_EB :
          F ∈ Geo.PointLine E B :=
        (hilbert_mem_pointLine_iff_onLine
          Geo E B F lineEB
          hEB
          hElineEB
          hBlineEB).mpr hFlineEB

      have hF_CF :
          F ∈ Geo.PointLine C F :=
        (hilbert_mem_pointLine_iff_onLine
          Geo C F F lineCF
          hCF
          hClineCF
          hFlineCF).mpr hFlineCF

      exact
        Set.disjoint_left.mp
          hEB_CF.2.2
          hF_EB
          hF_CF

    rcases
        hilbert_outer_pasch
          Geo
          F E Q B r
          hFBE
          hFQB
          hErQ
      with
      ⟨H, hEHB, hFrH⟩

    have hCrFcol :
        Collinear Geo C r F :=
      (HilbertOrder.between_incidence
        C r F hCrF).2.2.2.1

    have hCFr :
        Collinear Geo C F r :=
      PrimCollinearRotate
        Geo C r F hCrFcol

    have hFrHcol :
        Collinear Geo F r H :=
      (HilbertOrder.between_incidence
        F r H hFrH).2.2.2.1

    have hFr :
        F ≠ r :=
      (HilbertOrder.between_incidence
        F r H hFrH).1

    have hCFH :
        Collinear Geo C F H :=
      hilbert_primCollinear_trans
        Geo
        C F r H
        hFr
        hCFr
        hFrHcol

    have hFCH :
        Collinear Geo F C H :=
      PrimCollinearSwap
        Geo C F H hCFH

    have hEB :
        E ≠ B :=
      hEB_CF.1

    rcases
        HilbertPlaneIncidence.line_through
          E B hEB
      with
      ⟨lineEB, hElineEB, hBlineEB⟩

    have hHlineEB :
        HilbertIncidence.OnLine H lineEB :=
      hilbert_between_on_line
        Geo
        E H B
        lineEB
        hElineEB
        hBlineEB
        hEHB

    have hCF :
        C ≠ F :=
      hEB_CF.2.1

    rcases
        HilbertPlaneIncidence.line_through
          C F hCF
      with
      ⟨lineCF, hClineCF, hFlineCF⟩

    have hHlineCF :
        HilbertIncidence.OnLine H lineCF :=
      hilbert_collinear_on_line
        Geo
        C F H
        lineCF
        hCF
        hClineCF
        hFlineCF
        hCFH

    have hH_EB :
        H ∈ Geo.PointLine E B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo E B H lineEB
        hEB
        hElineEB
        hBlineEB).mpr hHlineEB

    have hH_CF :
        H ∈ Geo.PointLine C F :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C F H lineCF
        hCF
        hClineCF
        hFlineCF).mpr hHlineCF

    exact
      Set.disjoint_left.mp
        hEB_CF.2.2
        hH_EB
        hH_CF

  have hEF :
      E ≠ F :=
    (hBC_FE.2.1).symm

  rcases
      hilbert_between_trichotomy
        Geo
        A E F
        hAE
        hEF
        hAF
        hAEF
    with
    hAEFbetween | hEAF | hAFE

  · exact ⟨Q, hBQF, hAQCbetween, hAEFbetween⟩


  ·
    have hFAE :
        Geo.Between F A E :=
      (HilbertOrder.between_incidence
        E A F hEAF).2.2.2.2

    have hFAltFE :
        HilbertSegmentLess Geo F A F E :=
      hilbert_segmentLess_of_between
        Geo F A E hFAE

    have hAF_FA :
        Geo.Congruent A F F A :=
      CongruentReverseFirst
        Geo
        F A
        F A
        (hilbert_congruent_reflexive Geo F A)

    have hAFltFE :
        HilbertSegmentLess Geo A F F E :=
      hilbert_segmentLess_congruent_left
        Geo
        F A
        A F
        F E
        hFAltFE
        hAF_FA

    have hFE_EF :
        Geo.Congruent F E E F :=
      CongruentReverseFirst
        Geo
        E F
        E F
        (hilbert_congruent_reflexive Geo E F)

    have hAFltEF :
        HilbertSegmentLess Geo A F E F :=
      hilbert_segmentLess_congruent_right
        Geo
        A F
        F E
        E F
        hAFltFE
        hFE_EF

    have hADltAF :
        HilbertSegmentLess Geo A D A F :=
      hilbert_segmentLess_of_between
        Geo A D F hADF

    have hEF_AD :
        Geo.Congruent E F A D :=
      hilbert_congruent_symmetry
        Geo A D E F hAD_EF

    have hEFltAF :
        HilbertSegmentLess Geo E F A F :=
      hilbert_segmentLess_congruent_left
        Geo
        A D
        E F
        A F
        hADltAF
        hEF_AD

    have hFalse : False :=
      (hilbert_segmentLess_asymm
        Geo E F A F hEFltAF)
        hAFltEF

    exact hFalse.elim

  ·
    have hFalse : False :=
      hNotAFE hAFE

    exact hFalse.elim

/--
Test version of the ordered case of Hilbert Theorem 44 / Euclid I.35.

Nothing from this theorem is moved to HilbertInterface until the proof
is complete and the file builds without sorry.
-/
theorem test_prop35_between
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADF : Geo.Between A D F)
    (hAEF : Collinear Geo A E F) :
    HilbertEquicomplementable Geo
      (HilbertParallelogramFigure Geo A B C D)
      (HilbertParallelogramFigure Geo E B C F) := by

  have hSides1 :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hABCD

  have hSides2 :
      OppositeSidesCongruent Geo E B C F :=
    ParallelogramOppositeSidesCongruent
      Geo E B C F hEBCF

  have hBC_DA :
      Geo.Congruent B C D A :=
    hSides1.2

  have hBC_FE :
      Geo.Congruent B C F E :=
    hSides2.2

  have hAD_BC :
      Geo.Congruent A D B C := by
    have hDA_BC :
        Geo.Congruent D A B C :=
      CongruentSymmetry
        Geo B C D A hBC_DA

    exact
      CongruentReverseFirst
        Geo D A B C hDA_BC

  have hEF_BC :
      Geo.Congruent E F B C := by
    have hFE_BC :
        Geo.Congruent F E B C :=
      CongruentSymmetry
        Geo B C F E hBC_FE

    exact
      CongruentReverseFirst
        Geo F E B C hFE_BC

  rcases
      test_prop35_order_helper
        Geo
        A B C D E F
        hABCD
        hEBCF
        hADF
        hAEF
    with
    ⟨Q, hBQF, hAQCbetween, hAEFbetween⟩

  have hRightSwap0 :
      HilbertSameFigure Geo
        [
          ⟨A, B, F⟩,
          ⟨B, C, F⟩
        ]
        [
          ⟨B, A, F⟩,
          ⟨B, C, F⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        []
        [⟨B, C, F⟩]
        A B F)

  have hRightSplit :
      HilbertSameFigure Geo
        [
          ⟨B, A, F⟩,
          ⟨B, C, F⟩
        ]
        [
          ⟨B, A, E⟩,
          ⟨B, E, F⟩,
          ⟨B, C, F⟩
        ] := by
    simpa using
      (HilbertSameFigure.split
        []
        [⟨B, C, F⟩]
        B A F E
        hAEFbetween)

  have hRightSwap1 :
      HilbertSameFigure Geo
        [
          ⟨B, A, E⟩,
          ⟨B, E, F⟩,
          ⟨B, C, F⟩
        ]
        [
          ⟨A, B, E⟩,
          ⟨B, E, F⟩,
          ⟨B, C, F⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        []
        [
          ⟨B, E, F⟩,
          ⟨B, C, F⟩
        ]
        B A E)

  have hRightSwap2 :
      HilbertSameFigure Geo
        [
          ⟨A, B, E⟩,
          ⟨B, E, F⟩,
          ⟨B, C, F⟩
        ]
        [
          ⟨A, B, E⟩,
          ⟨E, B, F⟩,
          ⟨B, C, F⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        [⟨A, B, E⟩]
        [⟨B, C, F⟩]
        B E F)

  have hRightMerge :
      HilbertSameFigure Geo
        [
          ⟨A, B, E⟩,
          ⟨E, B, F⟩,
          ⟨B, C, F⟩
        ]
        [
          ⟨A, B, F⟩,
          ⟨B, C, F⟩
        ] :=
    HilbertSameFigure.symm
      (HilbertSameFigure.trans
        hRightSwap0
        (HilbertSameFigure.trans
          hRightSplit
          (HilbertSameFigure.trans
            hRightSwap1
            hRightSwap2)))

  have hRightMerge :
      HilbertSameFigure Geo
        [
          ⟨A, B, E⟩,
          ⟨E, B, F⟩,
          ⟨B, C, F⟩
        ]
        [
          ⟨A, B, F⟩,
          ⟨B, C, F⟩
        ] := by

    have hForward :
        HilbertSameFigure Geo
          [
            ⟨A, B, F⟩,
            ⟨B, C, F⟩
          ]
          [
            ⟨A, B, E⟩,
            ⟨E, B, F⟩,
            ⟨B, C, F⟩
          ] :=
      HilbertSameFigure.trans
        hRightSwap0
        (HilbertSameFigure.trans
          hRightSplit
          (HilbertSameFigure.trans
            hRightSwap1
            hRightSwap2))

    exact
      HilbertSameFigure.symm hForward


  have hAD_EF :
      Geo.Congruent A D E F := by
    exact
      hilbert_congruent_transitivity
        Geo
        A D
        B C
        E F
        hAD_BC
        (CongruentSymmetry
          Geo E F B C hEF_BC)

  have hFEA :
      Geo.Between F E A :=
    (HilbertOrder.between_incidence
      A E F hAEFbetween).2.2.2.2

  have hAD_FE :
      Geo.Congruent A D F E :=
    CongruentSwapSecond
      Geo A D E F hAD_EF

  have hAF_FA :
      Geo.Congruent A F F A :=
    CongruentReverseFirst
      Geo
      F A
      F A
      (hilbert_congruent_reflexive Geo F A)

  have hDF_EA :
      Geo.Congruent D F E A :=
    hilbert_segment_subtraction
      Geo
      A D F
      F E A
      hADF
      hFEA
      hAD_FE
      hAF_FA

  have hAE_DF :
      Geo.Congruent A E D F :=
    CongruentReverseFirst
      Geo
      E A
      D F
      (hilbert_congruent_symmetry
        Geo D F E A hDF_EA)

  have hDC_AB :
      Geo.Congruent D C A B := by
    have hCD_AB :
        Geo.Congruent C D A B :=
      hilbert_congruent_symmetry
        Geo A B C D hSides1.1

    exact
      CongruentReverseFirst
        Geo C D A B hCD_AB

  have hCF_BE :
      Geo.Congruent C F B E := by
    have hCF_EB :
        Geo.Congruent C F E B :=
      hilbert_congruent_symmetry
        Geo E B C F hSides2.1

    exact
      CongruentSwapSecond
        Geo C F E B hCF_EB

  have hDF_AE :
      Geo.Congruent D F A E :=
    hilbert_congruent_symmetry
      Geo A E D F hAE_DF

  have hABE :
      ¬ Collinear Geo A B E := by
    intro hABEcol

    have hAE :
        A ≠ E :=
      (HilbertOrder.between_incidence
        A E F hAEFbetween).1

    have hEB_CF :
        Geo.Parallel E B C F :=
      hEBCF.1

    have hBEF :
        ¬ Collinear Geo B E F := by
      intro hBEFcol

      have hEB :
          E ≠ B :=
        hEB_CF.1

      rcases
          HilbertPlaneIncidence.line_through
            E B hEB
        with
        ⟨lineEB, hElineEB, hBlineEB⟩

      have hEBF :
          Collinear Geo E B F :=
        PrimCollinearSwap
          Geo B E F hBEFcol

      have hFlineEB :
          HilbertIncidence.OnLine F lineEB :=
        hilbert_collinear_on_line
          Geo
          E B F
          lineEB
          hEB
          hElineEB
          hBlineEB
          hEBF

      have hCF :
          C ≠ F :=
        hEB_CF.2.1

      rcases
          HilbertPlaneIncidence.line_through
            C F hCF
        with
        ⟨lineCF, hClineCF, hFlineCF⟩

      have hF_EB :
          F ∈ Geo.PointLine E B :=
        (hilbert_mem_pointLine_iff_onLine
          Geo E B F lineEB
          hEB
          hElineEB
          hBlineEB).mpr hFlineEB

      have hF_CF :
          F ∈ Geo.PointLine C F :=
        (hilbert_mem_pointLine_iff_onLine
          Geo C F F lineCF
          hCF
          hClineCF
          hFlineCF).mpr hFlineCF

      exact
        Set.disjoint_left.mp
          hEB_CF.2.2
          hF_EB
          hF_CF

    have hBEA :
        Collinear Geo B E A :=
      PrimCollinearCycle
        Geo A B E hABEcol

    have hEAF :
        Collinear Geo E A F :=
      PrimCollinearSwap
        Geo A E F hAEF

    have hBEFcol :
        Collinear Geo B E F :=
      hilbert_primCollinear_trans
        Geo
        B E A F
        hAE.symm
        hBEA
        hEAF

    exact hBEF hBEFcol

  have hAB_DC :
      Geo.Congruent A B D C :=
    hilbert_congruent_symmetry
      Geo D C A B hDC_AB

  have hBE_CF :
      Geo.Congruent B E C F :=
    hilbert_congruent_symmetry
      Geo C F B E hCF_BE

  have hSSS :=
    HilbertSSS
      Geo
      A B E
      D C F
      hABE
      hAB_DC
      hBE_CF
      hAE_DF

  have hABE_DCF :
      HilbertTriangleCongruent
        Geo
        ⟨A, B, E⟩
        ⟨D, C, F⟩ :=
    hSSS.2

  let Pcomp : HilbertTriangulatedFigure Geo :=
    [⟨D, C, F⟩]

  let Qcomp : HilbertTriangulatedFigure Geo :=
    [⟨A, B, E⟩]

  have hDCF_ABE :
      HilbertTriangleCongruent
        Geo
        ⟨D, C, F⟩
        ⟨A, B, E⟩ :=
    hilbert_triangleCongruent_symm
      Geo hABE_DCF

  have hCompEquidecomp :
      HilbertEquidecomposable Geo Pcomp Qcomp := by
    refine ⟨Qcomp, List.Perm.refl _, ?_⟩

    exact
      HilbertTriangleListCongruent.cons
        hDCF_ABE
        HilbertTriangleListCongruent.nil

  have hComp :
      HilbertFigureEquidecomposable Geo Pcomp Qcomp :=
    HilbertFigureEquidecomposable.congruentTriangulations
      hCompEquidecomp

  let Common : HilbertTriangulatedFigure Geo :=
    [
      ⟨A, B, C⟩,
      ⟨C, A, F⟩
    ]

  have hLeftSplit :
      HilbertSameFigure
        Geo
        Common
        [
          ⟨A, B, C⟩,
          ⟨C, A, D⟩,
          ⟨C, D, F⟩
        ] := by
    change
      HilbertSameFigure
        Geo
        [
          ⟨A, B, C⟩,
          ⟨C, A, F⟩
        ]
        [
          ⟨A, B, C⟩,
          ⟨C, A, D⟩,
          ⟨C, D, F⟩
        ]

    simpa using
      (HilbertSameFigure.split
        [⟨A, B, C⟩]
        []
        C A F D
        hADF)

  have hLeftSwap1 :
      HilbertSameFigure
        Geo
        [
          ⟨A, B, C⟩,
          ⟨C, A, D⟩,
          ⟨C, D, F⟩
        ]
        [
          ⟨A, B, C⟩,
          ⟨A, C, D⟩,
          ⟨C, D, F⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        [⟨A, B, C⟩]
        [⟨C, D, F⟩]
        C A D)

  have hLeftSwap2 :
      HilbertSameFigure
        Geo
        [
          ⟨A, B, C⟩,
          ⟨A, C, D⟩,
          ⟨C, D, F⟩
        ]
        [
          ⟨A, B, C⟩,
          ⟨A, C, D⟩,
          ⟨D, C, F⟩
        ] := by
    simpa using
      (HilbertSameFigure.triangleSwapFirst
        [⟨A, B, C⟩, ⟨A, C, D⟩]
        []
        C D F)

  have hCommonLeft :
      HilbertSameFigure
        Geo
        Common
        (HilbertParallelogramFigure Geo A B C D ++ Pcomp) := by
    exact
      HilbertSameFigure.trans
        hLeftSplit
        (HilbertSameFigure.trans
          hLeftSwap1
          hLeftSwap2)

  have hLeft :
      HilbertFigureEquidecomposable
        Geo
        (HilbertParallelogramFigure Geo A B C D ++ Pcomp)
        Common :=
    HilbertFigureEquidecomposable.sameFigure
      (HilbertSameFigure.symm hCommonLeft)

  have hABCFflip :
      HilbertFigureEquidecomposable Geo
        [⟨A, B, C⟩, ⟨A, C, F⟩]
        [⟨A, B, F⟩, ⟨B, C, F⟩] :=
    quadrilateral_diagonal_flip
      Geo
      A B C F Q
      hAQCbetween
      hBQF

  rcases
      ParallelogramDiagonalIntersectionExists
        Geo E B C F hEBCF
    with
    ⟨N, hENC, hBNF⟩

  have hEBCFflip :
      HilbertFigureEquidecomposable Geo
        [⟨E, B, C⟩, ⟨E, C, F⟩]
        [⟨E, B, F⟩, ⟨B, C, F⟩] :=
    quadrilateral_diagonal_flip
      Geo
      E B C F N
      hENC
      hBNF

  have hRightStep1 :
      HilbertFigureEquidecomposable Geo
        (HilbertParallelogramFigure Geo E B C F ++ Qcomp)
        ([⟨E, B, F⟩, ⟨B, C, F⟩] ++ Qcomp) := by
    simpa [HilbertParallelogramFigure] using
      (hilbert_figureEquidecomposable_append_right
        Geo
        hEBCFflip
        Qcomp)

  have hRightStep2 :
      HilbertFigureEquidecomposable Geo
        ([⟨E, B, F⟩, ⟨B, C, F⟩] ++ Qcomp)
        (Qcomp ++ [⟨E, B, F⟩, ⟨B, C, F⟩]) :=
    hilbert_figureEquidecomposable_append_comm
      Geo
      [⟨E, B, F⟩, ⟨B, C, F⟩]
      Qcomp

  have hRightMergeFig :
      HilbertFigureEquidecomposable Geo
        (Qcomp ++ [⟨E, B, F⟩, ⟨B, C, F⟩])
        [⟨A, B, F⟩, ⟨B, C, F⟩] := by
    have h :
        HilbertFigureEquidecomposable Geo
          [
            ⟨A, B, E⟩,
            ⟨E, B, F⟩,
            ⟨B, C, F⟩
          ]
          [
            ⟨A, B, F⟩,
            ⟨B, C, F⟩
          ] :=
      HilbertFigureEquidecomposable.sameFigure
        hRightMerge

    simpa [Qcomp] using h

  have hToACF :
      HilbertFigureEquidecomposable Geo
        [⟨A, B, F⟩, ⟨B, C, F⟩]
        [⟨A, B, C⟩, ⟨A, C, F⟩] :=
    HilbertFigureEquidecomposable.symm
      hABCFflip

  have hACF_CAF :
      HilbertSameFigure Geo
        [⟨A, B, C⟩, ⟨A, C, F⟩]
        Common := by
    dsimp [Common]

    simpa using
      (HilbertSameFigure.triangleSwapFirst
        [⟨A, B, C⟩]
        []
        A C F)

  have hToCommon :
      HilbertFigureEquidecomposable Geo
        [⟨A, B, C⟩, ⟨A, C, F⟩]
        Common :=
    HilbertFigureEquidecomposable.sameFigure
      hACF_CAF

  have hRight :
      HilbertFigureEquidecomposable Geo
        (HilbertParallelogramFigure Geo E B C F ++ Qcomp)
        Common :=
    HilbertFigureEquidecomposable.trans
      hRightStep1
      (HilbertFigureEquidecomposable.trans
        hRightStep2
        (HilbertFigureEquidecomposable.trans
          hRightMergeFig
          (HilbertFigureEquidecomposable.trans
            hToACF
            hToCommon)))

  refine ⟨Pcomp, Qcomp, hComp, ?_⟩

  exact
    HilbertFigureEquidecomposable.trans
      hLeft
      (HilbertFigureEquidecomposable.symm hRight)












end Geometry

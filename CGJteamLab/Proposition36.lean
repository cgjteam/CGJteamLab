import CGJteamLab.Proposition35

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

theorem i36_from_intermediate
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F G H : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEFGH : IsParallelogram Geo E F G H)
    (hEBCH : IsParallelogram Geo E B C H)
    (hADH : Geo.Between A D H)
    (hAEH : Collinear Geo A E H)
    (hBCG : Geo.Between B C G)
    (hBFG : Collinear Geo B F G) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo E F G H) := by

  have hFirst :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo E B C H) :=
    euclid_proposition_35
      Geo
      A B C D E H
      hABCD
      hEBCH
      hADH
      hAEH

  have hEBCHrev :
      IsParallelogram Geo B E H C :=
    ParallelogramReverse
      Geo E B C H hEBCH

  have hEFGHrev :
      IsParallelogram Geo F E H G :=
    ParallelogramReverse
      Geo E F G H hEFGH

  have hSecondRev :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B E H C)
        (hilbertParallelogramTerm Geo F E H G) :=
    euclid_proposition_35
      Geo
      B E H C F G
      hEBCHrev
      hEFGHrev
      hBCG
      hBFG

  have hRevEBCH :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E B C H)
        (hilbertParallelogramTerm Geo B E H C) :=
    parallelogram_term_reverse
      Geo E B C H hEBCH

  have hRevEFGH :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E F G H)
        (hilbertParallelogramTerm Geo F E H G) :=
    parallelogram_term_reverse
      Geo E F G H hEFGH

  have hEBCHtoRev :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B C H)
        (hilbertParallelogramTerm Geo B E H C) :=
    equicomplementable_of_scissorsEq
      Geo hRevEBCH

  have hRevToEFGH :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo F E H G)
        (hilbertParallelogramTerm Geo E F G H) :=
    equicomplementable_of_scissorsEq
      Geo
      (HilbertScissorsEq.symm
        (Geo := Geo) hRevEFGH)

  have hSecond :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B C H)
        (hilbertParallelogramTerm Geo E F G H) :=
    equicomplementable_trans
      Geo
      hEBCHtoRev
      (equicomplementable_trans
        Geo
        hSecondRev
        hRevToEFGH)

  exact
    equicomplementable_trans
      Geo
      hFirst
      hSecond

theorem i36_equal_parallel_EH_BC
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C E F G H : Geo.Point)
    (hEFGH : IsParallelogram Geo E F G H)
    (hBCG : Geo.Between B C G)
    (hBFG : Collinear Geo B F G)
    (hBCFG : Geo.Congruent B C F G) :
    Geo.Parallel E H B C ∧
    Geo.Congruent E H B C := by

  --------------------------------------------------------------------
  -- First: BC is parallel to EH.
  --
  -- FG || HE because EFGH is a parallelogram.
  -- Since B, C, F, G lie on the same carrier, transport FG to BC.
  --------------------------------------------------------------------

  have hFG_HE :
      Geo.Parallel F G H E :=
    hEFGH.2

  have hFG_EH :
      Geo.Parallel F G E H :=
    ParallelSwapSecondLine
      Geo F G H E hFG_HE

  have hBG :
      B ≠ G :=
    (HilbertOrder.between_incidence
      B C G hBCG).2.2.1

  have hBG_EH :
      Geo.Parallel B G E H :=
    ParallelCollinearLeft
      Geo F G B E H
      hBG
      hFG_EH
      hBFG

  have hGB_EH :
      Geo.Parallel G B E H :=
    ParallelSwapFirstLine
      Geo B G E H hBG_EH

  have hBCGcol :
      Collinear Geo B C G :=
    (HilbertOrder.between_incidence
      B C G hBCG).2.2.2.1

  have hBGC :
    Collinear Geo B G C :=
  PrimCollinearRotate
    Geo B C G hBCGcol

  have hCGB :
    Collinear Geo C G B :=
  PrimCollinearSymm
    Geo B G C hBGC


  have hCB :
      C ≠ B :=
    (HilbertOrder.between_incidence
      B C G hBCG).1.symm

  have hCB_EH :
      Geo.Parallel C B E H :=
    ParallelCollinearLeft
      Geo G B C E H
      hCB
      hGB_EH
      hCGB

  have hBC_EH :
      Geo.Parallel B C E H :=
    ParallelSwapFirstLine
      Geo C B E H hCB_EH

  have hEH_BC :
      Geo.Parallel E H B C :=
    ParallelSymmetry
      Geo B C E H hBC_EH

  --------------------------------------------------------------------
  -- Second: EH is congruent to BC.
  --
  -- EFGH gives FG congruent HE.
  -- The hypothesis gives BC congruent FG.
  --------------------------------------------------------------------

  have hSides :
      OppositeSidesCongruent Geo E F G H :=
    ParallelogramOppositeSidesCongruent
      Geo E F G H hEFGH

  have hFG_EH_cong :
      Geo.Congruent F G E H :=
    CongruentSwapSecond
      Geo F G H E hSides.2

  have hBC_EH_cong :
      Geo.Congruent B C E H :=
    hilbert_congruent_transitivity
      Geo
      B C
      F G
      E H
      hBCFG
      hFG_EH_cong

  have hEH_BC_cong :
      Geo.Congruent E H B C :=
    hilbert_congruent_symmetry
      Geo B C E H hBC_EH_cong

  exact ⟨hEH_BC, hEH_BC_cong⟩

theorem i36_bottom_shift
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C F G : Geo.Point)
    (hBCF : Geo.Between B C F)
    (hCFG : Geo.Between C F G)
    (hBCFG : Geo.Congruent B C F G) :
    Geo.Congruent B F C G := by

  have hGFC :
      Geo.Between G F C :=
    (HilbertOrder.between_incidence
      C F G hCFG).2.2.2.2

  have hBC_GF :
      Geo.Congruent B C G F :=
    CongruentSwapSecond
      Geo B C F G hBCFG

  have hCF_FC :
      Geo.Congruent C F F C :=
    CongruentSwapSecond
      Geo C F C F
      (hilbert_congruent_reflexive
        Geo C F)

  have hBF_GC :
      Geo.Congruent B F G C :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      B C F
      G F C
      hBCF
      hGFC
      hBC_GF
      hCF_FC

  exact
    CongruentSwapSecond
      Geo B F G C hBF_GC

theorem i36_corresponding_angle
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C E F G H : Geo.Point)
    (hEFGH : IsParallelogram Geo E F G H)
    (hBCF : Geo.Between B C F)
    (hCFG : Geo.Between C F G) :
    Geo.AngleCongruent E F B H G C := by

  --------------------------------------------------------------------
  -- The line FG and the fact that H,E lie on the same side of it.
  --------------------------------------------------------------------

  have hHE_FG :
      Geo.Parallel H E F G :=
    ParallelSymmetry
      Geo F G H E hEFGH.2

  rcases
      parallel_endpoints_sameSide
        Geo H E F G hHE_FG with
    ⟨lineFG, hFline, hGline, hHESame⟩

  have hHoff :
      ¬ HilbertIncidence.OnLine H lineFG :=
    hHESame.1

  have hEoff :
      ¬ HilbertIncidence.OnLine E lineFG :=
    hHESame.2.1

  have hEHSame :
      HilbertSameSide Geo E H lineFG :=
    hilbert_sameSide_symm
      Geo H E lineFG hHESame

  --------------------------------------------------------------------
  -- Extend EF beyond F:
  --
  --   E-F-X.
  --------------------------------------------------------------------

  have hEF :
      E ≠ F :=
    hEFGH.1.1

  rcases
      HilbertOrder.between_extension
        E F hEF with
    ⟨X, hEFX⟩

  have hEFXData :=
    HilbertOrder.between_incidence
      E F X hEFX

  have hFX :
      F ≠ X :=
    hEFXData.2.1

  have hXF :
      X ≠ F :=
    hFX.symm

  have hEFXcol :
      Collinear Geo E F X :=
    hEFXData.2.2.2.1

  have hFXE :
      Collinear Geo F X E :=
    PrimCollinearCycle
      Geo E F X hEFXcol

  have hXEF :
      Collinear Geo X E F :=
    PrimCollinearCycle
      Geo F X E hFXE

  --------------------------------------------------------------------
  -- X is off FG.
  --------------------------------------------------------------------

  have hXoff :
      ¬ HilbertIncidence.OnLine X lineFG := by
    intro hXline

    have hEline :
        HilbertIncidence.OnLine E lineFG :=
      hilbert_collinear_on_line
        Geo F X E lineFG
        hFX
        hFline
        hXline
        hFXE

    exact hEoff hEline

  --------------------------------------------------------------------
  -- Since E-F-X and F lies on FG, E and X are on opposite sides
  -- of FG.  H is on the same side as E, hence X and H are opposite.
  --------------------------------------------------------------------

  have hOppEX :
      HilbertOppositeSide Geo E X lineFG :=
    ⟨hEoff,
      hXoff,
      ⟨F, hEFX, hFline⟩⟩

  have hOppXE :
      HilbertOppositeSide Geo X E lineFG :=
    hilbert_oppositeSide_symm
      Geo E X lineFG hOppEX

  have hOppXH :
      HilbertOppositeSide Geo X H lineFG :=
    hilbert_oppositeSide_transport_right
      Geo X E H lineFG
      hOppXE
      hEHSame

  --------------------------------------------------------------------
  -- Transport EF || GH to FX || GH.
  --------------------------------------------------------------------

  have hXF_GH :
      Geo.Parallel X F G H :=
    ParallelCollinearLeft
      Geo E F X G H
      hXF
      hEFGH.1
      hXEF

  have hFX_GH :
      Geo.Parallel F X G H :=
    ParallelSwapFirstLine
      Geo X F G H hXF_GH

  --------------------------------------------------------------------
  -- Choose T strictly between F and G and apply Hilbert Theorem 30.
  --------------------------------------------------------------------

  have hFG :
      F ≠ G :=
    hEFGH.2.1

  rcases
      hilbert_between_exists
        Geo F G hFG with
    ⟨T, hFTG⟩

  have hAngleRaw :
      Geo.AngleCongruent T F X T G H :=
    hilbert_alternate_angles_of_parallel_oppositeSide_lines
      Geo
      F X G T H
      lineFG
      hFTG
      hFline
      hGline
      hOppXH
      hFX_GH

  --------------------------------------------------------------------
  -- Replace T by G at F and by F at G.
  --------------------------------------------------------------------

  have hFTRay :
      HilbertSameRay Geo F T G :=
    hilbert_sameRay_of_between
      Geo F T G hFTG

  have hGTF :
      Geo.Between G T F :=
    (HilbertOrder.between_incidence
      F T G hFTG).2.2.2.2

  have hGTRay :
      HilbertSameRay Geo G T F :=
    hilbert_sameRay_of_between
      Geo G T F hGTF

  have hAtF :
      Geo.Angle T F X =
      Geo.Angle G F X :=
    hilbert_angle_eq_of_sameRay_first
      Geo F T G X hFTRay

  have hAtG :
      Geo.Angle T G H =
      Geo.Angle F G H :=
    hilbert_angle_eq_of_sameRay_first
      Geo G T F H hGTRay

  have hAlt0 :
      Geo.AngleCongruent G F X F G H := by
    unfold Geometry.Geo.AngleCongruent at hAngleRaw ⊢
    rw [← hAtF, ← hAtG]
    exact hAngleRaw

  have hAlt :
      Geo.AngleCongruent X F G H G F :=
    (Geo.angle_congruent_reverse_second
      X F G F G H).mp
      ((Geo.angle_congruent_reverse_first
        G F X F G H).mp hAlt0)

  --------------------------------------------------------------------
  -- Bottom order gives B-F-G.
  --------------------------------------------------------------------

  have hBottom :=
    hilbert_between_outer_trans
      Geo B C F G hBCF hCFG

  have hBFG :
      Geo.Between B F G :=
    hBottom.1

  have hBFGData :=
    HilbertOrder.between_incidence
      B F G hBFG

  have hFB :
      F ≠ B :=
    hBFGData.1.symm

  have hFGB :
      Collinear Geo F G B :=
    PrimCollinearCycle
      Geo B F G hBFGData.2.2.2.1

  have hBline :
      HilbertIncidence.OnLine B lineFG :=
    hilbert_collinear_on_line
      Geo F G B lineFG
      hFG
      hFline
      hGline
      hFGB

  have hFBE :
      ¬ Collinear Geo F B E :=
    hilbert_not_collinear_of_off_line
      Geo F B E lineFG
      hFB
      hFline
      hBline
      hEoff

  have hEFB :
      ¬ Collinear Geo E F B := by
    intro h
    exact
      hFBE
        (PrimCollinearCycle
          Geo E F B h)

  --------------------------------------------------------------------
  -- Vertical angles at F:
  --
  --   angle EFB ~= angle XFG.
  --------------------------------------------------------------------

  have hVertical :
      Geo.AngleCongruent E F B X F G :=
    VerticalAngles
      Geo
      E F B X G
      hEFX
      hBFG
      hEFB

  --------------------------------------------------------------------
  -- C and F are on the same ray from G:
  --
  --   angle HGF = angle HGC.
  --------------------------------------------------------------------

  have hGFC :
      Geo.Between G F C :=
    (HilbertOrder.between_incidence
      C F G hCFG).2.2.2.2

  have hGFCRay :
      HilbertSameRay Geo G F C :=
    hilbert_sameRay_of_between
      Geo G F C hGFC

  have hHGF_HGC :
      Geo.Angle H G F =
      Geo.Angle H G C :=
    hilbert_angle_eq_of_sameRay_second
      Geo G H F C hGFCRay

  have hAltTarget :
      Geo.AngleCongruent X F G H G C := by
    unfold Geometry.Geo.AngleCongruent at hAlt ⊢
    rw [← hHGF_HGC]
    exact hAlt

  --------------------------------------------------------------------
  -- Corresponding angles.
  --------------------------------------------------------------------

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E F B
      X F G
      H G C
      hVertical
      hAltTarget

theorem i36_cross_triangles_congruent
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C E F G H : Geo.Point)
    (hEFGH : IsParallelogram Geo E F G H)
    (hBCF : Geo.Between B C F)
    (hCFG : Geo.Between C F G)
    (hBCFG : Geo.Congruent B C F G) :
    TriangleCongruenceResult Geo
      F E B
      G H C := by

  --------------------------------------------------------------------
  -- Metric data.
  --------------------------------------------------------------------

  have hSides :
      OppositeSidesCongruent Geo E F G H :=
    ParallelogramOppositeSidesCongruent
      Geo E F G H hEFGH

  have hFE_GH :
      Geo.Congruent F E G H :=
    CongruentReverseFirst
      Geo E F G H hSides.1

  have hFB_GC :
    Geo.Congruent F B G C :=
  CongruentReverseBoth
    Geo B F C G
    (i36_bottom_shift
      Geo B C F G
      hBCF hCFG hBCFG)

  have hAngle :
      Geo.AngleCongruent E F B H G C :=
    i36_corresponding_angle
      Geo B C E F G H
      hEFGH hBCF hCFG

  --------------------------------------------------------------------
  -- Use the carrier FG to establish noncollinearity.
  --------------------------------------------------------------------

  have hHE_FG :
      Geo.Parallel H E F G :=
    ParallelSymmetry
      Geo F G H E hEFGH.2

  rcases
      parallel_endpoints_sameSide
        Geo H E F G hHE_FG with
    ⟨lineFG, hFline, hGline, hHESame⟩

  have hHoff :
      ¬ HilbertIncidence.OnLine H lineFG :=
    hHESame.1

  have hEoff :
      ¬ HilbertIncidence.OnLine E lineFG :=
    hHESame.2.1

  have hBottom :=
    hilbert_between_outer_trans
      Geo B C F G hBCF hCFG

  have hBFG :
      Geo.Between B F G :=
    hBottom.1

  have hBFGData :=
    HilbertOrder.between_incidence
      B F G hBFG

  have hFB :
      F ≠ B :=
    hBFGData.1.symm

  have hFGB :
      Collinear Geo F G B :=
    PrimCollinearCycle
      Geo B F G hBFGData.2.2.2.1

  have hBline :
      HilbertIncidence.OnLine B lineFG :=
    hilbert_collinear_on_line
      Geo F G B lineFG
      hEFGH.2.1
      hFline
      hGline
      hFGB

  have hFBE :
      ¬ Collinear Geo F B E :=
    hilbert_not_collinear_of_off_line
      Geo F B E lineFG
      hFB
      hFline
      hBline
      hEoff

  have hFEB :
      ¬ Collinear Geo F E B := by
    intro h
    exact
      hFBE
        (PrimCollinearRotate
          Geo F E B h)

  have hCFGData :=
    HilbertOrder.between_incidence
      C F G hCFG

  have hFGC :
      Collinear Geo F G C :=
    PrimCollinearCycle
      Geo C F G hCFGData.2.2.2.1

  have hGC :
      G ≠ C :=
    hCFGData.2.2.1.symm

  have hCline :
      HilbertIncidence.OnLine C lineFG :=
    hilbert_collinear_on_line
      Geo F G C lineFG
      hEFGH.2.1
      hFline
      hGline
      hFGC

  have hGCH :
      ¬ Collinear Geo G C H :=
    hilbert_not_collinear_of_off_line
      Geo G C H lineFG
      hGC
      hGline
      hCline
      hHoff

  have hGHC :
      ¬ Collinear Geo G H C := by
    intro h
    exact
      hGCH
        (PrimCollinearRotate
          Geo G H C h)

  --------------------------------------------------------------------
  -- SAS: triangle FEB ~= triangle GHC.
  --------------------------------------------------------------------

  have hTriangles :
      TriangleCongruenceResult Geo
        F E B
        G H C :=
    TriangleCongruentFromSAS
      Geo
      F E B
      G H C
      hFEB
      hGHC
      hFE_GH
      hAngle
      hFB_GC

  exact hTriangles

theorem i36_cross_parallel
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C E F G H : Geo.Point)
    (hEFGH : IsParallelogram Geo E F G H)
    (hBCF : Geo.Between B C F)
    (hCFG : Geo.Between C F G)
    (hBCFG : Geo.Congruent B C F G) :
    Geo.Parallel E B H C := by

  --------------------------------------------------------------------
  -- Use FG as the transversal carrier.
  --------------------------------------------------------------------

  have hHE_FG :
      Geo.Parallel H E F G :=
    ParallelSymmetry
      Geo F G H E hEFGH.2

  rcases
      parallel_endpoints_sameSide
        Geo H E F G hHE_FG with
    ⟨lineFG, hFline, hGline, hHESame⟩

  have hHoff :
      ¬ HilbertIncidence.OnLine H lineFG :=
    hHESame.1

  have hFG :
      F ≠ G :=
    hEFGH.2.1

  have hCFGData :=
    HilbertOrder.between_incidence
      C F G hCFG

  have hFGC :
      Collinear Geo F G C :=
    PrimCollinearCycle
      Geo C F G hCFGData.2.2.2.1

  have hCline :
      HilbertIncidence.OnLine C lineFG :=
    hilbert_collinear_on_line
      Geo F G C lineFG
      hFG
      hFline
      hGline
      hFGC

  have hBottom :=
    hilbert_between_outer_trans
      Geo B C F G hBCF hCFG

  have hBFG :
      Geo.Between B F G :=
    hBottom.1

  have hBCG :
      Geo.Between B C G :=
    hBottom.2

  have hBFGData :=
    HilbertOrder.between_incidence
      B F G hBFG

  have hFGB :
      Collinear Geo F G B :=
    PrimCollinearCycle
      Geo B F G hBFGData.2.2.2.1

  have hBline :
      HilbertIncidence.OnLine B lineFG :=
    hilbert_collinear_on_line
      Geo F G B lineFG
      hFG
      hFline
      hGline
      hFGB

  --------------------------------------------------------------------
  -- Choose T between B and C.
  --------------------------------------------------------------------

  have hBC :
      B ≠ C :=
    (HilbertOrder.between_incidence
      B C F hBCF).1

  rcases
      hilbert_between_exists
        Geo B C hBC with
    ⟨T, hBTC⟩

  have hBTF :
      Geo.Between B T F :=
    (hilbert_between_inner_trans
      Geo B T C F
      hBTC hBCF).2

  have hTCG :
      Geo.Between T C G :=
    (hilbert_between_inner_trans
      Geo B T C G
      hBTC hBCG).1

  have hGCT :
      Geo.Between G C T :=
    (HilbertOrder.between_incidence
      T C G hTCG).2.2.2.2

  --------------------------------------------------------------------
  -- Extend HC beyond C:
  --
  --   H-C-Y.
  --------------------------------------------------------------------

  have hHC :
      H ≠ C := by
    intro h
    subst C
    exact hHoff hCline

  rcases
      HilbertOrder.between_extension
        H C hHC with
    ⟨Y, hHCY⟩

  have hHCYData :=
    HilbertOrder.between_incidence
      H C Y hHCY

  have hHCYcol :
      Collinear Geo H C Y :=
    hHCYData.2.2.2.1

  have hHYC :
      Collinear Geo H Y C :=
    PrimCollinearRotate
      Geo H C Y hHCYcol

  have hCYH :
      Collinear Geo C Y H :=
    PrimCollinearSymm
      Geo H Y C hHYC

  have hCY :
      C ≠ Y :=
    hHCYData.2.1

  have hYoff :
      ¬ HilbertIncidence.OnLine Y lineFG := by
    intro hYline

    have hHline :
        HilbertIncidence.OnLine H lineFG :=
      hilbert_collinear_on_line
        Geo C Y H lineFG
        hCY
        hCline
        hYline
        hCYH

    exact hHoff hHline

  --------------------------------------------------------------------
  -- H and Y are opposite with respect to FG.
  -- Since H and E are on the same side, E and Y are opposite.
  --------------------------------------------------------------------

  have hOppHY :
      HilbertOppositeSide Geo H Y lineFG :=
    ⟨hHoff,
      hYoff,
      ⟨C, hHCY, hCline⟩⟩

  have hOppYH :
      HilbertOppositeSide Geo Y H lineFG :=
    hilbert_oppositeSide_symm
      Geo H Y lineFG hOppHY

  have hOppYE :
      HilbertOppositeSide Geo Y E lineFG :=
    hilbert_oppositeSide_transport_right
      Geo Y H E lineFG
      hOppYH
      hHESame

  have hOppEY :
      HilbertOppositeSide Geo E Y lineFG :=
    hilbert_oppositeSide_symm
      Geo Y E lineFG hOppYE

  --------------------------------------------------------------------
  -- SAS already gave:
  --
  --   angle FBE ~= angle GCH.
  --
  -- Replace F by T on the same ray from B.
  --------------------------------------------------------------------

  have hTriangles :=
    i36_cross_triangles_congruent
      Geo B C E F G H
      hEFGH hBCF hCFG hBCFG

  have hFBE_GCH :
      Geo.AngleCongruent F B E G C H :=
    hTriangles.angleC

  have hRayBTF :
      HilbertSameRay Geo B T F :=
    hilbert_sameRay_of_between
      Geo B T F hBTF

  have hTBE_FBE :
      Geo.Angle T B E =
      Geo.Angle F B E :=
    hilbert_angle_eq_of_sameRay_first
      Geo B T F E hRayBTF

  have hTBE_GCH :
      Geo.AngleCongruent T B E G C H := by
    unfold Geometry.Geo.AngleCongruent at hFBE_GCH ⊢
    rw [hTBE_FBE]
    exact hFBE_GCH

  --------------------------------------------------------------------
  -- At C the angles GCH and TCY are vertical.
  --------------------------------------------------------------------

  have hGC :
      G ≠ C :=
    hCFGData.2.2.1.symm

  have hGCH :
      ¬ Collinear Geo G C H :=
    hilbert_not_collinear_of_off_line
      Geo G C H lineFG
      hGC
      hGline
      hCline
      hHoff

  have hGCH_TCY :
      Geo.AngleCongruent G C H T C Y :=
    VerticalAngles
      Geo
      G C H T Y
      hGCT
      hHCY
      hGCH

  have hAngles :
      Geo.AngleCongruent T B E T C Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      T B E
      G C H
      T C Y
      hTBE_GCH
      hGCH_TCY

  --------------------------------------------------------------------
  -- Neutral alternate-angle criterion:
  --
  --   BE || CY.
  --------------------------------------------------------------------

  have hBE_CY :
      Geo.Parallel B E C Y :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo
      B E C T Y
      lineFG
      hBTC
      hBline
      hCline
      hOppEY
      hAngles

  --------------------------------------------------------------------
  -- CY is the same line as HC.
  --------------------------------------------------------------------

  have hCY_BE :
      Geo.Parallel C Y B E :=
    ParallelSymmetry
      Geo B E C Y hBE_CY

  have hYC_BE :
      Geo.Parallel Y C B E :=
    ParallelSwapFirstLine
      Geo C Y B E hCY_BE

  have hHC_BE :
      Geo.Parallel H C B E :=
    ParallelCollinearLeft
      Geo Y C H B E
      hHC
      hYC_BE
      hHYC

  have hBE_HC :
      Geo.Parallel B E H C :=
    ParallelSymmetry
      Geo H C B E hHC_BE

  exact
    ParallelSwapFirstLine
      Geo B E H C hBE_HC

theorem i36_intermediate_EBCH_no_crossing
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C E F G H : Geo.Point)
    (hEFGH : IsParallelogram Geo E F G H)
    (hBCF : Geo.Between B C F)
    (hCFG : Geo.Between C F G)
    (hBCFG : Geo.Congruent B C F G) :
    IsParallelogram Geo E B C H := by

  have hEH_BC :=
    i36_equal_parallel_EH_BC
      Geo B C E F G H
      hEFGH
      (hilbert_between_outer_trans
        Geo B C F G hBCF hCFG).2
      ((HilbertOrder.between_incidence
        B F G
        (hilbert_between_outer_trans
          Geo B C F G hBCF hCFG).1).2.2.2.1)
      hBCFG

  have hEB_HC :
      Geo.Parallel E B H C :=
    i36_cross_parallel
      Geo B C E F G H
      hEFGH hBCF hCFG hBCFG

  have hEB_CH :
      Geo.Parallel E B C H :=
    ParallelSwapSecondLine
      Geo E B H C hEB_HC

  have hBC_EH :
      Geo.Parallel B C E H :=
    ParallelSymmetry
      Geo E H B C hEH_BC.1

  have hBC_HE :
      Geo.Parallel B C H E :=
    ParallelSwapSecondLine
      Geo B C E H hBC_EH

  exact ⟨hEB_CH, hBC_HE⟩

theorem euclid_proposition_36
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F G H : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEFGH : IsParallelogram Geo E F G H)
    (hBCFG : Geo.Congruent B C F G)
    (hADE : Geo.Between A D E)
    (hDEH : Geo.Between D E H)
    (hBCF : Geo.Between B C F)
    (hCFG : Geo.Between C F G) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo E F G H) := by

  --------------------------------------------------------------------
  -- Upper line:
  --
  --   A-D-E-H
  --------------------------------------------------------------------

  have hTop :=
    hilbert_between_outer_trans
      Geo A D E H hADE hDEH

  have hAEH :
      Geo.Between A E H :=
    hTop.1

  have hADH :
      Geo.Between A D H :=
    hTop.2

  have hAEHcol :
      Collinear Geo A E H :=
    (HilbertOrder.between_incidence
      A E H hAEH).2.2.2.1

  --------------------------------------------------------------------
  -- Lower line:
  --
  --   B-C-F-G
  --------------------------------------------------------------------

  have hBottom :=
    hilbert_between_outer_trans
      Geo B C F G hBCF hCFG

  have hBFG :
      Geo.Between B F G :=
    hBottom.1

  have hBCG :
      Geo.Between B C G :=
    hBottom.2

  have hBFGcol :
      Collinear Geo B F G :=
    (HilbertOrder.between_incidence
      B F G hBFG).2.2.2.1

  --------------------------------------------------------------------
  -- Construct the intermediate parallelogram EBCH intrinsically.
  --------------------------------------------------------------------

  have hEBCH :
      IsParallelogram Geo E B C H :=
    i36_intermediate_EBCH_no_crossing
      Geo B C E F G H
      hEFGH hBCF hCFG hBCFG

  --------------------------------------------------------------------
  -- I.35 twice, through the intermediate parallelogram.
  --------------------------------------------------------------------

  exact
    i36_from_intermediate
      Geo A B C D E F G H
      hABCD
      hEFGH
      hEBCH
      hADH
      hAEHcol
      hBCG
      hBFGcol

end Geometry

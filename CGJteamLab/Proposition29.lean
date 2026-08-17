import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable {Geo : Geometry.Geo.{u}}

theorem euclid_proposition_29
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A C D B E F : Geo.Point)
    (hADC : Geo.Between A D C)
    (hCEB : Geo.Between C E B)
    (hDEF : Geo.Between D E F)
    (hCED : ¬ Collinear Geo C E D)
    (hParallel : Geo.Parallel A D B F) :
    Geo.AngleCongruent E C D E B F := by
  exact
    equal_angles_from_parallel
      Geo
      A C D
      B E F
      hADC
      hCEB
      hDEF
      hCED
      hParallel

theorem euclid_proposition_29_transversal
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D G H : Geo.Point)
    (trans : Geo.Line)
    (hAGB : Geo.Between A G B)
    (hCHD : Geo.Between C H D)
    (hGH : G ≠ H)
    (hGtrans : HilbertIncidence.OnLine G trans)
    (hHtrans : HilbertIncidence.OnLine H trans)
    (hOpposite : HilbertOppositeSide Geo A D trans)
    (hParallel : Geo.Parallel A B C D) :
    Geo.AngleCongruent A G H G H D := by

  have hAGBData :=
    HilbertOrder.between_incidence A G B hAGB

  have hCHDData :=
    HilbertOrder.between_incidence C H D hCHD

  have hGA : G ≠ A :=
    hAGBData.1.symm

  have hGB : G ≠ B :=
    hAGBData.2.1

  have hHD : H ≠ D :=
    hCHDData.2.1

  have hGAB : Collinear Geo G A B := by
    rcases hAGBData.2.2.2.1 with
      ⟨lineAB, hAline, hGline, hBline⟩
    exact ⟨lineAB, hGline, hAline, hBline⟩

  have hHCD : Collinear Geo H C D := by
    rcases hCHDData.2.2.2.1 with
      ⟨lineCD, hCline, hHline, hDline⟩
    exact ⟨lineCD, hHline, hCline, hDline⟩

  -- First transport AB || CD to GB || CD.
  have hGB_CD :
      Geo.Parallel G B C D :=
    ParallelCollinearLeft
      Geo A B G C D
      hGB
      hParallel
      hGAB

  -- Replace B by A on the same first line.
  have hGA_CD :
      Geo.Parallel G A C D :=
    collinear_parallel_trans
      Geo G A B C D
      hGA
      hGAB
      hGB_CD

  -- Transport the second parallel line from CD to HD.
  have hCD_GA :
      Geo.Parallel C D G A :=
    ParallelSymmetry
      Geo G A C D
      hGA_CD

  have hHD_GA :
      Geo.Parallel H D G A :=
    ParallelCollinearLeft
      Geo C D H G A
      hHD
      hCD_GA
      hHCD

  have hGA_HD :
      Geo.Parallel G A H D :=
    ParallelSymmetry
      Geo H D G A
      hHD_GA

  -- Choose an explicit point on the transversal between G and H.
  rcases hilbert_between_exists Geo G H hGH with
    ⟨M, hGMH⟩

  have hRaw :
      Geo.AngleCongruent M G A M H D :=
    hilbert_alternate_angles_of_parallel_oppositeSide_lines
      Geo
      G A
      H M D
      trans
      hGMH
      hGtrans
      hHtrans
      hOpposite
      hGA_HD

  -- Reverse the first angle so that its interior arm is GA.
  have hRaw' :
      Geo.AngleCongruent A G M M H D :=
    (Geo.angle_congruent_reverse_first
      M G A M H D).mp hRaw

  -- M and H determine the same ray from G.
  have hGMHray :
      HilbertSameRay Geo G M H :=
    hilbert_sameRay_of_between
      Geo G M H hGMH

  -- From the other endpoint, M and G determine the same ray from H.
  have hHMG : Geo.Between H M G :=
    (HilbertOrder.between_incidence
      G M H hGMH).2.2.2.2

  have hHMG_ray :
      HilbertSameRay Geo H M G :=
    hilbert_sameRay_of_between
      Geo H M G hHMG

  have hAtG :
      Geo.Angle A G M = Geo.Angle A G H :=
    hilbert_angle_eq_of_sameRay_second
      Geo G A M H hGMHray

  have hAtH :
      Geo.Angle M H D = Geo.Angle G H D :=
    hilbert_angle_eq_of_sameRay_first
      Geo H M G D hHMG_ray

  unfold Geometry.Geo.AngleCongruent at hRaw' ⊢
  rw [← hAtG, ← hAtH]
  exact hRaw'

theorem euclid_proposition_29_corresponding
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E G H : Geo.Point)
    (trans : Geo.Line)
    (hAGB : Geo.Between A G B)
    (hCHD : Geo.Between C H D)
    (hEGH : Geo.Between E G H)
    (hGH : G ≠ H)
    (hGtrans : HilbertIncidence.OnLine G trans)
    (hHtrans : HilbertIncidence.OnLine H trans)
    (hOpposite : HilbertOppositeSide Geo A D trans)
    (hParallel : Geo.Parallel A B C D) :
    Geo.AngleCongruent E G B G H D := by

  have hAlternate :
      Geo.AngleCongruent A G H G H D :=
    euclid_proposition_29_transversal
      (Geo := Geo)
      A B C D G H
      trans
      hAGB
      hCHD
      hGH
      hGtrans
      hHtrans
      hOpposite
      hParallel

  have hHGE : Geo.Between H G E :=
    (HilbertOrder.between_incidence
      E G H hEGH).2.2.2.2

  have hGHA :
      ¬ Collinear Geo G H A :=
    hilbert_not_collinear_of_off_line
      Geo G H A trans
      hGH
      hGtrans
      hHtrans
      hOpposite.1

  have hAGH :
      ¬ Collinear Geo A G H := by
    intro h
    exact hGHA
      (PrimCollinearCycle Geo A G H h)

  have hVerticalRaw :
      Geo.AngleCongruent A G H B G E :=
    VerticalAngles
      Geo
      A G H B E
      hAGB
      hHGE
      hAGH

  have hAGH_EGB :
      Geo.AngleCongruent A G H E G B :=
    (Geo.angle_congruent_reverse_second
      A G H B G E).mp
      hVerticalRaw

  have hEGB_AGH :
      Geo.AngleCongruent E G B A G H :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A G H
      E G B
      hAGH_EGB

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E G B
      A G H
      G H D
      hEGB_AGH
      hAlternate

theorem euclid_proposition_29_same_side
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D G H : Geo.Point)
    (trans : Geo.Line)
    (hAGB : Geo.Between A G B)
    (hCHD : Geo.Between C H D)
    (hGH : G ≠ H)
    (hGtrans : HilbertIncidence.OnLine G trans)
    (hHtrans : HilbertIncidence.OnLine H trans)
    (hOpposite : HilbertOppositeSide Geo A D trans)
    (hParallel : Geo.Parallel A B C D) :
    HilbertAnglesEqualTwoRightAnglesWithSupplement
      Geo G H D H G B A := by

  have hAlternate :
      Geo.AngleCongruent A G H G H D :=
    euclid_proposition_29_transversal
      (Geo := Geo)
      A B C D G H
      trans
      hAGB
      hCHD
      hGH
      hGtrans
      hHtrans
      hOpposite
      hParallel

  have hBGA : Geo.Between B G A :=
    (HilbertOrder.between_incidence
      A G B hAGB).2.2.2.2

  have hGHD_AGH :
      Geo.AngleCongruent G H D A G H :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A G H
      G H D
      hAlternate

  have hGHD_HGA :
      Geo.AngleCongruent G H D H G A :=
    (Geo.angle_congruent_reverse_second
      G H D A G H).mp
      hGHD_AGH

  exact
    ⟨hBGA, hGHD_HGA⟩

theorem euclid_proposition_29_all
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E G H : Geo.Point)
    (trans : Geo.Line)
    (hAGB : Geo.Between A G B)
    (hCHD : Geo.Between C H D)
    (hEGH : Geo.Between E G H)
    (hGH : G ≠ H)
    (hGtrans : HilbertIncidence.OnLine G trans)
    (hHtrans : HilbertIncidence.OnLine H trans)
    (hOpposite : HilbertOppositeSide Geo A D trans)
    (hParallel : Geo.Parallel A B C D) :
    Geo.AngleCongruent A G H G H D
      ∧ Geo.AngleCongruent E G B G H D
      ∧ HilbertAnglesEqualTwoRightAnglesWithSupplement
          Geo G H D H G B A := by

  have hAlternate :
      Geo.AngleCongruent A G H G H D :=
    euclid_proposition_29_transversal
      (Geo := Geo)
      A B C D G H
      trans
      hAGB
      hCHD
      hGH
      hGtrans
      hHtrans
      hOpposite
      hParallel

  have hCorresponding :
      Geo.AngleCongruent E G B G H D :=
    euclid_proposition_29_corresponding
      (Geo := Geo)
      A B C D E G H
      trans
      hAGB
      hCHD
      hEGH
      hGH
      hGtrans
      hHtrans
      hOpposite
      hParallel

  have hSameSide :
      HilbertAnglesEqualTwoRightAnglesWithSupplement
        Geo G H D H G B A :=
    euclid_proposition_29_same_side
      (Geo := Geo)
      A B C D G H
      trans
      hAGB
      hCHD
      hGH
      hGtrans
      hHtrans
      hOpposite
      hParallel

  exact ⟨hAlternate, hCorresponding, hSameSide⟩


end Geometry

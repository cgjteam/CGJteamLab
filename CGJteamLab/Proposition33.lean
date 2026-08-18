import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable {Geo : Geometry.Geo.{u}}

/--
Euclid I.33.

If two equal and parallel straight segments AB and CD are joined
towards the same parts, then the joining segments AC and BD are
also equal and parallel.

The phrase "towards the same parts" is represented synthetically by
requiring A and C to lie on the same side of the line BD.  This is
exactly the orientation condition needed to exclude the crossed
(bow-tie) configuration.
-/
theorem euclid_proposition_33
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hParallel : Geo.Parallel A B C D)
    (hCongruent : Geo.Congruent A B C D)
    (hOriented :
      exists l : Geo.Line,
        HilbertIncidence.OnLine B l /\
        HilbertIncidence.OnLine D l /\
        HilbertSameSide Geo A C l) :
    Geo.Parallel A C B D /\
    Geo.Congruent A C B D := by

  have hData :
      OnePairParallelCongruent Geo A C D B :=
    {
      parallel := hParallel
      congruent := hCongruent
      oriented := hOriented
    }

  have hParallelogram :
      IsParallelogram Geo A C D B :=
    OnePairParallelCongruentCriterion
      Geo A C D B hData

  have hParallelAC_DB :
      Geo.Parallel A C D B :=
    hParallelogram.1

  have hParallelAC_BD :
      Geo.Parallel A C B D :=
    ParallelSwapSecondLine
      Geo A C D B hParallelAC_DB

  have hSides :
      OppositeSidesCongruent Geo A C D B :=
    ParallelogramOppositeSidesCongruent
      Geo A C D B hParallelogram

  have hCongruentAC_DB :
      Geo.Congruent A C D B :=
    hSides.1

  have hCongruentAC_BD :
      Geo.Congruent A C B D :=
    CongruentSwapSecond
      Geo A C D B hCongruentAC_DB

  exact
    ⟨hParallelAC_BD, hCongruentAC_BD⟩

/--
Euclid I.33 in the explicit crossing configuration used by Beeson.

The equal parallel segments AB and CD are joined in the same direction,
expressed by the fact that the cross-joins AD and BC meet internally:

    A - M - D
    B - M - C

From this configuration the transversal BC separates A and D.
The Euclidean alternate-angle theorem then gives the included-angle
congruence needed for SAS. SAS yields AC ~= BD and a second pair of
equal alternate angles, from which AC || BD follows.
-/
theorem euclid_proposition_33_crossing
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D M : Geo.Point)
    (hParallel : Geo.Parallel A B C D)
    (hCongruent : Geo.Congruent A B C D)
    (hAMD : Geo.Between A M D)
    (hBMC : Geo.Between B M C) :
    Geo.Parallel A C B D /\
    Geo.Congruent A C B D := by

  have hBMCData :=
    HilbertOrder.between_incidence B M C hBMC

  have hBC : Not (B = C) :=
    hBMCData.2.2.1

  have hCB : Not (C = B) := by
    intro h
    exact hBC h.symm

  rcases hBMCData.2.2.2.1 with
    ⟨trans, hBtrans, hMtrans, hCtrans⟩

  have hAB : Not (A = B) :=
    hParallel.1

  have hCD : Not (C = D) :=
    hParallel.2.1

  ------------------------------------------------------------
  -- A and D are off the transversal BC.
  ------------------------------------------------------------

  rcases HilbertPlaneIncidence.line_through
      A B hAB with
    ⟨lineAB, hAab, hBab⟩

  rcases HilbertPlaneIncidence.line_through
      C D hCD with
    ⟨lineCD, hCcd, hDcd⟩

  have hAoff :
      Not (HilbertIncidence.OnLine A trans) := by
    intro hAtrans

    have hC_AB :
        C ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B C trans
        hAB hAtrans hBtrans).mpr hCtrans

    have hC_CD :
        C ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D C lineCD
        hCD hCcd hDcd).mpr hCcd

    exact
      Set.disjoint_left.mp hParallel.2.2
        hC_AB hC_CD

  have hDoff :
      Not (HilbertIncidence.OnLine D trans) := by
    intro hDtrans

    have hB_AB :
        B ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B B lineAB
        hAB hAab hBab).mpr hBab

    have hB_CD :
        B ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D B trans
        hCD hCtrans hDtrans).mpr hBtrans

    exact
      Set.disjoint_left.mp hParallel.2.2
        hB_AB hB_CD

  ------------------------------------------------------------
  -- A-M-D and M on BC put A and D on opposite sides of BC.
  ------------------------------------------------------------

  have hOppositeAD :
      HilbertOppositeSide Geo A D trans :=
    ⟨hAoff,
      hDoff,
      ⟨M, hAMD, hMtrans⟩⟩

  ------------------------------------------------------------
  -- Choose an interior point N of the transversal BC.
  ------------------------------------------------------------

  rcases hilbert_between_exists Geo B C hBC with
    ⟨N, hBNC⟩

  have hCNB : Geo.Between C N B :=
    (HilbertOrder.between_incidence
      B N C hBNC).2.2.2.2

  have hRayBNC :
      HilbertSameRay Geo B N C :=
    hilbert_sameRay_of_between
      Geo B N C hBNC

  have hRayCNB :
      HilbertSameRay Geo C N B :=
    hilbert_sameRay_of_between
      Geo C N B hCNB

  ------------------------------------------------------------
  -- I.29 / Hilbert Theorem 30:
  -- AB || CD cut by the transversal BC.
  ------------------------------------------------------------

  have hBA_CD :
      Geo.Parallel B A C D :=
    ParallelSwapFirstLine
      Geo A B C D hParallel

  have hRawAngle :
      Geo.AngleCongruent N B A N C D :=
    hilbert_alternate_angles_of_parallel_oppositeSide_lines
      Geo
      B A
      C N D
      trans
      hBNC
      hBtrans
      hCtrans
      hOppositeAD
      hBA_CD

  have hNBA_CBA :
      Geo.Angle N B A =
      Geo.Angle C B A :=
    hilbert_angle_eq_of_sameRay_first
      Geo B N C A hRayBNC

  have hNCD_BCD :
      Geo.Angle N C D =
      Geo.Angle B C D :=
    hilbert_angle_eq_of_sameRay_first
      Geo C N B D hRayCNB

  have hCBA_BCD :
      Geo.AngleCongruent C B A B C D := by
    unfold Geometry.Geo.AngleCongruent
      at hRawAngle ⊢
    rw [← hNBA_CBA, ← hNCD_BCD]
    exact hRawAngle

  have hABC_BCD :
      Geo.AngleCongruent A B C B C D :=
    (Geo.angle_congruent_reverse_first
      C B A B C D).mp hCBA_BCD

  have hABC_DCB :
      Geo.AngleCongruent A B C D C B :=
    (Geo.angle_congruent_reverse_second
      A B C B C D).mp hABC_BCD

  ------------------------------------------------------------
  -- Prepare SAS for triangles BAC and CDB.
  ------------------------------------------------------------

  have hBCA :
      Not (Collinear Geo B C A) :=
    hilbert_not_collinear_of_off_line
      Geo
      B C A
      trans
      hBC
      hBtrans
      hCtrans
      hAoff

  have hBAC :
      Not (Collinear Geo B A C) := by
    intro h
    exact hBCA
      (PrimCollinearRotate Geo B A C h)

  have hCBD :
      Not (Collinear Geo C B D) :=
    hilbert_not_collinear_of_off_line
      Geo
      C B D
      trans
      hCB
      hCtrans
      hBtrans
      hDoff

  have hCDB :
      Not (Collinear Geo C D B) := by
    intro h
    exact hCBD
      (PrimCollinearRotate Geo C D B h)

  have hBA_CD_congruent :
      Geo.Congruent B A C D :=
    CongruentReverseFirst
      Geo A B C D hCongruent

  have hBC_CB :
      Geo.Congruent B C C B :=
    CongruentSwapSecond
      Geo B C B C
      (hilbert_congruent_reflexive Geo B C)

  ------------------------------------------------------------
  -- SAS.
  ------------------------------------------------------------

  have hTriangles :
      TriangleCongruenceResult
        Geo B A C C D B :=
    SAS
      Geo
      B A C
      C D B
      hBAC
      hCDB
      hBA_CD_congruent
      hABC_DCB
      hBC_CB

  ------------------------------------------------------------
  -- First conclusion: AC ~= BD.
  ------------------------------------------------------------

  have hAC_DB :
      Geo.Congruent A C D B :=
    hTriangles.sideBC

  have hAC_BD :
      Geo.Congruent A C B D :=
    CongruentSwapSecond
      Geo A C D B hAC_DB

  ------------------------------------------------------------
  -- The remaining SAS angle gives the alternate angles
  -- needed for AC || BD.
  ------------------------------------------------------------

  have hBCA_CBD :
      Geo.AngleCongruent B C A C B D :=
    hTriangles.angleC

  have hNCA_BCA :
      Geo.Angle N C A =
      Geo.Angle B C A :=
    hilbert_angle_eq_of_sameRay_first
      Geo C N B A hRayCNB

  have hNBD_CBD :
      Geo.Angle N B D =
      Geo.Angle C B D :=
    hilbert_angle_eq_of_sameRay_first
      Geo B N C D hRayBNC

  have hAlternate :
      Geo.AngleCongruent N C A N B D := by
    unfold Geometry.Geo.AngleCongruent
      at hBCA_CBD ⊢
    rw [hNCA_BCA, hNBD_CBD]
    exact hBCA_CBD

  ------------------------------------------------------------
  -- I.27: equal alternate angles imply parallel lines.
  ------------------------------------------------------------

  have hCA_BD :
      Geo.Parallel C A B D :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo
      C A
      B N D
      trans
      hCNB
      hCtrans
      hBtrans
      hOppositeAD
      hAlternate

  have hParallelAC_BD :
      Geo.Parallel A C B D :=
    ParallelSwapFirstLine
      Geo C A B D hCA_BD

  exact
    ⟨hParallelAC_BD, hAC_BD⟩
end Geometry

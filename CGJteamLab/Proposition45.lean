import CGJteamLab.Proposition44

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.45
--
-- To construct, in a given rectilineal angle, a parallelogram equal
-- to a given rectilineal figure.
--
-- The library represents a rectilineal figure after triangulation as
-- `HilbertTriangulatedFigure Geo`, a finite list of `HilbertTriangle`
-- values.  Its scissors term, `rectilinealTerm`, is the sum of the
-- corresponding triangle terms.
--
-- The proof follows Euclid's recursive construction.  For a single
-- triangle, I.42 supplies the required parallelogram directly.  In the
-- induction step, the next triangle is placed as an oriented adjacent
-- parallelogram by the I.44 machinery, the required strict order is
-- recovered, the two parallelograms are pasted into one larger
-- parallelogram, and both scissors content and the prescribed angle are
-- preserved.  Thus `i45_extend_parallelogram` is a derived theorem;
-- I.45 introduces no additional geometric or content axiom.
------------------------------------------------------------------------

/--
The scissors term of a triangulated rectilineal figure.
-/
def rectilinealTerm
    (L : HilbertTriangulatedFigure Geo) :
    HilbertScissorsTerm Geo :=
  (L.map
    (fun t =>
      hilbertScissorsTriangle Geo t.A t.B t.C)).sum

theorem rectilinealTerm_cons
    (hd : HilbertTriangle Geo)
    (tl : HilbertTriangulatedFigure Geo) :
    rectilinealTerm Geo (hd :: tl) =
      hilbertScissorsTriangle Geo hd.A hd.B hd.C +
      rectilinealTerm Geo tl := by
  simp [rectilinealTerm]

theorem rectilinealTerm_nil :
    rectilinealTerm Geo ([] : HilbertTriangulatedFigure Geo) = 0 := by
  simp [rectilinealTerm]

theorem i45_outer_first_parallel
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D L M : Geo.Point)
    (hRight : IsParallelogram Geo B C M L)
    (hDCM : Geo.Between D C M)
    (hABL : Geo.Between A B L) :
    Geo.Parallel A L M D := by

  have hCM_LB :
      Geo.Parallel C M L B :=
    hRight.2

  have hDM :
      D ≠ M :=
    (HilbertOrder.between_incidence
      D C M hDCM).2.2.1

  have hDCMcol :
      Collinear Geo D C M :=
    (HilbertOrder.between_incidence
      D C M hDCM).2.2.2.1

  have hDM_LB :
      Geo.Parallel D M L B :=
    ParallelCollinearLeft
      Geo C M D L B
      hDM
      hCM_LB
      hDCMcol

  have hLB_DM :
      Geo.Parallel L B D M :=
    ParallelSymmetry
      Geo D M L B hDM_LB

  have hAL :
      A ≠ L :=
    (HilbertOrder.between_incidence
      A B L hABL).2.2.1

  have hLA :
      L ≠ A :=
    hAL.symm

  have hABLcol :
      Collinear Geo A B L :=
    (HilbertOrder.between_incidence
      A B L hABL).2.2.2.1

  have hBLA :
      Collinear Geo B L A :=
    PrimCollinearCycle
      Geo A B L hABLcol

  have hLAB :
      Collinear Geo L A B :=
    PrimCollinearCycle
      Geo B L A hBLA

  have hLA_DM :
      Geo.Parallel L A D M :=
    collinear_parallel_trans
      Geo
      L A B
      D M
      hLA
      hLAB
      hLB_DM

  have hAL_DM :
      Geo.Parallel A L D M :=
    ParallelSwapFirstLine
      Geo L A D M hLA_DM

  exact
    ParallelSwapSecondLine
      Geo A L D M hAL_DM

theorem i45_outer_second_parallel
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D L M : Geo.Point)
    (hLeft : IsParallelogram Geo A B C D)
    (hRight : IsParallelogram Geo B C M L)
    (hABL : Geo.Between A B L) :
    Geo.Parallel A D L M := by

  have hDA_BC :
      Geo.Parallel D A B C :=
    ParallelSymmetry
      Geo B C D A hLeft.2

  have hML_BC :
      Geo.Parallel M L B C :=
    ParallelSymmetry
      Geo B C M L hRight.1

  have hLM_BC :
      Geo.Parallel L M B C :=
    ParallelSwapFirstLine
      Geo M L B C hML_BC

  have hDA :
      D ≠ A :=
    hDA_BC.1

  have hBC :
      B ≠ C :=
    hDA_BC.2.1

  have hLM :
      L ≠ M :=
    hLM_BC.1

  have hDistinct :
      Geo.PointLine D A ≠ Geo.PointLine L M := by

    intro hEq

    rcases
        HilbertPlaneIncidence.line_through
          D A hDA with
      ⟨lineDA, hDda, hAda⟩

    rcases
        HilbertPlaneIncidence.line_through
          L M hLM with
      ⟨lineLM, hLlm, hMlm⟩

    rcases
        HilbertPlaneIncidence.line_through
          B C hBC with
      ⟨lineBC, hBbc, hCbc⟩

    have hL_LM :
        L ∈ Geo.PointLine L M :=
      (hilbert_mem_pointLine_iff_onLine
        Geo L M L lineLM
        hLM hLlm hMlm).mpr hLlm

    have hL_DA :
        L ∈ Geo.PointLine D A := by
      rw [hEq]
      exact hL_LM

    have hLda :
        HilbertIncidence.OnLine L lineDA :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D A L lineDA
        hDA hDda hAda).mp hL_DA

    have hBda :
        HilbertIncidence.OnLine B lineDA :=
      hilbert_between_on_line
        Geo A B L lineDA
        hAda hLda hABL

    have hB_DA :
        B ∈ Geo.PointLine D A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D A B lineDA
        hDA hDda hAda).mpr hBda

    have hB_BC :
        B ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C B lineBC
        hBC hBbc hCbc).mpr hBbc

    exact
      Set.disjoint_left.mp
        hDA_BC.2.2
        hB_DA
        hB_BC

  have hDA_LM :
      Geo.Parallel D A L M :=
    hilbert_parallel_transitive_distinct
      Geo
      D A
      L M
      B C
      hDA_BC
      hLM_BC
      hDistinct

  exact
    ParallelSwapFirstLine
      Geo D A L M hDA_LM

theorem i45_paste_parallelograms_geometry
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D L M : Geo.Point)
    (hLeft : IsParallelogram Geo A B C D)
    (hRight : IsParallelogram Geo B C M L)
    (hDCM : Geo.Between D C M)
    (hABL : Geo.Between A B L) :
    IsParallelogram Geo A L M D := by

  have hAL_MD :
      Geo.Parallel A L M D :=
    i45_outer_first_parallel
      Geo
      A B C D L M
      hRight
      hDCM
      hABL

  have hAD_LM :
      Geo.Parallel A D L M :=
    i45_outer_second_parallel
      Geo
      A B C D L M
      hLeft
      hRight
      hABL

  exact
    ParallelogramOfParallel
      Geo
      A L M D
      hAL_MD
      hAD_LM

theorem i45_paste_parallelograms_content_of_crossing
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D L M X : Geo.Point)
    (hABL : Geo.Between A B L)
    (hDCM : Geo.Between D C M)
    (hAXM : Geo.Between A X M)
    (hBXC : Geo.Between B X C) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A L M D)
      (hilbertParallelogramTerm Geo A B C D +
       hilbertParallelogramTerm Geo B C M L) := by

  have hTop0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      M A L B hABL

  have hTop :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A L M)
        (hilbertScissorsTriangle Geo A B M +
         hilbertScissorsTriangle Geo B M L) := by

    rw [scissors_triangle_cycle Geo M A L] at hTop0
    rw [scissors_triangle_cycle Geo M A B] at hTop0
    rw [scissors_triangle_cycle Geo M B L] at hTop0
    rw [scissors_triangle_swap23 Geo B L M] at hTop0

    exact hTop0

  have hMCD :
      Geo.Between M C D :=
    (HilbertOrder.between_incidence
      D C M hDCM).2.2.2.2

  have hBottom :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A M D)
        (hilbertScissorsTriangle Geo A M C +
         hilbertScissorsTriangle Geo A C D) :=
    HilbertScissorsEq.split
      (Geo := Geo)
      A M D C hMCD

  have hOuter :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A L M D)
        ((hilbertScissorsTriangle Geo A B M +
          hilbertScissorsTriangle Geo B M L) +
         (hilbertScissorsTriangle Geo A M C +
          hilbertScissorsTriangle Geo A C D)) := by

    simpa [hilbertParallelogramTerm] using
      (HilbertScissorsEq.add
        (Geo := Geo)
        hTop
        hBottom)

  have hCross0 :=
    crossing_quadrilateral_two_triangulations
      Geo
      A B M C X
      hAXM
      hBXC

  have hCross :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B M +
         hilbertScissorsTriangle Geo A M C)
        (hilbertScissorsTriangle Geo A B C +
         hilbertScissorsTriangle Geo B C M) := by

    rw [scissors_triangle_swap23 Geo B M C] at hCross0
    exact hCross0

  have hKeep :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B M L +
         hilbertScissorsTriangle Geo A C D)
        (hilbertScissorsTriangle Geo B M L +
         hilbertScissorsTriangle Geo A C D) :=
    HilbertScissorsEq.refl
      (Geo := Geo)
      (hilbertScissorsTriangle Geo B M L +
       hilbertScissorsTriangle Geo A C D)

  have hMiddle0 :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hCross
      hKeep

  have hMiddle :
      HilbertScissorsEq Geo
        ((hilbertScissorsTriangle Geo A B M +
          hilbertScissorsTriangle Geo B M L) +
         (hilbertScissorsTriangle Geo A M C +
          hilbertScissorsTriangle Geo A C D))
        ((hilbertScissorsTriangle Geo A B C +
          hilbertScissorsTriangle Geo A C D) +
         (hilbertScissorsTriangle Geo B C M +
          hilbertScissorsTriangle Geo B M L)) := by

    have hLeftRearr :
        ((hilbertScissorsTriangle Geo A B M +
          hilbertScissorsTriangle Geo B M L) +
         (hilbertScissorsTriangle Geo A M C +
          hilbertScissorsTriangle Geo A C D))
          =
        ((hilbertScissorsTriangle Geo A B M +
          hilbertScissorsTriangle Geo A M C) +
         (hilbertScissorsTriangle Geo B M L +
          hilbertScissorsTriangle Geo A C D)) := by

      calc
        ((hilbertScissorsTriangle Geo A B M +
          hilbertScissorsTriangle Geo B M L) +
         (hilbertScissorsTriangle Geo A M C +
          hilbertScissorsTriangle Geo A C D))
            =
          hilbertScissorsTriangle Geo A B M +
            (hilbertScissorsTriangle Geo B M L +
             (hilbertScissorsTriangle Geo A M C +
              hilbertScissorsTriangle Geo A C D)) :=
          Multiset.add_assoc _ _ _

        _ =
          hilbertScissorsTriangle Geo A B M +
            ((hilbertScissorsTriangle Geo B M L +
              hilbertScissorsTriangle Geo A M C) +
             hilbertScissorsTriangle Geo A C D) := by
          apply congrArg
            (fun T =>
              hilbertScissorsTriangle Geo A B M + T)
          exact
            (Multiset.add_assoc
              (hilbertScissorsTriangle Geo B M L)
              (hilbertScissorsTriangle Geo A M C)
              (hilbertScissorsTriangle Geo A C D)).symm

        _ =
          hilbertScissorsTriangle Geo A B M +
            ((hilbertScissorsTriangle Geo A M C +
              hilbertScissorsTriangle Geo B M L) +
             hilbertScissorsTriangle Geo A C D) := by
          apply congrArg
            (fun T =>
              hilbertScissorsTriangle Geo A B M + T)
          rw [Multiset.add_comm
            (hilbertScissorsTriangle Geo B M L)
            (hilbertScissorsTriangle Geo A M C)]

        _ =
          hilbertScissorsTriangle Geo A B M +
            (hilbertScissorsTriangle Geo A M C +
             (hilbertScissorsTriangle Geo B M L +
              hilbertScissorsTriangle Geo A C D)) := by
          apply congrArg
            (fun T =>
              hilbertScissorsTriangle Geo A B M + T)
          exact
            Multiset.add_assoc
              (hilbertScissorsTriangle Geo A M C)
              (hilbertScissorsTriangle Geo B M L)
              (hilbertScissorsTriangle Geo A C D)

        _ =
          ((hilbertScissorsTriangle Geo A B M +
            hilbertScissorsTriangle Geo A M C) +
           (hilbertScissorsTriangle Geo B M L +
            hilbertScissorsTriangle Geo A C D)) :=
          (Multiset.add_assoc _ _ _).symm

    have hRightRearr :
        ((hilbertScissorsTriangle Geo A B C +
          hilbertScissorsTriangle Geo A C D) +
         (hilbertScissorsTriangle Geo B C M +
          hilbertScissorsTriangle Geo B M L))
          =
        ((hilbertScissorsTriangle Geo A B C +
          hilbertScissorsTriangle Geo B C M) +
         (hilbertScissorsTriangle Geo B M L +
          hilbertScissorsTriangle Geo A C D)) := by

      calc
        ((hilbertScissorsTriangle Geo A B C +
          hilbertScissorsTriangle Geo A C D) +
         (hilbertScissorsTriangle Geo B C M +
          hilbertScissorsTriangle Geo B M L))
            =
          hilbertScissorsTriangle Geo A B C +
            (hilbertScissorsTriangle Geo A C D +
             (hilbertScissorsTriangle Geo B C M +
              hilbertScissorsTriangle Geo B M L)) :=
          Multiset.add_assoc _ _ _

        _ =
          hilbertScissorsTriangle Geo A B C +
            (hilbertScissorsTriangle Geo B C M +
             (hilbertScissorsTriangle Geo A C D +
              hilbertScissorsTriangle Geo B M L)) := by
          apply congrArg
            (fun T =>
              hilbertScissorsTriangle Geo A B C + T)
          calc
            hilbertScissorsTriangle Geo A C D +
                (hilbertScissorsTriangle Geo B C M +
                 hilbertScissorsTriangle Geo B M L)
                =
              (hilbertScissorsTriangle Geo A C D +
               hilbertScissorsTriangle Geo B C M) +
                hilbertScissorsTriangle Geo B M L :=
              (Multiset.add_assoc _ _ _).symm

            _ =
              (hilbertScissorsTriangle Geo B C M +
               hilbertScissorsTriangle Geo A C D) +
                hilbertScissorsTriangle Geo B M L := by
              rw [Multiset.add_comm
                (hilbertScissorsTriangle Geo A C D)
                (hilbertScissorsTriangle Geo B C M)]

            _ =
              hilbertScissorsTriangle Geo B C M +
                (hilbertScissorsTriangle Geo A C D +
                 hilbertScissorsTriangle Geo B M L) :=
              Multiset.add_assoc _ _ _

        _ =
          hilbertScissorsTriangle Geo A B C +
            (hilbertScissorsTriangle Geo B C M +
             (hilbertScissorsTriangle Geo B M L +
              hilbertScissorsTriangle Geo A C D)) := by
          apply congrArg
            (fun T =>
              hilbertScissorsTriangle Geo A B C +
                (hilbertScissorsTriangle Geo B C M + T))
          exact
            Multiset.add_comm
              (hilbertScissorsTriangle Geo A C D)
              (hilbertScissorsTriangle Geo B M L)

        _ =
          ((hilbertScissorsTriangle Geo A B C +
            hilbertScissorsTriangle Geo B C M) +
           (hilbertScissorsTriangle Geo B M L +
            hilbertScissorsTriangle Geo A C D)) :=
          (Multiset.add_assoc _ _ _).symm

    rw [hLeftRearr, hRightRearr]

    exact hMiddle0

  have hResult :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hOuter
      hMiddle

  simpa [hilbertParallelogramTerm] using hResult

theorem i45_paste_crossing
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D L M : Geo.Point)
    (hLeft : IsParallelogram Geo A B C D)
    (hRight : IsParallelogram Geo B C M L)
    (hDCM : Geo.Between D C M)
    (hABL : Geo.Between A B L) :
    ∃ X : Geo.Point,
      Geo.Between A X M ∧
      Geo.Between B X C := by

  --------------------------------------------------------------------
  -- The outer parallelogram ALMD.
  --------------------------------------------------------------------

  have hOuter :
      IsParallelogram Geo A L M D :=
    i45_paste_parallelograms_geometry
      Geo
      A B C D L M
      hLeft
      hRight
      hDCM
      hABL

  --------------------------------------------------------------------
  -- Fix the carrier BC.
  --
  -- DA || BC, so A and D lie off BC.
  --------------------------------------------------------------------

  have hDA_BC :
      Geo.Parallel D A B C :=
    ParallelSymmetry
      Geo B C D A hLeft.2

  rcases
      parallel_endpoints_sameSide
        Geo D A B C hDA_BC
    with
    ⟨lineBC, hBbc, hCbc, hDASame⟩

  have hAoff :
      ¬ HilbertIncidence.OnLine A lineBC :=
    hDASame.2.1

  --------------------------------------------------------------------
  -- ML || BC, so M and L lie off the same carrier BC.
  --------------------------------------------------------------------

  have hML_BC :
      Geo.Parallel M L B C :=
    ParallelSymmetry
      Geo B C M L hRight.1

  rcases
      parallel_endpoints_sameSide
        Geo M L B C hML_BC
    with
    ⟨lineBC', hBbc', hCbc', hMLSame⟩

  have hBC :
      B ≠ C :=
    hRight.1.1

  have hLineEq :
      lineBC = lineBC' :=
    HilbertPlaneIncidence.line_unique
      B C hBC
      lineBC lineBC'
      hBbc hCbc
      hBbc' hCbc'

  subst lineBC'

  have hMoff :
      ¬ HilbertIncidence.OnLine M lineBC :=
    hMLSame.1

  have hLoff :
      ¬ HilbertIncidence.OnLine L lineBC :=
    hMLSame.2.1

  --------------------------------------------------------------------
  -- Triangle A-L-M is noncollinear.
  --
  -- Otherwise A would lie on LM; but LM || DA and A lies on DA.
  --------------------------------------------------------------------

  have hALM :
      ¬ Collinear Geo A L M := by

    intro hCol

    have hLM :
        L ≠ M :=
      hOuter.2.1

    have hDA :
        D ≠ A :=
      hOuter.2.2.1

    rcases hCol with
      ⟨lineALM, hAalm, hLalm, hMalm⟩

    have hA_LM :
        A ∈ Geo.PointLine L M :=
      (hilbert_mem_pointLine_iff_onLine
        Geo L M A lineALM
        hLM hLalm hMalm).mpr hAalm

    rcases
        HilbertPlaneIncidence.line_through
          D A hDA
      with
      ⟨lineDA, hDda, hAda⟩

    have hA_DA :
        A ∈ Geo.PointLine D A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D A A lineDA
        hDA hDda hAda).mpr hAda

    exact
      Set.disjoint_left.mp
        hOuter.2.2.2
        hA_LM
        hA_DA

  --------------------------------------------------------------------
  -- BC enters triangle A-L-M through AL at B.
  --------------------------------------------------------------------

  have hMeetsAL :
      HilbertSegmentMeetsLine Geo A L lineBC :=
    ⟨B, hABL, hBbc⟩

  --------------------------------------------------------------------
  -- BC cannot leave through LM, because L and M are on the same
  -- side of BC.
  --------------------------------------------------------------------

  have hLMSame :
      HilbertSameSide Geo L M lineBC :=
    hilbert_sameSide_symm
      Geo M L lineBC hMLSame

  have hNotMeetsLM :
      ¬ HilbertSegmentMeetsLine Geo L M lineBC :=
    hilbert_sameSide_segment_avoids_line
      Geo L M lineBC hLMSame

  --------------------------------------------------------------------
  -- Forced Pasch: therefore BC meets AM internally.
  --------------------------------------------------------------------

  have hMeetsAM :
      HilbertSegmentMeetsLine Geo A M lineBC :=
    hilbert_pasch_forced
      Geo
      A L M
      lineBC
      hALM
      hAoff
      hLoff
      hMoff
      hMeetsAL
      hNotMeetsLM

  rcases hMeetsAM with
    ⟨X, hAXM, hXbc⟩

  have hBCX :
      Collinear Geo B C X :=
    ⟨lineBC, hBbc, hCbc, hXbc⟩

  --------------------------------------------------------------------
  -- AB || CM.
  --
  -- Start with AB || CD from the left parallelogram and transport
  -- CD along D-C-M.
  --------------------------------------------------------------------

  have hCD_AB :
      Geo.Parallel C D A B :=
    ParallelSymmetry
      Geo A B C D hLeft.1

  have hDCMcol :
      Collinear Geo D C M :=
    (HilbertOrder.between_incidence
      D C M hDCM).2.2.2.1

  have hCMD :
      Collinear Geo C M D :=
    PrimCollinearCycle
      Geo D C M hDCMcol

  have hMDC :
      Collinear Geo M D C :=
    PrimCollinearCycle
      Geo C M D hCMD

  have hMC :
      M ≠ C :=
    (HilbertOrder.between_incidence
      D C M hDCM).2.1.symm

  have hDC_AB :
      Geo.Parallel D C A B :=
    ParallelSwapFirstLine
      Geo C D A B hCD_AB

  have hMC_AB :
      Geo.Parallel M C A B :=
    ParallelCollinearLeft
      Geo
      D C M
      A B
      hMC
      hDC_AB
      hMDC

  have hCM_AB :
      Geo.Parallel C M A B :=
    ParallelSwapFirstLine
      Geo M C A B hMC_AB

  have hAB_CM :
      Geo.Parallel A B C M :=
    ParallelSymmetry
      Geo C M A B hCM_AB

  --------------------------------------------------------------------
  -- Since A-X-M and X lies on BC, parallel-order transfer gives
  -- B-X-C.
  --------------------------------------------------------------------

  have hBXC :
      Geo.Between B X C :=
    hilbert_collinear_between_of_parallel
      Geo
      A B C M X
      hAB_CM
      hAXM
      hBCX

  exact
    ⟨X, hAXM, hBXC⟩

theorem i45_paste_parallelograms_content
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D L M : Geo.Point)
    (hLeft : IsParallelogram Geo A B C D)
    (hRight : IsParallelogram Geo B C M L)
    (hDCM : Geo.Between D C M)
    (hABL : Geo.Between A B L) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A L M D)
      (hilbertParallelogramTerm Geo A B C D +
       hilbertParallelogramTerm Geo B C M L) := by

  rcases
      i45_paste_crossing
        Geo
        A B C D L M
        hLeft
        hRight
        hDCM
        hABL
    with
    ⟨X, hAXM, hBXC⟩

  exact
    i45_paste_parallelograms_content_of_crossing
      Geo
      A B C D L M X
      hABL
      hDCM
      hAXM
      hBXC

theorem i45_paste_equicomplementable
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D L M P Q R : Geo.Point)
    (hLeft : IsParallelogram Geo A B C D)
    (hRight : IsParallelogram Geo B C M L)
    (hDCM : Geo.Between D C M)
    (hABL : Geo.Between A B L)
    (hTriangleRight :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo P Q R)
        (hilbertParallelogramTerm Geo B C M L)) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A L M D)
      (hilbertScissorsTriangle Geo P Q R +
       hilbertParallelogramTerm Geo A B C D) := by

  have hPasteEq :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A L M D)
        (hilbertParallelogramTerm Geo A B C D +
         hilbertParallelogramTerm Geo B C M L) :=
    i45_paste_parallelograms_content
      Geo
      A B C D L M
      hLeft
      hRight
      hDCM
      hABL

  have hPaste :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A L M D)
        (hilbertParallelogramTerm Geo A B C D +
         hilbertParallelogramTerm Geo B C M L) :=
    equicomplementable_of_scissorsEq
      Geo hPasteEq

  have hLeftRefl :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A B C D) :=
    equicomplementable_refl
      Geo
      (hilbertParallelogramTerm Geo A B C D)

  have hRightTriangle :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C M L)
        (hilbertScissorsTriangle Geo P Q R) :=
    equicomplementable_symm
      Geo hTriangleRight

  have hSum :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D +
         hilbertParallelogramTerm Geo B C M L)
        (hilbertParallelogramTerm Geo A B C D +
         hilbertScissorsTriangle Geo P Q R) :=
    equicomplementable_add
      Geo
      hLeftRefl
      hRightTriangle

  have hResult :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A L M D)
        (hilbertParallelogramTerm Geo A B C D +
         hilbertScissorsTriangle Geo P Q R) :=
    equicomplementable_trans
      Geo
      hPaste
      hSum

  simpa [Multiset.add_comm] using hResult

theorem i45_paste_angle
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D L M X Y Z : Geo.Point)
    (hLeft : IsParallelogram Geo A B C D)
    (hRight : IsParallelogram Geo B C M L)
    (hDCM : Geo.Between D C M)
    (hABL : Geo.Between A B L)
    (hAngle : Geo.AngleCongruent A B C X Y Z) :
    Geo.AngleCongruent A L M X Y Z := by

  have hOuter :
      IsParallelogram Geo A L M D :=
    i45_paste_parallelograms_geometry
      Geo
      A B C D L M
      hLeft
      hRight
      hDCM
      hABL

  --------------------------------------------------------------------
  -- Opposite angles in the outer parallelogram:
  --
  --   angle ALM ~= angle MDA.
  --------------------------------------------------------------------

  have hOuterOpp :
      Geo.AngleCongruent A L M M D A :=
    ParallelogramOppositeAngleCongruent
      Geo
      A L M D
      hOuter

  --------------------------------------------------------------------
  -- Opposite angles in the old parallelogram:
  --
  --   angle ABC ~= angle CDA.
  --------------------------------------------------------------------

  have hLeftOpp :
      Geo.AngleCongruent A B C C D A :=
    ParallelogramOppositeAngleCongruent
      Geo
      A B C D
      hLeft

  --------------------------------------------------------------------
  -- D-C-M, hence C and M determine the same ray from D.
  -- Therefore angle CDA = angle MDA.
  --------------------------------------------------------------------

  have hRayDCM :
      HilbertSameRay Geo D C M :=
    hilbert_sameRay_of_between
      Geo D C M hDCM

  have hAngleAtD :
      Geo.Angle C D A =
      Geo.Angle M D A :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      D C M A
      hRayDCM

  have hOuterToCDA :
      Geo.AngleCongruent A L M C D A := by

    unfold Geometry.Geo.AngleCongruent at hOuterOpp ⊢
    rw [hAngleAtD]
    exact hOuterOpp

  --------------------------------------------------------------------
  -- angle CDA ~= angle ABC.
  --------------------------------------------------------------------

  have hCDA_ABC :
      Geo.AngleCongruent C D A A B C :=
    Geo.angle_congruent_symmetry
      A B C
      C D A
      hLeftOpp

  --------------------------------------------------------------------
  -- Hence angle ALM ~= angle ABC ~= angle XYZ.
  --------------------------------------------------------------------

  have hOuterOld :
      Geo.AngleCongruent A L M A B C :=
    Geo.angle_congruent_transitivity
      A L M
      C D A
      A B C
      hOuterToCDA
      hCDA_ABC

  exact
    Geo.angle_congruent_transitivity
      A L M
      A B C
      X Y Z
      hOuterOld
      hAngle

theorem i45_other_side_order
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (S T U V M L : Geo.Point)
    (hLeft : IsParallelogram Geo S T U V)
    (hRight : IsParallelogram Geo T U M L)
    (hVUM : Geo.Between V U M) :
    Geo.Between S T L := by

  --------------------------------------------------------------------
  -- The common side TU is used as a separator.
  --
  -- VS || TU, hence V and S lie on the same side of TU.
  --------------------------------------------------------------------

  have hVS_TU :
      Geo.Parallel V S T U :=
    ParallelSymmetry
      Geo T U V S hLeft.2

  rcases
      parallel_endpoints_sameSide
        Geo V S T U hVS_TU
    with
    ⟨base, hTbase, hUbase, hVSSame⟩

  have hTU :
      T ≠ U :=
    hLeft.2.1

  --------------------------------------------------------------------
  -- ML || TU, hence M and L lie on the same side of TU.
  --------------------------------------------------------------------

  have hML_TU :
      Geo.Parallel M L T U :=
    ParallelSymmetry
      Geo T U M L hRight.1

  rcases
      parallel_endpoints_sameSide
        Geo M L T U hML_TU
    with
    ⟨base', hTbase', hUbase', hMLSame'⟩

  have hBaseEq :
      base = base' :=
    HilbertPlaneIncidence.line_unique
      T U hTU
      base base'
      hTbase hUbase
      hTbase' hUbase'

  have hMLSame :
      HilbertSameSide Geo M L base := by
    rw [hBaseEq]
    exact hMLSame'

  --------------------------------------------------------------------
  -- V-U-M means that V and M are on opposite sides of TU.
  --------------------------------------------------------------------

  have hOppVM :
      HilbertOppositeSide Geo V M base :=
    ⟨hVSSame.1,
     hMLSame.1,
     ⟨U, hVUM, hUbase⟩⟩

  --------------------------------------------------------------------
  -- Transport through the two same-side pairs:
  --
  -- V opposite M,
  -- M same-side L
  -- gives V opposite L;
  --
  -- V same-side S
  -- then gives S opposite L.
  --------------------------------------------------------------------

  have hOppVL :
      HilbertOppositeSide Geo V L base :=
    hilbert_oppositeSide_transport_right
      Geo V M L base
      hOppVM
      hMLSame

  have hOppLV :
      HilbertOppositeSide Geo L V base :=
    hilbert_oppositeSide_symm
      Geo V L base hOppVL

  have hOppLS :
      HilbertOppositeSide Geo L S base :=
    hilbert_oppositeSide_transport_right
      Geo L V S base
      hOppLV
      hVSSame

  have hOppSL :
      HilbertOppositeSide Geo S L base :=
    hilbert_oppositeSide_symm
      Geo L S base hOppLS

  --------------------------------------------------------------------
  -- We now show that S,T,L lie on one carrier.
  --
  -- ST || UV.
  -- UM || LT, and V-U-M, so UV || LT.
  -- Thus ST and LT are the two parallels through T to UV.
  -- Euclidean uniqueness makes their carriers equal.
  --------------------------------------------------------------------

  have hVUMcol :
      Collinear Geo V U M :=
    (HilbertOrder.between_incidence
      V U M hVUM).2.2.2.1

  rcases hVUMcol with
    ⟨lineTop, hVtop, hUtop, hMtop⟩

  have hUVMcol :
      Collinear Geo U V M :=
    ⟨lineTop, hUtop, hVtop, hMtop⟩

  have hUV :
      U ≠ V :=
    hLeft.1.2.1

  have hUV_LT :
      Geo.Parallel U V L T :=
    collinear_parallel_trans
      Geo
      U V M
      L T
      hUV
      hUVMcol
      hRight.2

  have hLT_UV :
      Geo.Parallel L T U V :=
    ParallelSymmetry
      Geo U V L T hUV_LT

  have hST :
      S ≠ T :=
    hLeft.1.1

  have hLT :
      L ≠ T :=
    hLT_UV.1

  rcases
      HilbertPlaneIncidence.line_through
        S T hST
    with
    ⟨lineST, hSst, hTst⟩

  rcases
      HilbertPlaneIncidence.line_through
        L T hLT
    with
    ⟨lineLT, hLlt, hTlt⟩

  have hLinesST_top :
      HilbertLinesDisjoint Geo lineST lineTop := by

    rintro ⟨P, hPst, hPtop⟩

    have hPST :
        P ∈ Geo.PointLine S T :=
      (hilbert_mem_pointLine_iff_onLine
        Geo S T P lineST
        hST hSst hTst).mpr hPst

    have hPUV :
        P ∈ Geo.PointLine U V :=
      (hilbert_mem_pointLine_iff_onLine
        Geo U V P lineTop
        hUV hUtop hVtop).mpr hPtop

    exact
      Set.disjoint_left.mp
        hLeft.1.2.2
        hPST
        hPUV

  have hLinesLT_top :
      HilbertLinesDisjoint Geo lineLT lineTop := by

    rintro ⟨P, hPlt, hPtop⟩

    have hPLT :
        P ∈ Geo.PointLine L T :=
      (hilbert_mem_pointLine_iff_onLine
        Geo L T P lineLT
        hLT hLlt hTlt).mpr hPlt

    have hPUV :
        P ∈ Geo.PointLine U V :=
      (hilbert_mem_pointLine_iff_onLine
        Geo U V P lineTop
        hUV hUtop hVtop).mpr hPtop

    exact
      Set.disjoint_left.mp
        hLT_UV.2.2
        hPLT
        hPUV

  have hToffTop :
      ¬ HilbertIncidence.OnLine T lineTop := by
    intro hTtop
    exact
      hLinesST_top
        ⟨T, hTst, hTtop⟩

  have hLineEq :
      lineST = lineLT :=
    HilbertEuclideanPlane.parallel_unique
      (Geo := Geo)
      lineTop
      T
      hToffTop
      lineST
      lineLT
      hTst
      hLinesST_top
      hTlt
      hLinesLT_top

  have hLst :
      HilbertIncidence.OnLine L lineST := by
    rw [hLineEq]
    exact hLlt

  --------------------------------------------------------------------
  -- OppositeSide(S,L;base) gives some crossing X of SL with TU.
  -- But T also lies on both lines, hence incidence uniqueness gives X=T.
  --------------------------------------------------------------------

  rcases hOppSL.2.2 with
    ⟨X, hSXL, hXbase⟩

  have hXst :
      HilbertIncidence.OnLine X lineST :=
    hilbert_between_on_line
      Geo
      S X L
      lineST
      hSst
      hLst
      hSXL

  have hXT :
      X = T := by

    by_contra hXT

    have hSTeqBase :
        lineST = base :=
      HilbertPlaneIncidence.line_unique
        X T hXT
        lineST base
        hXst hTst
        hXbase hTbase

    have hSbase :
        HilbertIncidence.OnLine S base := by
      rw [← hSTeqBase]
      exact hSst

    exact
      hVSSame.2.1 hSbase

  subst X

  exact hSXL

theorem i45_extension_angle
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (S T U V E : Geo.Point)
    (hPar : IsParallelogram Geo S T U V)
    (hTUE : Geo.Between T U E) :
    Geo.AngleCongruent E U V S T U := by

  have hST_UV :
      Geo.Parallel S T U V :=
    hPar.1

  have hTU_VS :
      Geo.Parallel T U V S :=
    hPar.2

  rcases
      parallel_endpoints_sameSide
        Geo S T U V hST_UV
    with
    ⟨lineUV, hUuv, hVuv, hSTSame⟩

  have hToff :
      ¬ HilbertIncidence.OnLine T lineUV :=
    hSTSame.2.1

  have hData :=
    HilbertOrder.between_incidence
      T U E hTUE

  have hUE :
      U ≠ E :=
    hData.2.1

  have hTUEcol :
      Collinear Geo T U E :=
    hData.2.2.2.1

  have hUETcol :
      Collinear Geo U E T :=
    PrimCollinearCycle
      Geo T U E hTUEcol

  have hEoff :
      ¬ HilbertIncidence.OnLine E lineUV := by

    intro hEuv

    have hTuv :
        HilbertIncidence.OnLine T lineUV :=
      hilbert_collinear_on_line
        Geo
        U E T
        lineUV
        hUE
        hUuv
        hEuv
        hUETcol

    exact hToff hTuv

  have hOppTE :
      HilbertOppositeSide Geo T E lineUV :=
    ⟨hToff,
      hEoff,
      ⟨U, hTUE, hUuv⟩⟩

  have hOppET :
      HilbertOppositeSide Geo E T lineUV :=
    hilbert_oppositeSide_symm
      Geo T E lineUV hOppTE

  have hTSSame :
      HilbertSameSide Geo T S lineUV :=
    hilbert_sameSide_symm
      Geo S T lineUV hSTSame

  have hOppES :
      HilbertOppositeSide Geo E S lineUV :=
    hilbert_oppositeSide_transport_right
      Geo E T S lineUV hOppET hTSSame

  have hUT_VS :
      Geo.Parallel U T V S :=
    ParallelSwapFirstLine
      Geo T U V S hTU_VS

  have hUE_VS :
      Geo.Parallel U E V S :=
    collinear_parallel_trans
      Geo
      U E T
      V S
      hUE
      hUETcol
      hUT_VS

  have hUV :
      U ≠ V :=
    hST_UV.2.1

  rcases
      hilbert_between_exists
        Geo U V hUV
    with
    ⟨X, hUXV⟩

  have hAlt :
      Geo.AngleCongruent X U E X V S :=
    hilbert_alternate_angles_of_parallel_oppositeSide_lines
      Geo
      U E
      V X S
      lineUV
      hUXV
      hUuv
      hVuv
      hOppES
      hUE_VS

  have hVXU :
      Geo.Between V X U :=
    (HilbertOrder.between_incidence
      U X V hUXV).2.2.2.2

  have hRayUXV :
      HilbertSameRay Geo U X V :=
    hilbert_sameRay_of_between
      Geo U X V hUXV

  have hRayVXU :
      HilbertSameRay Geo V X U :=
    hilbert_sameRay_of_between
      Geo V X U hVXU

  have hAtU :
      Geo.Angle X U E =
      Geo.Angle V U E :=
    hilbert_angle_eq_of_sameRay_first
      Geo U X V E hRayUXV

  have hAtV :
      Geo.Angle X V S =
      Geo.Angle U V S :=
    hilbert_angle_eq_of_sameRay_first
      Geo V X U S hRayVXU

  have hVUE_UVS :
      Geo.AngleCongruent V U E U V S := by

    unfold Geometry.Geo.AngleCongruent
      at hAlt ⊢

    rw [← hAtU, ← hAtV]

    exact hAlt

  have hEUV_UVS :
      Geo.AngleCongruent E U V U V S :=
    (Geo.angle_congruent_reverse_first
      V U E U V S).mp hVUE_UVS

  have hSTU_UVS :
      Geo.AngleCongruent S T U U V S :=
    ParallelogramOppositeAngleCongruent
      Geo S T U V hPar

  have hUVS_STU :
      Geo.AngleCongruent U V S S T U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      S T U
      U V S
      hSTU_UVS

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E U V
      U V S
      S T U
      hEUV_UVS
      hUVS_STU

theorem i45_oriented_triangle_placement
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (S T U V P Q R : Geo.Point)
    (hPar : IsParallelogram Geo S T U V)
    (hPQR : Not (Collinear Geo P Q R)) :
    ∃ E F G : Geo.Point,
      Geo.Between T U E ∧
      IsParallelogram Geo U E F G ∧
      HilbertSameRay Geo U V G ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo P Q R)
        (hilbertParallelogramTerm Geo U E F G) := by

  --------------------------------------------------------------------
  -- STU is a genuine angle.
  --------------------------------------------------------------------

  have hSTU :
      Not (Collinear Geo S T U) := by

    intro hCol

    rcases hCol with
      ⟨lineSTU, hSline, hTline, hUline⟩

    have hST :
        S ≠ T :=
      hPar.1.1

    have hU_ST :
        U ∈ Geo.PointLine S T :=
      (hilbert_mem_pointLine_iff_onLine
        Geo S T U
        lineSTU
        hST
        hSline hTline).mpr
        hUline

    exact
      Set.disjoint_left.mp
        hPar.1.2.2
        hU_ST
        (intersection_test_left_mem Geo U V)

  --------------------------------------------------------------------
  -- I.42: make a source parallelogram equal to PQR
  -- and having angle STU.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_42
        Geo P Q R S T U
        hPQR hSTU
    with
    ⟨E0, F0, G0,
      hSourcePar,
      hSourceAngle,
      hTriangleSource⟩

  -- hSourcePar :
  --   IsParallelogram Geo F0 E0 R G0
  --
  -- hSourceAngle :
  --   angle F0 E0 R ~= angle S T U

  --------------------------------------------------------------------
  -- Extend TU beyond U.
  --------------------------------------------------------------------

  have hTU :
      T ≠ U :=
    hPar.2.1

  rcases
      HilbertOrder.between_extension
        T U hTU
    with
    ⟨W, hTUW⟩

  have hUW :
      U ≠ W :=
    (HilbertOrder.between_incidence
      T U W hTUW).2.1

  --------------------------------------------------------------------
  -- On ray UW lay off a copy of E0F0.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        E0 F0
        U W
        hUW
    with
    ⟨E, hRayUWE, hUE_E0F0⟩

  have hRayUTT :
      HilbertSameRay Geo U T T :=
    hilbert_sameRay_refl
      Geo U T hTU

  have hTUE :
      Geo.Between T U E :=
    hilbert_between_transport_sameRays
      Geo
      T U W
      T E
      hTUW
      hRayUTT
      hRayUWE

  --------------------------------------------------------------------
  -- On the OLD ray UV lay off a copy of E0R.
  -- This is the orientation control that I.44 by itself forgets.
  --------------------------------------------------------------------

  have hUV :
      U ≠ V :=
    hPar.1.2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        E0 R
        U V
        hUV
    with
    ⟨G, hRayUVG, hUG_E0R⟩

  --------------------------------------------------------------------
  -- E,U,V are noncollinear.
  --------------------------------------------------------------------

  have hTUV :
      Not (Collinear Geo T U V) := by

    intro hCol

    rcases hCol with
      ⟨lineTUV, hTline, hUline, hVline⟩

    have hV_TU :
        V ∈ Geo.PointLine T U :=
      (hilbert_mem_pointLine_iff_onLine
        Geo T U V
        lineTUV
        hTU
        hTline hUline).mpr
        hVline

    exact
      Set.disjoint_left.mp
        hPar.2.2.2
        hV_TU
        (intersection_test_left_mem Geo V S)

  have hTUEData :=
    HilbertOrder.between_incidence
      T U E hTUE

  have hUE :
      U ≠ E :=
    hTUEData.2.1

  have hTUEcol :
      Collinear Geo T U E :=
    hTUEData.2.2.2.1

  have hEUV :
      Not (Collinear Geo E U V) := by

    intro hCol

    rcases hTUEcol with
      ⟨lineTU, hTtu, hUtu, hEtu⟩

    rcases hCol with
      ⟨lineEUV, hEeuv, hUeuv, hVeuv⟩

    have hLineEq :
        lineTU = lineEUV :=
      HilbertPlaneIncidence.line_unique
        U E
        hUE
        lineTU lineEUV
        hUtu hEtu
        hUeuv hEeuv

    have hTeuv :
        HilbertIncidence.OnLine T lineEUV := by
      rw [← hLineEq]
      exact hTtu

    exact
      hTUV
        ⟨lineEUV, hTeuv, hUeuv, hVeuv⟩

  --------------------------------------------------------------------
  -- Replace V by G on the same ray: EUG is still noncollinear.
  --------------------------------------------------------------------

  have hEU :
      E ≠ U :=
    hUE.symm

  have hRayUEE :
      HilbertSameRay Geo U E E :=
    hilbert_sameRay_refl
      Geo U E hEU

  have hEUG :
      Not (Collinear Geo E U G) :=
    hilbert_noncollinear_of_sameRays
      Geo
      E U V
      E G
      hEUV
      hRayUEE
      hRayUVG

  have hUEG :
      Not (Collinear Geo U E G) := by
    intro h
    exact
      hEUG
        (PrimCollinearSwap
          Geo U E G h)

  --------------------------------------------------------------------
  -- Complete U-E-G to U-E-F-G.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo U E G hUEG
    with
    ⟨F, hPlacedPar⟩

  --------------------------------------------------------------------
  -- The placed angle EUG equals the source angle F0-E0-R.
  --------------------------------------------------------------------

  have hExtensionAngle :
      Geo.AngleCongruent E U V S T U :=
    i45_extension_angle
      Geo S T U V E
      hPar
      hTUE

  have hSTU_Source :
      Geo.AngleCongruent S T U F0 E0 R :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      F0 E0 R
      S T U
      hSourceAngle

  have hEUV_Source :
      Geo.AngleCongruent E U V F0 E0 R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E U V
      S T U
      F0 E0 R
      hExtensionAngle
      hSTU_Source

  have hAngleReplace :
      Geo.Angle E U V =
      Geo.Angle E U G :=
    hilbert_angle_eq_of_sameRay_second
      Geo U E V G hRayUVG

  have hPlacedAngle :
      Geo.AngleCongruent E U G F0 E0 R := by

    unfold Geometry.Geo.AngleCongruent
      at hEUV_Source ⊢

    rw [← hAngleReplace]

    exact hEUV_Source

  --------------------------------------------------------------------
  -- I.44 rigid-copy certificate:
  -- source parallelogram F0-E0-R-G0
  -- is equicomplementable with U-E-F-G.
  --------------------------------------------------------------------

  have hSourcePlaced :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo F0 E0 R G0)
        (hilbertParallelogramTerm Geo U E F G) :=
    i44_placed_parallelogram_content
      Geo
      U E F G
      F0 E0 R G0
      hSourcePar
      hPlacedPar
      hPlacedAngle
      hUE_E0F0
      hUG_E0R

  have hTrianglePlaced :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo P Q R)
        (hilbertParallelogramTerm Geo U E F G) :=
    equicomplementable_trans
      Geo
      hTriangleSource
      hSourcePlaced

  exact
    ⟨E, F, G,
      hTUE,
      hPlacedPar,
      hRayUVG,
      hTrianglePlaced⟩

theorem i45_positioned_content_ordered
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G : Geo.Point)
    (hABE : Geo.Between A B E)
    (hPar : IsParallelogram Geo B E F G) :
    ∃ M L : Geo.Point,
      IsParallelogram Geo A B M L ∧
      Geo.Between G B M ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B M L)
        (hilbertParallelogramTerm Geo B E F G) := by

  --------------------------------------------------------------------
  -- Same construction as i44_positioned_content.
  --------------------------------------------------------------------

  rcases
      i44_construct_H_ordered
        Geo A B E F G
        hABE hPar
    with
    ⟨H, hHGF, hAH_GB⟩

  rcases
      i44_construct_K_ordered
        Geo A B E F G H
        hABE hPar hHGF hAH_GB
    with
    ⟨K, hHBK, hFEK⟩

  rcases
      i44_construct_LM
        Geo A B E F G H K
        hABE hHGF hFEK
        hPar hAH_GB
    with
    ⟨Q, L, M,
      hKQ,
      hParBE_KQ,
      hHALcol,
      hGBM,
      hKQL,
      hKQM,
      hLKMcol⟩

  --------------------------------------------------------------------
  -- Recover H-A-L and L-M-K.
  --------------------------------------------------------------------

  have hHAL :
      Geo.Between H A L :=
    i44_order_HAL
      Geo
      A B E F G H K Q L
      hABE
      hHGF
      hHBK
      hPar
      hAH_GB
      hKQ
      hParBE_KQ
      hHALcol
      hKQL

  have hLMK :
      Geo.Between L M K :=
    i44_order_LMK
      Geo
      A B E F G H K L M
      hHBK
      hHAL
      hFEK
      hPar
      hAH_GB
      hGBM
      hLKMcol

  --------------------------------------------------------------------
  -- Diagonal parallelograms.
  --------------------------------------------------------------------

  have hHABG :
      IsParallelogram Geo H A B G :=
    i44_first_diagonal_parallelogram
      Geo
      A B E F G H
      hABE
      hHGF
      hPar
      hAH_GB

  have hBMKE :
      IsParallelogram Geo B M K E :=
    i44_second_diagonal_parallelogram
      Geo
      B E F G K Q L M
      hFEK
      hLMK
      hPar
      hKQ
      hParBE_KQ
      hGBM
      hKQM

  --------------------------------------------------------------------
  -- This is the extra fact discarded by i44_positioned_content:
  --
  --     G-B-M.
  --------------------------------------------------------------------

  have hGBMorder :
      Geo.Between G B M :=
    i44_order_GBM
      Geo
      B E F G H K M
      hHGF
      hHBK
      hPar
      hBMKE
      hGBM

  --------------------------------------------------------------------
  -- Large parallelogram.
  --------------------------------------------------------------------

  have hBig :
      IsParallelogram Geo H L K F :=
    i44_big_parallelogram
      Geo
      A B E F G H K Q L M
      hABE
      hHGF
      hFEK
      hHAL
      hLMK
      hPar
      hAH_GB
      hParBE_KQ
      hKQL

  --------------------------------------------------------------------
  -- Target ABML.
  --------------------------------------------------------------------

  have hABML :
      IsParallelogram Geo A B M L :=
    i44_target_parallelogram
      Geo
      A B E G H K L M
      hABE
      hHAL
      hLMK
      hAH_GB
      hGBM
      hBMKE

  --------------------------------------------------------------------
  -- I.43 content bridge.
  --------------------------------------------------------------------

  have hContent :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B M L)
        (hilbertParallelogramTerm Geo B E F G) :=
    i44_i43_content_bridge
      Geo
      A B E F G H K L M
      hBig
      hHBK
      hHAL
      hHGF
      hLMK
      hFEK
      hHABG
      hBMKE
      hABML

  exact
    ⟨M, L,
      hABML,
      hGBMorder,
      hContent⟩

theorem i45_adjacent_triangle_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (S T U V P Q R : Geo.Point)
    (hLeft : IsParallelogram Geo S T U V)
    (hPQR : Not (Collinear Geo P Q R)) :
    ∃ M L : Geo.Point,
      IsParallelogram Geo T U M L ∧
      Geo.Between V U M ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo P Q R)
        (hilbertParallelogramTerm Geo T U M L) := by

  --------------------------------------------------------------------
  -- Oriented rigid copy of the triangle beyond TU.
  --------------------------------------------------------------------

  rcases
      i45_oriented_triangle_placement
        Geo
        S T U V
        P Q R
        hLeft
        hPQR
    with
    ⟨E, F, G,
      hTUE,
      hUEFG,
      hRayUVG,
      hTriangleUEFG⟩

  --------------------------------------------------------------------
  -- Apply the positioned I.44 construction to the base TU.
  --
  -- It returns TUML and, crucially, G-U-M.
  --------------------------------------------------------------------

  rcases
      i45_positioned_content_ordered
        Geo
        T U E F G
        hTUE
        hUEFG
    with
    ⟨M, L,
      hTUML,
      hGUM,
      hTUML_UEFG⟩

  --------------------------------------------------------------------
  -- G and V lie on the same ray from U.
  -- Since G-U-M, also V-U-M.
  --------------------------------------------------------------------

  have hRayUGV :
      HilbertSameRay Geo U G V :=
    hilbert_sameRay_symm
      Geo U V G hRayUVG

  have hUM :
      U ≠ M :=
    (HilbertOrder.between_incidence
      G U M hGUM).2.1

  have hRayUMM :
      HilbertSameRay Geo U M M :=
    hilbert_sameRay_refl
      Geo U M hUM.symm

  have hVUM :
      Geo.Between V U M :=
    hilbert_between_transport_sameRays
      Geo
      G U M
      V M
      hGUM
      hRayUGV
      hRayUMM

  --------------------------------------------------------------------
  -- Content:
  --
  -- triangle PQR ~= UEFG
  -- TUML ~= UEFG
  --
  -- hence triangle PQR ~= TUML.
  --------------------------------------------------------------------

  have hUEFG_TUML :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo U E F G)
        (hilbertParallelogramTerm Geo T U M L) :=
    equicomplementable_symm
      Geo hTUML_UEFG

  have hTriangleTUML :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo P Q R)
        (hilbertParallelogramTerm Geo T U M L) :=
    equicomplementable_trans
      Geo
      hTriangleUEFG
      hUEFG_TUML

  exact
    ⟨M, L,
      hTUML,
      hVUM,
      hTriangleTUML⟩

/--
Induction step for Euclid I.45.

Starting from a parallelogram `S T U V` whose angle at `T` is
congruent to `X Y Z`, and from a nondegenerate triangle `P Q R`,
construct a larger parallelogram with the same prescribed angle and
with scissors content equal to the old parallelogram plus the triangle.

The construction uses the oriented I.44 placement on side `T U`,
recovers the strict order needed for adjacency, pastes the two
parallelograms, and transports both content and angle to the outer one.
-/
theorem i45_extend_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (S T U V P Q R X Y Z : Geo.Point)
    (hParallelogram : IsParallelogram Geo S T U V)
    (hAngle : Geo.AngleCongruent S T U X Y Z)
    (hPQR : Not (Collinear Geo P Q R)) :
    ∃ T' U' V' : Geo.Point,
      IsParallelogram Geo S T' U' V' ∧
      Geo.AngleCongruent S T' U' X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo S T' U' V')
        (hilbertScissorsTriangle Geo P Q R +
         hilbertParallelogramTerm Geo S T U V) := by

  --------------------------------------------------------------------
  -- Apply the new triangle as an adjacent parallelogram TUML.
  --------------------------------------------------------------------

  rcases
      i45_adjacent_triangle_parallelogram
        Geo
        S T U V
        P Q R
        hParallelogram
        hPQR
    with
    ⟨M, L,
      hTUML,
      hVUM,
      hTriangleTUML⟩

  --------------------------------------------------------------------
  -- The order on the opposite side follows automatically:
  --
  --     S-T-L.
  --------------------------------------------------------------------

  have hSTL :
      Geo.Between S T L :=
    i45_other_side_order
      Geo
      S T U V
      M L
      hParallelogram
      hTUML
      hVUM

  --------------------------------------------------------------------
  -- Paste STUV and TUML to obtain SLMV.
  --------------------------------------------------------------------

  have hOuter :
      IsParallelogram Geo S L M V :=
    i45_paste_parallelograms_geometry
      Geo
      S T U V
      L M
      hParallelogram
      hTUML
      hVUM
      hSTL

  --------------------------------------------------------------------
  -- The prescribed angle is preserved.
  --------------------------------------------------------------------

  have hOuterAngle :
      Geo.AngleCongruent S L M X Y Z :=
    i45_paste_angle
      Geo
      S T U V
      L M
      X Y Z
      hParallelogram
      hTUML
      hVUM
      hSTL
      hAngle

  --------------------------------------------------------------------
  -- Content:
  --
  --     SLMV ~= PQR + STUV.
  --------------------------------------------------------------------

  have hOuterContent :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo S L M V)
        (hilbertScissorsTriangle Geo P Q R +
         hilbertParallelogramTerm Geo S T U V) :=
    i45_paste_equicomplementable
      Geo
      S T U V
      L M
      P Q R
      hParallelogram
      hTUML
      hVUM
      hSTL
      hTriangleTUML

  exact
    ⟨L, M, V,
      hOuter,
      hOuterAngle,
      hOuterContent⟩

/--
Euclid I.45.

To construct, in a given rectilineal angle `XYZ`, a parallelogram
equal to a given rectilineal figure, presented via a triangulation
`L` (a nonempty list of triangles, each nondegenerate).
-/
theorem euclid_proposition_45
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (L : HilbertTriangulatedFigure Geo)
    (hNonempty : L ≠ [])
    (hTriangles :
      ∀ t ∈ L,
        Not (Collinear Geo t.A t.B t.C)) :
    ∃ S T U V : Geo.Point,
      IsParallelogram Geo S T U V ∧
      Geo.AngleCongruent S T U X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (rectilinealTerm Geo L)
        (hilbertParallelogramTerm Geo S T U V) := by

  revert hNonempty hTriangles
  induction L with
  | nil =>
    intro hNonempty _
    exact absurd rfl hNonempty
  | cons hd tl ih =>
    intro _ hTriangles
    rcases hd with ⟨P, Q, R⟩

    have hPQR :
        Not (Collinear Geo P Q R) :=
      hTriangles ⟨P, Q, R⟩ List.mem_cons_self

    have hRect :
        rectilinealTerm Geo (⟨P, Q, R⟩ :: tl) =
          hilbertScissorsTriangle Geo P Q R +
          rectilinealTerm Geo tl :=
      rectilinealTerm_cons Geo ⟨P, Q, R⟩ tl

    rcases tl with _ | ⟨hd2, tl2⟩

    ------------------------------------------------------------------
    -- Base case: a single triangle. Use I.42 directly.
    ------------------------------------------------------------------

    · rcases
          euclid_proposition_42
            Geo P Q R X Y Z hPQR hXYZ
        with
        ⟨E, F, G, hParallelogram, hAngle, hEquicomp⟩

      refine ⟨F, E, R, G, hParallelogram, hAngle, ?_⟩
      rw [hRect, rectilinealTerm_nil]
      simpa using hEquicomp

    ------------------------------------------------------------------
    -- Recursive case: extend the parallelogram for the tail by the
    -- new triangle P Q R.
    ------------------------------------------------------------------

    · have hTlNonempty :
          (hd2 :: tl2 : HilbertTriangulatedFigure Geo) ≠ [] :=
        List.cons_ne_nil hd2 tl2

      have hTlTriangles :
          ∀ t ∈ (hd2 :: tl2 : HilbertTriangulatedFigure Geo),
            Not (Collinear Geo t.A t.B t.C) :=
        fun t ht =>
          hTriangles t (List.mem_cons_of_mem _ ht)

      rcases
          ih hTlNonempty hTlTriangles
        with
        ⟨S, T, U, V, hParallelogram, hAngle, hEquicompTl⟩

      rcases
          i45_extend_parallelogram
            Geo S T U V P Q R X Y Z
            hParallelogram hAngle hPQR
        with
        ⟨T', U', V', hParallelogram2, hAngle2, hEquicompExt⟩

      refine ⟨S, T', U', V', hParallelogram2, hAngle2, ?_⟩

      rw [hRect]

      have hAddLeft :
          HilbertScissorsEquicomplementable Geo
            (hilbertScissorsTriangle Geo P Q R +
             rectilinealTerm Geo (hd2 :: tl2))
            (hilbertScissorsTriangle Geo P Q R +
             hilbertParallelogramTerm Geo S T U V) :=
        equicomplementable_add
          Geo
          (equicomplementable_refl
            Geo
            (hilbertScissorsTriangle Geo P Q R))
          hEquicompTl

      exact
        equicomplementable_trans
          Geo hAddLeft
          (equicomplementable_symm Geo hEquicompExt)

end Geometry

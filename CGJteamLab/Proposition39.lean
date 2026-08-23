import CGJteamLab.Proposition37
import CGJteamLab.HilbertScissorsPositivity

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid I.39 auxiliary point.

Assume A and D are distinct, lie on the same side of the base line BC,
and AD is not parallel to BC. Draw through A the parallel to BC.
It meets the carrier BD at a point E. The point E is distinct from B
and D, lies on the same side of the base as A, and either E = A or AE
itself is a nondegenerate parallel to BC.
-/
theorem proposition39_auxiliary_point
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hBC : B ≠ C)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hSame : HilbertSameSide Geo A D base)
    (hAD : A ≠ D)
    (hNotParallel : ¬ Geo.Parallel A D B C) :
    ∃ E : Geo.Point,
      Collinear Geo B E D ∧
      E ≠ B ∧
      E ≠ D ∧
      ¬ HilbertIncidence.OnLine E base ∧
      HilbertSameSide Geo A E base ∧
      (E = A ∨ Geo.Parallel A E B C) := by

  have hAoff :
      ¬ HilbertIncidence.OnLine A base :=
    hSame.1

  have hDoff :
      ¬ HilbertIncidence.OnLine D base :=
    hSame.2.1

  have hBCA :
      ¬ Collinear Geo B C A :=
    hilbert_not_collinear_of_off_line
      Geo B C A base hBC hBbase hCbase hAoff

  rcases
      hilbert_parallel_through_point_exists
        Geo B C A hBC hBCA
    with
    ⟨Q, hAQ, hBC_AQ⟩

  have hAQ_BC :
      Geo.Parallel A Q B C :=
    ParallelSymmetry
      Geo B C A Q hBC_AQ

  rcases
      HilbertPlaneIncidence.line_through
        A Q hAQ
    with
    ⟨lineAQ, hAaq, hQaq⟩

  have hLinesAQ_base :
      HilbertLinesDisjoint Geo lineAQ base := by
    rintro ⟨P, hPaq, hPbase⟩

    have hPAQ :
        P ∈ Geo.PointLine A Q :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A Q P lineAQ
        hAQ hAaq hQaq).mpr hPaq

    have hPBC :
        P ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C P base
        hBC hBbase hCbase).mpr hPbase

    exact
      Set.disjoint_left.mp
        hAQ_BC.2.2
        hPAQ hPBC

  have hBD : B ≠ D := by
    intro h
    subst D
    exact hDoff hBbase

  rcases
      HilbertPlaneIncidence.line_through
        B D hBD
    with
    ⟨lineBD, hBbd, hDbd⟩

  have hNotDisjoint :
      ¬ HilbertLinesDisjoint Geo lineAQ lineBD := by
    intro hLinesAQ_BD

    have hBoffAQ :
        ¬ HilbertIncidence.OnLine B lineAQ := by
      intro hBaq
      exact hLinesAQ_base ⟨B, hBaq, hBbase⟩

    have hLinesBD_AQ :
        HilbertLinesDisjoint Geo lineBD lineAQ := by
      rintro ⟨P, hPbd, hPaq⟩
      exact hLinesAQ_BD ⟨P, hPaq, hPbd⟩

    have hLinesBase_AQ :
        HilbertLinesDisjoint Geo base lineAQ := by
      rintro ⟨P, hPbase, hPaq⟩
      exact hLinesAQ_base ⟨P, hPaq, hPbase⟩

    have hLineBD_base :
        lineBD = base :=
      HilbertEuclideanPlane.parallel_unique
        (Geo := Geo)
        lineAQ B hBoffAQ
        lineBD base
        hBbd hLinesBD_AQ
        hBbase hLinesBase_AQ

    have hDbase :
        HilbertIncidence.OnLine D base := by
      rw [← hLineBD_base]
      exact hDbd

    exact hDoff hDbase

  have hMeet :
      HilbertLinesMeet Geo lineAQ lineBD := by
    by_contra hNoMeet
    exact hNotDisjoint hNoMeet

  rcases hMeet with
    ⟨E, hEaq, hEbd⟩

  have hEoff :
      ¬ HilbertIncidence.OnLine E base := by
    intro hEbase
    exact hLinesAQ_base ⟨E, hEaq, hEbase⟩

  have hEB : E ≠ B := by
    intro h
    subst E
    exact hEoff hBbase

  have hED : E ≠ D := by
    intro h
    subst E

    have hADQ :
        Collinear Geo A D Q :=
      ⟨lineAQ, hAaq, hEaq, hQaq⟩

    have hAD_BC :
        Geo.Parallel A D B C :=
      collinear_parallel_trans
        Geo A D Q B C hAD hADQ hAQ_BC

    exact hNotParallel hAD_BC

  have hBED :
      Collinear Geo B E D :=
    ⟨lineBD, hBbd, hEbd, hDbd⟩

  have hNoMeetAE :
      ¬ HilbertSegmentMeetsLine Geo A E base := by
    rintro ⟨X, hAXE, hXbase⟩

    have hXaq :
        HilbertIncidence.OnLine X lineAQ :=
      hilbert_between_on_line
        Geo A X E lineAQ
        hAaq hEaq hAXE

    exact hLinesAQ_base ⟨X, hXaq, hXbase⟩

  have hAESame :
      HilbertSameSide Geo A E base :=
    ⟨hAoff, hEoff,
      Relation.ReflTransGen.single
        ⟨hAoff, hEoff, hNoMeetAE⟩⟩

  have hEorParallel :
      E = A ∨ Geo.Parallel A E B C := by
    by_cases hEA : E = A

    · exact Or.inl hEA

    · have hAE : A ≠ E := by
        intro h
        exact hEA h.symm

      have hAEQ :
          Collinear Geo A E Q :=
        ⟨lineAQ, hAaq, hEaq, hQaq⟩

      have hAE_BC :
          Geo.Parallel A E B C :=
        collinear_parallel_trans
          Geo A E Q B C hAE hAEQ hAQ_BC

      exact Or.inr hAE_BC

  exact
    ⟨E,
      hBED,
      hEB,
      hED,
      hEoff,
      hAESame,
      hEorParallel⟩

/--
Order of the auxiliary point in Euclid I.39.

If B, E, D are distinct collinear points and E,D lie on the same
side of the base line through B, then B cannot lie between E and D.
Hence either B-E-D or B-D-E.
-/
theorem proposition39_auxiliary_order
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B D E : Geo.Point)
    (base : Geo.Line)
    (hBbase : HilbertIncidence.OnLine B base)
    (hSameAD : HilbertSameSide Geo A D base)
    (hSameAE : HilbertSameSide Geo A E base)
    (hBEDcol : Collinear Geo B E D)
    (hEB : E ≠ B)
    (hED : E ≠ D) :
    Geo.Between B E D ∨ Geo.Between B D E := by

  have hDoff :
      ¬ HilbertIncidence.OnLine D base :=
    hSameAD.2.1

  have hBD : B ≠ D := by
    intro hBD
    subst D
    exact hDoff hBbase

  have hSameED :
      HilbertSameSide Geo E D base :=
    hilbert_sameSide_trans
      Geo E A D base
      (hilbert_sameSide_symm Geo A E base hSameAE)
      hSameAD

  rcases
      hilbert_between_trichotomy
        Geo B E D
        hEB.symm
        hED
        hBD
        hBEDcol
    with
    hBED | hEBD | hBDE

  · exact Or.inl hBED

  · have hOppED :
        HilbertOppositeSide Geo E D base :=
      ⟨hSameAE.2.1,
         hSameAD.2.1,
         ⟨B, hEBD, hBbase⟩⟩

    exact False.elim
      ((hilbert_oppositeSide_not_sameSide
          Geo E D base hOppED)
        hSameED)

  · exact Or.inr hBDE

/-
Specialized De Zolt principle needed for Euclid I.39.

If X lies strictly between B and A, then triangle XBC is a proper
part of triangle ABC. The whole triangle cannot therefore be
Hilbert-scissors-equicomplementable with that proper subtriangle.

This is the single temporary content assumption of the De Zolt route.
-/
/-
axiom hilbert_scissors_triangle_proper_part
    [HilbertIncidence Geo]
    (A X B C : Geo.Point)
    (hBXA : Geo.Between B X A)
    (hBC : B ≠ C)
    (hNoncol : ¬ Collinear Geo B C A) :
    ¬ HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo X B C)
-/
/--
Convert point-line parallelism AD || BC into the line formulation
used in the statement of I.39, where `base` is the incidence line
through B and C.
-/
theorem proposition39_parallel_points_to_top_line
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A D B C : Geo.Point)
    (base : Geo.Line)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hAD_BC : Geo.Parallel A D B C) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  have hAD : A ≠ D := hAD_BC.1
  have hBC : B ≠ C := hAD_BC.2.1

  rcases
      HilbertPlaneIncidence.line_through
        A D hAD
    with
    ⟨top, hAtop, hDtop⟩

  have hDisjoint :
      HilbertLinesDisjoint Geo top base := by
    rintro ⟨P, hPtop, hPbase⟩

    have hPAD :
        P ∈ Geo.PointLine A D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A D P top
        hAD hAtop hDtop).mpr hPtop

    have hPBC :
        P ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C P base
        hBC hBbase hCbase).mpr hPbase

    exact
      Set.disjoint_left.mp
        hAD_BC.2.2
        hPAD hPBC

  exact ⟨top, hAtop, hDtop, hDisjoint⟩

/--
Euclid I.39 from I.37 plus the specialized De Zolt principle.

Equal (equicomplementable) triangles on the same base and on the
same side lie between the same parallels.
-/
theorem euclid_proposition_39
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (base : Geo.Line)
    (hBC : B ≠ C)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hSame : HilbertSameSide Geo A D base)
    (hEqual :
      HilbertScissorsEquicomplementable
        Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo D B C)) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  --------------------------------------------------------------------
  -- Coincident top vertices: draw the unique parallel through A.
  --------------------------------------------------------------------

  by_cases hAD : A = D

  · subst D

    have hAoff :
        ¬ HilbertIncidence.OnLine A base :=
      hSame.1

    have hBCA :
        ¬ Collinear Geo B C A :=
      hilbert_not_collinear_of_off_line
        Geo B C A base hBC hBbase hCbase hAoff

    rcases
        hilbert_parallel_through_point_exists
          Geo B C A hBC hBCA
      with
      ⟨Q, hAQ, hBC_AQ⟩

    have hAQ_BC :
        Geo.Parallel A Q B C :=
      ParallelSymmetry
        Geo B C A Q hBC_AQ

    rcases
        proposition39_parallel_points_to_top_line
          Geo A Q B C base
          hBbase hCbase hAQ_BC
      with
      ⟨top, hAtop, hQtop, hDisjoint⟩

    exact ⟨top, hAtop, hAtop, hDisjoint⟩

  --------------------------------------------------------------------
  -- Distinct top vertices. If AD is already parallel to BC, finish.
  --------------------------------------------------------------------

  · by_cases hParallel : Geo.Parallel A D B C

    · exact
        proposition39_parallel_points_to_top_line
          Geo A D B C base
          hBbase hCbase hParallel

    ------------------------------------------------------------------
    -- Otherwise construct E on BD on the parallel through A.
    ------------------------------------------------------------------

    · rcases
          proposition39_auxiliary_point
            Geo A B C D base
            hBC hBbase hCbase
            hSame hAD hParallel
        with
        ⟨E,
          hBEDcol,
          hEB,
          hED,
          hEoff,
          hSameAE,
          hEorParallel⟩

      ----------------------------------------------------------------
      -- I.37: ABC and EBC have equal content.
      ----------------------------------------------------------------

      have hABC_EBC :
          HilbertScissorsEquicomplementable Geo
            (hilbertScissorsTriangle Geo A B C)
            (hilbertScissorsTriangle Geo E B C) := by

        rcases hEorParallel with hEA | hAE_BC

        · subst E
          exact
            equicomplementable_refl
              Geo
              (hilbertScissorsTriangle Geo A B C)

        · exact
            euclid_proposition_37
              Geo A B C E hAE_BC

      ----------------------------------------------------------------
      -- Hence DBC and EBC have equal content.
      ----------------------------------------------------------------

      have hDBC_EBC :
          HilbertScissorsEquicomplementable Geo
            (hilbertScissorsTriangle Geo D B C)
            (hilbertScissorsTriangle Geo E B C) :=
        equicomplementable_trans
          Geo
          (equicomplementable_symm Geo hEqual)
          hABC_EBC

      ----------------------------------------------------------------
      -- On the ray from B, either E lies inside BD or D lies inside BE.
      ----------------------------------------------------------------

      rcases
          proposition39_auxiliary_order
            Geo A B D E base
            hBbase hSame hSameAE
            hBEDcol hEB hED
        with
        hBED | hBDE

      ----------------------------------------------------------------
      -- B-E-D: EBC is a proper part of DBC.
      ----------------------------------------------------------------

      · have hDoff :
            ¬ HilbertIncidence.OnLine D base :=
          hSame.2.1

        have hBCD :
            ¬ Collinear Geo B C D :=
          hilbert_not_collinear_of_off_line
            Geo B C D base hBC hBbase hCbase hDoff

        have hNo :
            ¬ HilbertScissorsEquicomplementable Geo
                (hilbertScissorsTriangle Geo D B C)
                (hilbertScissorsTriangle Geo E B C) :=
          hilbert_scissors_triangle_proper_part
            Geo D E B C hBED hBC hBCD

        exact False.elim (hNo hDBC_EBC)

      ----------------------------------------------------------------
      -- B-D-E: DBC is a proper part of EBC.
      ----------------------------------------------------------------

      · have hBCE :
            ¬ Collinear Geo B C E :=
          hilbert_not_collinear_of_off_line
            Geo B C E base hBC hBbase hCbase hEoff

        have hEBC_DBC :
            HilbertScissorsEquicomplementable Geo
              (hilbertScissorsTriangle Geo E B C)
              (hilbertScissorsTriangle Geo D B C) :=
          equicomplementable_symm Geo hDBC_EBC

        have hNo :
            ¬ HilbertScissorsEquicomplementable Geo
                (hilbertScissorsTriangle Geo E B C)
                (hilbertScissorsTriangle Geo D B C) :=
          hilbert_scissors_triangle_proper_part
            Geo E D B C hBDE hBC hBCE

        exact False.elim (hNo hEBC_DBC)

end Geometry

import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Intersection of two constructed lines
--
-- Target: eliminate `i46_complete_parallelogram` (and, with it, the
-- corresponding half of `i42_construct_parallelogram` and the Pasch
-- point `N` inside `i47_diagram`) by proving outright that the
-- parallelogram on a given base and a given third vertex can be
-- completed.
--
-- The observation that makes this cheap is that in this library
-- `Geo.Parallel` is *defined* as disjointness of the two extensional
-- point-line carriers.  So "two non-parallel lines meet" is not a new
-- axiom at all; it is the definition read backwards.  All the real
-- content sits in one step:
--
--   the line through `B` parallel to `AD` and the line through `D`
--   parallel to `AB` are not parallel to each other.
--
-- For if they were, `hilbert_parallel_transitive_distinct` (which is
-- where Hilbert's axiom IV is actually used) would force the line `AD`
-- either to be parallel to the line `DR` -- impossible, they share `D`
-- -- or to coincide with it, in which case `AB` would be parallel to a
-- line through `A`, again impossible.
--
-- Naming convention: auxiliary results carry the `intersection_test_`
-- prefix; the target theorem already carries the name it should have
-- once it is moved into `HilbertInterface.lean`, so that promotion is
-- a copy rather than a rename.
------------------------------------------------------------------------

/--
The first determining point of a point-line lies on it.
-/
theorem intersection_test_left_mem
    (A B : Geo.Point) :
    A ∈ Geo.PointLine A B := by
  change Geometry.Geo.LineCollinear Geo A B A
  exact Or.inr (Or.inl rfl)

/--
The second determining point of a point-line lies on it.
-/
theorem intersection_test_right_mem
    (A B : Geo.Point) :
    B ∈ Geo.PointLine A B := by
  change Geometry.Geo.LineCollinear Geo A B B
  exact Or.inr (Or.inr (Or.inl rfl))

/--
Two lines with a common point are not parallel.

Immediate from the definition of `Geo.Parallel` as disjointness of the
two carriers; stated separately because it is used three times below
and reads better than an inlined `Set.disjoint_left`.
-/
theorem intersection_test_not_parallel_of_common_point
    (A B C D P : Geo.Point)
    (hP₁ : P ∈ Geo.PointLine A B)
    (hP₂ : P ∈ Geo.PointLine C D) :
    ¬ Geo.Parallel A B C D := by
  intro hParallel
  exact
    Set.disjoint_left.mp hParallel.2.2
      hP₁ hP₂

/--
Disjoint incidence lines carry parallel point-lines.

This is the bridge between the incidence-level notion
`HilbertLinesDisjoint` and the extensional notion `Geo.Parallel`.
-/
theorem intersection_test_parallel_of_lines_disjoint
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (B Q D R : Geo.Point)
    (l m : Geo.Line)
    (hBQ : B ≠ Q)
    (hDR : D ≠ R)
    (hBl : HilbertIncidence.OnLine B l)
    (hQl : HilbertIncidence.OnLine Q l)
    (hDm : HilbertIncidence.OnLine D m)
    (hRm : HilbertIncidence.OnLine R m)
    (hDisjoint : HilbertLinesDisjoint Geo l m) :
    Geo.Parallel B Q D R := by

  refine ⟨hBQ, hDR, Set.disjoint_left.mpr ?_⟩

  intro X hXBQ hXDR

  have hXl :
      HilbertIncidence.OnLine X l :=
    (hilbert_mem_pointLine_iff_onLine
      Geo B Q X l hBQ hBl hQl).mp hXBQ

  have hXm :
      HilbertIncidence.OnLine X m :=
    (hilbert_mem_pointLine_iff_onLine
      Geo D R X m hDR hDm hRm).mp hXDR

  exact hDisjoint ⟨X, hXl, hXm⟩

------------------------------------------------------------------------
-- Target theorem
------------------------------------------------------------------------

/--
A parallelogram can be completed from three of its vertices.

Given a base `AB` and a point `D` off the line `AB`, there is a fourth
vertex `C` making `A B C D` a parallelogram.

`C` is the intersection of the line through `B` parallel to `AD` with
the line through `D` parallel to `AB`; both lines exist by I.31
(`hilbert_parallel_through_point_exists`), and the argument that they
are not parallel to each other is where Hilbert's axiom IV enters, via
`hilbert_parallel_transitive_distinct`.

This is the statement currently assumed as `i46_complete_parallelogram`
in `Proposition46.lean`.
-/
theorem hilbert_parallelogram_fourth_vertex_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B D : Geo.Point)
    (hABD : Not (Collinear Geo A B D)) :
    ∃ C : Geo.Point,
      IsParallelogram Geo A B C D := by

  --------------------------------------------------------------------
  -- Nondegeneracy.
  --------------------------------------------------------------------

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B D hABD

  have hADB :
      Not (Collinear Geo A D B) := by
    intro hCol
    exact
      hABD
        (PrimCollinearRotate Geo A D B hCol)

  have hAD : A ≠ D :=
    hilbert_noncollinear_ne_first
      Geo A D B hADB

  --------------------------------------------------------------------
  -- Step 1 [I.31]: the two constructed parallels.
  --------------------------------------------------------------------

  rcases
      hilbert_parallel_through_point_exists
        Geo A D B hAD hADB with
    ⟨Q, hBQ, hParAD_BQ⟩

  rcases
      hilbert_parallel_through_point_exists
        Geo A B D hAB hABD with
    ⟨R, hDR, hParAB_DR⟩

  rcases
      HilbertPlaneIncidence.line_through
        B Q hBQ with
    ⟨l, hBl, hQl⟩

  rcases
      HilbertPlaneIncidence.line_through
        D R hDR with
    ⟨m, hDm, hRm⟩

  --------------------------------------------------------------------
  -- Step 2: the two lines are not parallel, hence they meet.
  --------------------------------------------------------------------

  have hMeet :
      HilbertLinesMeet Geo l m := by

    by_contra hDisjoint

    have hParBQ_DR :
        Geo.Parallel B Q D R :=
      intersection_test_parallel_of_lines_disjoint
        Geo B Q D R l m
        hBQ hDR hBl hQl hDm hRm
        hDisjoint

    by_cases hSameCarrier :
        Geo.PointLine A D = Geo.PointLine D R

    ----------------------------------------------------------------
    -- If `AD` and `DR` are the same line, then `AB` is parallel to a
    -- line through `A`.
    ----------------------------------------------------------------

    · have hA_DR :
          A ∈ Geo.PointLine D R := by
        rw [← hSameCarrier]
        exact intersection_test_left_mem Geo A D

      exact
        intersection_test_not_parallel_of_common_point
          Geo A B D R A
          (intersection_test_left_mem Geo A B)
          hA_DR
          hParAB_DR

    ----------------------------------------------------------------
    -- Otherwise transitivity of parallelism makes `AD` parallel to
    -- `DR`, though they share `D`.
    ----------------------------------------------------------------

    · have hParDR_BQ :
          Geo.Parallel D R B Q :=
        ParallelSymmetry
          Geo B Q D R hParBQ_DR

      have hParAD_DR :
          Geo.Parallel A D D R :=
        hilbert_parallel_transitive_distinct
          Geo A D D R B Q
          hParAD_BQ
          hParDR_BQ
          hSameCarrier

      exact
        intersection_test_not_parallel_of_common_point
          Geo A D D R D
          (intersection_test_right_mem Geo A D)
          (intersection_test_left_mem Geo D R)
          hParAD_DR

  rcases hMeet with ⟨C, hCl, hCm⟩

  --------------------------------------------------------------------
  -- Step 3: the intersection point is distinct from `B` and from `D`.
  --------------------------------------------------------------------

  have hCB : C ≠ B := by
    intro hEq

    have hBm :
        HilbertIncidence.OnLine B m := by
      rw [← hEq]
      exact hCm

    have hB_DR :
        B ∈ Geo.PointLine D R :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D R B m hDR hDm hRm).mpr hBm

    exact
      intersection_test_not_parallel_of_common_point
        Geo A B D R B
        (intersection_test_right_mem Geo A B)
        hB_DR
        hParAB_DR

  have hCD : C ≠ D := by
    intro hEq

    have hDl :
        HilbertIncidence.OnLine D l := by
      rw [← hEq]
      exact hCl

    have hD_BQ :
        D ∈ Geo.PointLine B Q :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B Q D l hBQ hBl hQl).mpr hDl

    exact
      intersection_test_not_parallel_of_common_point
        Geo A D B Q D
        (intersection_test_right_mem Geo A D)
        hD_BQ
        hParAD_BQ

  --------------------------------------------------------------------
  -- Step 4: transport both parallels onto the sides `BC` and `DC`.
  --------------------------------------------------------------------

  have hColBCQ :
      Collinear Geo B C Q :=
    ⟨l, hBl, hCl, hQl⟩

  have hColDCR :
      Collinear Geo D C R :=
    ⟨m, hDm, hCm, hRm⟩

  have hParBC_DA :
      Geo.Parallel B C D A := by
    have hParBQ_AD :
        Geo.Parallel B Q A D :=
      ParallelSymmetry
        Geo A D B Q hParAD_BQ

    have hParBC_AD :
        Geo.Parallel B C A D :=
      collinear_parallel_trans
        Geo B C Q A D
        (Ne.symm hCB)
        hColBCQ
        hParBQ_AD

    exact
      ParallelSwapSecondLine
        Geo B C A D hParBC_AD

  have hParAB_CD :
      Geo.Parallel A B C D := by
    have hParDR_AB :
        Geo.Parallel D R A B :=
      ParallelSymmetry
        Geo A B D R hParAB_DR

    have hParDC_AB :
        Geo.Parallel D C A B :=
      collinear_parallel_trans
        Geo D C R A B
        (Ne.symm hCD)
        hColDCR
        hParDR_AB

    have hParAB_DC :
        Geo.Parallel A B D C :=
      ParallelSymmetry
        Geo D C A B hParDC_AB

    exact
      ParallelSwapSecondLine
        Geo A B D C hParAB_DC

  exact ⟨C, hParAB_CD, hParBC_DA⟩

------------------------------------------------------------------------
-- Follow-up targets for this file
--
-- 1. `i42_construct_parallelogram` (Proposition42.lean) asks for a
--    parallelogram on a given base with a prescribed angle at one
--    vertex.  With the theorem above, what remains of that axiom is
--    only the angle-construction part (III,4), not the intersection.
--
-- 2. The Pasch point `N` of `i47_diagram` -- the meeting of the
--    diagonal `DC` of the square with the cut `ML` -- should follow
--    from `HilbertOrder.pasch` applied to the triangle cut by the line
--    `ML`, not from the diagram axiom.
------------------------------------------------------------------------

end Geometry

import CGJteamLab.HilbertScissors

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
Euclid I.35.

This file contains the proposition-specific geometry and scissors argument.
The generic formal scissors calculus remains in `HilbertScissors.lean`.
-/


/- --------------------------------------------------------------------
  Formal decompositions for the disjoint configuration
---------------------------------------------------------------------/

theorem i35_left_augmented_decomposition
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E G : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hADE : Geo.Between A D E)
    (hEGB : Geo.Between E G B)
    (hDGC : Geo.Between D G C) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A B C D +
       hilbertScissorsTriangle Geo D G E)
      (hilbertScissorsTriangle Geo E A B +
       hilbertScissorsTriangle Geo G B C) := by

  --------------------------------------------------------------------
  -- First change the parallelogram triangulation from AC to BD.
  --------------------------------------------------------------------

  have hDiag :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B C D) := by
    simpa [hilbertParallelogramTerm] using
      parallelogram_two_triangulations
        Geo A B C D hABCD

  have hDiagPlus :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D +
         hilbertScissorsTriangle Geo D G E)
        ((hilbertScissorsTriangle Geo A B D +
          hilbertScissorsTriangle Geo B C D) +
         hilbertScissorsTriangle Geo D G E) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hDiag
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo D G E))

  --------------------------------------------------------------------
  -- Split BCD at G, since D-G-C.
  --
  --   BCD ~ BDG + BGC
  --------------------------------------------------------------------

  have hBCD0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      B D C G hDGC

  have hBCD :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B C D)
        (hilbertScissorsTriangle Geo B D G +
         hilbertScissorsTriangle Geo B G C) := by
    rw [scissors_triangle_swap23 Geo B D C] at hBCD0
    exact hBCD0

  have hRefinePar :
      HilbertScissorsEq Geo
        ((hilbertScissorsTriangle Geo A B D +
          hilbertScissorsTriangle Geo B C D) +
         hilbertScissorsTriangle Geo D G E)
        ((hilbertScissorsTriangle Geo A B D +
          (hilbertScissorsTriangle Geo B D G +
           hilbertScissorsTriangle Geo B G C)) +
         hilbertScissorsTriangle Geo D G E) := by

    have hABCDref :
        HilbertScissorsEq Geo
          (hilbertScissorsTriangle Geo A B D +
           hilbertScissorsTriangle Geo B C D)
          (hilbertScissorsTriangle Geo A B D +
           (hilbertScissorsTriangle Geo B D G +
            hilbertScissorsTriangle Geo B G C)) :=
      HilbertScissorsEq.add
        (Geo := Geo)
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertScissorsTriangle Geo A B D))
        hBCD

    exact
      HilbertScissorsEq.add
        (Geo := Geo)
        hABCDref
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertScissorsTriangle Geo D G E))

  --------------------------------------------------------------------
  -- Now decompose the large triangle EAB.
  --
  -- First A-D-E:
  --
  --   EAB ~ ABD + BDE
  --------------------------------------------------------------------

  have hEAB0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      B A E D hADE

  have hEAB1 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E A B)
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B D E) := by

    rw [scissors_triangle_cycle Geo B A E] at hEAB0
    rw [scissors_triangle_cycle Geo A E B] at hEAB0
    rw [scissors_triangle_swap23 Geo E B A] at hEAB0

    rw [scissors_triangle_swap12 Geo B A D] at hEAB0

    exact hEAB0

  --------------------------------------------------------------------
  -- Then E-G-B:
  --
  --   BDE ~ BDG + DGE
  --------------------------------------------------------------------

  have hBDE0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      D E B G hEGB

  have hBDE :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B D E)
        (hilbertScissorsTriangle Geo B D G +
         hilbertScissorsTriangle Geo D G E) := by

    have h := hBDE0

    -- D E B -> B D E
    rw [scissors_triangle_cycle Geo D E B] at h
    rw [scissors_triangle_cycle Geo E B D] at h

    -- D E G -> D G E
    rw [scissors_triangle_swap23 Geo D E G] at h

    -- D G B -> B D G
    rw [scissors_triangle_cycle Geo D G B] at h
    rw [scissors_triangle_cycle Geo G B D] at h

    -- The two pieces occur in the opposite formal order.
    rw [Multiset.add_comm
      (hilbertScissorsTriangle Geo D G E)
      (hilbertScissorsTriangle Geo B D G)] at h

    exact h

  have hEAB :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E A B)
        (hilbertScissorsTriangle Geo A B D +
         (hilbertScissorsTriangle Geo B D G +
          hilbertScissorsTriangle Geo D G E)) := by

    have hRest :
        HilbertScissorsEq Geo
          (hilbertScissorsTriangle Geo A B D +
           hilbertScissorsTriangle Geo B D E)
          (hilbertScissorsTriangle Geo A B D +
           (hilbertScissorsTriangle Geo B D G +
            hilbertScissorsTriangle Geo D G E)) :=
      HilbertScissorsEq.add
        (Geo := Geo)
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertScissorsTriangle Geo A B D))
        hBDE

    exact
      HilbertScissorsEq.trans
        (Geo := Geo)
        hEAB1 hRest

  --------------------------------------------------------------------
  -- Add the common triangle GBC to the EAB decomposition.
  --------------------------------------------------------------------

  have hTarget :
      HilbertScissorsEq Geo
        ((hilbertScissorsTriangle Geo A B D +
          (hilbertScissorsTriangle Geo B D G +
           hilbertScissorsTriangle Geo D G E)) +
         hilbertScissorsTriangle Geo G B C)
        (hilbertScissorsTriangle Geo E A B +
         hilbertScissorsTriangle Geo G B C) := by

    exact
      HilbertScissorsEq.add
        (Geo := Geo)
        (HilbertScissorsEq.symm
          (Geo := Geo) hEAB)
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertScissorsTriangle Geo G B C))

  --------------------------------------------------------------------
  -- The two refined terms contain exactly the same four triangles.
  --------------------------------------------------------------------

  have hArrange :
      ((hilbertScissorsTriangle Geo A B D +
        (hilbertScissorsTriangle Geo B D G +
         hilbertScissorsTriangle Geo B G C)) +
       hilbertScissorsTriangle Geo D G E)
        =
      ((hilbertScissorsTriangle Geo A B D +
        (hilbertScissorsTriangle Geo B D G +
         hilbertScissorsTriangle Geo D G E)) +
       hilbertScissorsTriangle Geo G B C) := by

    rw [scissors_triangle_swap12 Geo B G C]

    calc
      ((hilbertScissorsTriangle Geo A B D +
        (hilbertScissorsTriangle Geo B D G +
         hilbertScissorsTriangle Geo G B C)) +
       hilbertScissorsTriangle Geo D G E)
          =
        hilbertScissorsTriangle Geo A B D +
          ((hilbertScissorsTriangle Geo B D G +
            hilbertScissorsTriangle Geo G B C) +
           hilbertScissorsTriangle Geo D G E) :=
        Multiset.add_assoc _ _ _

      _ =
        hilbertScissorsTriangle Geo A B D +
          (hilbertScissorsTriangle Geo B D G +
           (hilbertScissorsTriangle Geo G B C +
            hilbertScissorsTriangle Geo D G E)) := by
        rw [Multiset.add_assoc]

      _ =
        hilbertScissorsTriangle Geo A B D +
          (hilbertScissorsTriangle Geo B D G +
           (hilbertScissorsTriangle Geo D G E +
            hilbertScissorsTriangle Geo G B C)) := by
        rw [Multiset.add_comm
          (hilbertScissorsTriangle Geo G B C)
          (hilbertScissorsTriangle Geo D G E)]

      _ =
        hilbertScissorsTriangle Geo A B D +
          ((hilbertScissorsTriangle Geo B D G +
            hilbertScissorsTriangle Geo D G E) +
           hilbertScissorsTriangle Geo G B C) := by
        apply congrArg
          (fun T =>
            hilbertScissorsTriangle Geo A B D + T)
        exact
          (Multiset.add_assoc
            (hilbertScissorsTriangle Geo B D G)
            (hilbertScissorsTriangle Geo D G E)
            (hilbertScissorsTriangle Geo G B C)).symm

      _ =
        ((hilbertScissorsTriangle Geo A B D +
          (hilbertScissorsTriangle Geo B D G +
           hilbertScissorsTriangle Geo D G E)) +
         hilbertScissorsTriangle Geo G B C) := by
        exact
          (Multiset.add_assoc
            (hilbertScissorsTriangle Geo A B D)
            (hilbertScissorsTriangle Geo B D G +
             hilbertScissorsTriangle Geo D G E)
            (hilbertScissorsTriangle Geo G B C)).symm


  rw [hArrange] at hRefinePar

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hDiagPlus
      (HilbertScissorsEq.trans
        (Geo := Geo)
        hRefinePar
        hTarget)

theorem i35_right_augmented_decomposition
    (D E F B C G : Geo.Point)
    (hDEF : Geo.Between D E F)
    (hEGB : Geo.Between E G B)
    (hDGC : Geo.Between D G C) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo E B C F +
       hilbertScissorsTriangle Geo D G E)
      (hilbertScissorsTriangle Geo D C F +
       hilbertScissorsTriangle Geo G B C) := by

  --------------------------------------------------------------------
  -- Split EBC at G, since E-G-B:
  --
  --   EBC ~ CEG + GBC
  --------------------------------------------------------------------

  have hEBC0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      C E B G hEGB

  have hEBC :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E B C)
        (hilbertScissorsTriangle Geo C E G +
         hilbertScissorsTriangle Geo G B C) := by

    rw [scissors_triangle_cycle Geo C E B] at hEBC0
    rw [scissors_triangle_cycle Geo C G B] at hEBC0

    exact hEBC0

  --------------------------------------------------------------------
  -- Refine EBCF.
  --------------------------------------------------------------------

  have hLeftBase :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E B C F)
        ((hilbertScissorsTriangle Geo C E G +
          hilbertScissorsTriangle Geo G B C) +
         hilbertScissorsTriangle Geo E C F) := by

    unfold hilbertParallelogramTerm

    exact
      HilbertScissorsEq.add
        (Geo := Geo)
        hEBC
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertScissorsTriangle Geo E C F))

  have hLeft :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E B C F +
         hilbertScissorsTriangle Geo D G E)
        (((hilbertScissorsTriangle Geo C E G +
           hilbertScissorsTriangle Geo G B C) +
          hilbertScissorsTriangle Geo E C F) +
         hilbertScissorsTriangle Geo D G E) :=

    HilbertScissorsEq.add
      (Geo := Geo)
      hLeftBase
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo D G E))

  --------------------------------------------------------------------
  -- Decompose DCF first at E, since D-E-F:
  --
  --   DCF ~ CDE + ECF
  --------------------------------------------------------------------

  have hDCF0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      C D F E hDEF

  have hDCF :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D C F)
        (hilbertScissorsTriangle Geo C D E +
         hilbertScissorsTriangle Geo E C F) := by

    rw [scissors_triangle_swap12 Geo C D F] at hDCF0
    rw [scissors_triangle_swap12 Geo C E F] at hDCF0

    exact hDCF0

  --------------------------------------------------------------------
  -- Split CDE at G, since D-G-C:
  --
  --   CDE ~ DGE + CEG
  --------------------------------------------------------------------

  have hCDE0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      E D C G hDGC

  have hCDE :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo C D E)
        (hilbertScissorsTriangle Geo D G E +
         hilbertScissorsTriangle Geo C E G) := by

    -- EDC -> CDE
    rw [scissors_triangle_swap23 Geo E D C] at hCDE0
    rw [scissors_triangle_cycle Geo E C D] at hCDE0

    -- EDG -> DGE
    rw [scissors_triangle_cycle Geo E D G] at hCDE0

    -- EGC -> CEG
    rw [scissors_triangle_cycle Geo E G C] at hCDE0
    rw [scissors_triangle_cycle Geo G C E] at hCDE0

    exact hCDE0

  have hDCFref :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D C F)
        ((hilbertScissorsTriangle Geo D G E +
          hilbertScissorsTriangle Geo C E G) +
         hilbertScissorsTriangle Geo E C F) := by

    have hRest :
        HilbertScissorsEq Geo
          (hilbertScissorsTriangle Geo C D E +
           hilbertScissorsTriangle Geo E C F)
          ((hilbertScissorsTriangle Geo D G E +
            hilbertScissorsTriangle Geo C E G) +
           hilbertScissorsTriangle Geo E C F) :=

      HilbertScissorsEq.add
        (Geo := Geo)
        hCDE
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertScissorsTriangle Geo E C F))

    exact
      HilbertScissorsEq.trans
        (Geo := Geo)
        hDCF hRest

  --------------------------------------------------------------------
  -- Add GBC.
  --------------------------------------------------------------------

  have hRight :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D C F +
         hilbertScissorsTriangle Geo G B C)
        (((hilbertScissorsTriangle Geo D G E +
           hilbertScissorsTriangle Geo C E G) +
          hilbertScissorsTriangle Geo E C F) +
         hilbertScissorsTriangle Geo G B C) :=

    HilbertScissorsEq.add
      (Geo := Geo)
      hDCFref
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo G B C))

  --------------------------------------------------------------------
  -- The two refinements contain the same four triangles.
  --------------------------------------------------------------------

  have hArrange :
      (((hilbertScissorsTriangle Geo C E G +
         hilbertScissorsTriangle Geo G B C) +
        hilbertScissorsTriangle Geo E C F) +
       hilbertScissorsTriangle Geo D G E)
        =
      (((hilbertScissorsTriangle Geo D G E +
         hilbertScissorsTriangle Geo C E G) +
        hilbertScissorsTriangle Geo E C F) +
       hilbertScissorsTriangle Geo G B C) := by

    calc
      (((hilbertScissorsTriangle Geo C E G +
         hilbertScissorsTriangle Geo G B C) +
        hilbertScissorsTriangle Geo E C F) +
       hilbertScissorsTriangle Geo D G E)
          =
        hilbertScissorsTriangle Geo D G E +
          ((hilbertScissorsTriangle Geo C E G +
            hilbertScissorsTriangle Geo G B C) +
           hilbertScissorsTriangle Geo E C F) :=
        Multiset.add_comm _ _

      _ =
        hilbertScissorsTriangle Geo D G E +
          (hilbertScissorsTriangle Geo C E G +
           (hilbertScissorsTriangle Geo G B C +
            hilbertScissorsTriangle Geo E C F)) := by
        apply congrArg
          (fun T =>
            hilbertScissorsTriangle Geo D G E + T)
        exact
          Multiset.add_assoc
            (hilbertScissorsTriangle Geo C E G)
            (hilbertScissorsTriangle Geo G B C)
            (hilbertScissorsTriangle Geo E C F)

      _ =
        hilbertScissorsTriangle Geo D G E +
          (hilbertScissorsTriangle Geo C E G +
           (hilbertScissorsTriangle Geo E C F +
            hilbertScissorsTriangle Geo G B C)) := by
        apply congrArg
          (fun T =>
            hilbertScissorsTriangle Geo D G E + T)
        apply congrArg
          (fun T =>
            hilbertScissorsTriangle Geo C E G + T)
        exact
          Multiset.add_comm
            (hilbertScissorsTriangle Geo G B C)
            (hilbertScissorsTriangle Geo E C F)

      _ =
        hilbertScissorsTriangle Geo D G E +
          ((hilbertScissorsTriangle Geo C E G +
            hilbertScissorsTriangle Geo E C F) +
           hilbertScissorsTriangle Geo G B C) := by
        apply congrArg
          (fun T =>
            hilbertScissorsTriangle Geo D G E + T)
        exact
          (Multiset.add_assoc
            (hilbertScissorsTriangle Geo C E G)
            (hilbertScissorsTriangle Geo E C F)
            (hilbertScissorsTriangle Geo G B C)).symm

      _ =
        (hilbertScissorsTriangle Geo D G E +
         (hilbertScissorsTriangle Geo C E G +
          hilbertScissorsTriangle Geo E C F)) +
        hilbertScissorsTriangle Geo G B C := by
        exact
          (Multiset.add_assoc
            (hilbertScissorsTriangle Geo D G E)
            (hilbertScissorsTriangle Geo C E G +
             hilbertScissorsTriangle Geo E C F)
            (hilbertScissorsTriangle Geo G B C)).symm

      _ =
        ((hilbertScissorsTriangle Geo D G E +
          hilbertScissorsTriangle Geo C E G) +
         hilbertScissorsTriangle Geo E C F) +
        hilbertScissorsTriangle Geo G B C := by
        rw [Multiset.add_assoc
          (hilbertScissorsTriangle Geo D G E)
          (hilbertScissorsTriangle Geo C E G)
          (hilbertScissorsTriangle Geo E C F)]

  rw [hArrange] at hLeft

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hLeft
      (HilbertScissorsEq.symm
        (Geo := Geo) hRight)

theorem i35_outer_triangles_congruent
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADE : Geo.Between A D E)
    (hDEF : Geo.Between D E F) :
    TriangleCongruenceResult Geo E A B F D C := by

  --------------------------------------------------------------------
  -- Opposite sides of the two parallelograms.
  --------------------------------------------------------------------

  have hSides1 :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hABCD

  have hSides2 :
      OppositeSidesCongruent Geo E B C F :=
    ParallelogramOppositeSidesCongruent
      Geo E B C F hEBCF

  --------------------------------------------------------------------
  -- AD congruent FE.
  --
  -- Both are congruent to the common base BC.
  --------------------------------------------------------------------

  have hDA_FE :
      Geo.Congruent D A F E :=
    HilbertCongruence.segment_congruence_common
      (Geo := Geo)
      B C D A F E
      hSides1.2
      hSides2.2

  have hAD_FE :
      Geo.Congruent A D F E :=
    CongruentReverseFirst
      Geo D A F E hDA_FE

  --------------------------------------------------------------------
  -- DE congruent ED.
  --------------------------------------------------------------------

  have hDE_ED :
      Geo.Congruent D E E D := by
    exact
      CongruentSwapSecond
        Geo D E D E
        (hilbert_congruent_reflexive Geo D E)

  --------------------------------------------------------------------
  -- From
  --
  --   A-D-E
  --   F-E-D
  --   AD congruent FE
  --   DE congruent ED
  --
  -- obtain AE congruent FD by Hilbert III.3.
  --------------------------------------------------------------------

  have hFED :
      Geo.Between F E D :=
    (HilbertOrder.between_incidence
      D E F hDEF).2.2.2.2

  have hAE_FD :
      Geo.Congruent A E F D :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A D E
      F E D
      hADE
      hFED
      hAD_FE
      hDE_ED

  have hEA_FD :
      Geo.Congruent E A F D :=
    CongruentReverseFirst
      Geo A E F D hAE_FD

  --------------------------------------------------------------------
  -- The other two pairs of sides.
  --------------------------------------------------------------------

  have hAB_DC :
      Geo.Congruent A B D C :=
    CongruentSwapSecond
      Geo A B C D hSides1.1

  have hEB_FC :
      Geo.Congruent E B F C :=
    CongruentSwapSecond
      Geo E B C F hSides2.1

  --------------------------------------------------------------------
  -- EAB is noncollinear.
  --
  -- If E,A,B were collinear, then A-D-E would force D,A,B
  -- collinear. Hence B would lie simultaneously on BC and DA,
  -- contradicting BC parallel DA.
  --------------------------------------------------------------------

  have hEAB :
      ¬ Collinear Geo E A B := by
    intro hCol

    have hAE :
        A ≠ E :=
      (HilbertOrder.between_incidence
        A D E hADE).2.2.1

    have hADEcol :
        Collinear Geo A D E :=
      (HilbertOrder.between_incidence
        A D E hADE).2.2.2.1

    have hDAE :
        Collinear Geo D A E :=
      PrimCollinearSwap
        Geo A D E hADEcol

    have hAEB :
        Collinear Geo A E B :=
      PrimCollinearSwap
        Geo E A B hCol

    have hDAB :
        Collinear Geo D A B :=
      hilbert_primCollinear_trans
        Geo D A E B
        hAE
        hDAE
        hAEB

    have hBC_DA :
        Geo.Parallel B C D A :=
      hABCD.2

    rcases hDAB with
      ⟨lineDA, hDline, hAline, hBline⟩

    have hB_DA :
        B ∈ Geo.PointLine D A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D A B
        lineDA
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

  --------------------------------------------------------------------
  -- SSS:
  --
  --   EA congruent FD
  --   AB congruent DC
  --   EB congruent FC
  --------------------------------------------------------------------

  have hSSS :=
    HilbertSSS
      Geo
      E A B
      F D C
      hEAB
      hEA_FD
      hAB_DC
      hEB_FC

  exact hSSS.2

theorem i35_equicomplementable_core
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F G : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADE : Geo.Between A D E)
    (hDEF : Geo.Between D E F)
    (hEGB : Geo.Between E G B)
    (hDGC : Geo.Between D G C) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo E B C F) := by

  --------------------------------------------------------------------
  -- Left augmented decomposition:
  --
  --   ABCD + DGE ~ EAB + GBC
  --------------------------------------------------------------------

  have hLeft :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D +
         hilbertScissorsTriangle Geo D G E)
        (hilbertScissorsTriangle Geo E A B +
         hilbertScissorsTriangle Geo G B C) :=
    i35_left_augmented_decomposition
      Geo
      A B C D E G
      hABCD
      hADE
      hEGB
      hDGC

  --------------------------------------------------------------------
  -- Right augmented decomposition:
  --
  --   EBCF + DGE ~ DCF + GBC
  --------------------------------------------------------------------

  have hRight :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E B C F +
         hilbertScissorsTriangle Geo D G E)
        (hilbertScissorsTriangle Geo D C F +
         hilbertScissorsTriangle Geo G B C) :=
    i35_right_augmented_decomposition
      Geo
      D E F B C G
      hDEF
      hEGB
      hDGC

  --------------------------------------------------------------------
  -- Outer triangles:
  --
  --   EAB congruent FDC
  --------------------------------------------------------------------

  have hOuter :
      TriangleCongruenceResult Geo
        E A B
        F D C :=
    i35_outer_triangles_congruent
      Geo
      A B C D E F
      hABCD
      hEBCF
      hADE
      hDEF

  have hOuterScissors0 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E A B)
        (hilbertScissorsTriangle Geo F D C) :=
    HilbertScissorsEq.congruent
      (Geo := Geo)
      E A B
      F D C
      hOuter

  --------------------------------------------------------------------
  -- Triangle FDC is the same formal triangle as DCF.
  --------------------------------------------------------------------

  have hOuterScissors :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E A B)
        (hilbertScissorsTriangle Geo D C F) := by

    have h := hOuterScissors0

    rw [scissors_triangle_cycle Geo F D C] at h

    exact h

  --------------------------------------------------------------------
  -- Add the common triangle GBC.
  --------------------------------------------------------------------

  have hMiddle :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E A B +
         hilbertScissorsTriangle Geo G B C)
        (hilbertScissorsTriangle Geo D C F +
         hilbertScissorsTriangle Geo G B C) :=

    HilbertScissorsEq.add
      (Geo := Geo)
      hOuterScissors
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo G B C))

  --------------------------------------------------------------------
  -- Hence the two augmented parallelograms are equidecomposable.
  --------------------------------------------------------------------

  have hAugmented :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D +
         hilbertScissorsTriangle Geo D G E)
        (hilbertParallelogramTerm Geo E B C F +
         hilbertScissorsTriangle Geo D G E) :=

    HilbertScissorsEq.trans
      (Geo := Geo)
      hLeft
      (HilbertScissorsEq.trans
        (Geo := Geo)
        hMiddle
        (HilbertScissorsEq.symm
          (Geo := Geo) hRight))

  --------------------------------------------------------------------
  -- The complements on both sides are literally the same triangle DGE.
  --------------------------------------------------------------------

  refine
    ⟨hilbertScissorsTriangle Geo D G E,
     hilbertScissorsTriangle Geo D G E,
     ?_,
     hAugmented⟩

  exact
    HilbertScissorsEq.refl
      (Geo := Geo)
      (hilbertScissorsTriangle Geo D G E)

theorem i35_disjoint_intersection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hADE : Geo.Between A D E) :
    ∃ G : Geo.Point,
      Geo.Between E G B ∧
      Geo.Between D G C := by

  have hAB_CD :
      Geo.Parallel A B C D :=
    hABCD.1

  have hBC_DA :
      Geo.Parallel B C D A :=
    hABCD.2

  have hAB : A ≠ B :=
    hAB_CD.1

  have hCD : C ≠ D :=
    hAB_CD.2.1

  have hDC : D ≠ C :=
    hCD.symm

  have hData :=
    HilbertOrder.between_incidence
      A D E hADE

  have hDE : D ≠ E :=
    hData.2.1

  have hAE : A ≠ E :=
    hData.2.2.1

  have hADEcol :
      Collinear Geo A D E :=
    hData.2.2.2.1

  --------------------------------------------------------------------
  -- Choose the actual Hilbert lines AB and DC.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A B hAB
    with
    ⟨lineAB, hA_AB, hB_AB⟩

  rcases
      HilbertPlaneIncidence.line_through
        D C hDC
    with
    ⟨lineDC, hD_DC, hC_DC⟩

  --------------------------------------------------------------------
  -- The two actual lines are disjoint because AB || CD.
  --------------------------------------------------------------------

  have hLinesDisjoint :
      HilbertLinesDisjoint Geo lineAB lineDC := by

    rintro ⟨X, hX_AB, hX_DC⟩

    have hXPointAB :
        X ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B X
        lineAB
        hAB
        hA_AB
        hB_AB).mpr hX_AB

    have hXPointCD :
        X ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D X
        lineDC
        hCD
        hC_DC
        hD_DC).mpr hX_DC

    exact
      Set.disjoint_left.mp
        hAB_CD.2.2
        hXPointAB
        hXPointCD

  have hA_not_DC :
      ¬ HilbertIncidence.OnLine A lineDC := by
    intro h
    exact
      hLinesDisjoint
        ⟨A, hA_AB, h⟩

  have hB_not_DC :
      ¬ HilbertIncidence.OnLine B lineDC := by
    intro h
    exact
      hLinesDisjoint
        ⟨B, hB_AB, h⟩

  --------------------------------------------------------------------
  -- E is not on DC.
  --
  -- Otherwise D,E determine DC, while A,D,E are collinear,
  -- forcing A onto DC, contrary to AB || DC.
  --------------------------------------------------------------------

  have hE_not_DC :
      ¬ HilbertIncidence.OnLine E lineDC := by
    intro hE_DC

    have hDEA :
        Collinear Geo D E A :=
      PrimCollinearCycle
        Geo A D E hADEcol

    have hA_DC :
        HilbertIncidence.OnLine A lineDC :=
      hilbert_collinear_on_line
        Geo
        D E A
        lineDC
        hDE
        hD_DC
        hE_DC
        hDEA

    exact hA_not_DC hA_DC

  --------------------------------------------------------------------
  -- Triangle AEB is nondegenerate.
  --------------------------------------------------------------------

  have hAEB :
      ¬ Collinear Geo A E B := by
    intro hCol

    have hABE :
        Collinear Geo A B E :=
      PrimCollinearRotate
        Geo A E B hCol

    have hE_AB :
        HilbertIncidence.OnLine E lineAB :=
      hilbert_collinear_on_line
        Geo
        A B E
        lineAB
        hAB
        hA_AB
        hB_AB
        hABE

    have hD_AB :
        HilbertIncidence.OnLine D lineAB :=
      hilbert_between_on_line
        Geo
        A D E
        lineAB
        hA_AB
        hE_AB
        hADE

    exact
      hLinesDisjoint
        ⟨D, hD_AB, hD_DC⟩

  --------------------------------------------------------------------
  -- DC meets the open side AE at D.
  --------------------------------------------------------------------

  have hMeetAE :
      HilbertSegmentMeetsLine
        Geo A E lineDC :=
    ⟨D, hADE, hD_DC⟩

  --------------------------------------------------------------------
  -- DC cannot meet the open side AB.
  --------------------------------------------------------------------

  have hNoMeetAB :
      ¬ HilbertSegmentMeetsLine
          Geo A B lineDC := by

    rintro ⟨X, hAXB, hX_DC⟩

    have hX_AB :
        HilbertIncidence.OnLine X lineAB :=
      hilbert_between_on_line
        Geo
        A X B
        lineAB
        hA_AB
        hB_AB
        hAXB

    exact
      hLinesDisjoint
        ⟨X, hX_AB, hX_DC⟩

  --------------------------------------------------------------------
  -- Pasch in triangle AEB.
  --
  -- Since DC enters through AE and cannot leave through AB,
  -- it must meet EB.
  --------------------------------------------------------------------

  have hPasch :=
    HilbertOrder.pasch
      (Geo := Geo)
      A E B
      hAEB
      lineDC
      hA_not_DC
      hE_not_DC
      hB_not_DC
      hMeetAE

  have hMeetEB :
      HilbertSegmentMeetsLine
        Geo E B lineDC := by

    rcases hPasch with
      hMeetAB | hMeetEB

    · exact False.elim (hNoMeetAB hMeetAB)

    · exact hMeetEB

  rcases hMeetEB with
    ⟨G, hEGB, hG_DC⟩

  --------------------------------------------------------------------
  -- G lies on DC.
  --------------------------------------------------------------------

  have hDCG :
      Collinear Geo D C G :=
    ⟨lineDC, hD_DC, hC_DC, hG_DC⟩

  --------------------------------------------------------------------
  -- ED is the same upper parallel as DA, hence ED || CB.
  --------------------------------------------------------------------

  have hDA_BC :
      Geo.Parallel D A B C :=
    ParallelSymmetry
      Geo B C D A hBC_DA

  have hEDA :
      Collinear Geo E D A :=
    PrimCollinearSymm
      Geo A D E hADEcol

  have hEA_BC :
      Geo.Parallel E A B C :=
    ParallelCollinearLeft
      Geo
      D A E B C
      hAE.symm
      hDA_BC
      hEDA

  have hED_BC :
      Geo.Parallel E D B C :=
    collinear_parallel_trans
      Geo
      E D A B C
      hDE.symm
      hEDA
      hEA_BC

  have hED_CB :
      Geo.Parallel E D C B :=
    ParallelSwapSecondLine
      Geo E D B C hED_BC

  --------------------------------------------------------------------
  -- Parallel crossing order:
  --
  -- E-G-B and D,G,C collinear imply D-G-C.
  --------------------------------------------------------------------

  have hDGC :
      Geo.Between D G C :=
    hilbert_collinear_between_of_parallel
      Geo
      E D C B G
      hED_CB
      hEGB
      hDCG

  exact
    ⟨G, hEGB, hDGC⟩


/- --------------------------------------------------------------------
  Common-endpoint configuration
---------------------------------------------------------------------/

theorem i35_common_endpoint
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hDBCF : IsParallelogram Geo D B C F) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo D B C F) := by

  --------------------------------------------------------------------
  -- Opposite-side congruences.
  --------------------------------------------------------------------

  have hSides1 :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hABCD

  have hSides2 :
      OppositeSidesCongruent Geo D B C F :=
    ParallelogramOppositeSidesCongruent
      Geo D B C F hDBCF

  --------------------------------------------------------------------
  -- DA congruent FD, because both are congruent to BC.
  --------------------------------------------------------------------

  have hDA_FD :
      Geo.Congruent D A F D :=
    HilbertCongruence.segment_congruence_common
      (Geo := Geo)
      B C
      D A
      F D
      hSides1.2
      hSides2.2

  --------------------------------------------------------------------
  -- AB congruent DC.
  --------------------------------------------------------------------

  have hAB_DC :
      Geo.Congruent A B D C :=
    CongruentSwapSecond
      Geo A B C D hSides1.1

  --------------------------------------------------------------------
  -- DB congruent FC.
  --------------------------------------------------------------------

  have hDB_FC :
      Geo.Congruent D B F C :=
    CongruentSwapSecond
      Geo D B C F hSides2.1

  --------------------------------------------------------------------
  -- Triangle DAB is noncollinear.
  --------------------------------------------------------------------

  have hDAB :
      ¬ Collinear Geo D A B := by
    intro hCol

    have hBC_DA :
        Geo.Parallel B C D A :=
      hABCD.2

    rcases hCol with
      ⟨lineDA, hDline, hAline, hBline⟩

    have hB_DA :
        B ∈ Geo.PointLine D A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D A B
        lineDA
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

  --------------------------------------------------------------------
  -- SSS:
  --
  --   DAB congruent FDC.
  --------------------------------------------------------------------

  have hOuter0 :=
    HilbertSSS
      Geo
      D A B
      F D C
      hDAB
      hDA_FD
      hAB_DC
      hDB_FC

  have hOuter :
      TriangleCongruenceResult Geo
        D A B
        F D C :=
    hOuter0.2

  have hOuterScissors0 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo D A B)
        (hilbertScissorsTriangle Geo F D C) :=
    HilbertScissorsEq.congruent
      (Geo := Geo)
      D A B
      F D C
      hOuter

  --------------------------------------------------------------------
  -- Normalize triangle vertex order:
  --
  --   DAB -> ABD
  --   FDC -> DCF
  --------------------------------------------------------------------

  have hOuterScissors :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D)
        (hilbertScissorsTriangle Geo D C F) := by

    have h := hOuterScissors0

    rw [scissors_triangle_cycle Geo D A B] at h
    rw [scissors_triangle_cycle Geo F D C] at h

    exact h

  --------------------------------------------------------------------
  -- The common triangle BCD is the same as DBC.
  --------------------------------------------------------------------

  have hCommon :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B C D)
        (hilbertScissorsTriangle Geo D B C) := by

    rw [scissors_triangle_cycle Geo D B C]

    exact
      HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo B C D)

  --------------------------------------------------------------------
  -- First parallelogram, triangulated by BD:
  --
  --   ABCD ~ ABD + BCD.
  --------------------------------------------------------------------

  have hFirst :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B C D) := by

    simpa [hilbertParallelogramTerm] using
      parallelogram_two_triangulations
        Geo A B C D hABCD

  --------------------------------------------------------------------
  -- Replace the outer triangle and retain the common triangle.
  --------------------------------------------------------------------

  have hMiddle :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B C D)
        (hilbertScissorsTriangle Geo D C F +
         hilbertScissorsTriangle Geo D B C) :=

    HilbertScissorsEq.add
      (Geo := Geo)
      hOuterScissors
      hCommon

  --------------------------------------------------------------------
  -- Reorder the two formal pieces.
  --------------------------------------------------------------------

  have hMiddle' :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B C D)
        (hilbertScissorsTriangle Geo D B C +
         hilbertScissorsTriangle Geo D C F) := by

    have h := hMiddle

    rw [Multiset.add_comm
      (hilbertScissorsTriangle Geo D C F)
      (hilbertScissorsTriangle Geo D B C)] at h

    exact h

  --------------------------------------------------------------------
  -- Hence the parallelograms themselves are scissors-equivalent.
  --------------------------------------------------------------------

  have hEq :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo D B C F) := by

    exact
      HilbertScissorsEq.trans
        (Geo := Geo)
        hFirst
        hMiddle'

  --------------------------------------------------------------------
  -- Therefore they are equicomplementable with zero complements.
  --------------------------------------------------------------------

  refine
    ⟨0, 0,
     HilbertScissorsEq.refl (Geo := Geo) 0,
     ?_⟩

  simpa using hEq


/- --------------------------------------------------------------------
  Overlap configuration
---------------------------------------------------------------------/

theorem i35_overlap_outer_triangles_congruent
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hAED : Geo.Between A E D)
    (hEDF : Geo.Between E D F) :
    TriangleCongruenceResult Geo E A B F D C := by

  --------------------------------------------------------------------
  -- Opposite sides of the two parallelograms.
  --------------------------------------------------------------------

  have hSides1 :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hABCD

  have hSides2 :
      OppositeSidesCongruent Geo E B C F :=
    ParallelogramOppositeSidesCongruent
      Geo E B C F hEBCF

  --------------------------------------------------------------------
  -- DA congruent EF, since both are congruent to BC.
  --------------------------------------------------------------------

  have hDA_FE :
      Geo.Congruent D A F E :=
    HilbertCongruence.segment_congruence_common
      (Geo := Geo)
      B C
      D A
      F E
      hSides1.2
      hSides2.2

  have hDA_EF :
      Geo.Congruent D A E F :=
    CongruentSwapSecond
      Geo D A F E hDA_FE

  --------------------------------------------------------------------
  -- DE congruent ED.
  --------------------------------------------------------------------

  have hDE_ED :
      Geo.Congruent D E E D :=
    CongruentSwapSecond
      Geo D E D E
      (hilbert_congruent_reflexive Geo D E)

  --------------------------------------------------------------------
  -- A-E-D gives D-E-A.
  --------------------------------------------------------------------

  have hDEA :
      Geo.Between D E A :=
    (HilbertOrder.between_incidence
      A E D hAED).2.2.2.2

  --------------------------------------------------------------------
  -- Segment subtraction:
  --
  --   D-E-A
  --   E-D-F
  --   DE congruent ED
  --   DA congruent EF
  --
  -- therefore EA congruent DF.
  --------------------------------------------------------------------

  have hEA_DF :
      Geo.Congruent E A D F :=
    hilbert_segment_subtraction
      Geo
      D E A
      E D F
      hDEA
      hEDF
      hDE_ED
      hDA_EF

  have hEA_FD :
      Geo.Congruent E A F D :=
    CongruentSwapSecond
      Geo E A D F hEA_DF

  --------------------------------------------------------------------
  -- AB congruent DC.
  --------------------------------------------------------------------

  have hAB_DC :
      Geo.Congruent A B D C :=
    CongruentSwapSecond
      Geo A B C D hSides1.1

  --------------------------------------------------------------------
  -- EB congruent FC.
  --------------------------------------------------------------------

  have hEB_FC :
      Geo.Congruent E B F C :=
    CongruentSwapSecond
      Geo E B C F hSides2.1

  --------------------------------------------------------------------
  -- Triangle EAB is noncollinear.
  --------------------------------------------------------------------

  have hEAB :
      ¬ Collinear Geo E A B := by
    intro hCol

    have hAE :
        A ≠ E :=
      (HilbertOrder.between_incidence
        A E D hAED).1

    have hAEDcol :
        Collinear Geo A E D :=
      (HilbertOrder.between_incidence
        A E D hAED).2.2.2.1

    have hDEAcol :
        Collinear Geo D E A :=
      PrimCollinearSymm
        Geo A E D hAEDcol

    have hDAE :
        Collinear Geo D A E :=
      PrimCollinearRotate
        Geo D E A hDEAcol

    have hAEB :
        Collinear Geo A E B :=
      PrimCollinearSwap
        Geo E A B hCol

    have hDAB :
        Collinear Geo D A B :=
      hilbert_primCollinear_trans
        Geo
        D A E B
        hAE
        hDAE
        hAEB

    have hBC_DA :
        Geo.Parallel B C D A :=
      hABCD.2

    rcases hDAB with
      ⟨lineDA, hDline, hAline, hBline⟩

    have hB_DA :
        B ∈ Geo.PointLine D A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D A B
        lineDA
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

  --------------------------------------------------------------------
  -- SSS.
  --------------------------------------------------------------------

  have hSSS :=
    HilbertSSS
      Geo
      E A B
      F D C
      hEAB
      hEA_FD
      hAB_DC
      hEB_FC

  exact hSSS.2

theorem i35_overlap_trapezoid_intersection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hAED : Geo.Between A E D) :
    ∃ G : Geo.Point,
      Geo.Between E G C ∧
      Geo.Between B G D := by

  --------------------------------------------------------------------
  -- Start with the diagonal intersection of ABCD.
  --------------------------------------------------------------------

  rcases
      ParallelogramDiagonalIntersectionExists
        Geo A B C D hABCD
    with
    ⟨M, hAMC, hBMD⟩

  --------------------------------------------------------------------
  -- D,A,M is noncollinear.
  --------------------------------------------------------------------

  have hDAM :
      ¬ Collinear Geo D A M := by
    intro hCol

    have hAM :
        A ≠ M :=
      (HilbertOrder.between_incidence
        A M C hAMC).1

    have hAMCcol :
        Collinear Geo A M C :=
      (HilbertOrder.between_incidence
        A M C hAMC).2.2.2.1

    have hDAC :
        Collinear Geo D A C :=
      hilbert_primCollinear_trans
        Geo
        D A M C
        hAM
        hCol
        hAMCcol

    have hBC_DA :
        Geo.Parallel B C D A :=
      hABCD.2

    rcases hDAC with
      ⟨lineDA, hDline, hAline, hCline⟩

    have hC_DA :
        C ∈ Geo.PointLine D A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D A C
        lineDA
        hBC_DA.2.1
        hDline
        hAline).mpr hCline

    have hC_BC :
        C ∈ Geo.PointLine B C := by
      change Geometry.Geo.LineCollinear Geo B C C
      exact Or.inr (Or.inr (Or.inl rfl))

    exact
      Set.disjoint_left.mp
        hBC_DA.2.2
        hC_BC
        hC_DA

  --------------------------------------------------------------------
  -- A-E-D gives D-E-A.
  --------------------------------------------------------------------

  have hDEA :
      Geo.Between D E A :=
    (HilbertOrder.between_incidence
      A E D hAED).2.2.2.2

  --------------------------------------------------------------------
  -- Inner Pasch in triangle D-A-M:
  --
  --   A-M-C
  --   D-E-A
  --
  -- produces G with
  --
  --   C-G-E
  --   D-G-M.
  --------------------------------------------------------------------

  rcases
      hilbert_inner_pasch_strong
        Geo
        D A M
        C E
        hDAM
        hAMC
        hDEA
    with
    ⟨G, hCGE, hDGM⟩

  have hEGC :
      Geo.Between E G C :=
    (HilbertOrder.between_incidence
      C G E hCGE).2.2.2.2

  --------------------------------------------------------------------
  -- Since B-M-D and D-G-M, we have B-G-D.
  --------------------------------------------------------------------

  have hDMB :
      Geo.Between D M B :=
    (HilbertOrder.between_incidence
      B M D hBMD).2.2.2.2

  have hDGB :
      Geo.Between D G B :=
    (hilbert_between_inner_trans
      Geo
      D G M B
      hDGM
      hDMB).2

  have hBGD :
      Geo.Between B G D :=
    (HilbertOrder.between_incidence
      D G B hDGB).2.2.2.2

  exact
    ⟨G, hEGC, hBGD⟩

theorem i35_overlap
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hAED : Geo.Between A E D)
    (hEDF : Geo.Between E D F) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo E B C F) := by

  --------------------------------------------------------------------
  -- The common trapezoid EBCD has crossing diagonals EC and BD.
  --------------------------------------------------------------------

  rcases
      i35_overlap_trapezoid_intersection
        Geo
        A B C D E
        hABCD
        hAED
    with
    ⟨G, hEGC, hBGD⟩

  have hTrap :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E B C +
         hilbertScissorsTriangle Geo E C D)
        (hilbertScissorsTriangle Geo E B D +
         hilbertScissorsTriangle Geo B C D) :=
    crossing_quadrilateral_two_triangulations
      Geo
      E B C D G
      hEGC
      hBGD

  --------------------------------------------------------------------
  -- Outer triangles EAB and FDC are congruent.
  --------------------------------------------------------------------

  have hOuterCong :
      TriangleCongruenceResult Geo
        E A B
        F D C :=
    i35_overlap_outer_triangles_congruent
      Geo
      A B C D E F
      hABCD
      hEBCF
      hAED
      hEDF

  have hOuter0 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E A B)
        (hilbertScissorsTriangle Geo F D C) :=
    HilbertScissorsEq.congruent
      (Geo := Geo)
      E A B
      F D C
      hOuterCong

  have hOuter :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B E)
        (hilbertScissorsTriangle Geo D C F) := by

    have h := hOuter0

    rw [scissors_triangle_cycle Geo E A B] at h
    rw [scissors_triangle_cycle Geo F D C] at h

    exact h

  --------------------------------------------------------------------
  -- First parallelogram:
  --
  --   ABCD
  --     ~ ABD + BCD
  --     ~ ABE + EBD + BCD.
  --------------------------------------------------------------------

  have hDiag :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B C D) := by

    simpa [hilbertParallelogramTerm] using
      parallelogram_two_triangulations
        Geo A B C D hABCD

  have hABD0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      B A D E
      hAED

  have hABD :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D)
        (hilbertScissorsTriangle Geo A B E +
         hilbertScissorsTriangle Geo E B D) := by

    rw [scissors_triangle_swap12 Geo B A D] at hABD0
    rw [scissors_triangle_swap12 Geo B A E] at hABD0
    rw [scissors_triangle_swap12 Geo B E D] at hABD0

    exact hABD0

  have hLeft0 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B C D)
        ((hilbertScissorsTriangle Geo A B E +
          hilbertScissorsTriangle Geo E B D) +
         hilbertScissorsTriangle Geo B C D) :=

    HilbertScissorsEq.add
      (Geo := Geo)
      hABD
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo B C D))

  have hLeft1 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B C D)
        (hilbertScissorsTriangle Geo A B E +
         (hilbertScissorsTriangle Geo E B D +
          hilbertScissorsTriangle Geo B C D)) := by

    have h := hLeft0

    rw [Multiset.add_assoc
      (hilbertScissorsTriangle Geo A B E)
      (hilbertScissorsTriangle Geo E B D)
      (hilbertScissorsTriangle Geo B C D)] at h

    exact h

  have hLeft :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B E +
         (hilbertScissorsTriangle Geo E B D +
          hilbertScissorsTriangle Geo B C D)) :=

    HilbertScissorsEq.trans
      (Geo := Geo)
      hDiag
      hLeft1

  --------------------------------------------------------------------
  -- Second parallelogram:
  --
  --   EBCF
  --     = EBC + ECF
  --     ~ EBC + ECD + DCF.
  --------------------------------------------------------------------

  have hECF0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      C E F D
      hEDF

  have hECF :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E C F)
        (hilbertScissorsTriangle Geo E C D +
         hilbertScissorsTriangle Geo D C F) := by

    rw [scissors_triangle_swap12 Geo C E F] at hECF0
    rw [scissors_triangle_swap12 Geo C E D] at hECF0
    rw [scissors_triangle_swap12 Geo C D F] at hECF0

    exact hECF0

  have hRight0 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E B C F)
        (hilbertScissorsTriangle Geo E B C +
         (hilbertScissorsTriangle Geo E C D +
          hilbertScissorsTriangle Geo D C F)) := by

    unfold hilbertParallelogramTerm

    exact
      HilbertScissorsEq.add
        (Geo := Geo)
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertScissorsTriangle Geo E B C))
        hECF

  have hRight :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo E B C F)
        (hilbertScissorsTriangle Geo D C F +
         (hilbertScissorsTriangle Geo E B C +
          hilbertScissorsTriangle Geo E C D)) := by

    have h := hRight0

    rw [← Multiset.add_assoc
      (hilbertScissorsTriangle Geo E B C)
      (hilbertScissorsTriangle Geo E C D)
      (hilbertScissorsTriangle Geo D C F)] at h

    rw [Multiset.add_comm
      (hilbertScissorsTriangle Geo E B C +
       hilbertScissorsTriangle Geo E C D)
      (hilbertScissorsTriangle Geo D C F)] at h

    exact h

  --------------------------------------------------------------------
  -- Replace the outer triangle and the common trapezoid.
  --------------------------------------------------------------------

  have hMiddle :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B E +
         (hilbertScissorsTriangle Geo E B D +
          hilbertScissorsTriangle Geo B C D))
        (hilbertScissorsTriangle Geo D C F +
         (hilbertScissorsTriangle Geo E B C +
          hilbertScissorsTriangle Geo E C D)) :=

    HilbertScissorsEq.add
      (Geo := Geo)
      hOuter
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hTrap)

  --------------------------------------------------------------------
  -- Hence the parallelograms themselves are scissors-equivalent.
  --------------------------------------------------------------------

  have hEq :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo E B C F) :=

    HilbertScissorsEq.trans
      (Geo := Geo)
      hLeft
      (HilbertScissorsEq.trans
        (Geo := Geo)
        hMiddle
        (HilbertScissorsEq.symm
          (Geo := Geo)
          hRight))

  --------------------------------------------------------------------
  -- Therefore they are equicomplementable with zero complements.
  --------------------------------------------------------------------

  refine
    ⟨0, 0,
     HilbertScissorsEq.refl
       (Geo := Geo) 0,
     ?_⟩

  simpa using hEq


/- --------------------------------------------------------------------
  Exhaustion of the three upper-side configurations
---------------------------------------------------------------------/

def I35RightCases
    (A D E F : Geo.Point) : Prop :=
  (Geo.Between A E D ∧ Geo.Between E D F) ∨
  E = D ∨
  (Geo.Between A D E ∧ Geo.Between D E F)

theorem i35_from_three_cases
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hCases :
      (Geo.Between A E D ∧ Geo.Between E D F) ∨
      E = D ∨
      (Geo.Between A D E ∧ Geo.Between D E F)) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo E B C F) := by

  rcases hCases with hOverlap | hCommon | hDisjoint

  --------------------------------------------------------------------
  -- Case 1: overlap
  --
  --   A-E-D-F
  --------------------------------------------------------------------

  · rcases hOverlap with ⟨hAED, hEDF⟩

    exact
      i35_overlap
        Geo
        A B C D E F
        hABCD
        hEBCF
        hAED
        hEDF

  --------------------------------------------------------------------
  -- Case 2: common endpoint
  --
  --   E = D
  --------------------------------------------------------------------

  · subst E

    exact
      i35_common_endpoint
        Geo
        A B C D F
        hABCD
        hEBCF

  --------------------------------------------------------------------
  -- Case 3: disjoint
  --
  --   A-D-E-F
  --------------------------------------------------------------------

  · rcases hDisjoint with ⟨hADE, hDEF⟩

    rcases
        i35_disjoint_intersection
          Geo
          A B C D E
          hABCD
          hADE
      with
      ⟨G, hEGB, hDGC⟩

    exact
      i35_equicomplementable_core
        Geo
        A B C D E F G
        hABCD
        hEBCF
        hADE
        hDEF
        hEGB
        hDGC

theorem i35_right_cases_of_common_container
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A D E F : Geo.Point)
    (hADF : Geo.Between A D F)
    (hAEF : Geo.Between A E F) :
    I35RightCases Geo A D E F := by

  by_cases hDE : D = E

  --------------------------------------------------------------------
  -- Common endpoint.
  --------------------------------------------------------------------

  · subst E

    exact
      Or.inr
        (Or.inl rfl)

  --------------------------------------------------------------------
  -- D and E are distinct interior points of AF.
  --------------------------------------------------------------------

  have hAF :
      A ≠ F :=
    (HilbertOrder.between_incidence
      A D F hADF).2.2.1

  have hAD :
      A ≠ D :=
    (HilbertOrder.between_incidence
      A D F hADF).1

  have hAE :
      A ≠ E :=
    (HilbertOrder.between_incidence
      A E F hAEF).1

  have hADFcol :
      Collinear Geo A D F :=
    (HilbertOrder.between_incidence
      A D F hADF).2.2.2.1

  have hAEFcol :
      Collinear Geo A E F :=
    (HilbertOrder.between_incidence
      A E F hAEF).2.2.2.1

  --------------------------------------------------------------------
  -- D and E lie on the same line AF.
  --------------------------------------------------------------------

  have hDAF :
      Collinear Geo D A F :=
    PrimCollinearSwap
      Geo A D F hADFcol

  have hAFE :
      Collinear Geo A F E :=
    PrimCollinearRotate
      Geo A E F hAEFcol

  have hDAE :
      Collinear Geo D A E :=
    hilbert_primCollinear_trans
      Geo
      D A F E
      hAF
      hDAF
      hAFE

  have hADEcol :
      Collinear Geo A D E :=
    PrimCollinearSwap
      Geo D A E hDAE

  --------------------------------------------------------------------
  -- Trichotomy for A,D,E.
  --------------------------------------------------------------------

  rcases
      hilbert_between_trichotomy
        Geo
        A D E
        hAD
        hDE
        hAE
        hADEcol
    with
    hADE | hDAEbetween | hAED

  --------------------------------------------------------------------
  -- A-D-E and A-E-F:
  --
  -- hence D-E-F.
  --
  -- This is the disjoint case A-D-E-F.
  --------------------------------------------------------------------

  · have hDEF :
        Geo.Between D E F :=
      (hilbert_between_inner_trans
        Geo
        A D E F
        hADE
        hAEF).1

    exact
      Or.inr
        (Or.inr
          ⟨hADE, hDEF⟩)

  --------------------------------------------------------------------
  -- D-A-E is impossible:
  --
  -- D-A-E and A-E-F imply D-A-F,
  -- contradicting A-D-F.
  --------------------------------------------------------------------

  · have hDAFbetween :
        Geo.Between D A F :=
      (hilbert_between_outer_trans
        Geo
        D A E F
        hDAEbetween
        hAEF).2

    have hNotDAF :
        ¬ Geo.Between D A F :=
      (HilbertOrder.between_unique
        (Geo := Geo)
        A D F
        hADFcol
        hADF).1

    exact
      False.elim
        (hNotDAF hDAFbetween)

  --------------------------------------------------------------------
  -- A-E-D and A-D-F:
  --
  -- hence E-D-F.
  --
  -- This is the overlap case A-E-D-F.
  --------------------------------------------------------------------

  · have hEDF :
        Geo.Between E D F :=
      (hilbert_between_inner_trans
        Geo
        A E D F
        hAED
        hADF).1

    exact
      Or.inl
        ⟨hAED, hEDF⟩


/- --------------------------------------------------------------------
  Order normalization for the stated configuration
---------------------------------------------------------------------/

theorem i35_not_EAF
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADF : Geo.Between A D F) :
    ¬ Geo.Between E A F := by

  intro hEAF

  --------------------------------------------------------------------
  -- AD congruent EF.
  --------------------------------------------------------------------

  have hSides1 :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hABCD

  have hSides2 :
      OppositeSidesCongruent Geo E B C F :=
    ParallelogramOppositeSidesCongruent
      Geo E B C F hEBCF

  have hAD_BC :
      Geo.Congruent A D B C := by

    have hDA_BC :
        Geo.Congruent D A B C :=
      CongruentSymmetry
        Geo B C D A hSides1.2

    exact
      CongruentReverseFirst
        Geo D A B C hDA_BC

  have hEF_BC :
      Geo.Congruent E F B C := by

    have hFE_BC :
        Geo.Congruent F E B C :=
      CongruentSymmetry
        Geo B C F E hSides2.2

    exact
      CongruentReverseFirst
        Geo F E B C hFE_BC

  have hAD_EF :
      Geo.Congruent A D E F :=
    hilbert_congruent_transitivity
      Geo
      A D
      B C
      E F
      hAD_BC
      (CongruentSymmetry
        Geo E F B C hEF_BC)

  --------------------------------------------------------------------
  -- A-D-F gives AD < AF.
  --------------------------------------------------------------------

  have hADltAF :
      HilbertSegmentLess Geo A D A F :=
    hilbert_segmentLess_of_between
      Geo A D F hADF

  --------------------------------------------------------------------
  -- Transfer AD < AF across AD congruent EF:
  --
  -- EF < AF.
  --------------------------------------------------------------------

  have hEF_AD :
      Geo.Congruent E F A D :=
    CongruentSymmetry
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

  --------------------------------------------------------------------
  -- E-A-F gives F-A-E, hence FA < FE.
  --------------------------------------------------------------------

  have hFAE :
      Geo.Between F A E :=
    (HilbertOrder.between_incidence
      E A F hEAF).2.2.2.2

  have hFAltFE :
      HilbertSegmentLess Geo F A F E :=
    hilbert_segmentLess_of_between
      Geo F A E hFAE

  --------------------------------------------------------------------
  -- Normalize endpoint orientations:
  --
  -- AF < EF.
  --------------------------------------------------------------------

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

  --------------------------------------------------------------------
  -- Contradiction:
  --
  -- EF < AF and AF < EF.
  --------------------------------------------------------------------

  exact
    (hilbert_segmentLess_asymm
      Geo E F A F hEFltAF)
      hAFltEF

theorem i35_cross_intersection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hADF : Geo.Between A D F) :
    ∃ Q : Geo.Point,
      Geo.Between B Q F ∧
      Geo.Between A Q C := by

  --------------------------------------------------------------------
  -- Diagonal intersection of ABCD.
  --------------------------------------------------------------------

  rcases
      ParallelogramDiagonalIntersectionExists
        Geo A B C D hABCD
    with
    ⟨M, hAMC, hBMD⟩

  --------------------------------------------------------------------
  -- A,D,B are noncollinear.
  --------------------------------------------------------------------

  have hADB :
      ¬ Collinear Geo A D B := by
    intro hCol

    have hBC_DA :
        Geo.Parallel B C D A :=
      hABCD.2

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

  --------------------------------------------------------------------
  -- Hence A,F,B are noncollinear, since D lies on AF.
  --------------------------------------------------------------------

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

  --------------------------------------------------------------------
  -- Outer Pasch:
  --
  -- A-D-F
  -- B-M-D
  --
  -- gives Q with B-Q-F and A-M-Q.
  --------------------------------------------------------------------

  rcases
      hilbert_outer_pasch
        Geo
        A B D F M
        hAFB
        hADF
        hBMD
    with
    ⟨Q, hBQF, hAMQ⟩

  --------------------------------------------------------------------
  -- Q lies on AC.
  --------------------------------------------------------------------

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

  have hACQ :
      Collinear Geo A C Q :=
    PrimCollinearRotate
      Geo A Q C
      (PrimCollinearSwap
        Geo Q A C hQAC)

  --------------------------------------------------------------------
  -- FA is parallel to CB.
  --
  -- F lies on DA, and DA is parallel to BC.
  --------------------------------------------------------------------

  have hBC_DA :
      Geo.Parallel B C D A :=
    hABCD.2

  have hDA_BC :
      Geo.Parallel D A B C :=
    ParallelSymmetry
      Geo B C D A hBC_DA

  have hFA :
      F ≠ A :=
    hAF.symm

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

  --------------------------------------------------------------------
  -- F-Q-B together with FA || CB and Q on AC
  -- forces A-Q-C.
  --------------------------------------------------------------------

  have hFQB :
      Geo.Between F Q B :=
    (HilbertOrder.between_incidence
      B Q F hBQF).2.2.2.2

  have hAQC :
      Geo.Between A Q C :=
    hilbert_collinear_between_of_parallel
      Geo
      F A C B Q
      hFA_CB
      hFQB
      hACQ

  exact
    ⟨Q, hBQF, hAQC⟩

theorem i35_not_AFE
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADF : Geo.Between A D F) :
    ¬ Geo.Between A F E := by

  intro hAFE

  --------------------------------------------------------------------
  -- From the first parallelogram:
  --
  -- BF crosses AC internally.
  --------------------------------------------------------------------

  rcases
      i35_cross_intersection
        Geo
        A B C D F
        hABCD
        hADF
    with
    ⟨Q, hBQF, hAQC⟩

  --------------------------------------------------------------------
  -- From the second parallelogram:
  --
  -- its diagonals EC and BF cross internally.
  --------------------------------------------------------------------

  rcases
      ParallelogramDiagonalIntersectionExists
        Geo E B C F hEBCF
    with
    ⟨N, hENC, hBNF⟩

  --------------------------------------------------------------------
  -- Triangle AEC is noncollinear.
  --
  -- A,F,E lie on the upper line FE, while C lies on BC,
  -- and FE is parallel to BC.
  --------------------------------------------------------------------

  have hAEC :
      ¬ Collinear Geo A E C := by
    intro hCol

    have hAE :
        A ≠ E :=
      (HilbertOrder.between_incidence
        A F E hAFE).2.2.1

    have hAFEcol :
        Collinear Geo A F E :=
      (HilbertOrder.between_incidence
        A F E hAFE).2.2.2.1

    have hFEA :
        Collinear Geo F E A :=
      PrimCollinearCycle
        Geo A F E hAFEcol

    have hEAC :
        Collinear Geo E A C :=
      PrimCollinearSwap
        Geo A E C hCol

    have hFEC :
        Collinear Geo F E C :=
      hilbert_primCollinear_trans
        Geo
        F E A C
        hAE.symm
        hFEA
        hEAC

    have hBC_FE :
        Geo.Parallel B C F E :=
      hEBCF.2

    rcases hFEC with
      ⟨lineFE, hFline, hEline, hCline⟩

    have hC_FE :
        C ∈ Geo.PointLine F E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        F E C
        lineFE
        hBC_FE.2.1
        hFline
        hEline).mpr hCline

    have hC_BC :
        C ∈ Geo.PointLine B C := by
      change Geometry.Geo.LineCollinear Geo B C C
      exact Or.inr (Or.inr (Or.inl rfl))

    exact
      Set.disjoint_left.mp
        hBC_FE.2.2
        hC_BC
        hC_FE

  --------------------------------------------------------------------
  -- Choose the incidence line BF.
  --------------------------------------------------------------------

  have hBF :
      B ≠ F :=
    (HilbertOrder.between_incidence
      B N F hBNF).2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        B F hBF
    with
    ⟨lineBF, hBline, hFline⟩

  --------------------------------------------------------------------
  -- Q lies on BF because B-Q-F.
  --------------------------------------------------------------------

  have hQline :
      HilbertIncidence.OnLine Q lineBF :=
    hilbert_between_on_line
      Geo
      B Q F
      lineBF
      hBline
      hFline
      hBQF

  --------------------------------------------------------------------
  -- Since BF meets AF? More precisely:
  --
  -- in triangle AEC,
  --   F is interior to AE,
  --   Q is interior to AC.
  --
  -- Therefore BF cannot meet EC.
  --------------------------------------------------------------------

  have hNoMeetEC :
      ¬ HilbertSegmentMeetsLine Geo E C lineBF :=
    hilbert_line_avoids_third_triangle_side
      Geo
      A E C
      F Q
      lineBF
      hAEC
      hAFE
      hAQC
      hFline
      hQline

  --------------------------------------------------------------------
  -- But the second parallelogram gives N interior to EC and BF.
  --------------------------------------------------------------------

  have hNline :
      HilbertIncidence.OnLine N lineBF :=
    hilbert_between_on_line
      Geo
      B N F
      lineBF
      hBline
      hFline
      hBNF

  have hMeetEC :
      HilbertSegmentMeetsLine Geo E C lineBF :=
    ⟨N, hENC, hNline⟩

  exact
    hNoMeetEC hMeetEC

theorem i35_upper_order
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADF : Geo.Between A D F)
    (hAEF : Collinear Geo A E F) :
    Geo.Between A E F := by

  --------------------------------------------------------------------
  -- AD congruent EF.
  --------------------------------------------------------------------

  have hSides1 :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hABCD

  have hSides2 :
      OppositeSidesCongruent Geo E B C F :=
    ParallelogramOppositeSidesCongruent
      Geo E B C F hEBCF

  have hAD_BC :
      Geo.Congruent A D B C := by

    have hDA_BC :
        Geo.Congruent D A B C :=
      CongruentSymmetry
        Geo B C D A hSides1.2

    exact
      CongruentReverseFirst
        Geo D A B C hDA_BC

  have hEF_BC :
      Geo.Congruent E F B C := by

    have hFE_BC :
        Geo.Congruent F E B C :=
      CongruentSymmetry
        Geo B C F E hSides2.2

    exact
      CongruentReverseFirst
        Geo F E B C hFE_BC

  have hAD_EF :
      Geo.Congruent A D E F :=
    hilbert_congruent_transitivity
      Geo
      A D
      B C
      E F
      hAD_BC
      (CongruentSymmetry
        Geo E F B C hEF_BC)

  --------------------------------------------------------------------
  -- Distinctness needed for Hilbert Theorem 4.
  --------------------------------------------------------------------

  have hAF :
      A ≠ F :=
    (HilbertOrder.between_incidence
      A D F hADF).2.2.1

  have hEF :
      E ≠ F := by
    have hBC_FE :
        Geo.Parallel B C F E :=
      hEBCF.2

    exact
      hBC_FE.2.1.symm

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

  --------------------------------------------------------------------
  -- Hilbert Theorem 4 on A,E,F.
  --------------------------------------------------------------------

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

  --------------------------------------------------------------------
  -- The desired order.
  --------------------------------------------------------------------

  · exact hAEFbetween

  --------------------------------------------------------------------
  -- E-A-F was excluded by segment comparison.
  --------------------------------------------------------------------

  · exact
      False.elim
        ((i35_not_EAF
            Geo
            A B C D E F
            hABCD
            hEBCF
            hADF)
          hEAF)

  --------------------------------------------------------------------
  -- A-F-E was excluded by the line-separation argument.
  --------------------------------------------------------------------

  · exact
      False.elim
        ((i35_not_AFE
            Geo
            A B C D E F
            hABCD
            hEBCF
            hADF)
          hAFE)

theorem i35_ordered
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADF : Geo.Between A D F)
    (hAEF : Collinear Geo A E F) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo E B C F) := by

  --------------------------------------------------------------------
  -- First recover the actual order A-E-F on the common upper line.
  --------------------------------------------------------------------

  have hAEFbetween :
      Geo.Between A E F :=
    i35_upper_order
      Geo
      A B C D E F
      hABCD
      hEBCF
      hADF
      hAEF

  --------------------------------------------------------------------
  -- Compare the two interior points D and E of AF.
  --
  -- This produces exactly:
  --
  --   A-E-D-F
  --   E = D
  --   A-D-E-F
  --------------------------------------------------------------------

  have hCases :
      I35RightCases Geo A D E F :=
    i35_right_cases_of_common_container
      Geo
      A D E F
      hADF
      hAEFbetween

  --------------------------------------------------------------------
  -- Each of the three configurations has already been proved.
  --------------------------------------------------------------------

  exact
    i35_from_three_cases
      Geo
      A B C D E F
      hABCD
      hEBCF
      hCases


/- --------------------------------------------------------------------
  Euclid I.35
---------------------------------------------------------------------/

/--
Euclid I.35.

Parallelograms on the same base and in the same parallels are
equicomplementable in the formal Hilbert scissors calculus.

The hypotheses `hADF` and `hAEF` encode the common upper parallel
configuration used in the present Hilbert reconstruction.
-/
theorem euclid_proposition_35
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hEBCF : IsParallelogram Geo E B C F)
    (hADF : Geo.Between A D F)
    (hAEF : Collinear Geo A E F) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo E B C F) := by
  exact
    i35_ordered
      Geo
      A B C D E F
      hABCD
      hEBCF
      hADF
      hAEF

end Geometry

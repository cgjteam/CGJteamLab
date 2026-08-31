import CGJteamLab.HilbertRectangle
import CGJteamLab.Proposition2_2
import CGJteamLab.Proposition2_3
import CGJteamLab.Proposition2_6
import CGJteamLab.Proposition10
import CGJteamLab.Proposition16
import CGJteamLab.Proposition19
import CGJteamLab.Proposition20
import CGJteamLab.Proposition46
import CGJteamLab.Proposition47
import CGJteamLab.HilbertSquareTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid II.11 -- generic rectangle cut core.

Core cut constructor for an arbitrary rectangle.

Given

    D -------- E
    |          |
    |          |
    B --- M -- C

with B-M-C, construct L so that

    D --- L --- E
    |     |     |
    |     |     |
    B --- M --- C

and both pieces are parallelograms.

This is the generic version of the square-cut geometry used in I.47.
No betweenness D-L-E or diagonal intersection is proved yet.
-/
private theorem proposition2_11_rectangle_cut_core
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C) :
    exists L : Geo.Point,
      Collinear Geo D L E /\
      IsParallelogram Geo L D B M /\
      IsParallelogram Geo C E L M := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hBM : Ne B M :=
    hBMCdata.1

  have hMC : Ne M C :=
    hBMCdata.2.1

  have hBC : Ne B C :=
    hBMCdata.2.2.1

  have hBMCcol :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  have hBCMcol :
      Collinear Geo B C M :=
    PrimCollinearRotate
      Geo B M C hBMCcol

  --------------------------------------------------------------------
  -- C,E,M are noncollinear.
  --------------------------------------------------------------------

  have hRectNC :=
    parallelogram_vertices_noncollinear
      Geo B C E D hRect.1

  have hBCE :
      Not (Collinear Geo B C E) :=
    hRectNC.2.1

  have hCEM :
      Not (Collinear Geo C E M) := by
    intro hCEMcol

    have hCME :
        Collinear Geo C M E :=
      PrimCollinearRotate
        Geo C E M hCEMcol

    have hBCEcol :
        Collinear Geo B C E :=
      hilbert_primCollinear_trans
        Geo
        B C M E
        hMC.symm
        hBCMcol
        hCME

    exact hBCE hBCEcol

  --------------------------------------------------------------------
  -- Complete C-E-M to the parallelogram C-E-L-M.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo C E M hCEM with
    ⟨L, hRightPar⟩

  --------------------------------------------------------------------
  -- First show that EL is parallel to BC.
  --
  -- Right cut: EL || MC.
  -- Since B,M,C are collinear, MC has the same carrier as BC.
  --------------------------------------------------------------------

  have hParMC_EL :
      Geo.Parallel M C E L :=
    ParallelSymmetry
      Geo
      E L M C
      hRightPar.2

  have hParBC_EL :
      Geo.Parallel B C E L :=
    ParallelCollinearLeft
      Geo
      M C B
      E L
      hBC
      hParMC_EL
      hBMCcol

  have hParEL_BC :
      Geo.Parallel E L B C :=
    ParallelSymmetry
      Geo B C E L hParBC_EL

  --------------------------------------------------------------------
  -- The upper side ED of the original rectangle is also parallel BC.
  --------------------------------------------------------------------

  have hParBC_ED :
      Geo.Parallel B C E D :=
    hRect.1.1

  have hParED_BC :
      Geo.Parallel E D B C :=
    ParallelSymmetry
      Geo B C E D hParBC_ED

  --------------------------------------------------------------------
  -- EL and ED pass through E and are both parallel to BC.
  -- Hilbert IV identifies their incidence carriers.
  --------------------------------------------------------------------

  have hEL : Ne E L :=
    hParEL_BC.1

  have hED : Ne E D :=
    hParED_BC.1

  rcases
      HilbertPlaneIncidence.line_through
        B C hBC with
    ⟨lineBC, hBbc, hCbc⟩

  rcases
      HilbertPlaneIncidence.line_through
        E D hED with
    ⟨lineED, hEed, hDed⟩

  rcases
      HilbertPlaneIncidence.line_through
        E L hEL with
    ⟨lineEL, hEel, hLel⟩

  have hLinesED_BC :
      HilbertLinesDisjoint Geo lineED lineBC := by
    rintro ⟨X, hXed, hXbc⟩

    have hXED :
        X ∈ Geo.PointLine E D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo E D X lineED
        hED hEed hDed).mpr hXed

    have hXBC :
        X ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X lineBC
        hBC hBbc hCbc).mpr hXbc

    exact
      Set.disjoint_left.mp
        hParED_BC.2.2
        hXED hXBC

  have hLinesEL_BC :
      HilbertLinesDisjoint Geo lineEL lineBC := by
    rintro ⟨X, hXel, hXbc⟩

    have hXEL :
        X ∈ Geo.PointLine E L :=
      (hilbert_mem_pointLine_iff_onLine
        Geo E L X lineEL
        hEL hEel hLel).mpr hXel

    have hXBC :
        X ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X lineBC
        hBC hBbc hCbc).mpr hXbc

    exact
      Set.disjoint_left.mp
        hParEL_BC.2.2
        hXEL hXBC

  have hEoffBC :
      Not (HilbertIncidence.OnLine E lineBC) := by
    intro hEbc
    exact
      hLinesED_BC
        ⟨E, hEed, hEbc⟩

  have hLineED_EL :
      lineED = lineEL :=
    HilbertEuclideanPlane.parallel_unique
      (Geo := Geo)
      lineBC
      E
      hEoffBC
      lineED
      lineEL
      hEed
      hLinesED_BC
      hEel
      hLinesEL_BC

  have hLed :
      HilbertIncidence.OnLine L lineED := by
    rw [hLineED_EL]
    exact hLel

  have hDLEcol :
      Collinear Geo D L E :=
    ⟨lineED, hDed, hLed, hEed⟩

  --------------------------------------------------------------------
  -- L is distinct from D.
  --
  -- Otherwise DB and DM would be two parallels through D to CE.
  -- Their carriers would coincide, putting D,B,M,C on one line,
  -- contradicting the rectangle.
  --------------------------------------------------------------------

  have hLD : Ne L D := by
    intro hLD_eq
    subst L

    have hParDB_CE :
        Geo.Parallel D B C E :=
      ParallelSymmetry
        Geo C E D B hRect.1.2

    have hParDM_CE :
        Geo.Parallel D M C E :=
      ParallelSymmetry
        Geo C E D M hRightPar.1

    have hCarrier :
        Geo.PointLine D B =
        Geo.PointLine D M := by
      by_contra hDistinct

      have hDB_DM :
          Geo.Parallel D B D M :=
        hilbert_parallel_transitive_distinct
          Geo
          D B
          D M
          C E
          hParDB_CE
          hParDM_CE
          hDistinct

      exact
        (intersection_test_not_parallel_of_common_point
          Geo
          D B
          D M
          D
          (intersection_test_left_mem Geo D B)
          (intersection_test_left_mem Geo D M))
          hDB_DM

    have hDB : Ne D B :=
      hParDB_CE.1

    rcases
        HilbertPlaneIncidence.line_through
          D B hDB with
      ⟨lineDB, hDdb, hBdb⟩

    have hM_DM :
        M ∈ Geo.PointLine D M :=
      intersection_test_right_mem
        Geo D M

    have hM_DB :
        M ∈ Geo.PointLine D B := by
      rw [hCarrier]
      exact hM_DM

    have hMdb :
        HilbertIncidence.OnLine M lineDB :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D B M lineDB
        hDB hDdb hBdb).mp hM_DB

    have hDBM :
        Collinear Geo D B M :=
      ⟨lineDB, hDdb, hBdb, hMdb⟩

    have hDBC :
        Collinear Geo D B C :=
      hilbert_primCollinear_trans
        Geo
        D B M C
        hBM
        hDBM
        hBMCcol

    exact hRectNC.1 hDBC

  --------------------------------------------------------------------
  -- First opposite pair of the left piece:
  --
  --     LD || BM.
  --------------------------------------------------------------------

  have hLEDcol :
      Collinear Geo L E D :=
    PrimCollinearCycle
      Geo D L E hDLEcol

  have hParLD_BC :
      Geo.Parallel L D B C :=
    ParallelCollinearLeft
      Geo
      E D L
      B C
      hLD
      hParED_BC
      hLEDcol

  have hParBC_LD :
      Geo.Parallel B C L D :=
    ParallelSymmetry
      Geo L D B C hParLD_BC

  have hParBM_LD :
      Geo.Parallel B M L D :=
    collinear_parallel_trans
      Geo
      B M C
      L D
      hBM
      hBMCcol
      hParBC_LD

  have hParLD_BM :
      Geo.Parallel L D B M :=
    ParallelSymmetry
      Geo B M L D hParBM_LD

  --------------------------------------------------------------------
  -- Second opposite pair:
  --
  --     DB || ML.
  --------------------------------------------------------------------

  have hParDB_CE :
      Geo.Parallel D B C E :=
    ParallelSymmetry
      Geo C E D B hRect.1.2

  have hParLM_CE :
      Geo.Parallel L M C E :=
    ParallelSymmetry
      Geo C E L M hRightPar.1

  have hDistinctDB_LM :
      Geo.PointLine D B ≠
      Geo.PointLine L M := by
    intro hCarrier

    have hDB : Ne D B :=
      hParDB_CE.1

    rcases
        HilbertPlaneIncidence.line_through
          D B hDB with
      ⟨lineDB, hDdb, hBdb⟩

    have hM_LM :
        M ∈ Geo.PointLine L M :=
      intersection_test_right_mem
        Geo L M

    have hM_DB :
        M ∈ Geo.PointLine D B := by
      rw [hCarrier]
      exact hM_LM

    have hMdb :
        HilbertIncidence.OnLine M lineDB :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D B M lineDB
        hDB hDdb hBdb).mp hM_DB

    have hDBM :
        Collinear Geo D B M :=
      ⟨lineDB, hDdb, hBdb, hMdb⟩

    have hDBC :
        Collinear Geo D B C :=
      hilbert_primCollinear_trans
        Geo
        D B M C
        hBM
        hDBM
        hBMCcol

    exact hRectNC.1 hDBC

  have hParDB_LM :
      Geo.Parallel D B L M :=
    hilbert_parallel_transitive_distinct
      Geo
      D B
      L M
      C E
      hParDB_CE
      hParLM_CE
      hDistinctDB_LM

  have hParDB_ML :
      Geo.Parallel D B M L :=
    ParallelSwapSecondLine
      Geo D B L M hParDB_LM

  have hLeftPar :
      IsParallelogram Geo L D B M :=
    ⟨hParLD_BM, hParDB_ML⟩

  exact
    ⟨L,
      hDLEcol,
      hLeftPar,
      hRightPar⟩


/--
Euclid II.11 -- upper-side order transfer.

Strengthen the generic rectangle cut from mere collinearity

    D, L, E

to the strict order

    D --- L --- E.

The proof is Hilbert Theorem 27.

From the original rectangle and the two cut parallelograms:

    BM ~= DL,
    BC ~= DE,
    MC ~= LE.

Since B-M-C, the corresponding point L lies strictly between D and E.
-/
private theorem proposition2_11_rectangle_cut_between
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C) :
    exists L : Geo.Point,
      Geo.Between D L E /\
      IsParallelogram Geo L D B M /\
      IsParallelogram Geo C E L M := by

  rcases
      proposition2_11_rectangle_cut_core
        Geo
        B C D E M
        hRect
        hBMC with
    ⟨L, hDLEcol, hLeftPar, hRightPar⟩

  --------------------------------------------------------------------
  -- Distinctness of D,L,E.
  --------------------------------------------------------------------

  have hDL : Ne D L :=
    hLeftPar.1.1.symm

  have hLE : Ne L E :=
    hRightPar.2.1.symm

  have hDE : Ne D E :=
    hRect.1.1.2.1.symm

  --------------------------------------------------------------------
  -- BM ~= DL from L-D-B-M.
  --------------------------------------------------------------------

  have hLeftSides :
      OppositeSidesCongruent Geo L D B M :=
    ParallelogramOppositeSidesCongruent
      Geo L D B M hLeftPar

  have hLD_BM :
      Geo.Congruent L D B M :=
    hLeftSides.1

  have hBM_LD :
      Geo.Congruent B M L D :=
    hilbert_congruent_symmetry
      Geo L D B M hLD_BM

  have hBM_DL :
      Geo.Congruent B M D L :=
    CongruentSwapSecond
      Geo B M L D hBM_LD

  --------------------------------------------------------------------
  -- BC ~= DE from the original rectangle.
  --------------------------------------------------------------------

  have hWholeSides :
      OppositeSidesCongruent Geo B C E D :=
    ParallelogramOppositeSidesCongruent
      Geo B C E D hRect.1

  have hBC_ED :
      Geo.Congruent B C E D :=
    hWholeSides.1

  have hBC_DE :
      Geo.Congruent B C D E :=
    CongruentSwapSecond
      Geo B C E D hBC_ED

  --------------------------------------------------------------------
  -- MC ~= LE from C-E-L-M.
  --------------------------------------------------------------------

  have hRightSides :
      OppositeSidesCongruent Geo C E L M :=
    ParallelogramOppositeSidesCongruent
      Geo C E L M hRightPar

  have hEL_MC :
      Geo.Congruent E L M C :=
    hRightSides.2

  have hMC_EL :
      Geo.Congruent M C E L :=
    hilbert_congruent_symmetry
      Geo E L M C hEL_MC

  have hMC_LE :
      Geo.Congruent M C L E :=
    CongruentSwapSecond
      Geo M C E L hMC_EL

  --------------------------------------------------------------------
  -- Hilbert Theorem 27 transports B-M-C to D-L-E.
  --------------------------------------------------------------------

  have hDLE :
      Geo.Between D L E :=
    hilbert_theorem27_three_points
      Geo
      B M C
      D L E
      hBMC
      hDL
      hLE
      hDE
      hBM_DL
      hBC_DE
      hMC_LE

  exact
    ⟨L,
      hDLE,
      hLeftPar,
      hRightPar⟩


/--
Euclid II.11 -- diagonal/cut intersection.

Generic diagonal/cut intersection for a rectangle.

This is the I.47 Pasch argument with the square hypothesis weakened
to an arbitrary rectangle.  Only the parallelogram structure of the
rectangle is used to prove that triangle C-B-D is nondegenerate.
-/
private theorem proposition2_11_diagonal_cut_intersection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M L : Geo.Point)
    (hBMC : Geo.Between B M C)
    (hRect : IsRectangle Geo B C E D)
    (hLeftPar : IsParallelogram Geo L D B M) :
    exists N : Geo.Point,
      Geo.Between D N C /\
      Geo.Between M N L := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hBMC

  have hBM : Ne B M :=
    hBMCdata.1

  have hMC : Ne M C :=
    hBMCdata.2.1

  have hBC : Ne B C :=
    hBMCdata.2.2.1

  have hBMCcol :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  have hCMB :
      Geo.Between C M B :=
    hBMCdata.2.2.2.2

  have hCMBcol :
      Collinear Geo C M B :=
    (HilbertOrder.between_incidence
      C M B hCMB).2.2.2.1

  --------------------------------------------------------------------
  -- DB || ML from the left cut parallelogram.
  --------------------------------------------------------------------

  have hDB_ML :
      Geo.Parallel D B M L :=
    hLeftPar.2

  have hDB : Ne D B :=
    hDB_ML.1

  have hML : Ne M L :=
    hDB_ML.2.1

  --------------------------------------------------------------------
  -- Choose actual incidence carriers DB and ML.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        D B hDB with
    ⟨lineDB, hDdb, hBdb⟩

  rcases
      HilbertPlaneIncidence.line_through
        M L hML with
    ⟨lineML, hMml, hLml⟩

  --------------------------------------------------------------------
  -- The two incidence lines are disjoint because DB || ML.
  --------------------------------------------------------------------

  have hLinesDB_ML :
      HilbertLinesDisjoint Geo lineDB lineML := by

    rintro ⟨X, hXdb, hXml⟩

    have hX_DB :
        X ∈ Geo.PointLine D B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D B X
        lineDB
        hDB
        hDdb
        hBdb).mpr hXdb

    have hX_ML :
        X ∈ Geo.PointLine M L :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        M L X
        lineML
        hML
        hMml
        hLml).mpr hXml

    exact
      Set.disjoint_left.mp
        hDB_ML.2.2
        hX_DB
        hX_ML

  --------------------------------------------------------------------
  -- B and D are off ML.
  --------------------------------------------------------------------

  have hBoff :
      Not (HilbertIncidence.OnLine B lineML) := by
    intro hBml
    exact
      hLinesDB_ML
        ⟨B, hBdb, hBml⟩

  have hDoff :
      Not (HilbertIncidence.OnLine D lineML) := by
    intro hDml
    exact
      hLinesDB_ML
        ⟨D, hDdb, hDml⟩

  --------------------------------------------------------------------
  -- C is also off ML.
  --------------------------------------------------------------------

  have hCoff :
      Not (HilbertIncidence.OnLine C lineML) := by
    intro hCml

    have hBml :
        HilbertIncidence.OnLine B lineML :=
      hilbert_collinear_on_line
        Geo
        C M B
        lineML
        hMC.symm
        hCml
        hMml
        hCMBcol

    exact hBoff hBml

  --------------------------------------------------------------------
  -- Triangle C-B-D is nondegenerate.
  --
  -- Here the I.47 proof used hSquare.1.  A rectangle already has the
  -- same parallelogram structure as its first component.
  --------------------------------------------------------------------

  have hRectNC :=
    parallelogram_vertices_noncollinear
      Geo B C E D hRect.1

  have hDBC :
      Not (Collinear Geo D B C) :=
    hRectNC.1

  have hCBD :
      Not (Collinear Geo C B D) := by
    intro h
    exact
      hDBC
        (PrimCollinearSymm
          Geo C B D h)

  --------------------------------------------------------------------
  -- ML enters triangle C-B-D through CB at M.
  --------------------------------------------------------------------

  have hMeetsCB :
      HilbertSegmentMeetsLine Geo C B lineML :=
    ⟨M, hCMB, hMml⟩

  --------------------------------------------------------------------
  -- ML cannot meet the open side BD because DB || ML.
  --------------------------------------------------------------------

  have hNotMeetsBD :
      Not (HilbertSegmentMeetsLine Geo B D lineML) := by

    rintro ⟨X, hBXD, hXml⟩

    have hXdb :
        HilbertIncidence.OnLine X lineDB :=
      hilbert_between_on_line
        Geo
        B X D
        lineDB
        hBdb
        hDdb
        hBXD

    exact
      hLinesDB_ML
        ⟨X, hXdb, hXml⟩

  --------------------------------------------------------------------
  -- Forced Pasch: ML meets CD internally.
  --------------------------------------------------------------------

  have hMeetsCD :
      HilbertSegmentMeetsLine Geo C D lineML :=
    hilbert_pasch_forced
      Geo
      C B D
      lineML
      hCBD
      hCoff
      hBoff
      hDoff
      hMeetsCB
      hNotMeetsBD

  rcases hMeetsCD with
    ⟨N, hCND, hNml⟩

  have hDNC :
      Geo.Between D N C :=
    (HilbertOrder.between_incidence
      C N D hCND).2.2.2.2

  have hLMN :
      Collinear Geo L M N :=
    ⟨lineML,
      hLml,
      hMml,
      hNml⟩

  --------------------------------------------------------------------
  -- DL || MC.
  --------------------------------------------------------------------

  have hDL_BM :
      Geo.Parallel D L B M :=
    ParallelSwapFirstLine
      Geo
      L D B M
      hLeftPar.1

  have hBM_DL :
      Geo.Parallel B M D L :=
    ParallelSymmetry
      Geo
      D L B M
      hDL_BM

  have hMB_DL :
      Geo.Parallel M B D L :=
    ParallelSwapFirstLine
      Geo
      B M D L
      hBM_DL

  have hMCBcol :
      Collinear Geo M C B :=
    PrimCollinearCycle
      Geo B M C hBMCcol

  have hMC_DL :
      Geo.Parallel M C D L :=
    collinear_parallel_trans
      Geo
      M C B
      D L
      hMC
      hMCBcol
      hMB_DL

  have hDL_MC :
      Geo.Parallel D L M C :=
    ParallelSymmetry
      Geo M C D L hMC_DL

  --------------------------------------------------------------------
  -- Parallel crossing order gives L-N-M, hence M-N-L.
  --------------------------------------------------------------------

  have hLNM :
      Geo.Between L N M :=
    hilbert_collinear_between_of_parallel
      Geo
      D L M C N
      hDL_MC
      hDNC
      hLMN

  have hMNL :
      Geo.Between M N L :=
    (HilbertOrder.between_incidence
      L N M hLNM).2.2.2.2

  exact
    ⟨N,
      hDNC,
      hMNL⟩


/--
Euclid II.11 -- reusable rectangle cut.

Exported reusable cut constructor for an arbitrary rectangle.

From

    IsRectangle B C E D
    B-M-C

construct L and N satisfying exactly the geometric cut package used
by rectangle_split and the current Book II APIs:

    D-L-E,
    D-N-C,
    M-N-L,
    L-D-B-M parallelogram,
    C-E-L-M parallelogram.
-/
private theorem proposition2_11_rectangle_cut_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C D E M : Geo.Point)
    (hRect : IsRectangle Geo B C E D)
    (hBMC : Geo.Between B M C) :
    exists L N : Geo.Point,
      Geo.Between D L E /\
      Geo.Between D N C /\
      Geo.Between M N L /\
      IsParallelogram Geo L D B M /\
      IsParallelogram Geo C E L M := by

  rcases
      proposition2_11_rectangle_cut_between
        Geo
        B C D E M
        hRect
        hBMC with
    ⟨L, hDLE, hLeftPar, hRightPar⟩

  rcases
      proposition2_11_diagonal_cut_intersection
        Geo
        B C D E M L
        hBMC
        hRect
        hLeftPar with
    ⟨N, hDNC, hMNL⟩

  exact
    ⟨L, N,
      hDLE,
      hDNC,
      hMNL,
      hLeftPar,
      hRightPar⟩

/--
Euclid II.11 -- existential II.6 wrapper.

Existential wrapper around Euclid II.6 for the II.11 substitution

    (A, B, C, D)_II6 = (D, A, E, F)_II11.

Input:

    E is the midpoint of DA,
    D-A-F.

All rectangles, squares, and cut diagrams required by the current
low-level API of II.6 are constructed internally.

Output:

    Square(AE) + Rect(DF,AF) = Square(EF).
-/
private theorem proposition2_11_II6_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (D A E F : Geo.Point)
    (hMidE : HilbertIsMidpoint Geo E D A)
    (hDAF : Geo.Between D A F) :
    exists
      SAE0 SAE1
      P0 P1 P2 P3
      SEF0 SEF1 : Geo.Point,
      IsSquare Geo A E SAE0 SAE1 /\
      IsRectangleContainedBy Geo
        P0 P1 P2 P3 D F A F /\
      IsSquare Geo E F SEF0 SEF1 /\
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A E SAE0 SAE1 +
         hilbertParallelogramTerm Geo P0 P1 P2 P3)
        (hilbertParallelogramTerm Geo E F SEF0 SEF1) := by

  --------------------------------------------------------------------
  -- Directed order D-E-A-F.
  --------------------------------------------------------------------

  have hDEA :
      Geo.Between D E A :=
    hMidE.1

  have hOrder :=
    hilbert_between_inner_trans
      Geo
      D E A F
      hDEA
      hDAF

  have hEAF :
      Geo.Between E A F :=
    hOrder.1

  have hDEF :
      Geo.Between D E F :=
    hOrder.2

  have hFAE :
      Geo.Between F A E :=
    (HilbertOrder.between_incidence
      E A F hEAF).2.2.2.2

  --------------------------------------------------------------------
  -- Nondegenerate segments used by the constructors.
  --------------------------------------------------------------------

  have hDEAdata :=
    HilbertOrder.between_incidence
      D E A hDEA

  have hDAFdata :=
    HilbertOrder.between_incidence
      D A F hDAF

  have hEAFdata :=
    HilbertOrder.between_incidence
      E A F hEAF

  have hDA : Ne D A :=
    hDEAdata.2.2.1

  have hDE : Ne D E :=
    hDEAdata.1

  have hEA : Ne E A :=
    hDEAdata.2.1

  have hAE : Ne A E :=
    hEA.symm

  have hDF : Ne D F :=
    hDAFdata.2.2.1

  have hAF : Ne A F :=
    hDAFdata.2.1

  have hEF : Ne E F :=
    hEAFdata.2.2.1

  have hFE : Ne F E :=
    hEF.symm

  --------------------------------------------------------------------
  -- The three squares used by II.6:
  --
  --   Square(AF) = Square(BD)_II6,
  --   Square(AE) = Square(BC)_II6,
  --   Square(EF) = Square(CD)_II6.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_46
        Geo A F hAF with
    ⟨SAF0, SAF1, hSqAF⟩

  rcases
      euclid_proposition_46
        Geo A E hAE with
    ⟨SAE0, SAE1, hSqAE⟩

  rcases
      euclid_proposition_46
        Geo E F hEF with
    ⟨SEF0, SEF1, hSqEF⟩

  --------------------------------------------------------------------
  -- Rect(DF,AF).
  --
  -- This concrete rectangle is simultaneously:
  --
  --   * the target rectangle in the conclusion,
  --   * the Rect(AD,BD) representative required by II.6,
  --   * the whole rectangle for the first II.3 cut at A.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        D F
        A F
        hDF with
    ⟨H2, E2, hDF_AF⟩

  rcases
      proposition2_11_rectangle_cut_exists
        Geo
        D F E2 H2 A
        hDF_AF.1
        hDAF with
    ⟨L2, X2,
      hE2L2H2,
      hE2X2F,
      hAX2L2,
      hLeftPar2,
      hRightPar2⟩

  --------------------------------------------------------------------
  -- Rect(DA,AF).
  --
  -- This is both the Rect(AB,BD) representative and the whole
  -- rectangle for the midpoint cut D-E-A.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        D A
        A F
        hDA with
    ⟨H3, E3, hDA_AF⟩

  rcases
      proposition2_11_rectangle_cut_exists
        Geo
        D A E3 H3 E
        hDA_AF.1
        hDEA with
    ⟨L3, X3,
      hE3L3H3,
      hE3X3A,
      hEX3L3,
      hLeftPar3,
      hRightPar3⟩

  --------------------------------------------------------------------
  -- Rect(DE,AF) and Rect(EA,AF), the two parts of Rect(DA,AF).
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        D E
        A F
        hDE with
    ⟨Y2, Y3, hDE_AF⟩

  rcases
      rectangle_contained_by_exists
        Geo
        E A
        A F
        hEA with
    ⟨Z2, Z3, hEA_AF⟩

  --------------------------------------------------------------------
  -- Cut Square(EF) at A.
  --
  -- The generic cut constructor expects an IsRectangle.  A square is
  -- a rectangle; for E-F-SEF0-SEF1 the required right angle is the
  -- square angle E-F-SEF0.
  --------------------------------------------------------------------

  have hRectEF :
      IsRectangle Geo E F SEF0 SEF1 :=
    ⟨hSqEF.1,
      hSqEF.2.2.2.2.2.1⟩

  rcases
      proposition2_11_rectangle_cut_exists
        Geo
        E F SEF1 SEF0 A
        hRectEF
        hEAF with
    ⟨L0, X0,
      hSEF1_L0_SEF0,
      hSEF1_X0_F,
      hAX0L0,
      hII4LeftPar,
      hII4RightPar⟩

  --------------------------------------------------------------------
  -- Arbitrary representatives required internally by II.4:
  --
  --   Rect(EF,EA),
  --   Rect(EF,AF).
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        E F
        E A
        hEF with
    ⟨J2, J3, hEF_EA⟩

  rcases
      rectangle_contained_by_exists
        Geo
        E F
        A F
        hEF with
    ⟨E4, D2, hEF_AF⟩

  --------------------------------------------------------------------
  -- Left II.3 decomposition inside II.4.
  --
  -- Whole rectangle: Rect(FE,AE), cut at A with F-A-E.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        F E
        A E
        hFE with
    ⟨E1, D1, hFE_AE⟩

  rcases
      proposition2_11_rectangle_cut_exists
        Geo
        F E D1 E1 A
        hFE_AE.1
        hFAE with
    ⟨L1, X1,
      hD1L1E1,
      hD1X1E,
      hAX1L1,
      hLeftLeftPar,
      hLeftRightPar⟩

  --------------------------------------------------------------------
  -- Right II.3 decomposition inside II.4.
  --
  -- Reuse Rect(EF,AF), cut at A with E-A-F.
  --------------------------------------------------------------------

  rcases
      proposition2_11_rectangle_cut_exists
        Geo
        E F D2 E4 A
        hEF_AF.1
        hEAF with
    ⟨L4, X4,
      hD2L4E4,
      hD2X4F,
      hAX4L4,
      hRightLeftPar,
      hRightRightPar⟩

  --------------------------------------------------------------------
  -- Apply the current public II.6 API with the substitution
  --
  --   A -> D
  --   B -> A
  --   C -> E
  --   D -> F.
  --------------------------------------------------------------------

  have hII6 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A E SAE0 SAE1 +
         hilbertParallelogramTerm Geo D F H2 E2)
        (hilbertParallelogramTerm Geo E F SEF0 SEF1) :=
    euclid_proposition_2_6
      Geo
      D A E F
      hMidE
      hDAF

      -- test 06, first II.3 cut
      E2 H2 L2 X2
      hDF_AF.1
      hDF_AF.2.2
      hE2L2H2
      hE2X2F
      hAX2L2
      hLeftPar2
      hRightPar2

      -- Square(AF)
      SAF0 SAF1
      hSqAF

      -- Rect(DF,AF)
      D F H2 E2
      hDF_AF

      -- Rect(DA,AF)
      D A H3 E3
      hDA_AF

      -- midpoint cut of Rect(DA,AF)
      E3 H3 L3 X3
      hDA_AF.1
      hDA_AF.2.2
      hE3L3H3
      hE3X3A
      hEX3L3
      hLeftPar3
      hRightPar3

      -- Rect(DE,AF)
      D E Y2 Y3
      hDE_AF

      -- Rect(EA,AF)
      E A Z2 Z3
      hEA_AF

      -- II.4 outer cut of Square(EF) at A
      SEF1 SEF0 L0 X0
      hSqEF
      hSEF1_L0_SEF0
      hSEF1_X0_F
      hAX0L0
      hII4LeftPar
      hII4RightPar

      -- Rect(EF,EA)
      E F J2 J3

      -- Rect(EF,AF)
      E F E4 D2

      hEF_EA
      hEF_AF

      -- left II.3 inside II.4
      D1 E1 L1 X1
      hFE_AE.1
      hFE_AE.2.2
      hD1L1E1
      hD1X1E
      hAX1L1
      hLeftLeftPar
      hLeftRightPar

      -- Square(AE)
      SAE0 SAE1
      hSqAE

      -- right II.3 inside II.4
      D2 E4 L4 X4
      hEF_AF.1
      hEF_AF.2.2
      hD2L4E4
      hD2X4F
      hAX4L4
      hRightLeftPar
      hRightRightPar

  exact
    ⟨SAE0, SAE1,
      D, F, H2, E2,
      SEF0, SEF1,
      hSqAE,
      hDF_AF,
      hSqEF,
      hII6⟩

/--
Common Notion 3 in the scissors calculus:

    R + P ~ec R + Q
    ----------------
          P ~ec Q.
-/
private theorem proposition2_11_common_notion_3
    (P Q R : HilbertScissorsTerm Geo)
    (hWhole :
      HilbertScissorsEquicomplementable Geo
        (R + P)
        (R + Q)) :
    HilbertScissorsEquicomplementable Geo P Q := by

  rcases hWhole with
    ⟨U, V, hUV, hWholeUV⟩

  refine
    ⟨R + U,
      R + V,
      ?_,
      ?_⟩

  · exact
      HilbertScissorsEq.add
        (Geo := Geo)
        (HilbertScissorsEq.refl
          (Geo := Geo) R)
        hUV

  · have hLeft :
        (R + P) + U = P + (R + U) := by
      ac_rfl

    have hRight :
        (R + Q) + V = Q + (R + V) := by
      ac_rfl

    rw [hLeft, hRight] at hWholeUV
    exact hWholeUV


/--
Euclid II.11 -- central equality.

Close the central equality

    Rect(DF,AF) ~ec Square(AB).

The two inputs are:

1. II.6, internally constructed by the II.6 wrapper:

       Square(AE) + Rect(DF,AF) = Square(EF).

2. I.47 in the right triangle E-A-B, together with EF ~= EB:

       Square(EF) ~ec Square(AE) + Square(AB).

After transport to common square representatives, Common Notion 3
cancels Square(AE).
-/
private theorem proposition2_11_central_equality
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D E F : Geo.Point)

    (hSquareAB : IsSquare Geo A B C D)
    (hMidE : HilbertIsMidpoint Geo E D A)
    (hDAF : Geo.Between D A F)

    (hEF_EB : Geo.Congruent E F E B)

    (hEABnc : Not (Collinear Geo E A B))
    (hRightEAB : HilbertRightAngle Geo E A B) :

    exists P0 P1 P2 P3 : Geo.Point,
      IsRectangleContainedBy Geo
        P0 P1 P2 P3 D F A F /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo P0 P1 P2 P3)
        (hilbertParallelogramTerm Geo A B C D) := by

  --------------------------------------------------------------------
  -- II.6:
  --
  --   Square(AE) + Rect(DF,AF) = Square(EF).
  --------------------------------------------------------------------

  rcases
      proposition2_11_II6_exists
        Geo
        D A E F
        hMidE
        hDAF with
    ⟨SAE0, SAE1,
      P0, P1, P2, P3,
      SEF0, SEF1,
      hSqAE,
      hDF_AF,
      hSqEF,
      hII6⟩

  --------------------------------------------------------------------
  -- I.47 in triangle A-E-B, right at A:
  --
  --   Square(EB) ~ec Square(AE) + Square(AB).
  --
  -- The correct I.47 substitution is
  --
  --   (A, B, C)_I47 = (A, E, B).
  --------------------------------------------------------------------

  have hAEBnc :
      Not (Collinear Geo A E B) := by
    intro h
    exact
      hEABnc
        (PrimCollinearSwap
          Geo A E B h)

  rcases
      euclid_proposition_47
        Geo
        A E B
        hAEBnc
        hRightEAB with
    ⟨QEB0, QEB1,
      QAE0, QAE1,
      QAB0, QAB1,
      hSqEB,
      hSqAE47,
      hSqAB47,
      hPyth⟩

  --------------------------------------------------------------------
  -- Transport the I.47 square on AE to the II.6 square on AE.
  --------------------------------------------------------------------

  have hAE_refl :
      Geo.Congruent A E A E :=
    hilbert_congruent_reflexive
      Geo A E

  have hSqAE47_to_AE :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A E QAE0 QAE1)
        (hilbertParallelogramTerm Geo A E SAE0 SAE1) :=
    hilbert_square_transport
      Geo
      A E QAE0 QAE1
      A E SAE0 SAE1
      hSqAE47
      hSqAE
      hAE_refl

  --------------------------------------------------------------------
  -- Transport the I.47 square on AB to the original square ABCD.
  --------------------------------------------------------------------

  have hAB_refl :
      Geo.Congruent A B A B :=
    hilbert_congruent_reflexive
      Geo A B

  have hSqAB47_to_AB :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B QAB1 QAB0)
        (hilbertParallelogramTerm Geo A B C D) :=
    hilbert_square_transport
      Geo
      A B QAB1 QAB0
      A B C D
      hSqAB47
      hSquareAB
      hAB_refl

  --------------------------------------------------------------------
  -- Therefore the two I.47 leg squares transport to the common
  -- target representatives:
  --
  --   Square(AE)_I47 + Square(AB)_I47
  --     ~ec
  --   Square(AE)_II6 + Square(AB)_target.
  --------------------------------------------------------------------

  have hLegsTransport :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A E QAE0 QAE1 +
         hilbertParallelogramTerm Geo A B QAB1 QAB0)
        (hilbertParallelogramTerm Geo A E SAE0 SAE1 +
         hilbertParallelogramTerm Geo A B C D) :=
    i47_aux_equicomplementable_add
      Geo
      hSqAE47_to_AE
      hSqAB47_to_AB

  have hSqEB_to_sum :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E B QEB1 QEB0)
        (hilbertParallelogramTerm Geo A E SAE0 SAE1 +
         hilbertParallelogramTerm Geo A B C D) :=
    equicomplementable_trans
      Geo
      hPyth
      hLegsTransport

  --------------------------------------------------------------------
  -- Transport Square(EF) to the I.47 square on EB using EF ~= EB.
  --------------------------------------------------------------------

  have hSqEF_to_EB :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E F SEF0 SEF1)
        (hilbertParallelogramTerm Geo E B QEB1 QEB0) :=
    hilbert_square_transport
      Geo
      E F SEF0 SEF1
      E B QEB1 QEB0
      hSqEF
      hSqEB
      hEF_EB

  have hSqEF_to_sum :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E F SEF0 SEF1)
        (hilbertParallelogramTerm Geo A E SAE0 SAE1 +
         hilbertParallelogramTerm Geo A B C D) :=
    equicomplementable_trans
      Geo
      hSqEF_to_EB
      hSqEB_to_sum

  --------------------------------------------------------------------
  -- Convert II.6 from exact scissors equality to equicomplementability:
  --
  --   Square(AE) + Rect(DF,AF)
  --     ~ec
  --   Square(EF).
  --------------------------------------------------------------------

  have hII6ec :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A E SAE0 SAE1 +
         hilbertParallelogramTerm Geo P0 P1 P2 P3)
        (hilbertParallelogramTerm Geo E F SEF0 SEF1) :=
    equicomplementable_of_scissorsEq
      Geo hII6

  have hWhole :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A E SAE0 SAE1 +
         hilbertParallelogramTerm Geo P0 P1 P2 P3)
        (hilbertParallelogramTerm Geo A E SAE0 SAE1 +
         hilbertParallelogramTerm Geo A B C D) :=
    equicomplementable_trans
      Geo
      hII6ec
      hSqEF_to_sum

  --------------------------------------------------------------------
  -- Common Notion 3: cancel Square(AE).
  --------------------------------------------------------------------

  have hCentral :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo P0 P1 P2 P3)
        (hilbertParallelogramTerm Geo A B C D) :=
    proposition2_11_common_notion_3
      Geo
      (hilbertParallelogramTerm Geo P0 P1 P2 P3)
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo A E SAE0 SAE1)
      hWhole

  exact
    ⟨P0, P1, P2, P3,
      hDF_AF,
      hCentral⟩

/--
Common Notion 3 in the scissors calculus.
-/
private theorem proposition2_11_common_notion_3_second
    (P Q R : HilbertScissorsTerm Geo)
    (hWhole :
      HilbertScissorsEquicomplementable Geo
        (R + P)
        (R + Q)) :
    HilbertScissorsEquicomplementable Geo P Q := by

  rcases hWhole with
    ⟨U, V, hUV, hWholeUV⟩

  refine
    ⟨R + U,
      R + V,
      ?_,
      ?_⟩

  · exact
      HilbertScissorsEq.add
        (Geo := Geo)
        (HilbertScissorsEq.refl
          (Geo := Geo) R)
        hUV

  · have hLeft :
        (R + P) + U = P + (R + U) := by
      ac_rfl

    have hRight :
        (R + Q) + V = Q + (R + V) := by
      ac_rfl

    rw [hLeft, hRight] at hWholeUV
    exact hWholeUV


/--
Euclid II.11 -- second subtraction block.

Second subtraction block.

Assume the II.11 construction data

    D-A-F,
    A-H-B,
    AF ~= AH,

together with the square ABCD, the midpoint E of DA, and the data
needed by the already proved central equality.

Then:

1. II.3 gives

       Rect(DF,AF) = Rect(DA,AF) + Sq(AF).

2. II.2 gives

       Rect(AB,AH) + Rect(AB,HB) = Sq(AB).

3. Rectangle transport gives

       Rect(DA,AF) = Rect(AB,AH).

4. Common Notion 3 gives

       Sq(AF) ~ec Rect(AB,HB).
-/
private theorem proposition2_11_second_subtraction
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D E F H : Geo.Point)

    (hSquareAB : IsSquare Geo A B C D)
    (hMidE : HilbertIsMidpoint Geo E D A)
    (hDAF : Geo.Between D A F)

    (hEF_EB : Geo.Congruent E F E B)
    (hEABnc : Not (Collinear Geo E A B))
    (hRightEAB : HilbertRightAngle Geo E A B)

    (hAHB : Geo.Between A H B)
    (hAF_AH : Geo.Congruent A F A H) :

    exists
      SAF0 SAF1
      U0 U1 U2 U3 : Geo.Point,
      IsSquare Geo A F SAF0 SAF1 /\
      IsRectangleContainedBy Geo
        U0 U1 U2 U3 A B H B /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A F SAF0 SAF1)
        (hilbertParallelogramTerm Geo U0 U1 U2 U3) := by

  --------------------------------------------------------------------
  -- Central equality from the central equality:
  --
  --   Rect(DF,AF) ~ec Sq(AB).
  --------------------------------------------------------------------

  rcases
      proposition2_11_central_equality
        Geo
        A B C D E F
        hSquareAB
        hMidE
        hDAF
        hEF_EB
        hEABnc
        hRightEAB with
    ⟨P0, P1, P2, P3,
      hDF_AF,
      hCentral⟩

  --------------------------------------------------------------------
  -- Basic order/nondegeneracy.
  --------------------------------------------------------------------

  have hDAFdata :=
    HilbertOrder.between_incidence
      D A F hDAF

  have hDF : Ne D F :=
    hDAFdata.2.2.1

  have hAF : Ne A F :=
    hDAFdata.2.1

  have hAHBdata :=
    HilbertOrder.between_incidence
      A H B hAHB

  have hAB : Ne A B :=
    hAHBdata.2.2.1

  --------------------------------------------------------------------
  -- Square on AF.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_46
        Geo A F hAF with
    ⟨SAF0, SAF1, hSqAF⟩

  --------------------------------------------------------------------
  -- II.3:
  --
  --   Rect(DF,AF) = Rect(DA,AF) + Sq(AF).
  --
  -- The whole representative P comes from the central equality.
  -- A separate concrete rectangle on DF x AF supplies the cut diagram.
  --------------------------------------------------------------------

  rcases
      rectangle_contained_by_exists
        Geo
        D F
        A F
        hDF with
    ⟨RF2, RF3, hConcreteDF_AF⟩

  rcases
      proposition2_11_rectangle_cut_exists
        Geo
        D F RF3 RF2 A
        hConcreteDF_AF.1
        hDAF with
    ⟨L3, X3,
      hRF3L3RF2,
      hRF3X3F,
      hAX3L3,
      hII3LeftPar,
      hII3RightPar⟩

  rcases
      rectangle_contained_by_exists
        Geo
        D A
        A F
        hDAFdata.1 with
    ⟨R2, R3, hDA_AF⟩

  have hII3 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo P0 P1 P2 P3)
        (hilbertParallelogramTerm Geo D A R2 R3 +
         hilbertParallelogramTerm Geo A F SAF0 SAF1) :=
    euclid_proposition_2_3
      Geo
      D F RF3 RF2 L3 A X3
      hConcreteDF_AF.1
      hConcreteDF_AF.2.2
      hDAF
      hRF3L3RF2
      hRF3X3F
      hAX3L3
      hII3LeftPar
      hII3RightPar
      SAF0 SAF1
      hSqAF
      P0 P1 P2 P3
      D A R2 R3
      hDF_AF
      hDA_AF

  --------------------------------------------------------------------
  -- II.2:
  --
  --   Rect(AB,AH) + Rect(AB,HB) = Sq(AB).
  --------------------------------------------------------------------

  have hRectAB :
      IsRectangle Geo A B C D :=
    ⟨hSquareAB.1,
      hSquareAB.2.2.2.2.2.1⟩

  rcases
      proposition2_11_rectangle_cut_exists
        Geo
        A B D C H
        hRectAB
        hAHB with
    ⟨L2, X2,
      hDL2C,
      hDX2B,
      hHX2L2,
      hII2LeftPar,
      hII2RightPar⟩

  rcases
      rectangle_contained_by_exists
        Geo
        A B
        A H
        hAB with
    ⟨T2, T3, hAB_AH⟩

  rcases
      rectangle_contained_by_exists
        Geo
        A B
        H B
        hAB with
    ⟨U2, U3, hAB_HB⟩

  have hII2 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B T2 T3 +
         hilbertParallelogramTerm Geo A B U2 U3)
        (hilbertParallelogramTerm Geo A B C D) :=
    euclid_proposition_2_2
      Geo
      A B D C L2 H X2
      hSquareAB
      hAHB
      hDL2C
      hDX2B
      hHX2L2
      hII2LeftPar
      hII2RightPar
      A B T2 T3
      A B U2 U3
      hAB_AH
      hAB_HB

  --------------------------------------------------------------------
  -- Rect(DA,AF) = Rect(AB,AH).
  --------------------------------------------------------------------

  have hBC_DA :
      Geo.Congruent B C D A :=
    (ParallelogramOppositeSidesCongruent
      Geo A B C D hSquareAB.1).2

  have hAB_DA :
      Geo.Congruent A B D A :=
    hilbert_congruent_transitivity
      Geo
      A B
      B C
      D A
      hSquareAB.2.1
      hBC_DA

  have hDA_AB :
      Geo.Congruent D A A B :=
    hilbert_congruent_symmetry
      Geo A B D A hAB_DA

  have hAH_BT2 :
      Geo.Congruent A H B T2 :=
    hilbert_congruent_symmetry
      Geo B T2 A H
      hAB_AH.2.2

  have hAR2_AH :
      Geo.Congruent A R2 A H :=
    hilbert_congruent_transitivity
      Geo
      A R2
      A F
      A H
      hDA_AF.2.2
      hAF_AH

  have hAR2_BT2 :
      Geo.Congruent A R2 B T2 :=
    hilbert_congruent_transitivity
      Geo
      A R2
      A H
      B T2
      hAR2_AH
      hAH_BT2

  have hCommon :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo D A R2 R3)
        (hilbertParallelogramTerm Geo A B T2 T3) :=
    rectangle_transport_scissorsEq
      Geo
      D A R2 R3
      A B T2 T3
      hDA_AF.1
      hAB_AH.1
      hDA_AB
      hAR2_BT2

  --------------------------------------------------------------------
  -- Assemble:
  --
  --   R + S ~ec P ~ec Q ~ec T + U ~sc R + U,
  --
  -- where
  --
  --   R = Rect(DA,AF),
  --   S = Sq(AF),
  --   P = Rect(DF,AF),
  --   Q = Sq(AB),
  --   T = Rect(AB,AH),
  --   U = Rect(AB,HB).
  --------------------------------------------------------------------

  have hRS_P :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D A R2 R3 +
         hilbertParallelogramTerm Geo A F SAF0 SAF1)
        (hilbertParallelogramTerm Geo P0 P1 P2 P3) :=
    equicomplementable_of_scissorsEq
      Geo
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hII3)

  have hRS_Q :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D A R2 R3 +
         hilbertParallelogramTerm Geo A F SAF0 SAF1)
        (hilbertParallelogramTerm Geo A B C D) :=
    equicomplementable_trans
      Geo
      hRS_P
      hCentral

  have hQ_TU :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A B T2 T3 +
         hilbertParallelogramTerm Geo A B U2 U3) :=
    equicomplementable_of_scissorsEq
      Geo
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hII2)

  have hRS_TU :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D A R2 R3 +
         hilbertParallelogramTerm Geo A F SAF0 SAF1)
        (hilbertParallelogramTerm Geo A B T2 T3 +
         hilbertParallelogramTerm Geo A B U2 U3) :=
    equicomplementable_trans
      Geo
      hRS_Q
      hQ_TU

  have hTU_RU :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B T2 T3 +
         hilbertParallelogramTerm Geo A B U2 U3)
        (hilbertParallelogramTerm Geo D A R2 R3 +
         hilbertParallelogramTerm Geo A B U2 U3) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hCommon)
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertParallelogramTerm Geo A B U2 U3))

  have hTU_RU_ec :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B T2 T3 +
         hilbertParallelogramTerm Geo A B U2 U3)
        (hilbertParallelogramTerm Geo D A R2 R3 +
         hilbertParallelogramTerm Geo A B U2 U3) :=
    equicomplementable_of_scissorsEq
      Geo hTU_RU

  have hRS_RU :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D A R2 R3 +
         hilbertParallelogramTerm Geo A F SAF0 SAF1)
        (hilbertParallelogramTerm Geo D A R2 R3 +
         hilbertParallelogramTerm Geo A B U2 U3) :=
    equicomplementable_trans
      Geo
      hRS_TU
      hTU_RU_ec

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A F SAF0 SAF1)
        (hilbertParallelogramTerm Geo A B U2 U3) :=
    proposition2_11_common_notion_3_second
      Geo
      (hilbertParallelogramTerm Geo A F SAF0 SAF1)
      (hilbertParallelogramTerm Geo A B U2 U3)
      (hilbertParallelogramTerm Geo D A R2 R3)
      hRS_RU

  exact
    ⟨SAF0, SAF1,
      A, B, U2, U3,
      hSqAF,
      hAB_HB,
      hFinal⟩

/--
Euclid II.11 -- final square transport.

Final transport step.

From the second subtraction block:

    Square(AF) ~ec Rect(AB,HB),

and from the construction:

    AF ~= AH,

transport the square on AF to a square on AH and conclude

    Rect(AB,HB) ~ec Square(AH).
-/
private theorem proposition2_11_final_transport
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]

    (A B C D E F H : Geo.Point)

    (hSquareAB : IsSquare Geo A B C D)
    (hMidE : HilbertIsMidpoint Geo E D A)
    (hDAF : Geo.Between D A F)

    (hEF_EB : Geo.Congruent E F E B)
    (hEABnc : Not (Collinear Geo E A B))
    (hRightEAB : HilbertRightAngle Geo E A B)

    (hAHB : Geo.Between A H B)
    (hAF_AH : Geo.Congruent A F A H) :

    exists
      R0 R1 R2 R3
      Q0 Q1 : Geo.Point,
      IsRectangleContainedBy Geo
        R0 R1 R2 R3 A B H B /\
      IsSquare Geo A H Q0 Q1 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo R0 R1 R2 R3)
        (hilbertParallelogramTerm Geo A H Q0 Q1) := by

  --------------------------------------------------------------------
  -- the second subtraction block:
  --
  --   Square(AF) ~ec Rect(AB,HB).
  --------------------------------------------------------------------

  rcases
      proposition2_11_second_subtraction
        Geo
        A B C D E F H
        hSquareAB
        hMidE
        hDAF
        hEF_EB
        hEABnc
        hRightEAB
        hAHB
        hAF_AH with
    ⟨SAF0, SAF1,
      R0, R1, R2, R3,
      hSqAF,
      hAB_HB,
      hSqAF_Rect⟩

  --------------------------------------------------------------------
  -- Construct the target square on AH.
  --------------------------------------------------------------------

  have hAH : Ne A H :=
    (HilbertOrder.between_incidence
      A H B hAHB).1

  rcases
      euclid_proposition_46
        Geo A H hAH with
    ⟨Q0, Q1, hSqAH⟩

  --------------------------------------------------------------------
  -- Transport Square(AF) to Square(AH).
  --------------------------------------------------------------------

  have hSqAF_SqAH :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A F SAF0 SAF1)
        (hilbertParallelogramTerm Geo A H Q0 Q1) :=
    hilbert_square_transport
      Geo
      A F SAF0 SAF1
      A H Q0 Q1
      hSqAF
      hSqAH
      hAF_AH

  --------------------------------------------------------------------
  -- Reverse the second subtraction block and compose:
  --
  --   Rect(AB,HB) ~ec Square(AF) ~ec Square(AH).
  --------------------------------------------------------------------

  have hRect_SqAF :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo R0 R1 R2 R3)
        (hilbertParallelogramTerm Geo A F SAF0 SAF1) :=
    equicomplementable_symm
      Geo
      hSqAF_Rect

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo R0 R1 R2 R3)
        (hilbertParallelogramTerm Geo A H Q0 Q1) :=
    equicomplementable_trans
      Geo
      hRect_SqAF
      hSqAF_SqAH

  exact
    ⟨R0, R1, R2, R3,
      Q0, Q1,
      hAB_HB,
      hSqAH,
      hFinal⟩

/--
Euclid II.11 -- test 03.

Starting from the square A-B-C-D and the midpoint E of D-A,
prove the hidden order fact

    EA < EB.

The proof is synthetic:

1. angle EAB is right;
2. extend EA beyond A to X;
3. I.16 in triangle B-E-A gives

       angle EBA < angle BAX;

4. because E-A-X, angle BAX is the opposite extension of
   the right angle EAB, hence it is congruent to EAB;
5. transport the angle inequality;
6. I.19 gives EA < EB.
-/
private theorem proposition2_11_EA_lt_EB_aux
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    exists C D E : Geo.Point,
      IsSquare Geo A B C D /\
      HilbertIsMidpoint Geo E D A /\
      Geo.Between D E A /\
      Geo.Congruent D A A B /\
      Not (Collinear Geo E A B) /\
      HilbertRightAngle Geo E A B /\
      HilbertSegmentLess Geo E A E B := by

  rcases
      euclid_proposition_46
        Geo A B hAB with
    ⟨C, D, hSquare⟩

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo A B C D hSquare.1

  have hDABnc :
      Not (Collinear Geo D A B) :=
    hNC.1

  have hDA : Ne D A :=
    hilbert_noncollinear_ne_first
      Geo D A B hDABnc

  rcases
      euclid_proposition_10
        Geo D A hDA with
    ⟨E, hMidE⟩

  have hDEA :
      Geo.Between D E A :=
    hMidE.1

  have hDEAdata :=
    HilbertOrder.between_incidence
      D E A hDEA

  have hEA : Ne E A :=
    hDEAdata.2.1

  have hAE : Ne A E :=
    hEA.symm

  --------------------------------------------------------------------
  -- DA ~= AB.
  --------------------------------------------------------------------

  have hAB_BC :
      Geo.Congruent A B B C :=
    hSquare.2.1

  have hOpp :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hSquare.1

  have hBC_DA :
      Geo.Congruent B C D A :=
    hOpp.2

  have hAB_DA :
      Geo.Congruent A B D A :=
    hilbert_congruent_transitivity
      Geo
      A B
      B C
      D A
      hAB_BC
      hBC_DA

  have hDA_AB :
      Geo.Congruent D A A B :=
    hilbert_congruent_symmetry
      Geo A B D A hAB_DA

  --------------------------------------------------------------------
  -- E,A,B is noncollinear.
  --------------------------------------------------------------------

  have hDEAcol :
      Collinear Geo D E A :=
    hDEAdata.2.2.2.1

  have hDAEcol :
      Collinear Geo D A E :=
    PrimCollinearRotate
      Geo D E A hDEAcol

  have hEABnc :
      Not (Collinear Geo E A B) := by
    intro hEAB

    have hAEB :
        Collinear Geo A E B :=
      PrimCollinearSwap
        Geo E A B hEAB

    have hDAB :
        Collinear Geo D A B :=
      hilbert_primCollinear_trans
        Geo
        D A E B
        hAE
        hDAEcol
        hAEB

    exact hDABnc hDAB

  --------------------------------------------------------------------
  -- angle EAB is right.
  --------------------------------------------------------------------

  have hAED :
      Geo.Between A E D :=
    hDEAdata.2.2.2.2

  have hRayAED :
      HilbertSameRay Geo A E D :=
    hilbert_sameRay_of_between
      Geo A E D hAED

  have hRayADE :
      HilbertSameRay Geo A D E :=
    hilbert_sameRay_symm
      Geo A E D hRayAED

  have hAngleEq :
      Geo.Angle D A B =
      Geo.Angle E A B :=
    hilbert_angle_eq_of_sameRay_first
      Geo A D E B hRayADE

  have hDABrefl :
      Geo.AngleCongruent D A B D A B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      D A B
      hDABnc

  have hDAB_EAB :
      Geo.AngleCongruent D A B E A B := by
    unfold Geometry.Geo.AngleCongruent
      at hDABrefl ⊢
    rw [← hAngleEq]
    exact hDABrefl

  have hRightDAB :
      HilbertRightAngle Geo D A B :=
    hSquare.2.2.2.2.1

  have hRightEAB :
      HilbertRightAngle Geo E A B :=
    hilbert_right_angle_transport
      Geo
      D A B
      E A B
      hDABnc
      hEABnc
      hRightDAB
      hDAB_EAB

  --------------------------------------------------------------------
  -- Extend EA beyond A:
  --
  --     E --- A --- X.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        E A hEA with
    ⟨X, hEAX⟩

  --------------------------------------------------------------------
  -- Triangle B-E-A is nondegenerate.
  --------------------------------------------------------------------

  have hBEAnc :
      Not (Collinear Geo B E A) := by
    intro hBEA
    exact
      hEABnc
        (PrimCollinearCycle
          Geo B E A hBEA)

  --------------------------------------------------------------------
  -- I.16:
  --
  --     angle EBA < angle BAX.
  --------------------------------------------------------------------

  have hEBA_lt_BAX :
      HilbertAngleLess Geo E B A B A X :=
    euclid_proposition_16_first
      Geo
      B E A X
      hBEAnc
      hEAX

  --------------------------------------------------------------------
  -- Since E-A-X, BAX is the opposite extension of the right
  -- angle EAB.
  --------------------------------------------------------------------

  have hEAB_BAX :
      Geo.AngleCongruent E A B B A X :=
    hilbert_right_angle_opposite_extension
      Geo
      E A B X
      hEABnc
      hRightEAB
      hEAX

  have hBAX_EAB :
      Geo.AngleCongruent B A X E A B :=
    Geo.angle_congruent_symmetry
      E A B
      B A X
      hEAB_BAX

  --------------------------------------------------------------------
  -- Replace the exterior right angle BAX by EAB.
  --------------------------------------------------------------------

  have hEBA_lt_EAB :
      HilbertAngleLess Geo E B A E A B :=
    hilbert_angleLess_transport_right
      Geo
      E B A
      B A X
      E A B
      hEBA_lt_BAX
      hEABnc
      hBAX_EAB

  --------------------------------------------------------------------
  -- I.19 in triangle E-A-B:
  --
  --     angle EBA < angle EAB
  --
  -- implies
  --
  --     EA < EB.
  --------------------------------------------------------------------

  have hEA_lt_EB :
      HilbertSegmentLess Geo E A E B :=
    euclid_proposition_19
      Geo
      E A B
      hEABnc
      hEBA_lt_EAB

  exact
    ⟨C, D, E,
      hSquare,
      hMidE,
      hDEA,
      hDA_AB,
      hEABnc,
      hRightEAB,
      hEA_lt_EB⟩


/--
Euclid II.11 -- test 04.

Construct the source point F on ray EA such that

    EF ~= EB.

The strict inequality EA < EB proved in the auxiliary lemma forces
the order

    E --- A --- F.

Together with D-E-A this yields the four-point order

    D --- E --- A --- F.
-/
private theorem proposition2_11_construct_F_aux
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    exists C D E F : Geo.Point,
      IsSquare Geo A B C D /\
      HilbertIsMidpoint Geo E D A /\
      Geo.Between D E A /\
      Geo.Between E A F /\
      Geo.Between D E F /\
      Geo.Congruent E F E B /\
      HilbertSegmentLess Geo E A E B /\
      Not (Collinear Geo E A B) /\
      HilbertRightAngle Geo E A B := by

  rcases
      proposition2_11_EA_lt_EB_aux
        Geo A B hAB with
    ⟨C, D, E,
      hSquare,
      hMidE,
      hDEA,
      _hDA_AB,
      hEABnc,
      hRightEAB,
      hEA_lt_EB⟩

  have hDEAdata :=
    HilbertOrder.between_incidence
      D E A hDEA

  have hEA : Ne E A :=
    hDEAdata.2.1

  --------------------------------------------------------------------
  -- Hilbert III.1 / Euclid I.3:
  -- lay off EB on ray EA.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        E B
        E A
        hEA with
    ⟨F, hRayEAF, hEF_EB⟩

  have hEB_EF :
      Geo.Congruent E B E F :=
    hilbert_congruent_symmetry
      Geo E F E B hEF_EB

  --------------------------------------------------------------------
  -- Transport EA < EB through EB ~= EF:
  --
  --     EA < EF.
  --------------------------------------------------------------------

  have hEA_lt_EF :
      HilbertSegmentLess Geo E A E F :=
    hilbert_segmentLess_congruent_right
      Geo
      E A
      E B
      E F
      hEA_lt_EB
      hEB_EF

  --------------------------------------------------------------------
  -- Distinctness needed for order trichotomy.
  --------------------------------------------------------------------

  have hEF : Ne E F :=
    hRayEAF.2.1.symm

  have hAF : Ne A F := by
    intro hAF
    subst F

    have hEA_not_EA :
        Not (Geo.Congruent E A E A) :=
      hilbert_segmentLess_not_congruent
        Geo E A E A hEA_lt_EF

    exact
      hEA_not_EA
        (hilbert_congruent_reflexive
          Geo E A)

  have hEAFcol :
      Collinear Geo E A F :=
    hRayEAF.2.2.1

  --------------------------------------------------------------------
  -- Among E,A,F exactly one point lies between the other two.
  --
  -- SameRay rules out A-E-F.
  -- EA < EF rules out E-F-A.
  -- Therefore E-A-F.
  --------------------------------------------------------------------

  have hEAF :
      Geo.Between E A F := by

    rcases
        hilbert_between_trichotomy
          Geo
          E A F
          hEA
          hAF
          hEF
          hEAFcol with
      hEAF_order | hAEF_order | hEFA_order

    · exact hEAF_order

    · exact
        False.elim
          (hRayEAF.2.2.2 hAEF_order)

    ·
      have hEF_lt_EA :
          HilbertSegmentLess Geo E F E A :=
        hilbert_segmentLess_of_between
          Geo E F A hEFA_order

      exact
        False.elim
          ((hilbert_segmentLess_asymm
              Geo E A E F hEA_lt_EF)
            hEF_lt_EA)

  --------------------------------------------------------------------
  -- Combine D-E-A and E-A-F.
  --------------------------------------------------------------------

  have hOrder :=
    hilbert_between_outer_trans
      Geo
      D E A F
      hDEA
      hEAF

  have hDEF :
      Geo.Between D E F :=
    hOrder.2

  exact
    ⟨C, D, E, F,
      hSquare,
      hMidE,
      hDEA,
      hEAF,
      hDEF,
      hEF_EB,
      hEA_lt_EB,
      hEABnc,
      hRightEAB⟩


/--
Euclid II.11 -- test 05.

From the source configuration

    D --- E --- A --- F

with EF ~= EB, prove

    AF < AB.

Synthetic proof:

1. I.20 in triangle EAB gives a point T with

       E --- A --- T,
       AT ~= AB,
       EB < ET;

2. transport EB < ET through EF ~= EB, obtaining EF < ET;
3. unpack strict comparison to a point P on ET with EP ~= EF;
4. uniqueness of segment construction on ray EA identifies P with F;
5. hence E-F-T and, together with E-A-F, obtain A-F-T;
6. therefore AF < AT, and AT ~= AB gives AF < AB.
-/
private theorem proposition2_11_AF_lt_AB_aux
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    exists C D E F : Geo.Point,
      IsSquare Geo A B C D /\
      HilbertIsMidpoint Geo E D A /\
      Geo.Between D E A /\
      Geo.Between E A F /\
      Geo.Between D E F /\
      Geo.Congruent E F E B /\
      HilbertSegmentLess Geo E A E B /\
      HilbertSegmentLess Geo A F A B /\
      Not (Collinear Geo E A B) /\
      HilbertRightAngle Geo E A B := by

  rcases
      proposition2_11_construct_F_aux
        Geo A B hAB with
    ⟨C, D, E, F,
      hSquare,
      hMidE,
      hDEA,
      hEAF,
      hDEF,
      hEF_EB,
      hEA_lt_EB,
      hEABnc,
      hRightEAB⟩

  --------------------------------------------------------------------
  -- I.20 in triangle E-A-B.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_20
        Geo
        A E B
        (by
          intro hAEB
          exact
            hEABnc
              (PrimCollinearSwap
                Geo A E B hAEB)) with
    ⟨T, hEAT, hAT_AB, hEB_lt_ET⟩

  --------------------------------------------------------------------
  -- EF ~= EB, so I.20 gives EF < ET.
  --------------------------------------------------------------------

  have hEF_lt_ET :
      HilbertSegmentLess Geo E F E T :=
    hilbert_segmentLess_congruent_left
      Geo
      E B
      E F
      E T
      hEB_lt_ET
      hEF_EB

  --------------------------------------------------------------------
  -- Unpack EF < ET:
  --
  --     E --- P --- T
  --     EF ~= EP.
  --------------------------------------------------------------------

  rcases hEF_lt_ET with
    ⟨P, hEPT, hEF_EP⟩

  have hEP_EF :
      Geo.Congruent E P E F :=
    hilbert_congruent_symmetry
      Geo E F E P hEF_EP

  have hEP_EB :
      Geo.Congruent E P E B :=
    hilbert_congruent_transitivity
      Geo
      E P
      E F
      E B
      hEP_EF
      hEF_EB

  --------------------------------------------------------------------
  -- F and P lie on the same prescribed ray EA.
  --------------------------------------------------------------------

  have hRayEAF :
      HilbertSameRay Geo E A F :=
    hilbert_sameRay_of_between
      Geo E A F hEAF

  have hRayEAT :
      HilbertSameRay Geo E A T :=
    hilbert_sameRay_of_between
      Geo E A T hEAT

  have hRayETA :
      HilbertSameRay Geo E T A :=
    hilbert_sameRay_symm
      Geo E A T hRayEAT

  have hRayEPT :
      HilbertSameRay Geo E P T :=
    hilbert_sameRay_of_between
      Geo E P T hEPT

  have hRayETP :
      HilbertSameRay Geo E T P :=
    hilbert_sameRay_symm
      Geo E P T hRayEPT

  have hRayEAP :
      HilbertSameRay Geo E A P :=
    hilbert_sameRay_of_common
      Geo
      E T A P
      hRayETA
      hRayETP

  --------------------------------------------------------------------
  -- Both F and P are the unique point on ray EA whose distance
  -- from E is congruent to EB.
  --------------------------------------------------------------------

  have hFP : F = P :=
    hilbert_segment_construction_unique
      Geo
      E B
      E A
      F P
      hRayEAF
      hRayEAP
      hEF_EB
      hEP_EB

  subst P

  have hEFT :
      Geo.Between E F T :=
    hEPT

  --------------------------------------------------------------------
  -- E-A-F and E-F-T imply A-F-T.
  --------------------------------------------------------------------

  have hAFT :
      Geo.Between A F T :=
    (hilbert_between_inner_trans
      Geo
      E A F T
      hEAF
      hEFT).1

  have hAF_lt_AT :
      HilbertSegmentLess Geo A F A T :=
    hilbert_segmentLess_of_between
      Geo A F T hAFT

  --------------------------------------------------------------------
  -- Transport AT to AB.
  --------------------------------------------------------------------

  have hAF_lt_AB :
      HilbertSegmentLess Geo A F A B :=
    hilbert_segmentLess_congruent_right
      Geo
      A F
      A T
      A B
      hAF_lt_AT
      hAT_AB

  exact
    ⟨C, D, E, F,
      hSquare,
      hMidE,
      hDEA,
      hEAF,
      hDEF,
      hEF_EB,
      hEA_lt_EB,
      hAF_lt_AB,
      hEABnc,
      hRightEAB⟩


/--
Euclid II.11 -- test 06.

Construct the actual cut point H on AB.

From test 05 we already know

    AF < AB.

By the definition of HilbertSegmentLess there is a point H such that

    A --- H --- B
    AF ~= AH.

This is the geometric cut required by Euclid II.11.
-/
private theorem proposition2_11_construct_H
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    exists C D E F H : Geo.Point,
      IsSquare Geo A B C D /\
      HilbertIsMidpoint Geo E D A /\
      Geo.Between D E A /\
      Geo.Between E A F /\
      Geo.Between D E F /\
      Geo.Congruent E F E B /\
      HilbertSegmentLess Geo E A E B /\
      HilbertSegmentLess Geo A F A B /\
      Geo.Between A H B /\
      Geo.Congruent A F A H /\
      Not (Collinear Geo E A B) /\
      HilbertRightAngle Geo E A B := by

  rcases
      proposition2_11_AF_lt_AB_aux
        Geo A B hAB with
    ⟨C, D, E, F,
      hSquare,
      hMidE,
      hDEA,
      hEAF,
      hDEF,
      hEF_EB,
      hEA_lt_EB,
      hAF_lt_AB,
      hEABnc,
      hRightEAB⟩

  --------------------------------------------------------------------
  -- Unpack AF < AB.
  --
  -- By definition:
  --
  --     AF < AB
  --
  -- means that there exists H with
  --
  --     A-H-B
  --     AF ~= AH.
  --------------------------------------------------------------------

  rcases hAF_lt_AB with
    ⟨H, hAHB, hAF_AH⟩

  exact
    ⟨C, D, E, F, H,
      hSquare,
      hMidE,
      hDEA,
      hEAF,
      hDEF,
      hEF_EB,
      hEA_lt_EB,
      ⟨H, hAHB, hAF_AH⟩,
      hAHB,
      hAF_AH,
      hEABnc,
      hRightEAB⟩


/--
Euclid II.11 -- full construction and assembly.

Full existential assembly from the proposition's natural input:

    A != B.

The construction part is exactly the already clean the construction block chain.
The content equality is exactly the already clean the final transport block chain.

Conclusion:

there is an interior point H of AB such that the rectangle contained
by AB and HB is equicomplementable with the square on AH.
-/
theorem euclid_proposition_2_11
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    exists
      H
      R0 R1 R2 R3
      Q0 Q1 : Geo.Point,
      Geo.Between A H B /\
      IsRectangleContainedBy Geo
        R0 R1 R2 R3 A B H B /\
      IsSquare Geo A H Q0 Q1 /\
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo R0 R1 R2 R3)
        (hilbertParallelogramTerm Geo A H Q0 Q1) := by

  --------------------------------------------------------------------
  -- Construction layer: the construction block.
  --------------------------------------------------------------------

  rcases
      proposition2_11_construct_H
        Geo A B hAB with
    ⟨C, D, E, F, H,
      hSquareAB,
      hMidE,
      hDEA,
      hEAF,
      _hDEF,
      hEF_EB,
      _hEA_lt_EB,
      _hAF_lt_AB,
      hAHB,
      hAF_AH,
      hEABnc,
      hRightEAB⟩

  --------------------------------------------------------------------
  -- Combine D-E-A and E-A-F:
  --
  --     D --- E --- A --- F
  --
  -- gives
  --
  --     D --- A --- F.
  --------------------------------------------------------------------

  have hDAF :
      Geo.Between D A F :=
    (hilbert_between_outer_trans
      Geo
      D E A F
      hDEA
      hEAF).1

  --------------------------------------------------------------------
  -- Content layer: the final transport block.
  --------------------------------------------------------------------

  rcases
      proposition2_11_final_transport
        Geo
        A B C D E F H
        hSquareAB
        hMidE
        hDAF
        hEF_EB
        hEABnc
        hRightEAB
        hAHB
        hAF_AH with
    ⟨R0, R1, R2, R3,
      Q0, Q1,
      hAB_HB,
      hSqAH,
      hFinal⟩

  exact
    ⟨H,
      R0, R1, R2, R3,
      Q0, Q1,
      hAHB,
      hAB_HB,
      hSqAH,
      hFinal⟩

end Geometry

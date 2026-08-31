import CGJteamLab.Proposition47

namespace Geometry

universe u
variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Squares on congruent segments.
--
-- Proposition-independent scissors transport for squares.
------------------------------------------------------------------------

/--
Squares erected on congruent segments are equicomplementable.

This is a proposition-independent scissors lemma.  It is proved here
locally so that Euclid II.9 does not depend on the later Proposition I.48
module merely for a helper theorem.
-/
theorem hilbert_square_transport
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D A' B' C' D' : Geo.Point)
    (hSquare : IsSquare Geo A B C D)
    (hSquare' : IsSquare Geo A' B' C' D')
    (hCong : Geo.Congruent A B A' B') :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo A' B' C' D') := by

  --------------------------------------------------------------------
  -- All four corresponding sides are congruent.
  --------------------------------------------------------------------

  have hBC :
      Geo.Congruent B C B' C' :=
    hilbert_congruent_transitivity
      Geo B C A' B' B' C'
      (hilbert_congruent_transitivity
        Geo B C A B A' B'
        (hilbert_congruent_symmetry
          Geo A B B C hSquare.2.1)
        hCong)
      hSquare'.2.1

  have hCD :
      Geo.Congruent C D C' D' :=
    hilbert_congruent_transitivity
      Geo C D B' C' C' D'
      (hilbert_congruent_transitivity
        Geo C D B C B' C'
        (hilbert_congruent_symmetry
          Geo B C C D hSquare.2.2.1)
        hBC)
      hSquare'.2.2.1

  have hDA :
      Geo.Congruent D A D' A' :=
    hilbert_congruent_transitivity
      Geo D A C' D' D' A'
      (hilbert_congruent_transitivity
        Geo D A C D C' D'
        (hilbert_congruent_symmetry
          Geo C D D A hSquare.2.2.2.1)
        hCD)
      hSquare'.2.2.2.1

  have hAD :
      Geo.Congruent A D A' D' :=
    CongruentReverseBoth
      Geo D A D' A' hDA

  --------------------------------------------------------------------
  -- Nondegeneracy.
  --------------------------------------------------------------------

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo A B C D hSquare.1

  have hNC' :=
    parallelogram_vertices_noncollinear
      Geo A' B' C' D' hSquare'.1

  have hNCABC :
      Not (Collinear Geo A B C) :=
    hNC.2.1

  have hNCA'B'C' :
      Not (Collinear Geo A' B' C') :=
    hNC'.2.1

  have hNCBAC :
      Not (Collinear Geo B A C) := by
    intro hCol
    exact
      hNCABC
        (PrimCollinearSwap Geo B A C hCol)

  have hNCB'A'C' :
      Not (Collinear Geo B' A' C') := by
    intro hCol
    exact
      hNCA'B'C'
        (PrimCollinearSwap Geo B' A' C' hCol)

  have hNCACD :
      Not (Collinear Geo A C D) := by
    intro hCol
    exact
      hNC.2.2.2
        (PrimCollinearCycle Geo A C D hCol)

  --------------------------------------------------------------------
  -- Match the diagonals by SAS at the right angles.
  --------------------------------------------------------------------

  have hRightAngles :
      Geo.AngleCongruent A B C A' B' C' :=
    hilbert_all_right_angles_congruent
      Geo
      A B C
      A' B' C'
      hNCABC
      hNCA'B'C'
      hSquare.2.2.2.2.2.1
      hSquare'.2.2.2.2.2.1

  have hBA :
      Geo.Congruent B A B' A' :=
    CongruentReverseBoth
      Geo A B A' B' hCong

  have hDiagonalTriangle :
      TriangleCongruenceResult Geo B A C B' A' C' :=
    SAS
      Geo
      B A C
      B' A' C'
      hNCBAC
      hNCB'A'C'
      hBA
      hRightAngles
      hBC

  have hAC :
      Geo.Congruent A C A' C' :=
    hDiagonalTriangle.sideBC

  --------------------------------------------------------------------
  -- Both diagonal halves correspond by SSS.
  --------------------------------------------------------------------

  have hHalf1 :
      TriangleCongruenceResult Geo A B C A' B' C' :=
    (HilbertSSS
      Geo
      A B C
      A' B' C'
      hNCABC
      hCong
      hBC
      hAC).2

  have hHalf2 :
      TriangleCongruenceResult Geo A C D A' C' D' :=
    (HilbertSSS
      Geo
      A C D
      A' C' D'
      hNCACD
      hAC
      hCD
      hAD).2

  --------------------------------------------------------------------
  -- Hence the diagonal triangulations are scissors-equal.
  --------------------------------------------------------------------

  have hScissors :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A' B' C' D') := by
    unfold hilbertParallelogramTerm
    exact
      HilbertScissorsEq.add
        (Geo := Geo)
        (scissors_congruent
          Geo A B C A' B' C' hHalf1)
        (scissors_congruent
          Geo A C D A' C' D' hHalf2)

  exact
    equicomplementable_of_scissorsEq
      Geo hScissors


end Geometry

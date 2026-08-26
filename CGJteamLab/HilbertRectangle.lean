import CGJteamLab.Proposition48

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

def IsRectangle
    (A B C D : Geo.Point) : Prop :=
  IsParallelogram Geo A B C D ∧
  HilbertRightAngle Geo A B C

theorem rectangle_transport_scissorsEq
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D A' B' C' D' : Geo.Point)
    (hRect : IsRectangle Geo A B C D)
    (hRect' : IsRectangle Geo A' B' C' D')
    (hAB : Geo.Congruent A B A' B')
    (hBC : Geo.Congruent B C B' C') :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo A' B' C' D') := by

  have hPar :
      IsParallelogram Geo A B C D :=
    hRect.1

  have hPar' :
      IsParallelogram Geo A' B' C' D' :=
    hRect'.1

  have hSides :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hPar

  have hSides' :=
    ParallelogramOppositeSidesCongruent
      Geo A' B' C' D' hPar'

  have hCD_AB :
      Geo.Congruent C D A B :=
    hilbert_congruent_symmetry
      Geo A B C D hSides.1

  have hCD_A'B' :
      Geo.Congruent C D A' B' :=
    hilbert_congruent_transitivity
      Geo C D A B A' B'
      hCD_AB hAB

  have hCD :
      Geo.Congruent C D C' D' :=
    hilbert_congruent_transitivity
      Geo C D A' B' C' D'
      hCD_A'B' hSides'.1

  have hDA_BC :
      Geo.Congruent D A B C :=
    hilbert_congruent_symmetry
      Geo B C D A hSides.2

  have hDA_B'C' :
      Geo.Congruent D A B' C' :=
    hilbert_congruent_transitivity
      Geo D A B C B' C'
      hDA_BC hBC

  have hDA_D'A' :
      Geo.Congruent D A D' A' :=
    hilbert_congruent_transitivity
      Geo D A B' C' D' A'
      hDA_B'C' hSides'.2

  have hAD :
      Geo.Congruent A D A' D' :=
    CongruentReverseBoth
      Geo D A D' A' hDA_D'A'

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo A B C D hPar

  have hNC' :=
    parallelogram_vertices_noncollinear
      Geo A' B' C' D' hPar'

  have hNCABC :
      Not (Collinear Geo A B C) :=
    hNC.2.1

  have hNCA'B'C' :
      Not (Collinear Geo A' B' C') :=
    hNC'.2.1

  have hNCBAC :
      Not (Collinear Geo B A C) := by
    intro h
    exact hNCABC
      (PrimCollinearSwap Geo B A C h)

  have hNCB'A'C' :
      Not (Collinear Geo B' A' C') := by
    intro h
    exact hNCA'B'C'
      (PrimCollinearSwap Geo B' A' C' h)

  have hNCACD :
      Not (Collinear Geo A C D) := by
    intro h
    exact
      hNC.2.2.2
        (PrimCollinearCycle Geo A C D h)

  have hRightAngles :
      Geo.AngleCongruent A B C A' B' C' :=
    hilbert_all_right_angles_congruent
      Geo
      A B C
      A' B' C'
      hNCABC
      hNCA'B'C'
      hRect.2
      hRect'.2

  have hBA :
      Geo.Congruent B A B' A' :=
    CongruentReverseBoth
      Geo A B A' B' hAB

  have hDiag :
      TriangleCongruenceResult
        Geo B A C B' A' C' :=
    SAS
      Geo B A C B' A' C'
      hNCBAC
      hNCB'A'C'
      hBA
      hRightAngles
      hBC

  have hAC :
      Geo.Congruent A C A' C' :=
    hDiag.sideBC

  have hHalf1 :
      TriangleCongruenceResult
        Geo A B C A' B' C' :=
    (HilbertSSS
      Geo A B C A' B' C'
      hNCABC
      hAB
      hBC
      hAC).2

  have hHalf2 :
      TriangleCongruenceResult
        Geo A C D A' C' D' :=
    (HilbertSSS
      Geo A C D A' C' D'
      hNCACD
      hAC
      hCD
      hAD).2

  unfold hilbertParallelogramTerm

  exact
    HilbertScissorsEq.add
      (Geo := Geo)
      (scissors_congruent
        Geo A B C A' B' C' hHalf1)
      (scissors_congruent
        Geo A C D A' C' D' hHalf2)

theorem rectangle_transport
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D A' B' C' D' : Geo.Point)
    (hRect : IsRectangle Geo A B C D)
    (hRect' : IsRectangle Geo A' B' C' D')
    (hAB : Geo.Congruent A B A' B')
    (hBC : Geo.Congruent B C B' C') :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo A' B' C' D') :=
  equicomplementable_of_scissorsEq
    Geo
    (rectangle_transport_scissorsEq
      Geo A B C D A' B' C' D'
      hRect hRect' hAB hBC)

/--
A concrete rectangle `A B C D` is contained by the two segments
`P Q` and `R S` when its adjacent sides `AB` and `BC` are congruent
to those segments.
-/
def IsRectangleContainedBy
    (A B C D P Q R S : Geo.Point) : Prop :=
  IsRectangle Geo A B C D /\
  Geo.Congruent A B P Q /\
  Geo.Congruent B C R S

/--
Any two rectangles contained by the same two segments are scissors
equivalent.

Thus the Euclidean expression "the rectangle contained by PQ, RS"
has a well-defined scissors content, independently of the concrete
rectangle chosen to represent it.
-/
theorem rectangle_contained_by_unique
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D A' B' C' D' P Q R S : Geo.Point)
    (hRect :
      IsRectangleContainedBy
        Geo A B C D P Q R S)
    (hRect' :
      IsRectangleContainedBy
        Geo A' B' C' D' P Q R S) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo A' B' C' D') := by

  have hAB_PQ :
      Geo.Congruent A B P Q :=
    hRect.2.1

  have hA'B'_PQ :
      Geo.Congruent A' B' P Q :=
    hRect'.2.1

  have hPQ_A'B' :
      Geo.Congruent P Q A' B' :=
    hilbert_congruent_symmetry
      Geo A' B' P Q hA'B'_PQ

  have hAB :
      Geo.Congruent A B A' B' :=
    hilbert_congruent_transitivity
      Geo A B P Q A' B'
      hAB_PQ hPQ_A'B'

  have hBC_RS :
      Geo.Congruent B C R S :=
    hRect.2.2

  have hB'C'_RS :
      Geo.Congruent B' C' R S :=
    hRect'.2.2

  have hRS_B'C' :
      Geo.Congruent R S B' C' :=
    hilbert_congruent_symmetry
      Geo B' C' R S hB'C'_RS

  have hBC :
      Geo.Congruent B C B' C' :=
    hilbert_congruent_transitivity
      Geo B C R S B' C'
      hBC_RS hRS_B'C'

  exact
    rectangle_transport_scissorsEq
      Geo
      A B C D
      A' B' C' D'
      hRect.1
      hRect'.1
      hAB
      hBC

/--
Given a nondegenerate segment `PQ` and an arbitrary segment `RS`,
there exists a rectangle contained by `PQ` and `RS`.

The concrete representative is constructed on `PQ`: first erect at
`P` a perpendicular segment congruent to `RS`, then complete the
parallelogram.
-/
theorem rectangle_contained_by_exists
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (P Q R S : Geo.Point)
    (hPQ : Ne P Q) :
    exists C D : Geo.Point,
      IsRectangleContainedBy
        Geo P Q C D P Q R S := by

  --------------------------------------------------------------------
  -- Erect PD perpendicular to PQ, with PD ~= RS.
  --------------------------------------------------------------------

  rcases
      i48_erect_perpendicular
        Geo P Q R S hPQ with
    ⟨D, hNCDPQ, hRightDPQ, hPD_RS⟩

  --------------------------------------------------------------------
  -- Reorient noncollinearity for completion of P-Q-C-D.
  --------------------------------------------------------------------

  have hNCPQD :
      Not (Collinear Geo P Q D) := by
    intro h
    exact
      hNCDPQ
        (PrimCollinearCycle
          Geo Q D P
          (PrimCollinearCycle Geo P Q D h))

  --------------------------------------------------------------------
  -- Complete P-Q-C-D to a parallelogram.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo P Q D hNCPQD with
    ⟨C, hPar⟩

  --------------------------------------------------------------------
  -- Since DPQ is right, the adjacent angle PQC is right.
  --------------------------------------------------------------------

  have hRightPQC :
      HilbertRightAngle Geo P Q C :=
    parallelogram_adjacent_right_angle
      Geo P Q C D hPar hRightDPQ

  have hRect :
      IsRectangle Geo P Q C D :=
    ⟨hPar, hRightPQC⟩

  --------------------------------------------------------------------
  -- Opposite side QC is congruent to DP, hence to PD and therefore RS.
  --------------------------------------------------------------------

  have hSides :
      OppositeSidesCongruent Geo P Q C D :=
    ParallelogramOppositeSidesCongruent
      Geo P Q C D hPar

  have hQC_PD :
      Geo.Congruent Q C P D :=
    CongruentSwapSecond
      Geo Q C D P hSides.2

  have hQC_RS :
      Geo.Congruent Q C R S :=
    hilbert_congruent_transitivity
      Geo Q C P D R S
      hQC_PD hPD_RS

  --------------------------------------------------------------------
  -- The base PQ represents itself.
  --------------------------------------------------------------------

  have hPQ_PQ :
      Geo.Congruent P Q P Q :=
    hilbert_congruent_reflexive Geo P Q

  exact
    ⟨C, D,
      hRect,
      hPQ_PQ,
      hQC_RS⟩

/--
Rotating a rectangle by one vertex exchanges the two segments by which
it is contained.

Thus a rectangle contained by PQ, RS is scissors-equal to a concrete
rectangle contained by RS, PQ.
-/
theorem rectangle_contained_by_swap
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D P Q R S : Geo.Point)
    (hRect :
      IsRectangleContainedBy Geo
        A B C D P Q R S) :
    IsRectangleContainedBy Geo
      B C D A R S P Q /\
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo B C D A) := by

  have hPar :
      IsParallelogram Geo A B C D :=
    hRect.1.1

  --------------------------------------------------------------------
  -- Rotate the parallelogram A-B-C-D to B-C-D-A.
  --------------------------------------------------------------------

  have hParRot :
      IsParallelogram Geo B C D A :=
    ⟨hPar.2,
      ParallelSymmetry
        Geo A B C D hPar.1⟩

  --------------------------------------------------------------------
  -- The right angle ABC becomes the preceding right angle for the
  -- rotated parallelogram; propagate it to BCD.
  --------------------------------------------------------------------

  have hRightBCD :
      HilbertRightAngle Geo B C D :=
    parallelogram_adjacent_right_angle
      Geo B C D A
      hParRot
      hRect.1.2

  have hRectRot :
      IsRectangle Geo B C D A :=
    ⟨hParRot, hRightBCD⟩

  --------------------------------------------------------------------
  -- The first rotated side BC already represents RS.
  --------------------------------------------------------------------

  have hBC_RS :
      Geo.Congruent B C R S :=
    hRect.2.2

  --------------------------------------------------------------------
  -- The second rotated side CD is congruent to AB, hence to PQ.
  --------------------------------------------------------------------

  have hSides :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hPar

  have hCD_AB :
      Geo.Congruent C D A B :=
    hilbert_congruent_symmetry
      Geo A B C D hSides.1

  have hCD_PQ :
      Geo.Congruent C D P Q :=
    hilbert_congruent_transitivity
      Geo C D A B P Q
      hCD_AB
      hRect.2.1

  have hContainedRot :
      IsRectangleContainedBy Geo
        B C D A R S P Q :=
    ⟨hRectRot,
      hBC_RS,
      hCD_PQ⟩

  --------------------------------------------------------------------
  -- Rotation changes only the presentation of the parallelogram term.
  --------------------------------------------------------------------

  have hRotate1 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo D A B C) :=
    parallelogram_term_rotateOne
      Geo A B C D hPar

  have hPar1 :
      IsParallelogram Geo D A B C :=
    ⟨ParallelSymmetry
        Geo B C D A hPar.2,
      hPar.1⟩

  have hRotate2 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo D A B C)
        (hilbertParallelogramTerm Geo C D A B) :=
    parallelogram_term_rotateOne
      Geo D A B C hPar1

  have hPar2 :
      IsParallelogram Geo C D A B :=
    ⟨ParallelSymmetry
        Geo A B C D hPar.1,
      ParallelSymmetry
        Geo B C D A hPar.2⟩

  have hRotate3 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo C D A B)
        (hilbertParallelogramTerm Geo B C D A) :=
    parallelogram_term_rotateOne
      Geo C D A B hPar2

  have hRotate :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo B C D A) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hRotate1
      (HilbertScissorsEq.trans
        (Geo := Geo)
        hRotate2
        hRotate3)

  exact
    ⟨hContainedRot, hRotate⟩

/--
Commutativity of the Euclidean "rectangle contained by" construction.

Any rectangle contained by PQ, RS is scissors-equal to any rectangle
contained by RS, PQ.
-/
theorem rectangle_contained_by_comm
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D A' B' C' D' P Q R S : Geo.Point)
    (hRect :
      IsRectangleContainedBy Geo
        A B C D P Q R S)
    (hRect' :
      IsRectangleContainedBy Geo
        A' B' C' D' R S P Q) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo A' B' C' D') := by

  rcases
      rectangle_contained_by_swap
        Geo A B C D P Q R S hRect with
    ⟨hRot, hRotate⟩

  have hUnique :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B C D A)
        (hilbertParallelogramTerm Geo A' B' C' D') :=
    rectangle_contained_by_unique
      Geo
      B C D A
      A' B' C' D'
      R S P Q
      hRot
      hRect'

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hRotate
      hUnique

/--
A square on AB is, in particular, a rectangle contained by AB and AB.
-/
theorem square_is_rectangle_contained_by_side
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hSquare : IsSquare Geo A B C D) :
    IsRectangleContainedBy Geo
      A B C D A B A B := by

  have hRect :
      IsRectangle Geo A B C D :=
    ⟨hSquare.1,
      hSquare.2.2.2.2.2.1⟩

  have hAB_AB :
      Geo.Congruent A B A B :=
    hilbert_congruent_reflexive Geo A B

  have hBC_AB :
      Geo.Congruent B C A B :=
    hilbert_congruent_symmetry
      Geo A B B C hSquare.2.1

  exact
    ⟨hRect,
      hAB_AB,
      hBC_AB⟩

end Geometry

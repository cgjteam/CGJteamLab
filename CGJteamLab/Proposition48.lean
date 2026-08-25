import CGJteamLab.Proposition47
import CGJteamLab.Proposition42
import CGJteamLab.Proposition45
import CGJteamLab.HilbertScissorsPositivity

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.48
--
-- If in a triangle the square on one side is equal to the squares on
-- the remaining two sides together, then the angle contained by those
-- two sides is right.
--
-- Proof architecture for triangle A B C:
--
--   1. Erect AD perpendicular to AC at A and lay off AD congruent to AB.
--   2. Transport the square on AD to the given square on AB.
--   3. Apply I.47 to the right triangle ADC.
--   4. Compare the square on DC with the given square on BC.
--   5. Use segment trichotomy plus scissors positivity (De Zolt) to
--      deduce DC congruent to BC from equality of the two squares.
--   6. Apply SSS to triangles DAC and BAC and transport the right angle.
--
-- The former proposition-local assumptions have been eliminated:
--
--   * congruence of right angles is supplied by
--     `hilbert_all_right_angles_congruent`;
--   * "equal squares have congruent sides" is proved below as
--     `i48_congruent_of_equal_squares`.
--
-- The latter uses the project-wide scissors positivity principle from
-- `HilbertScissorsPositivity`: a nondegenerate triangle cannot be
-- equicomplementable with zero.  The proof constructs an inner square
-- from a strict side inequality, decomposes the outer square into that
-- inner square plus a nonempty triangulated remainder, and contradicts
-- positivity.  Segment trichotomy then yields congruence of the sides.
------------------------------------------------------------------------

/--
Any two nondegenerate right angles are congruent.
-/
theorem i48_right_angles_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B A' O' B' : Geo.Point)
    (hAOB : Not (Collinear Geo A O B))
    (hA'O'B' : Not (Collinear Geo A' O' B'))
    (hRight : HilbertRightAngle Geo A O B)
    (hRight' : HilbertRightAngle Geo A' O' B') :
    Geo.AngleCongruent A O B A' O' B' := by
  exact
    hilbert_all_right_angles_congruent
      Geo
      A O B
      A' O' B'
      hAOB
      hA'O'B'
      hRight
      hRight'

------------------------------------------------------------------------
-- Auxiliary results
------------------------------------------------------------------------

/--
If AB is shorter than a side of the square A'B'C'D', then the length AB
can be marked off as proper initial parts of both sides issuing from A'.
-/
theorem i48_aux_square_side_cuts
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B A' B' C' D' : Geo.Point)
    (hSquare' : IsSquare Geo A' B' C' D')
    (hLess : HilbertSegmentLess Geo A B A' B') :
    Exists fun X : Geo.Point =>
      Exists fun Y : Geo.Point =>
        And (Geo.Between A' X B')
          (And (Geo.Between A' Y D')
            (And (Geo.Congruent A B A' X)
                 (Geo.Congruent A B A' Y))) := by

  have hSides :=
    euclid_proposition_46_side
      Geo A' B' C' D' hSquare'

  have hA'B'_A'D' :
      Geo.Congruent A' B' A' D' :=
    CongruentSwapSecond
      Geo A' B' D' A'
      hSides.2.2

  have hLessAD :
      HilbertSegmentLess Geo A B A' D' :=
    hilbert_segmentLess_congruent_right
      Geo
      A B
      A' B'
      A' D'
      hLess
      hA'B'_A'D'

  let X : Geo.Point := Classical.choose hLess
  have hX :=
    Classical.choose_spec hLess

  let Y : Geo.Point := Classical.choose hLessAD
  have hY :=
    Classical.choose_spec hLessAD

  exact
    Exists.intro X
      (Exists.intro Y
        (And.intro hX.1
          (And.intro hY.1
            (And.intro hX.2 hY.2))))

/--
Two congruent perpendicular segments issuing from one point can be
completed to a square.
-/
theorem i48_aux_complete_square
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (O X Y : Geo.Point)
    (hNC : Not (Collinear Geo O X Y))
    (hRight : HilbertRightAngle Geo Y O X)
    (hCong : Geo.Congruent O X O Y) :
    Exists fun Z : Geo.Point =>
      IsSquare Geo O X Z Y := by

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo O X Y hNC with
    ⟨Z, hParallelogram⟩

  have hI34 :=
    euclid_proposition_34
      Geo O X Z Y hParallelogram

  have hSides :
      OppositeSidesCongruent Geo O X Z Y :=
    hI34.1

  --------------------------------------------------------------------
  -- All four sides are congruent.
  --------------------------------------------------------------------

  have hOY_OX :
      Geo.Congruent O Y O X :=
    hilbert_congruent_symmetry
      Geo O X O Y hCong

  have hYO_OX :
      Geo.Congruent Y O O X :=
    CongruentReverseFirst
      Geo O Y O X hOY_OX

  have hXZ_OX :
      Geo.Congruent X Z O X :=
    hilbert_congruent_transitivity
      Geo X Z Y O O X
      hSides.2
      hYO_OX

  have hOX_XZ :
      Geo.Congruent O X X Z :=
    hilbert_congruent_symmetry
      Geo X Z O X hXZ_OX

  have hXZ_ZY :
      Geo.Congruent X Z Z Y :=
    hilbert_congruent_transitivity
      Geo X Z O X Z Y
      hXZ_OX
      hSides.1

  have hZY_OX :
      Geo.Congruent Z Y O X :=
    hilbert_congruent_symmetry
      Geo O X Z Y hSides.1

  have hOX_YO :
      Geo.Congruent O X Y O :=
    CongruentSwapSecond
      Geo O X O Y hCong

  have hZY_YO :
      Geo.Congruent Z Y Y O :=
    hilbert_congruent_transitivity
      Geo Z Y O X Y O
      hZY_OX
      hOX_YO

  --------------------------------------------------------------------
  -- All four angles are right.
  --------------------------------------------------------------------

  have hNCs :=
    parallelogram_vertices_noncollinear
      Geo O X Z Y hParallelogram

  have hRightOXZ :
      HilbertRightAngle Geo O X Z :=
    parallelogram_adjacent_right_angle
      Geo O X Z Y
      hParallelogram
      hRight

  have hOppositeAngles :
      OppositeAnglesCongruent Geo O X Z Y :=
    hI34.2

  have hRightXZY :
      HilbertRightAngle Geo X Z Y :=
    hilbert_right_angle_transport
      Geo
      Y O X
      X Z Y
      hNCs.1
      hNCs.2.2.1
      hRight
      hOppositeAngles.1

  have hRightZYO :
      HilbertRightAngle Geo Z Y O :=
    hilbert_right_angle_transport
      Geo
      O X Z
      Z Y O
      hNCs.2.1
      hNCs.2.2.2
      hRightOXZ
      hOppositeAngles.2

  exact
    ⟨Z,
      hParallelogram,
      hOX_XZ,
      hXZ_ZY,
      hZY_YO,
      hRight,
      hRightOXZ,
      hRightXZY,
      hRightZYO⟩

/--
If AB is shorter than the side A'B' of a square A'B'C'D', then a
square with side congruent to AB can be inscribed at the vertex A'.
Its two adjacent vertices lie strictly inside A'B' and A'D'.
-/
theorem i48_aux_inner_square_of_less
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B A' B' C' D' : Geo.Point)
    (hSquare' : IsSquare Geo A' B' C' D')
    (hLess : HilbertSegmentLess Geo A B A' B') :
    Exists fun X : Geo.Point =>
      Exists fun Y : Geo.Point =>
        Exists fun Z : Geo.Point =>
          And (Geo.Between A' X B')
            (And (Geo.Between A' Y D')
              (And (Geo.Congruent A B A' X)
                (And (Geo.Congruent A B A' Y)
                     (IsSquare Geo A' X Z Y)))) := by

  rcases
      i48_aux_square_side_cuts
        Geo A B A' B' C' D'
        hSquare' hLess with
    ⟨X, Y, hAXB, hAYD, hABAX, hABAY⟩

  --------------------------------------------------------------------
  -- Basic data from the large square and the two strict cuts.
  --------------------------------------------------------------------

  have hBigNC :=
    parallelogram_vertices_noncollinear
      Geo A' B' C' D' hSquare'.1

  have hA'X : A' ≠ X :=
    (HilbertOrder.between_incidence
      A' X B' hAXB).1

  have hA'Y : A' ≠ Y :=
    (HilbertOrder.between_incidence
      A' Y D' hAYD).1

  have hA'XB' :
      Collinear Geo A' X B' :=
    (HilbertOrder.between_incidence
      A' X B' hAXB).2.2.2.1

  have hA'YD' :
      Collinear Geo A' Y D' :=
    (HilbertOrder.between_incidence
      A' Y D' hAYD).2.2.2.1

  --------------------------------------------------------------------
  -- D', A', Y are collinear.
  --------------------------------------------------------------------

  have hD'YA' :
      Collinear Geo D' Y A' :=
    PrimCollinearSymm
      Geo A' Y D' hA'YD'

  have hD'A'Y :
      Collinear Geo D' A' Y :=
    PrimCollinearRotate
      Geo D' Y A' hD'YA'

  --------------------------------------------------------------------
  -- Y, A', X are noncollinear.
  --
  -- Otherwise Y-A'-X together with D'-A'-Y and A'-X-B'
  -- would force D', A', B' to be collinear, contradicting the
  -- nondegeneracy of the large square.
  --------------------------------------------------------------------

  have hNCYAX :
      Not (Collinear Geo Y A' X) := by

    intro hYAX

    have hA'XY :
        Collinear Geo A' X Y :=
      PrimCollinearCycle
        Geo Y A' X hYAX

    have hA'YX :
        Collinear Geo A' Y X :=
      PrimCollinearRotate
        Geo A' X Y hA'XY

    have hD'A'X :
        Collinear Geo D' A' X :=
      hilbert_primCollinear_trans
        Geo
        D' A' Y X
        hA'Y
        hD'A'Y
        hA'YX

    have hD'A'B' :
        Collinear Geo D' A' B' :=
      hilbert_primCollinear_trans
        Geo
        D' A' X B'
        hA'X
        hD'A'X
        hA'XB'

    exact hBigNC.1 hD'A'B'

  --------------------------------------------------------------------
  -- The same noncollinearity in the orientation required by
  -- i48_aux_complete_square.
  --------------------------------------------------------------------

  have hNCAXY :
      Not (Collinear Geo A' X Y) := by

    intro hAXY

    have hXYA' :
        Collinear Geo X Y A' :=
      PrimCollinearCycle
        Geo A' X Y hAXY

    have hYA'X :
        Collinear Geo Y A' X :=
      PrimCollinearCycle
        Geo X Y A' hXYA'

    exact hNCYAX hYA'X

  --------------------------------------------------------------------
  -- X and B' determine the same ray from A'.
  -- Y and D' determine the same ray from A'.
  --------------------------------------------------------------------

  have hRayY_D :
      HilbertSameRay Geo A' Y D' :=
    hilbert_sameRay_of_between
      Geo A' Y D' hAYD

  have hRayD_Y :
      HilbertSameRay Geo A' D' Y :=
    hilbert_sameRay_symm
      Geo A' Y D' hRayY_D

  have hRayX_B :
      HilbertSameRay Geo A' X B' :=
    hilbert_sameRay_of_between
      Geo A' X B' hAXB

  have hRayB_X :
      HilbertSameRay Geo A' B' X :=
    hilbert_sameRay_symm
      Geo A' X B' hRayX_B

  --------------------------------------------------------------------
  -- Hence angle D'A'B' is the same angle as Y A' X.
  --------------------------------------------------------------------

  have hAngleFirst :
      Geo.Angle D' A' B' =
      Geo.Angle Y A' B' :=
    hilbert_angle_eq_of_sameRay_first
      Geo A' D' Y B' hRayD_Y

  have hAngleSecond :
      Geo.Angle Y A' B' =
      Geo.Angle Y A' X :=
    hilbert_angle_eq_of_sameRay_second
      Geo A' Y B' X hRayB_X

  have hAngleEq :
      Geo.Angle D' A' B' =
      Geo.Angle Y A' X :=
    hAngleFirst.trans hAngleSecond

  have hAngleRefl :
      Geo.AngleCongruent
        D' A' B'
        D' A' B' :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      D' A' B'
      hBigNC.1

  have hAngle :
      Geo.AngleCongruent
        D' A' B'
        Y A' X := by

    unfold Geometry.Geo.AngleCongruent
      at hAngleRefl ⊢

    rw [← hAngleEq]

    exact hAngleRefl

  --------------------------------------------------------------------
  -- The corner of the inner figure is therefore right.
  --------------------------------------------------------------------

  have hRightYAX :
      HilbertRightAngle Geo Y A' X :=
    hilbert_right_angle_transport
      Geo
      D' A' B'
      Y A' X
      hBigNC.1
      hNCYAX
      hSquare'.2.2.2.2.1
      hAngle

  --------------------------------------------------------------------
  -- Its two adjacent sides are congruent.
  --------------------------------------------------------------------

  have hAXAB :
      Geo.Congruent A' X A B :=
    hilbert_congruent_symmetry
      Geo A B A' X hABAX

  have hAXAY :
      Geo.Congruent A' X A' Y :=
    hilbert_congruent_transitivity
      Geo
      A' X
      A B
      A' Y
      hAXAB
      hABAY

  --------------------------------------------------------------------
  -- Complete the two perpendicular equal sides to the inner square.
  --------------------------------------------------------------------

  rcases
      i48_aux_complete_square
        Geo A' X Y
        hNCAXY
        hRightYAX
        hAXAY with
    ⟨Z, hInnerSquare⟩

  exact
    ⟨X, Y, Z,
      hAXB,
      hAYD,
      hABAX,
      hABAY,
      hInnerSquare⟩


/--
Euclid I.11 and I.3 at an endpoint, with an independently prescribed
length.

At the endpoint `A` of a segment `AC` there is a point `D` making a
right angle with `AC` and satisfying `AD ≅ PQ`.

This generalizes `i46_erect_equal_perpendicular`, which is the case
`PQ = AB` with `C = B`; the proof is unchanged.
-/
theorem i48_erect_perpendicular
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A C P Q : Geo.Point)
    (hAC : A ≠ C) :
    ∃ D : Geo.Point,
      Not (Collinear Geo D A C) ∧
      HilbertRightAngle Geo D A C ∧
      Geo.Congruent A D P Q := by

  have hCA : C ≠ A := hAC.symm

  --------------------------------------------------------------------
  -- Extend `CA` beyond `A`, so that I.11 applies at `A`.
  --------------------------------------------------------------------

  rcases
      ExtendSegmentBeyond
        Geo C A hCA with
    ⟨F, hCAF, _hCongCA⟩

  rcases
      hilbert_right_angle_exists_nondegenerate
        Geo C A F hCAF with
    ⟨X, hNCCAX, hRightCAX⟩

  have hAX : A ≠ X := by
    intro hEq
    subst hEq
    rcases
        HilbertPlaneIncidence.line_through
          C A hCA with
      ⟨l, hCl, hAl⟩
    exact hNCCAX ⟨l, hCl, hAl, hAl⟩

  --------------------------------------------------------------------
  -- Lay off `PQ` on the perpendicular ray (Hilbert III,1).
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo) P Q A X hAX with
    ⟨D, hRayAXD, hCongAD⟩

  have hDA : D ≠ A :=
    hRayAXD.2.1

  have hADX :
      Collinear Geo A D X :=
    PrimCollinearRotate
      Geo A X D hRayAXD.2.2.1

  have hNCCAD :
      Not (Collinear Geo C A D) := by
    intro hCol
    apply hNCCAX
    exact
      hilbert_primCollinear_trans
        Geo C A D X
        hDA.symm
        hCol
        hADX

  have hNCDAC :
      Not (Collinear Geo D A C) := by
    intro hCol
    exact
      hNCCAD
        (PrimCollinearSymm Geo D A C hCol)

  --------------------------------------------------------------------
  -- Replacing `X` by `D` does not change the angle at `A`.
  --------------------------------------------------------------------

  have hAngleEq :
      Geo.Angle C A X = Geo.Angle C A D :=
    hilbert_angle_eq_of_sameRay_second
      Geo A C X D hRayAXD

  have hRefl :
      Geo.AngleCongruent C A X C A X :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo) C A X hNCCAX

  have hAngleCAX_CAD :
      Geo.AngleCongruent C A X C A D := by
    unfold Geometry.Geo.AngleCongruent
    rw [← hAngleEq]
    exact hRefl

  have hRightCAD :
      HilbertRightAngle Geo C A D :=
    hilbert_right_angle_transport
      Geo
      C A X
      C A D
      hNCCAX
      hNCCAD
      hRightCAX
      hAngleCAX_CAD

  have hArmSwap :
      Geo.AngleCongruent C A D D A C :=
    bookZero_56_ABCequalsCBA
      Geo C A D hNCCAD

  have hRightDAC :
      HilbertRightAngle Geo D A C :=
    hilbert_right_angle_transport
      Geo
      C A D
      D A C
      hNCCAD
      hNCDAC
      hRightCAD
      hArmSwap

  exact ⟨D, hNCDAC, hRightDAC, hCongAD⟩

/--
Squares erected on congruent segments are equal.

Both squares are cut by a diagonal into two triangles; the two pairs
correspond under SSS, once the diagonals have been matched by SAS
using Postulate 4 to identify the two right angles at the second
vertex.

This is Euclid's silent step "the square on `AD` equals the square on
`AB`, for `AD ≅ AB`".
-/
theorem i48_square_transport
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
  -- The remaining sides correspond, all four being congruent to the
  -- side already matched.
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
  -- Nondegeneracy of the four vertex triples of both squares.
  --------------------------------------------------------------------

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo A B C D hSquare.1

  have hNC' :=
    parallelogram_vertices_noncollinear
      Geo A' B' C' D' hSquare'.1

  have hNCABC :
      Not (Collinear Geo A B C) := hNC.2.1

  have hNCA'B'C' :
      Not (Collinear Geo A' B' C') := hNC'.2.1

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
  -- The diagonals correspond: SAS at the right angle `∠ABC`.
  --------------------------------------------------------------------

  have hRightAngles :
      Geo.AngleCongruent A B C A' B' C' :=
    i48_right_angles_congruent
      Geo A B C A' B' C'
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
      Geo B A C B' A' C'
      hNCBAC
      hNCB'A'C'
      hBA
      hRightAngles
      hBC

  have hAC :
      Geo.Congruent A C A' C' :=
    hDiagonalTriangle.sideBC

  --------------------------------------------------------------------
  -- Both halves now correspond by SSS.
  --------------------------------------------------------------------

  have hHalf1 :
      TriangleCongruenceResult Geo A B C A' B' C' :=
    (HilbertSSS
      Geo A B C A' B' C'
      hNCABC
      hCong
      hBC
      hAC).2

  have hHalf2 :
      TriangleCongruenceResult Geo A C D A' C' D' :=
    (HilbertSSS
      Geo A C D A' C' D'
      hNCACD
      hAC
      hCD
      hAD).2

  --------------------------------------------------------------------
  -- Hence the two diagonal triangulations agree term by term.
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

/--
If the side AB of a square is shorter than the side A'B' of another
square, then the first square is equicomplementable with an inner square
based at A' inside the second square.
-/
theorem i48_aux_inner_square_transport
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D A' B' C' D' : Geo.Point)
    (hSquare : IsSquare Geo A B C D)
    (hSquare' : IsSquare Geo A' B' C' D')
    (hLess : HilbertSegmentLess Geo A B A' B') :
    Exists fun X : Geo.Point =>
      Exists fun Y : Geo.Point =>
        Exists fun Z : Geo.Point =>
          And (Geo.Between A' X B')
            (And (Geo.Between A' Y D')
              (And (IsSquare Geo A' X Z Y)
                (HilbertScissorsEquicomplementable Geo
                  (hilbertParallelogramTerm Geo A B C D)
                  (hilbertParallelogramTerm Geo A' X Z Y)))) := by

  rcases
      i48_aux_inner_square_of_less
        Geo
        A B
        A' B' C' D'
        hSquare'
        hLess with
    ⟨X, Y, Z,
      hAXB,
      hAYD,
      hABAX,
      _hABAY,
      hInnerSquare⟩

  have hTransport :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A' X Z Y) :=
    i48_square_transport
      Geo
      A B C D
      A' X Z Y
      hSquare
      hInnerSquare
      hABAX

  exact
    ⟨X, Y, Z,
      hAXB,
      hAYD,
      hInnerSquare,
      hTransport⟩

/--
A common scissors term may be cancelled from the right of an
equicomplementability relation.
-/
theorem i48_aux_equicomplementable_cancel_right
    {P Q T : HilbertScissorsTerm Geo}
    (h :
      HilbertScissorsEquicomplementable Geo
        (P + T)
        (Q + T)) :
    HilbertScissorsEquicomplementable Geo P Q := by

  rcases h with
    ⟨R, S, hRS, hPQ⟩

  refine
    ⟨R + T, S + T, ?_, ?_⟩

  · exact
      HilbertScissorsEq.add
        (Geo := Geo)
        hRS
        (HilbertScissorsEq.refl
          (Geo := Geo) T)

  · have hPQ' :
        HilbertScissorsEq Geo
          (P + (R + T))
          (Q + (S + T)) := by

      simpa only
        [Multiset.add_assoc,
         Multiset.add_comm T R,
         Multiset.add_comm T S]
        using hPQ

    exact hPQ'

/--
Every nondegenerate parallelogram is equicomplementable with a single
nondegenerate triangle.

The diagonal gives two equicomplementable halves.  Extending BC beyond
C by a congruent segment makes C the midpoint of BE, so I.42 identifies
the two halves of triangle ABE.  Thus the two diagonal halves of the
parallelogram can be joined into one triangle.
-/
theorem i48_aux_parallelogram_to_triangle
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hPar : IsParallelogram Geo A B C D) :
    Exists fun E : Geo.Point =>
      And (Not (Collinear Geo A B E))
        (HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo A B C D)
          (hilbertScissorsTriangle Geo A B E)) := by

  --------------------------------------------------------------------
  -- Nondegeneracy of the parallelogram.
  --------------------------------------------------------------------

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo A B C D hPar

  have hABC :
      Not (Collinear Geo A B C) :=
    hNC.2.1

  have hBC :
      Not (B = C) := by
    exact hPar.2.1

  --------------------------------------------------------------------
  -- Extend BC beyond C by an equal segment:
  --
  --     B - C - E
  --     BC ~= CE.
  --------------------------------------------------------------------

  rcases
      ExtendSegmentBeyond
        Geo B C hBC with
    ⟨E, hBCE, hBC_CE⟩

  have hBCEData :=
    HilbertOrder.between_incidence
      B C E hBCE

  have hBE :
      Not (B = E) :=
    hBCEData.2.2.1

  have hBCEcol :
      Collinear Geo B C E :=
    hBCEData.2.2.2.1

  have hBECcol :
      Collinear Geo B E C :=
    PrimCollinearRotate
      Geo B C E hBCEcol

  --------------------------------------------------------------------
  -- Triangle ABE is nondegenerate.
  --------------------------------------------------------------------

  have hABE :
      Not (Collinear Geo A B E) := by

    intro hABEcol

    have hABC' :
        Collinear Geo A B C :=
      hilbert_primCollinear_trans
        Geo
        A B E C
        hBE
        hABEcol
        hBECcol

    exact hABC hABC'

  --------------------------------------------------------------------
  -- C is the midpoint of BE.
  --------------------------------------------------------------------

  have hMid :
      HilbertIsMidpoint Geo C B E :=
    ⟨hBCE, hBC_CE⟩

  --------------------------------------------------------------------
  -- I.42: the midpoint divides triangle ABE into equal-content
  -- triangles ABC and ACE.
  --------------------------------------------------------------------

  have hHalf :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo A C E) :=
    i42_median_bisects_area
      Geo
      A B E C
      hABE
      hMid

  --------------------------------------------------------------------
  -- I.34: the diagonal AC divides the parallelogram into two
  -- congruent triangles ABC and ACD.
  --------------------------------------------------------------------

  have hCong :
      TriangleCongruenceResult
        Geo A B C C D A :=
    euclid_proposition_34_diagonal
      Geo A B C D hPar

  have hScABC_CDA :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo C D A) :=
    scissors_congruent
      Geo
      A B C
      C D A
      hCong

  have hCDA_ACD :
      hilbertScissorsTriangle Geo C D A =
      hilbertScissorsTriangle Geo A C D := by
    rw [scissors_triangle_cycle Geo C D A,
        scissors_triangle_cycle Geo D A C]

  have hScABC_ACD :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo A C D) := by
    rw [hCDA_ACD] at hScABC_CDA
    exact hScABC_CDA

  have hParSplit :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B C +
         hilbertScissorsTriangle Geo A B C) := by

    unfold hilbertParallelogramTerm

    exact
      HilbertScissorsEq.add
        (Geo := Geo)
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (hilbertScissorsTriangle Geo A B C))
        (HilbertScissorsEq.symm
          (Geo := Geo)
          hScABC_ACD)

  have hParDouble :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B C +
         hilbertScissorsTriangle Geo A B C) :=
    equicomplementable_of_scissorsEq
      Geo hParSplit

  --------------------------------------------------------------------
  -- Replace the second ABC by ACE.
  --------------------------------------------------------------------

  have hDoublePieces :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C +
         hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo A B C +
         hilbertScissorsTriangle Geo A C E) :=
    equicomplementable_add
      Geo
      (equicomplementable_refl
        Geo
        (hilbertScissorsTriangle Geo A B C))
      hHalf

  --------------------------------------------------------------------
  -- Triangle ABE splits exactly as ABC + ACE.
  --------------------------------------------------------------------

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B E)
        (hilbertScissorsTriangle Geo A B C +
         hilbertScissorsTriangle Geo A C E) :=
    HilbertScissorsEq.split
      (Geo := Geo)
      A B E C
      hBCE

  have hPiecesWhole :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C +
         hilbertScissorsTriangle Geo A C E)
        (hilbertScissorsTriangle Geo A B E) :=
    equicomplementable_of_scissorsEq
      Geo
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hSplit)

  --------------------------------------------------------------------
  -- Chain the three equivalences.
  --------------------------------------------------------------------

  have hResult :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B E) :=
    equicomplementable_trans
      Geo
      hParDouble
      (equicomplementable_trans
        Geo
        hDoublePieces
        hPiecesWhole)

  exact
    ⟨E, hABE, hResult⟩

/--
Every nonempty triangulated figure whose triangles are nondegenerate
is equicomplementable with one nondegenerate triangle.
-/
theorem i48_aux_rectilineal_to_triangle
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (L : HilbertTriangulatedFigure Geo)
    (hNonempty : L ≠ [])
    (hTriangles :
      ∀ t ∈ L,
        Not (Collinear Geo t.A t.B t.C)) :
    ∃ S T E : Geo.Point,
      Not (Collinear Geo S T E) ∧
      HilbertScissorsEquicomplementable Geo
        (rectilinealTerm Geo L)
        (hilbertScissorsTriangle Geo S T E) := by

  rcases
      euclid_proposition_45
        Geo
        X Y Z
        hXYZ
        L
        hNonempty
        hTriangles with
    ⟨S, T, U, V,
      hPar,
      _hAngle,
      hFigurePar⟩

  rcases
      i48_aux_parallelogram_to_triangle
        Geo
        S T U V
        hPar with
    ⟨E, hSTE, hParTriangle⟩

  have hResult :
      HilbertScissorsEquicomplementable Geo
        (rectilinealTerm Geo L)
        (hilbertScissorsTriangle Geo S T E) :=
    equicomplementable_trans
      Geo
      hFigurePar
      hParTriangle

  exact
    ⟨S, T, E, hSTE, hResult⟩


/--
A nonempty triangulated figure consisting only of nondegenerate
triangles cannot have zero scissors content.
-/
theorem i48_aux_rectilineal_positive
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (L : HilbertTriangulatedFigure Geo)
    (hNonempty : L ≠ [])
    (hTriangles :
      ∀ t ∈ L,
        Not (Collinear Geo t.A t.B t.C)) :
    Not
      (HilbertScissorsEquicomplementable Geo
        (rectilinealTerm Geo L)
        0) := by

  intro hZero

  rcases
      i48_aux_rectilineal_to_triangle
        Geo
        X Y Z
        hXYZ
        L
        hNonempty
        hTriangles with
    ⟨S, T, E, hSTE, hFigureTriangle⟩

  have hTriangleZero :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo S T E)
        0 :=
    equicomplementable_trans
      Geo
      (equicomplementable_symm
        Geo hFigureTriangle)
      hZero

  have hPositive :=
    hilbert_scissors_triangle_positive
      Geo
      0
      S T E
      hSTE

  apply hPositive

  simpa using hTriangleZero

/--
If Q decomposes as P plus a scissors term R of nonzero content,
then Q cannot be equicomplementable with P.
-/
theorem i48_aux_not_equal_of_positive_remainder
    (P Q R : HilbertScissorsTerm Geo)
    (hSplit :
      HilbertScissorsEq Geo
        Q
        (P + R))
    (hPositive :
      Not
        (HilbertScissorsEquicomplementable Geo
          R
          0)) :
    Not
      (HilbertScissorsEquicomplementable Geo
        Q
        P) := by

  intro hQP

  have hSplitEqui :
      HilbertScissorsEquicomplementable Geo
        (P + R)
        Q :=
    equicomplementable_symm
      Geo
      (equicomplementable_of_scissorsEq
        Geo hSplit)

  have hPR_P :
      HilbertScissorsEquicomplementable Geo
        (P + R)
        P :=
    equicomplementable_trans
      Geo
      hSplitEqui
      hQP

  have hRP_0P :
      HilbertScissorsEquicomplementable Geo
        (R + P)
        (0 + P) := by

    simpa only
      [Multiset.zero_add,
       Multiset.add_comm P R]
      using hPR_P

  have hR0 :
      HilbertScissorsEquicomplementable Geo
        R
        0 :=
    i48_aux_equicomplementable_cancel_right
      Geo
      hRP_0P

  exact hPositive hR0

/--
A parallelogram ABCD is scissors-equal to two copies of the corner
triangle ABD.  This is the triangulation along the other diagonal BD.
-/
theorem i48_aux_parallelogram_double_corner
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hPar : IsParallelogram Geo A B C D) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertScissorsTriangle Geo A B D +
       hilbertScissorsTriangle Geo A B D) := by

  --------------------------------------------------------------------
  -- Retriangulate the parallelogram along BD:
  --
  --   ABCD = ABD + BCD.
  --------------------------------------------------------------------

  have hTwo :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B C D) := by

    simpa [hilbertParallelogramTerm] using
      (parallelogram_two_triangulations
        Geo A B C D hPar)

  --------------------------------------------------------------------
  -- Rotate the parallelogram:
  --
  --   B C D A
  --
  -- and apply I.34 to its diagonal BD.  Hence
  --
  --   BCD ~= DAB = ABD.
  --------------------------------------------------------------------

  have hRot :
      IsParallelogram Geo B C D A := by
    constructor

    · exact hPar.2

    · exact
        ParallelSymmetry
          Geo A B C D hPar.1

  have hCong :
      TriangleCongruenceResult
        Geo B C D
        D A B :=
    euclid_proposition_34_diagonal
      Geo B C D A hRot

  have hBCD_DAB :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B C D)
        (hilbertScissorsTriangle Geo D A B) :=
    scissors_congruent
      Geo
      B C D
      D A B
      hCong

  have hBCD_ABD :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B C D)
        (hilbertScissorsTriangle Geo A B D) := by

    rw [scissors_triangle_cycle Geo D A B]
      at hBCD_DAB

    exact hBCD_DAB

  --------------------------------------------------------------------
  -- Replace BCD by the congruent copy ABD.
  --------------------------------------------------------------------

  have hDouble :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo B C D)
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo A B D) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo A B D))
      hBCD_ABD

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hTwo
      hDouble

/--
If X lies strictly between A and B, and Y lies strictly between A and D,
then the corner triangle ABD splits into the inner triangle AXY and
the two remaining triangles YDX and XBD.
-/
theorem i48_aux_corner_triangle_split
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B D X Y : Geo.Point)
    (hAXB : Geo.Between A X B)
    (hAYD : Geo.Between A Y D) :
    HilbertScissorsEq Geo
      (hilbertScissorsTriangle Geo A B D)
      (hilbertScissorsTriangle Geo A X Y +
       (hilbertScissorsTriangle Geo Y D X +
        hilbertScissorsTriangle Geo X B D)) := by

  --------------------------------------------------------------------
  -- First cut ABD at X on AB:
  --
  --   ABD = AXD + XBD.
  --------------------------------------------------------------------

  have hFirst0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      D A B X
      hAXB

  have hFirst :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D)
        (hilbertScissorsTriangle Geo A X D +
         hilbertScissorsTriangle Geo X B D) := by

    rw [scissors_triangle_cycle Geo D A B] at hFirst0
    rw [scissors_triangle_cycle Geo D A X] at hFirst0
    rw [scissors_triangle_cycle Geo D X B] at hFirst0

    exact hFirst0

  --------------------------------------------------------------------
  -- Then cut AXD at Y on AD:
  --
  --   AXD = AXY + YDX.
  --------------------------------------------------------------------

  have hSecond0 :=
    HilbertScissorsEq.split
      (Geo := Geo)
      X A D Y
      hAYD

  have hSecond :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A X D)
        (hilbertScissorsTriangle Geo A X Y +
         hilbertScissorsTriangle Geo Y D X) := by

    rw [scissors_triangle_swap12 Geo X A D] at hSecond0
    rw [scissors_triangle_swap12 Geo X A Y] at hSecond0
    rw [scissors_triangle_cycle Geo X Y D] at hSecond0

    exact hSecond0

  --------------------------------------------------------------------
  -- Keep XBD unchanged and substitute the second cut into the first.
  --------------------------------------------------------------------

  have hSubstitute :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A X D +
         hilbertScissorsTriangle Geo X B D)
        ((hilbertScissorsTriangle Geo A X Y +
          hilbertScissorsTriangle Geo Y D X) +
         hilbertScissorsTriangle Geo X B D) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hSecond
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo X B D))

  have hResult :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D)
        ((hilbertScissorsTriangle Geo A X Y +
          hilbertScissorsTriangle Geo Y D X) +
         hilbertScissorsTriangle Geo X B D) :=
    HilbertScissorsEq.trans
      (Geo := Geo)
      hFirst
      hSubstitute

  simpa only [Multiset.add_assoc] using hResult

/--
If AXYZ is an inner square based at the same vertex A as the square
ABCD, with X on AB and Y on AD, then the large square splits into the
inner square plus two copies of the two triangular remainder pieces.
-/
theorem i48_aux_square_split_with_remainder
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D X Y Z : Geo.Point)
    (hSquare : IsSquare Geo A B C D)
    (hInnerSquare : IsSquare Geo A X Z Y)
    (hAXB : Geo.Between A X B)
    (hAYD : Geo.Between A Y D) :
    HilbertScissorsEq Geo
      (hilbertParallelogramTerm Geo A B C D)
      (hilbertParallelogramTerm Geo A X Z Y +
       ((hilbertScissorsTriangle Geo Y D X +
         hilbertScissorsTriangle Geo X B D) +
        (hilbertScissorsTriangle Geo Y D X +
         hilbertScissorsTriangle Geo X B D))) := by

  --------------------------------------------------------------------
  -- Large square = two copies of triangle ABD.
  --------------------------------------------------------------------

  have hBig :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo A B D) :=
    i48_aux_parallelogram_double_corner
      Geo
      A B C D
      hSquare.1

  --------------------------------------------------------------------
  -- Inner square = two copies of triangle AXY.
  --------------------------------------------------------------------

  have hInner :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A X Z Y)
        (hilbertScissorsTriangle Geo A X Y +
         hilbertScissorsTriangle Geo A X Y) :=
    i48_aux_parallelogram_double_corner
      Geo
      A X Z Y
      hInnerSquare.1

  --------------------------------------------------------------------
  -- Each copy of ABD splits as
  --
  --   AXY + (YDX + XBD).
  --------------------------------------------------------------------

  have hCorner :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D)
        (hilbertScissorsTriangle Geo A X Y +
         (hilbertScissorsTriangle Geo Y D X +
          hilbertScissorsTriangle Geo X B D)) :=
    i48_aux_corner_triangle_split
      Geo
      A B D X Y
      hAXB
      hAYD

  --------------------------------------------------------------------
  -- Split both copies.
  --------------------------------------------------------------------

  have hBoth0 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo A B D)
        ((hilbertScissorsTriangle Geo A X Y +
          (hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D)) +
         (hilbertScissorsTriangle Geo A X Y +
          (hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D))) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hCorner
      hCorner

  --------------------------------------------------------------------
  -- Regroup:
  --
  --   (I + R) + (I + R)
  --       =
  --   (I + I) + (R + R).
  --------------------------------------------------------------------

  have hRegroup :
      ((hilbertScissorsTriangle Geo A X Y +
        (hilbertScissorsTriangle Geo Y D X +
         hilbertScissorsTriangle Geo X B D)) +
       (hilbertScissorsTriangle Geo A X Y +
        (hilbertScissorsTriangle Geo Y D X +
         hilbertScissorsTriangle Geo X B D)))
        =
      ((hilbertScissorsTriangle Geo A X Y +
        hilbertScissorsTriangle Geo A X Y) +
       ((hilbertScissorsTriangle Geo Y D X +
         hilbertScissorsTriangle Geo X B D) +
        (hilbertScissorsTriangle Geo Y D X +
         hilbertScissorsTriangle Geo X B D))) := by
    ac_rfl

  have hBoth :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B D +
         hilbertScissorsTriangle Geo A B D)
        ((hilbertScissorsTriangle Geo A X Y +
          hilbertScissorsTriangle Geo A X Y) +
         ((hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D) +
          (hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D))) := by

    rw [hRegroup] at hBoth0
    exact hBoth0

  --------------------------------------------------------------------
  -- Replace the double AXY by the inner square itself.
  --------------------------------------------------------------------

  have hReplace :
      HilbertScissorsEq Geo
        ((hilbertScissorsTriangle Geo A X Y +
          hilbertScissorsTriangle Geo A X Y) +
         ((hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D) +
          (hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D)))
        (hilbertParallelogramTerm Geo A X Z Y +
         ((hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D) +
          (hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D))) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hInner)
      (HilbertScissorsEq.refl
        (Geo := Geo)
        ((hilbertScissorsTriangle Geo Y D X +
          hilbertScissorsTriangle Geo X B D) +
         (hilbertScissorsTriangle Geo Y D X +
          hilbertScissorsTriangle Geo X B D)))

  --------------------------------------------------------------------
  -- Chain everything.
  --------------------------------------------------------------------

  exact
    HilbertScissorsEq.trans
      (Geo := Geo)
      hBig
      (HilbertScissorsEq.trans
        (Geo := Geo)
        hBoth
        hReplace)

/--
The two triangle types occurring in the square remainder are
nondegenerate.
-/
theorem i48_aux_remainder_triangles_nondegenerate
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D X Y : Geo.Point)
    (hSquare : IsSquare Geo A B C D)
    (hAXB : Geo.Between A X B)
    (hAYD : Geo.Between A Y D) :
    Not (Collinear Geo Y D X) ∧
    Not (Collinear Geo X B D) := by

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo A B C D hSquare.1

  have hDAB :
      Not (Collinear Geo D A B) :=
    hNC.1

  have hAXBData :=
    HilbertOrder.between_incidence
      A X B hAXB

  have hAX :
      A ≠ X :=
    hAXBData.1

  have hXB :
      X ≠ B :=
    hAXBData.2.1

  have hAXBcol :
      Collinear Geo A X B :=
    hAXBData.2.2.2.1

  have hABX :
      Collinear Geo A B X :=
    PrimCollinearRotate
      Geo A X B hAXBcol

  have hAYDData :=
    HilbertOrder.between_incidence
      A Y D hAYD

  have hYD :
      Y ≠ D :=
    hAYDData.2.1

  have hAYDcol :
      Collinear Geo A Y D :=
    hAYDData.2.2.2.1

  --------------------------------------------------------------------
  -- YDX is noncollinear.
  --------------------------------------------------------------------

  have hYDX :
      Not (Collinear Geo Y D X) := by

    intro hCol

    have hXDY :
        Collinear Geo X D Y :=
      PrimCollinearSymm
        Geo Y D X hCol

    have hDYA :
        Collinear Geo D Y A :=
      PrimCollinearSymm
        Geo A Y D hAYDcol

    have hXDA :
        Collinear Geo X D A :=
      hilbert_primCollinear_trans
        Geo
        X D Y A
        hYD.symm
        hXDY
        hDYA

    have hDAX :
        Collinear Geo D A X :=
      PrimCollinearCycle
        Geo X D A hXDA

    have hDAB' :
        Collinear Geo D A B :=
      hilbert_primCollinear_trans
        Geo
        D A X B
        hAX
        hDAX
        hAXBcol

    exact hDAB hDAB'

  --------------------------------------------------------------------
  -- XBD is noncollinear.
  --------------------------------------------------------------------

  have hXBD :
      Not (Collinear Geo X B D) := by

    intro hCol

    have hXDB :
        Collinear Geo X D B :=
      PrimCollinearRotate
        Geo X B D hCol

    have hDBX :
        Collinear Geo D B X :=
      PrimCollinearCycle
        Geo X D B hXDB

    have hBXD :
        Collinear Geo B X D :=
      PrimCollinearCycle
        Geo D B X hDBX

    have hABD :
        Collinear Geo A B D :=
      hilbert_primCollinear_trans
        Geo
        A B X D
        hXB.symm
        hABX
        hBXD

    have hBDA :
        Collinear Geo B D A :=
      PrimCollinearCycle
        Geo A B D hABD

    have hDAB' :
        Collinear Geo D A B :=
      PrimCollinearCycle
        Geo B D A hBDA

    exact hDAB hDAB'

  exact ⟨hYDX, hXBD⟩

/--
The remainder in the inner-square decomposition is the rectilineal
term of a nonempty four-triangle figure, and every triangle in that
figure is nondegenerate.
-/
theorem i48_aux_remainder_figure
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D X Y : Geo.Point)
    (hSquare : IsSquare Geo A B C D)
    (hAXB : Geo.Between A X B)
    (hAYD : Geo.Between A Y D) :
    Exists fun L : HilbertTriangulatedFigure Geo =>
      And (Not (L = []))
        (And
          (forall t, t ∈ L ->
            Not (Collinear Geo t.A t.B t.C))
          (rectilinealTerm Geo L =
            ((hilbertScissorsTriangle Geo Y D X +
              hilbertScissorsTriangle Geo X B D) +
             (hilbertScissorsTriangle Geo Y D X +
              hilbertScissorsTriangle Geo X B D)))) := by

  have hNondeg :
      Not (Collinear Geo Y D X) ∧
      Not (Collinear Geo X B D) :=
    i48_aux_remainder_triangles_nondegenerate
      Geo
      A B C D X Y
      hSquare
      hAXB
      hAYD

  let t1 : HilbertTriangle Geo :=
    ⟨Y, D, X⟩

  let t2 : HilbertTriangle Geo :=
    ⟨X, B, D⟩

  let L : HilbertTriangulatedFigure Geo :=
    [t1, t2, t1, t2]

  have hNonempty :
      Not (L = []) := by
    simp [L]

  have hTriangles :
      forall t, t ∈ L ->
        Not (Collinear Geo t.A t.B t.C) := by

    intro t ht

    simp [L] at ht

    rcases ht with h | h | h | h

    · cases h
      simpa [t1] using hNondeg.1

    · cases h
      simpa [t2] using hNondeg.2

    · cases h
      simpa [t1] using hNondeg.1

    · cases h
      simpa [t2] using hNondeg.2

  have hTerm :
      rectilinealTerm Geo L =
        ((hilbertScissorsTriangle Geo Y D X +
          hilbertScissorsTriangle Geo X B D) +
         (hilbertScissorsTriangle Geo Y D X +
          hilbertScissorsTriangle Geo X B D)) := by

    simp
      [L,
       t1,
       t2,
       rectilinealTerm]
    ac_rfl

  exact
    ⟨L,
      hNonempty,
      hTriangles,
      hTerm⟩

/--
If a scissors term Q is obtained from P by adjoining a nonempty
triangulated figure made of nondegenerate triangles, then Q and P
cannot be equicomplementable.
-/
theorem i48_aux_not_equal_of_rectilineal_remainder
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (X Y Z : Geo.Point)
    (hXYZ : Not (Collinear Geo X Y Z))
    (P Q : HilbertScissorsTerm Geo)
    (L : HilbertTriangulatedFigure Geo)
    (hNonempty : Not (L = []))
    (hTriangles :
      forall t, t ∈ L ->
        Not (Collinear Geo t.A t.B t.C))
    (hSplit :
      HilbertScissorsEq Geo
        Q
        (P + rectilinealTerm Geo L)) :
    Not
      (HilbertScissorsEquicomplementable Geo
        Q
        P) := by

  have hPositive :
      Not
        (HilbertScissorsEquicomplementable Geo
          (rectilinealTerm Geo L)
          0) :=
    i48_aux_rectilineal_positive
      Geo
      X Y Z
      hXYZ
      L
      hNonempty
      hTriangles

  exact
    i48_aux_not_equal_of_positive_remainder
      Geo
      P
      Q
      (rectilinealTerm Geo L)
      hSplit
      hPositive

/--
A square which contains a strictly smaller square at one vertex
cannot be equicomplementable with that inner square.
-/
theorem i48_aux_inner_square_proper_part
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D X Y Z : Geo.Point)
    (hSquare : IsSquare Geo A B C D)
    (hInnerSquare : IsSquare Geo A X Z Y)
    (hAXB : Geo.Between A X B)
    (hAYD : Geo.Between A Y D) :
    Not
      (HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A X Z Y)) := by

  rcases
      i48_aux_remainder_figure
        Geo
        A B C D X Y
        hSquare
        hAXB
        hAYD with
    ⟨L, hNonempty, hTriangles, hTerm⟩

  have hSplit0 :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A X Z Y +
         ((hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D) +
          (hilbertScissorsTriangle Geo Y D X +
           hilbertScissorsTriangle Geo X B D))) :=
    i48_aux_square_split_with_remainder
      Geo
      A B C D X Y Z
      hSquare
      hInnerSquare
      hAXB
      hAYD

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A X Z Y +
         rectilinealTerm Geo L) := by
    rw [hTerm]
    exact hSplit0

  have hNondeg :
      Not (Collinear Geo Y D X) :=
    (i48_aux_remainder_triangles_nondegenerate
      Geo
      A B C D X Y
      hSquare
      hAXB
      hAYD).1

  exact
    i48_aux_not_equal_of_rectilineal_remainder
      Geo
      Y D X
      hNondeg
      (hilbertParallelogramTerm Geo A X Z Y)
      (hilbertParallelogramTerm Geo A B C D)
      L
      hNonempty
      hTriangles
      hSplit

/--
Strict inequality of square sides implies inequality of the
corresponding square scissors contents.
-/
theorem i48_aux_square_not_equal_of_less
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D A' B' C' D' : Geo.Point)
    (hSquare : IsSquare Geo A B C D)
    (hSquare' : IsSquare Geo A' B' C' D')
    (hLess : HilbertSegmentLess Geo A B A' B') :
    Not
      (HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A' B' C' D')) := by

  rcases
      i48_aux_inner_square_transport
        Geo
        A B C D
        A' B' C' D'
        hSquare
        hSquare'
        hLess with
    ⟨X, Y, Z,
      hAXB,
      hAYD,
      hInnerSquare,
      hTransport⟩

  have hProper :
      Not
        (HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo A' B' C' D')
          (hilbertParallelogramTerm Geo A' X Z Y)) :=
    i48_aux_inner_square_proper_part
      Geo
      A' B' C' D'
      X Y Z
      hSquare'
      hInnerSquare
      hAXB
      hAYD

  intro hEqual

  have hBigInner :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A' B' C' D')
        (hilbertParallelogramTerm Geo A' X Z Y) :=
    equicomplementable_trans
      Geo
      (equicomplementable_symm
        Geo hEqual)
      hTransport

  exact hProper hBigInner

/--
Squares with equal scissors content have congruent sides.
-/
theorem i48_congruent_of_equal_squares
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D A' B' C' D' : Geo.Point)
    (hSquare : IsSquare Geo A B C D)
    (hSquare' : IsSquare Geo A' B' C' D')
    (hEqual :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A' B' C' D')) :
    Geo.Congruent A B A' B' := by

  --------------------------------------------------------------------
  -- AB cannot be strictly shorter than A'B'.
  --------------------------------------------------------------------

  have hNotLess :
      Not (HilbertSegmentLess Geo A B A' B') := by

    intro hLess

    have hNotEqual :=
      i48_aux_square_not_equal_of_less
        Geo
        A B C D
        A' B' C' D'
        hSquare
        hSquare'
        hLess

    exact hNotEqual hEqual

  --------------------------------------------------------------------
  -- Nor can A'B' be strictly shorter than AB.
  --------------------------------------------------------------------

  have hNotLess' :
      Not (HilbertSegmentLess Geo A' B' A B) := by

    intro hLess

    have hNotEqual :=
      i48_aux_square_not_equal_of_less
        Geo
        A' B' C' D'
        A B C D
        hSquare'
        hSquare
        hLess

    exact
      hNotEqual
        (equicomplementable_symm
          Geo hEqual)

  --------------------------------------------------------------------
  -- Both sides are nondegenerate because they are sides of squares.
  --------------------------------------------------------------------

  have hAB :
      A ≠ B :=
    hSquare.1.1.1

  have hA'B' :
      A' ≠ B' :=
    hSquare'.1.1.1

  --------------------------------------------------------------------
  -- Segment trichotomy leaves only congruence.
  --------------------------------------------------------------------

  exact
    bookZero_31_trichotomy1
      Geo
      A B
      A' B'
      hNotLess
      hNotLess'
      hAB
      hA'B'

------------------------------------------------------------------------
-- Euclid I.48
------------------------------------------------------------------------

/--
Euclid, Elements, Book I, Proposition 48.

If in the triangle `A B C` the square on `BC` is equal to the squares
on `AB` and `AC` together, then the angle `BAC` is right.

The three squares are given as data, since a square is not determined
by its side alone; the hypothesis is the equality of the corresponding
scissors terms.
-/
theorem euclid_proposition_48
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C P Q R S T U : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hSqBC : IsSquare Geo B C P Q)
    (hSqAB : IsSquare Geo A B R S)
    (hSqAC : IsSquare Geo A C T U)
    (hEqual :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B C P Q)
        (hilbertParallelogramTerm Geo A B R S +
         hilbertParallelogramTerm Geo A C T U)) :
    HilbertRightAngle Geo B A C := by

  --------------------------------------------------------------------
  -- `A ≠ C`, from the nondegeneracy of the triangle.
  --------------------------------------------------------------------

  have hAC : A ≠ C := by
    intro hEq
    apply hABC
    by_cases hAB : A = B
    · rcases
          hilbert_line_through_point Geo A with
        ⟨l, hAl⟩
      refine ⟨l, hAl, ?_, ?_⟩
      · rw [← hAB]; exact hAl
      · rw [← hEq]; exact hAl
    · rcases
          HilbertPlaneIncidence.line_through
            A B hAB with
        ⟨m, hAm, hBm⟩
      refine ⟨m, hAm, hBm, ?_⟩
      rw [← hEq]; exact hAm

  --------------------------------------------------------------------
  -- Step 1 [I.11, I.3]: erect `AD ⊥ AC` at `A` with `AD ≅ AB`.
  --------------------------------------------------------------------

  rcases
      i48_erect_perpendicular
        Geo A C A B hAC with
    ⟨D, hNCDAC, hRightDAC, hCongAD_AB⟩

  have hNCADC :
      Not (Collinear Geo A D C) := by
    intro hCol
    exact
      hNCDAC
        (PrimCollinearSwap Geo A D C hCol)

  --------------------------------------------------------------------
  -- Step 3 [I.47]: the square on `DC` equals the squares on `AD`
  -- and `AC`.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo A D C hNCADC hRightDAC with
    ⟨D₁, E₁, F₁, G₁, H₁, K₁,
     hSqDC, hSqAD, hSqAC₁, hPythagoras⟩

  --------------------------------------------------------------------
  -- Step 2: replace the two summands by the given squares.
  --------------------------------------------------------------------

  have hLeg1 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A D F₁ G₁)
        (hilbertParallelogramTerm Geo A B R S) :=
    i48_square_transport
      Geo A D F₁ G₁ A B R S
      hSqAD hSqAB hCongAD_AB

  have hLeg2 :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A C K₁ H₁)
        (hilbertParallelogramTerm Geo A C T U) :=
    i48_square_transport
      Geo A C K₁ H₁ A C T U
      hSqAC₁ hSqAC
      (hilbert_congruent_reflexive Geo A C)

  have hLegs :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A D F₁ G₁ +
         hilbertParallelogramTerm Geo A C K₁ H₁)
        (hilbertParallelogramTerm Geo A B R S +
         hilbertParallelogramTerm Geo A C T U) :=
    i47_aux_equicomplementable_add
      Geo hLeg1 hLeg2

  --------------------------------------------------------------------
  -- Step 4: the squares on `DC` and on `BC` are equal, hence the
  -- sides are congruent.
  --------------------------------------------------------------------

  have hSquaresEqual :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D C E₁ D₁)
        (hilbertParallelogramTerm Geo B C P Q) :=
    equicomplementable_trans
      Geo
      (equicomplementable_trans
        Geo hPythagoras hLegs)
      (equicomplementable_symm Geo hEqual)

  have hCongDC_BC :
      Geo.Congruent D C B C :=
    i48_congruent_of_equal_squares
      Geo D C E₁ D₁ B C P Q
      hSqDC hSqBC hSquaresEqual

  --------------------------------------------------------------------
  -- Step 5 [I.8]: the triangles `D A C` and `B A C` are congruent, so
  -- the angle at `A` is transported.
  --------------------------------------------------------------------

  have hCongDA_BA :
      Geo.Congruent D A B A :=
    CongruentReverseBoth
      Geo A D A B hCongAD_AB

  have hSSS :=
    HilbertSSS
      Geo D A C B A C
      hNCDAC
      hCongDA_BA
      (hilbert_congruent_reflexive Geo A C)
      hCongDC_BC

  exact
    hilbert_right_angle_transport
      Geo
      D A C
      B A C
      hNCDAC
      hSSS.1
      hRightDAC
      hSSS.2.angleB

end Geometry

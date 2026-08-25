import CGJteamLab.Proposition47

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.48
--
-- If in a triangle the square on one of the sides is equal to the
-- squares on the remaining two sides of the triangle, then the angle
-- contained by the remaining two sides of the triangle is right.
--
-- Euclid's proof, for triangle `A B C` with the square on `BC` equal
-- to the squares on `AB` and `AC`:
--
--   1. Draw `AD` at right angles to `AC` at `A` [I.11], with
--      `AD ≅ AB` [I.3], and join `DC`.
--   2. Since `AD ≅ AB`, the square on `AD` equals the square on `AB`;
--      adding the square on `AC` to each, the squares on `AD`, `AC`
--      together equal the squares on `AB`, `AC` together, which by
--      hypothesis equal the square on `BC`.
--   3. But the angle `DAC` is right, so by I.47 the squares on `AD`,
--      `AC` together equal the square on `DC`.
--   4. Hence the square on `DC` equals the square on `BC`, so
--      `DC ≅ BC`.
--   5. The triangles `DAC` and `BAC` have `DA ≅ BA`, `AC` common and
--      `DC ≅ BC`, so they are congruent [I.8], and the angle `DAC`
--      equals the angle `BAC`.  Since `DAC` is right, so is `BAC`.
--
-- Formalization notes.
--
-- Steps 1, 3 and 5 are proved here in full.  Step 1 uses
-- `i48_erect_perpendicular`, the generalization of
-- `i46_erect_equal_perpendicular` in which the length laid off on the
-- perpendicular is an arbitrary given segment rather than the base
-- itself; the proof is the same and `Proposition46.lean` could be
-- refactored to use it.  Step 3 is `euclid_proposition_47`, step 5 is
-- `HilbertSSS` followed by `hilbert_right_angle_transport`.
--
-- Two facts are assumed locally.
--
--   * `i48_right_angles_congruent` (Euclid Post. 4, Hilbert's
--     Theorem 21): all right angles are congruent.  This is proved in
--     `Hilbert48_test.lean` as
--     `hilbert48_test_all_right_angles_congruent` but has not been
--     promoted to the main library; it is also one of the pieces
--     currently buried inside `i47_diagram`.  Everything else in
--     step 2 -- that squares on congruent segments are
--     equicomplementable -- is *proved* from it here, as
--     `i48_square_transport`.
--
--   * `i48_congruent_of_equal_squares` (step 4): if the squares on two
--     segments are equal, the segments are congruent.  This is the one
--     genuinely new mathematical content of I.48, and it is not a
--     scissors-calculus fact at all: the calculus has no order
--     relation, so "equal squares implies equal sides" needs Hilbert's
--     theory of area from Grundlagen ch. IV (the measure of area and
--     the segment arithmetic behind it), where the corresponding
--     statement is that a figure is never equicomplementable with a
--     proper part of itself.  Recording it as a local axiom marks
--     exactly where Book I outgrows the equidecomposition machinery
--     the project currently has.
------------------------------------------------------------------------

/--
Local axiom 1: Euclid, Postulate 4.

Any two right angles are congruent.

Proved in `Hilbert48_test.lean` as
`hilbert48_test_all_right_angles_congruent`; assumed here because that
file is not part of the main import chain.
-/
axiom i48_right_angles_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B A' O' B' : Geo.Point)
    (hAOB : Not (Collinear Geo A O B))
    (hA'O'B' : Not (Collinear Geo A' O' B'))
    (hRight : HilbertRightAngle Geo A O B)
    (hRight' : HilbertRightAngle Geo A' O' B') :
    Geo.AngleCongruent A O B A' O' B'

/--
Local axiom 2: equal squares stand on congruent segments.

The converse direction of the correspondence between a segment and the
square on it.  In Hilbert's development this belongs to the theory of
area (Grundlagen ch. IV): the scissors calculus used in this project
has no order relation, so nothing in it can distinguish a figure from
a proper part of itself, and this implication is therefore not
derivable at the present level.
-/
axiom i48_congruent_of_equal_squares
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D A' B' C' D' : Geo.Point)
    (hSquare : IsSquare Geo A B C D)
    (hSquare' : IsSquare Geo A' B' C' D')
    (hEqual :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B C D)
        (hilbertParallelogramTerm Geo A' B' C' D')) :
    Geo.Congruent A B A' B'

------------------------------------------------------------------------
-- Auxiliary results
------------------------------------------------------------------------

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

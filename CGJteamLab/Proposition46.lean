import CGJteamLab.Proposition11
import CGJteamLab.Proposition34

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.46
--
-- On a given straight line to describe a square.
--
-- Euclid's proof:
--
--   1. From A draw AC at right angles to AB [I.11].
--   2. Cut off AD equal to AB on that perpendicular [I.3 / III,1].
--   3. Through D draw DE parallel to AB, and through B draw BE
--      parallel to AD [I.31]; ADEB is then a parallelogram.
--   4. By I.34 the opposite sides are equal, so all four sides equal
--      AB.
--   5. Since AD meets the parallels AB and DE, the angles BAD and ADE
--      are together equal to two right angles [I.29]; BAD is right,
--      hence ADE is right; by I.34 the opposite angles are equal, so
--      all four angles are right.
--   Therefore the figure is a square, described on AB.
--
-- Formalization notes.
--
-- Step 1 and step 2 are proved here in full, from
-- `hilbert_right_angle_exists_nondegenerate` (the Book Zero form of
-- I.11) and Hilbert III,1 (`segment_construction`).  Note that the
-- library's I.11 erects the perpendicular at a point *between* two
-- others, so the segment `BA` is first extended beyond `A`
-- (`ExtendSegmentBeyond`), exactly as Euclid must do to apply I.11 at
-- an endpoint.
--
-- Step 3 needs the fourth vertex, obtained as the intersection of two
-- lines constructed parallel to two different given directions.  This
-- is `hilbert_parallelogram_fourth_vertex_exists`, proved in
-- `HilbertInterface.lean`: since `Geo.Parallel` is disjointness of the
-- two point-line carriers, the only real content is that the two
-- constructed parallels are not parallel to each other, which follows
-- from `hilbert_parallel_transitive_distinct` (axiom IV).
--
-- Step 5 is Euclid's own citation of I.29.  The library does prove
-- I.29 (`euclid_proposition_29`), but only in the explicit transversal
-- configuration `A-D-C`, `C-E-B`, `D-E-F`; connecting that
-- configuration to the parallelogram `A B C D` with a right angle at
-- `A` is a configuration-normalization exercise of the kind carried
-- out in `Proposition27.lean`, and is not yet available as a reusable
-- lemma.  It is recorded below as the second local assumption
-- `i46_parallelogram_adjacent_right_angle`, and is the natural
-- candidate for elimination once the co-interior-angle form of I.29 is
-- packaged.
--
-- Everything else -- the four side congruences and the remaining two
-- right angles (via the opposite-angle theorem I.34 and
-- `hilbert_right_angle_transport`), together with all four
-- noncollinearity side conditions -- is proved here without further
-- assumptions.
------------------------------------------------------------------------

/--
Euclid's Definition I.22 for the square, in the vertex order
`A B C D`: the quadrilateral is a parallelogram, all four sides are
congruent, and all four angles are right.

The parallelogram clause is not part of Euclid's definition (he says
only "equilateral and right-angled"), but it is the form in which the
figure is produced by the construction, and it is what makes the
figure a genuine quadrilateral rather than a crossed one.
-/
def IsSquare
    (A B C D : Geo.Point) : Prop :=
  IsParallelogram Geo A B C D ∧
  Geo.Congruent A B B C ∧
  Geo.Congruent B C C D ∧
  Geo.Congruent C D D A ∧
  HilbertRightAngle Geo D A B ∧
  HilbertRightAngle Geo A B C ∧
  HilbertRightAngle Geo B C D ∧
  HilbertRightAngle Geo C D A

/--
Local axiom.

In a parallelogram `A B C D`, an angle adjacent to a right angle is
itself right.

This is Euclid's citation of I.29 in the proof of I.46: the side `AB`
is a transversal of the parallels `AD` and `BC`, so the co-interior
angles `∠DAB` and `∠ABC` are together equal to two right angles.  The
library proves I.29 only in an explicit transversal configuration
(`euclid_proposition_29`), and the normalization of the parallelogram
configuration to that form is not yet available as a reusable lemma.
-/
axiom i46_parallelogram_adjacent_right_angle
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D)
    (hRight : HilbertRightAngle Geo D A B) :
    HilbertRightAngle Geo A B C

------------------------------------------------------------------------
-- Auxiliary results
------------------------------------------------------------------------

/--
An endpoint of one of two parallel lines is not collinear with the
other line.

Immediate from the definition of `Geo.Parallel` as disjointness of the
two point-line carriers.
-/
theorem parallel_first_not_collinear
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hParallel : Geo.Parallel A B C D) :
    Not (Collinear Geo A B C) := by

  intro hCol

  rcases hCol with ⟨l, hAl, hBl, hCl⟩

  have hAB : A ≠ B :=
    hParallel.1

  have hC_AB :
      C ∈ Geo.PointLine A B :=
    (hilbert_mem_pointLine_iff_onLine
      Geo A B C l hAB hAl hBl).mpr hCl

  have hC_CD :
      C ∈ Geo.PointLine C D := by
    change Geometry.Geo.LineCollinear Geo C D C
    exact Or.inr (Or.inl rfl)

  exact
    Set.disjoint_left.mp hParallel.2.2
      hC_AB hC_CD

/--
All four vertex triples of a parallelogram are noncollinear.

These are the side conditions required by every angle theorem applied
below.
-/
theorem parallelogram_vertices_noncollinear
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D) :
    Not (Collinear Geo D A B) ∧
    Not (Collinear Geo A B C) ∧
    Not (Collinear Geo B C D) ∧
    Not (Collinear Geo C D A) := by

  have hAB_CD :
      Geo.Parallel A B C D :=
    hParallelogram.1

  have hBC_DA :
      Geo.Parallel B C D A :=
    hParallelogram.2

  ----------------------------------------------------------------
  -- `A B C`
  ----------------------------------------------------------------

  have hABC :
      Not (Collinear Geo A B C) :=
    parallel_first_not_collinear
      Geo A B C D hAB_CD

  ----------------------------------------------------------------
  -- `B C D`
  ----------------------------------------------------------------

  have hBCD :
      Not (Collinear Geo B C D) :=
    parallel_first_not_collinear
      Geo B C D A hBC_DA

  ----------------------------------------------------------------
  -- `C D A`
  ----------------------------------------------------------------

  have hCD_AB :
      Geo.Parallel C D A B :=
    ParallelSymmetry
      Geo A B C D hAB_CD

  have hCDA :
      Not (Collinear Geo C D A) :=
    parallel_first_not_collinear
      Geo C D A B hCD_AB

  ----------------------------------------------------------------
  -- `D A B`
  ----------------------------------------------------------------

  have hDA_BC :
      Geo.Parallel D A B C :=
    ParallelSymmetry
      Geo B C D A hBC_DA

  have hDAB :
      Not (Collinear Geo D A B) :=
    parallel_first_not_collinear
      Geo D A B C hDA_BC

  exact ⟨hDAB, hABC, hBCD, hCDA⟩

/--
Euclid I.11 at an endpoint, together with I.3.

On a given segment `AB` there is a point `D` making a right angle at
`A` with `AB` and satisfying `AD ≅ AB`.

The library's I.11 (`hilbert_right_angle_exists_nondegenerate`) erects
a perpendicular at a point lying strictly between two others, so `BA`
is first extended beyond `A`.  The perpendicular ray is then trimmed to
the required length by Hilbert III,1.
-/
theorem i46_erect_equal_perpendicular
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ D : Geo.Point,
      Not (Collinear Geo A B D) ∧
      HilbertRightAngle Geo D A B ∧
      Geo.Congruent A D A B := by

  have hBA : B ≠ A := hAB.symm

  --------------------------------------------------------------------
  -- Step 1. Extend `BA` beyond `A`, so that I.11 applies at `A`.
  --------------------------------------------------------------------

  rcases
      ExtendSegmentBeyond
        Geo B A hBA with
    ⟨F, hBAF, _hCongBA⟩

  --------------------------------------------------------------------
  -- Step 2. Erect the perpendicular at `A` (Euclid I.11).
  --------------------------------------------------------------------

  rcases
      hilbert_right_angle_exists_nondegenerate
        Geo B A F hBAF with
    ⟨X, hNCBAX, hRightBAX⟩

  have hAX : A ≠ X := by
    intro hEq
    subst hEq
    rcases
        HilbertPlaneIncidence.line_through
          B A hBA with
      ⟨l, hBl, hAl⟩
    exact hNCBAX ⟨l, hBl, hAl, hAl⟩

  --------------------------------------------------------------------
  -- Step 3. Lay off `AB` on the perpendicular ray (Hilbert III,1).
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo) A B A X hAX with
    ⟨D, hRayAXD, hCongAD⟩

  have hDA : D ≠ A :=
    hRayAXD.2.1

  have hAXD :
      Collinear Geo A X D :=
    hRayAXD.2.2.1

  have hADX :
      Collinear Geo A D X :=
    PrimCollinearRotate
      Geo A X D hAXD

  --------------------------------------------------------------------
  -- Step 4. `B A D` is noncollinear, because `D` lies on the ray `AX`.
  --------------------------------------------------------------------

  have hNCBAD :
      Not (Collinear Geo B A D) := by
    intro hCol
    apply hNCBAX
    exact
      hilbert_primCollinear_trans
        Geo B A D X
        hDA.symm
        hCol
        hADX

  have hNCDAB :
      Not (Collinear Geo D A B) := by
    intro hCol
    exact
      hNCBAD
        (PrimCollinearSymm Geo D A B hCol)

  have hNCABD :
      Not (Collinear Geo A B D) := by
    intro hCol
    exact
      hNCBAD
        (PrimCollinearSwap Geo A B D hCol)

  --------------------------------------------------------------------
  -- Step 5. Replacing `X` by `D` does not change the angle at `A`.
  --------------------------------------------------------------------

  have hAngleEq :
      Geo.Angle B A X = Geo.Angle B A D :=
    hilbert_angle_eq_of_sameRay_second
      Geo A B X D hRayAXD

  have hRefl :
      Geo.AngleCongruent B A X B A X :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo) B A X hNCBAX

  have hAngleBAX_BAD :
      Geo.AngleCongruent B A X B A D := by
    unfold Geometry.Geo.AngleCongruent
    rw [← hAngleEq]
    exact hRefl

  have hRightBAD :
      HilbertRightAngle Geo B A D :=
    hilbert_right_angle_transport
      Geo
      B A X
      B A D
      hNCBAX
      hNCBAD
      hRightBAX
      hAngleBAX_BAD

  --------------------------------------------------------------------
  -- Step 6. The angle is unoriented, so the arms may be exchanged.
  --------------------------------------------------------------------

  have hArmSwap :
      Geo.AngleCongruent B A D D A B :=
    bookZero_56_ABCequalsCBA
      Geo B A D hNCBAD

  have hRightDAB :
      HilbertRightAngle Geo D A B :=
    hilbert_right_angle_transport
      Geo
      B A D
      D A B
      hNCBAD
      hNCDAB
      hRightBAD
      hArmSwap

  exact ⟨D, hNCABD, hRightDAB, hCongAD⟩

------------------------------------------------------------------------
-- Euclid I.46
------------------------------------------------------------------------

/--
Euclid, Elements, Book I, Proposition 46.

On a given straight line `AB` to describe a square: for distinct points
`A` and `B` there are points `C` and `D` such that `A B C D` is a
square, the given segment `AB` being one of its sides.
-/
theorem euclid_proposition_46
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ C D : Geo.Point,
      IsSquare Geo A B C D := by

  --------------------------------------------------------------------
  -- Steps 1-2 (I.11, I.3): the perpendicular side `AD` at `A`.
  --------------------------------------------------------------------

  rcases
      i46_erect_equal_perpendicular
        Geo A B hAB with
    ⟨D, hNCABD, hRightDAB, hCongAD_AB⟩

  --------------------------------------------------------------------
  -- Step 3 (I.31): complete the parallelogram.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo A B D hNCABD with
    ⟨C, hParallelogram⟩

  --------------------------------------------------------------------
  -- Step 4 (I.34): all four sides are congruent to `AB`.
  --------------------------------------------------------------------

  have hI34 :=
    euclid_proposition_34
      Geo A B C D hParallelogram

  have hSides :
      OppositeSidesCongruent Geo A B C D :=
    hI34.1

  have hCongDA_AB :
      Geo.Congruent D A A B :=
    CongruentReverseFirst
      Geo A D A B hCongAD_AB

  have hCongBC_AB :
      Geo.Congruent B C A B :=
    hilbert_congruent_transitivity
      Geo B C D A A B
      hSides.2
      hCongDA_AB

  have hCongAB_BC :
      Geo.Congruent A B B C :=
    hilbert_congruent_symmetry
      Geo B C A B hCongBC_AB

  have hCongBC_CD :
      Geo.Congruent B C C D :=
    hilbert_congruent_transitivity
      Geo B C A B C D
      hCongBC_AB
      hSides.1

  have hCongCD_AB :
      Geo.Congruent C D A B :=
    hilbert_congruent_symmetry
      Geo A B C D hSides.1

  have hCongAB_DA :
      Geo.Congruent A B D A :=
    hilbert_congruent_symmetry
      Geo D A A B hCongDA_AB

  have hCongCD_DA :
      Geo.Congruent C D D A :=
    hilbert_congruent_transitivity
      Geo C D A B D A
      hCongCD_AB
      hCongAB_DA

  --------------------------------------------------------------------
  -- Step 5 (I.29 and I.34): all four angles are right.
  --------------------------------------------------------------------

  have hNC :=
    parallelogram_vertices_noncollinear
      Geo A B C D hParallelogram

  have hRightABC :
      HilbertRightAngle Geo A B C :=
    i46_parallelogram_adjacent_right_angle
      Geo A B C D hParallelogram hRightDAB

  have hOppositeAngles :
      OppositeAnglesCongruent Geo A B C D :=
    hI34.2

  have hRightBCD :
      HilbertRightAngle Geo B C D :=
    hilbert_right_angle_transport
      Geo
      D A B
      B C D
      hNC.1
      hNC.2.2.1
      hRightDAB
      hOppositeAngles.1

  have hRightCDA :
      HilbertRightAngle Geo C D A :=
    hilbert_right_angle_transport
      Geo
      A B C
      C D A
      hNC.2.1
      hNC.2.2.2
      hRightABC
      hOppositeAngles.2

  --------------------------------------------------------------------
  -- The described figure is a square on `AB`.
  --------------------------------------------------------------------

  exact
    ⟨C, D,
      hParallelogram,
      hCongAB_BC,
      hCongBC_CD,
      hCongCD_DA,
      hRightDAB,
      hRightABC,
      hRightBCD,
      hRightCDA⟩

/--
The square produced by I.46 has the given segment `AB` as a side, and
that side is congruent to the perpendicular side `DA` erected at `A`.

This is the form in which I.46 is used in I.47.
-/
theorem euclid_proposition_46_side
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hSquare : IsSquare Geo A B C D) :
    Geo.Congruent A B B C ∧
    Geo.Congruent A B C D ∧
    Geo.Congruent A B D A := by

  refine ⟨hSquare.2.1, ?_, ?_⟩

  · exact
      hilbert_congruent_transitivity
        Geo A B B C C D
        hSquare.2.1
        hSquare.2.2.1

  · have hAB_CD :
        Geo.Congruent A B C D :=
      hilbert_congruent_transitivity
        Geo A B B C C D
        hSquare.2.1
        hSquare.2.2.1
    exact
      hilbert_congruent_transitivity
        Geo A B C D D A
        hAB_CD
        hSquare.2.2.2.1

end Geometry

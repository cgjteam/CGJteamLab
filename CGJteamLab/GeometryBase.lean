import CGJteamLab.HilbertAxioms

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

variable [HilbertIncidence Geo]

/-!
# GeometryBase

Fundamental geometric language for the CGJteam Lab project.

The library is organized by mathematical concepts rather than by
historical axiom systems or individual proofs.

Each section introduces reusable notions that serve as building
blocks for higher-level geometric theories.

Declarations headed `Previous provisional declaration` are retained
inside block comments as historical API records; they are not active
axioms.  See `docs/HilbertDerivations.md` for the mathematical source,
proof dependency, and downstream role of every replacement.
-/

------------------------------------------------------------------------
-- Part I. Basic Definitions
------------------------------------------------------------------------

abbrev Collinear
    (A B C : Geo.Point) : Prop :=
  PrimCollinear Geo A B C


def IsMidpoint
    (M A B : Geo.Point) : Prop :=
  Collinear Geo A M B ∧
  Geo.Congruent A M M B


/--
A midpoint in Hilbert's strict order language: `M` lies between the
distinct endpoints and the two component segments are congruent.
-/
def HilbertIsMidpoint
    (M A B : Geo.Point) : Prop :=
  Geo.Between A M B ∧
  Geo.Congruent A M M B


def IsIntersection
    (A B C D P : Geo.Point) : Prop :=
  Collinear Geo A P B ∧
  Collinear Geo C P D


def IsMedian
    (_ M B C : Geo.Point) : Prop :=
  IsMidpoint Geo M B C


def OppositeSidesParallel
    (A B C D : Geo.Point) : Prop :=
  Geo.Parallel A B C D ∧
  Geo.Parallel B C D A


def OppositeSidesCongruent
    (A B C D : Geo.Point) : Prop :=
  Geo.Congruent A B C D ∧
  Geo.Congruent B C D A


def IsParallelogram
    (A B C D : Geo.Point) : Prop :=
  OppositeSidesParallel Geo A B C D


------------------------------------------------------------------------
-- Part II. Elementary Derived Results
------------------------------------------------------------------------

theorem midpoint_collinear
    (A B M : Geo.Point) :
    IsMidpoint Geo M A B →
    Collinear Geo A M B := by
  intro h
  exact h.left


theorem midpoint_of_hilbert
    [HilbertOrder Geo]
    (M A B : Geo.Point) :
    HilbertIsMidpoint Geo M A B →
    IsMidpoint Geo M A B := by
  intro h
  constructor
  · exact
      (HilbertOrder.between_incidence
        A M B h.left).2.2.2.1
  · exact h.right


omit [HilbertIncidence Geo] in
theorem hilbert_midpoint_between
    (M A B : Geo.Point) :
    HilbertIsMidpoint Geo M A B →
    Geo.Between A M B := by
  intro h
  exact h.left


theorem MidpointMedian
    (A B C M : Geo.Point) :
    IsMidpoint Geo M B C →
    IsMedian Geo A M B C := by
  intro h
  exact h

------------------------------------------------------------------------
-- Part III. Collinearity
------------------------------------------------------------------------

/-
Previous provisional declaration:

axiom CollinearSymmetry
    (A B C : Geo.Point) :
    Collinear Geo A B C →
    Collinear Geo C B A
-/

/--
The former symmetry axiom is only a permutation of the three incidence
witnesses in `PrimCollinear`; it needs no geometric axiom beyond the
incidence relation used by `Collinear`.
-/
theorem CollinearSymmetry
    (A B C : Geo.Point) :
    Collinear Geo A B C →
    Collinear Geo C B A := by
  exact PrimCollinearSymm Geo A B C


theorem CollinearRotate
    (A B C : Geo.Point) :
    Collinear Geo A B C →
    Collinear Geo A C B := by
  exact PrimCollinearRotate Geo A B C


/-
Previous provisional declaration:

axiom CollinearTrans
    (A G P D : Geo.Point) :
    Collinear Geo A G P →
    Collinear Geo P D G →
    Collinear Geo A G D
-/

/--
Incidence consequence of Hilbert I.2.  The shared distinct points `G`
and `P` force the two witnessing lines to coincide.
-/
theorem CollinearTrans
    [HilbertPlaneIncidence Geo]
    (A G P D : Geo.Point)
    (hGP : G ≠ P) :
    Collinear Geo A G P →
    Collinear Geo P D G →
    Collinear Geo A G D := by
  intro hAGP hPDG
  have hGPD : Collinear Geo G P D :=
    PrimCollinearRotate Geo G D P
      (PrimCollinearSymm Geo P D G hPDG)
  exact
    hilbert_primCollinear_trans
      Geo A G P D hGP hAGP hGPD


------------------------------------------------------------------------
-- Part IV. Congruence
------------------------------------------------------------------------

/-
Previous provisional declaration:

axiom CongruentSymmetry
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent C D A B
-/

/--
Symmetry of segment congruence, derived from Hilbert III.1--III.2 as
described immediately after III.2 in the second English edition.
-/
theorem CongruentSymmetry
    [HilbertCongruence Geo]
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent C D A B := by
  exact hilbert_congruent_symmetry Geo A B C D


/-
Previous provisional declaration:

axiom CongruentReverseFirst
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent B A C D
-/

omit [HilbertIncidence Geo] in
/--
Reversing the endpoints of the first segment changes no mathematical
object because `Geo.Segment` is represented by `Sym2`.
-/
theorem CongruentReverseFirst
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent B A C D := by
  exact (Geometry.Geo.congruent_reverse_first Geo A B C D).mp


/-
Previous provisional declaration:

axiom CongruentReverseBoth
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent B A D C
-/

omit [HilbertIncidence Geo] in
/--
Endpoint reversal on both segments, obtained definitionally from their
unordered `Sym2` representation.
-/
theorem CongruentReverseBoth
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent B A D C := by
  intro h
  exact
    (Geometry.Geo.congruent_reverse_second Geo B A C D).mp
      ((Geometry.Geo.congruent_reverse_first Geo A B C D).mp h)


/-
Previous provisional declaration:

axiom CongruentSwapSecond
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent A B D C
-/

omit [HilbertIncidence Geo] in
/--
Endpoint reversal on the second segment.  This is representational,
not an additional congruence axiom.
-/
theorem CongruentSwapSecond
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent A B D C := by
  intro h
  exact
    CongruentReverseFirst Geo B A D C
      (CongruentReverseBoth Geo A B C D h)


------------------------------------------------------------------------
-- Part V. Angle Congruence
------------------------------------------------------------------------

/-
Previous provisional declaration:

axiom AngleCongruentReverse
    (A B C D E F : Geo.Point) :
    Geo.AngleCongruent A B C D E F →
    Geo.AngleCongruent C B A F E D
-/

omit [HilbertIncidence Geo] in
/--
Reversing both sides of each angle changes no angle because
`Geo.Angle` is an unordered pair of rays with a common vertex.
-/
theorem AngleCongruentReverse
    (A B C D E F : Geo.Point) :
    Geo.AngleCongruent A B C D E F →
    Geo.AngleCongruent C B A F E D := by
  intro h
  exact
    (Geometry.Geo.angle_congruent_reverse_second
      Geo C B A D E F).mp
      ((Geometry.Geo.angle_congruent_reverse_first
        Geo A B C D E F).mp h)


/-
Previous provisional declaration:

axiom VerticalAngles
    (C E D B F : Geo.Point) :
    Collinear Geo C E B →
    Collinear Geo D E F →
    Geo.AngleCongruent C E D B E F
-/

/--
The vertical-angle corollary of Hilbert's Theorem 14.  Strict
betweenness exposes the two pairs of opposite rays, while
noncollinearity excludes degenerate angles.
-/
theorem VerticalAngles
    [HilbertCongruence Geo]
    (C E D B F : Geo.Point) :
    Geo.Between C E B →
    Geo.Between D E F →
    ¬ Collinear Geo C E D →
    Geo.AngleCongruent C E D B E F := by
  exact hilbert_vertical_angles Geo C E D B F

------------------------------------------------------------------------
-- Part VI. Parallelism
------------------------------------------------------------------------

/-
Previous provisional declaration:

axiom ParallelSymmetry
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel C D A B
-/

omit [HilbertIncidence Geo] in
/--
Symmetry of disjoint extensional point-lines.  This follows directly
from the definition of `Geo.Parallel`.
-/
theorem ParallelSymmetry
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel C D A B := by
  exact (Geometry.Geo.parallel_symmetry Geo A B C D).mp


/-
Previous provisional declaration:

axiom ParallelSwapFirstLine
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel B A C D
-/

omit [HilbertIncidence Geo] in
/--
Reversing the two determining points of the first line preserves its
extensional carrier and hence preserves parallelism.
-/
theorem ParallelSwapFirstLine
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel B A C D := by
  exact (Geometry.Geo.parallel_swap_first Geo A B C D).mp


/-
Previous provisional declaration:

axiom ParallelSwapSecondLine
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel A B D C
-/

omit [HilbertIncidence Geo] in
/--
Reversing the two determining points of the second line preserves its
extensional carrier and hence preserves parallelism.
-/
theorem ParallelSwapSecondLine
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel A B D C := by
  exact (Geometry.Geo.parallel_swap_second Geo A B C D).mp


/-
Previous provisional declaration:

axiom ParallelCollinearLeft
    (A B C D E : Geo.Point) :
    Geo.Parallel A B D E →
    Collinear Geo C A B →
    Geo.Parallel C B D E
-/

/--
Transport parallelism to another nondegenerate pair on the same
Hilbert line.  Incidence uniqueness and Hilbert's Theorem 4 identify
the two extensional `PointLine` carriers.
-/
theorem ParallelCollinearLeft
    [HilbertOrder Geo]
    (A B C D E : Geo.Point)
    (hCB : C ≠ B) :
    Geo.Parallel A B D E →
    Collinear Geo C A B →
    Geo.Parallel C B D E := by
  intro hParallel hCollinear
  rcases hParallel with ⟨hAB, hDE, hConfiguration⟩
  rcases hCollinear with ⟨l, hCl, hAl, hBl⟩
  have hPointLine :
      Geo.PointLine A B = Geo.PointLine C B :=
    hilbert_pointLine_eq_of_points_on_line
      Geo A B C B l hAB hCB hAl hBl hCl hBl
  refine ⟨hCB, hDE, ?_⟩
  exact hPointLine ▸ hConfiguration


/-
Previous provisional declaration:

axiom collinear_parallel_trans
    (A B C D E : Geo.Point) :
    Collinear Geo A B C →
    Geo.Parallel A C D E →
    Geo.Parallel A B D E
-/

/--
The companion transport theorem for replacing the second determining
point on the left line.  The proof again reduces to equality of the
two extensional point-line carriers.
-/
theorem collinear_parallel_trans
    [HilbertOrder Geo]
    (A B C D E : Geo.Point)
    (hAB : A ≠ B) :
    Collinear Geo A B C →
    Geo.Parallel A C D E →
    Geo.Parallel A B D E := by
  intro hCollinear hParallel
  rcases hCollinear with ⟨l, hAl, hBl, hCl⟩
  rcases hParallel with ⟨hAC, hDE, hConfiguration⟩
  have hPointLine :
      Geo.PointLine A C = Geo.PointLine A B :=
    hilbert_pointLine_eq_of_points_on_line
      Geo A C A B l hAC hAB hAl hCl hAl hBl
  refine ⟨hAB, hDE, ?_⟩
  exact hPointLine ▸ hConfiguration


/-
Previous provisional declaration:

axiom parallel_from_equal_angles
    (A C D B E F : Geo.Point) :
    Collinear Geo A C D →
    Geo.AngleCongruent E C D E B F →
    Geo.Parallel A D B F
-/

/--
The equal-alternate-angles direction of Hilbert's Theorem 30.
This direction is neutral: it follows from the non-equality part of
the exterior-angle theorem (Theorem 22) and does not use axiom IV.
-/
theorem parallel_from_equal_angles
    [HilbertCongruence Geo]
    (A C D B E F : Geo.Point)
    (hADC : Geo.Between A D C)
    (hCEB : Geo.Between C E B)
    (hDEF : Geo.Between D E F)
    (hCED : ¬ Collinear Geo C E D) :
    Geo.AngleCongruent E C D E B F →
    Geo.Parallel A D B F := by
  exact
    hilbert_parallel_of_alternate_angles
      Geo A C D B E F
      hADC hCEB hDEF hCED

/--
The Euclidean direction of Hilbert's Theorem 30: parallel lines cut
by a transversal make congruent alternate interior angles.

Unlike `parallel_from_equal_angles`, this direction explicitly
requires `HilbertEuclideanPlane`, hence Hilbert's axiom IV.
-/
theorem equal_angles_from_parallel
    [HilbertEuclideanPlane Geo]
    (A C D B E F : Geo.Point)
    (hADC : Geo.Between A D C)
    (hCEB : Geo.Between C E B)
    (hDEF : Geo.Between D E F)
    (hCED : ¬ Collinear Geo C E D) :
    Geo.Parallel A D B F →
    Geo.AngleCongruent E C D E B F := by
  exact
    hilbert_alternate_angles_of_parallel
      Geo A C D B E F
      hADC hCEB hDEF hCED


------------------------------------------------------------------------
-- Part VII. Geometric Constructions
------------------------------------------------------------------------

/-
Previous provisional declaration:

axiom ExtendSegment
    (A B : Geo.Point) :
    ∃ T : Geo.Point,
      Collinear Geo A B T ∧
      Geo.Congruent A B B T
-/

/--
Lay off a copy of `AB` beyond `B`.  For distinct endpoints the proof
combines order extension II.2 with segment construction III.1; the
degenerate case follows from reflexivity of segment congruence.
-/
theorem ExtendSegment
    [HilbertCongruence Geo]
    (A B : Geo.Point) :
    ∃ T : Geo.Point,
      Collinear Geo A B T ∧
      Geo.Congruent A B B T := by
  exact hilbert_extend_segment Geo A B

theorem ExtendSegmentDistinct
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ T : Geo.Point,
      Collinear Geo A B T ∧
      Geo.Congruent A B B T ∧
      B ≠ T := by
  exact hilbert_extend_segment_distinct Geo A B hAB


theorem ExtendSegmentBeyond
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ T : Geo.Point,
      Geo.Between A B T ∧
      Geo.Congruent A B B T := by
  exact hilbert_extend_segment_beyond Geo A B hAB


/-
Previous provisional declaration:

axiom IntersectionOnSameLine
    (A G P B C D : Geo.Point) :
    Collinear Geo A G P →
    IsIntersection Geo A P B C D →
    IsIntersection Geo P G B C D
-/

/--
Changing the named pair that determines an intersection line.
Hilbert I.2 identifies the two lines through the distinct points
`A` and `P`.
-/
theorem IntersectionOnSameLine
    [HilbertPlaneIncidence Geo]
    (A G P B C D : Geo.Point)
    (hAP : A ≠ P) :
    Collinear Geo A G P →
    IsIntersection Geo A P B C D →
    IsIntersection Geo P G B C D := by
  intro hAGP hInt
  rcases hAGP with ⟨l, hAl, hGl, hPl⟩
  rcases hInt.left with ⟨m, hAm, hDm, hPm⟩
  have hlm : l = m :=
    HilbertPlaneIncidence.line_unique
      A P hAP l m hAl hPl hAm hPm
  have hDl : HilbertIncidence.OnLine D l := by
    rw [hlm]
    exact hDm
  constructor
  · exact ⟨l, hPl, hDl, hGl⟩
  · exact hInt.right


/-
Previous provisional declaration:

axiom congruent_transitivity
    (A D C B F : Geo.Point) :
    Geo.Congruent A D D C →
    Geo.Congruent C D B F →
    Geo.Congruent A D B F
-/

/--
The project-specific orientation of transitivity of segment
congruence, derived from Hilbert III.1--III.2 plus the unordered
segment representation.
-/
theorem congruent_transitivity
    [HilbertCongruence Geo]
    (A D C B F : Geo.Point) :
    Geo.Congruent A D D C →
    Geo.Congruent C D B F →
    Geo.Congruent A D B F := by
  intro h₁ h₂
  exact
    hilbert_congruent_transitivity Geo A D C D B F
      (CongruentSwapSecond Geo A D D C h₁)
      h₂


------------------------------------------------------------------------
-- Part VIII. Triangle Congruence
------------------------------------------------------------------------

structure TriangleCongruenceResult
    (A B C D E F : Geo.Point) where
  sideAB : Geo.Congruent A B D E
  sideBC : Geo.Congruent B C E F
  sideAC : Geo.Congruent A C D F
  angleA : Geo.AngleCongruent B A C E D F
  angleB : Geo.AngleCongruent A B C D E F
  angleC : Geo.AngleCongruent A C B D F E


/-
Previous provisional declaration:

axiom SAS
    (A B C D E F : Geo.Point) :
    Geo.Congruent A B D E →
    Geo.AngleCongruent B A C E D F →
    Geo.Congruent A C D F →
    TriangleCongruenceResult Geo A B C D E F
-/

/--
Hilbert's Theorem 12 in the form used by the project.

Only the third side and the angle at `C` require the derived
construction argument; the remaining fields are hypotheses or direct
consequences of III.5.
-/
theorem SAS
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point) :
    ¬ Collinear Geo A B C →
    ¬ Collinear Geo D E F →
    Geo.Congruent A B D E →
    Geo.AngleCongruent B A C E D F →
    Geo.Congruent A C D F →
    TriangleCongruenceResult Geo A B C D E F := by
  intro hABC hDEF hAB hAngleA hAC
  have hAngles :=
    hilbert_sas_remaining_angles
      Geo A B C D E F hABC hDEF hAB hAC hAngleA
  have hNeeded :=
    hilbert_sas_third_side_and_angle
      Geo A B C D E F hABC hDEF hAB hAC hAngleA
  exact
    { sideAB := hAB
      sideBC := hNeeded.1
      sideAC := hAC
      angleA := hAngleA
      angleB := hAngles.1
      angleC := hNeeded.2 }


/-
Previous provisional declaration:

axiom TriangleCongruentFromSAS
    (A B C D E F : Geo.Point) :
    Geo.Congruent A B D E →
    Geo.AngleCongruent B A C E D F →
    Geo.Congruent A C D F →
    TriangleCongruenceResult Geo A B C D E F
-/

/--
Compatibility name for `SAS`, the formalized form of Hilbert's
Theorem 12.  The explicit noncollinearity hypotheses record Hilbert's
standing convention that triangle vertices are noncollinear.
-/
theorem TriangleCongruentFromSAS
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point) :
    ¬ Collinear Geo A B C →
    ¬ Collinear Geo D E F →
    Geo.Congruent A B D E →
    Geo.AngleCongruent B A C E D F →
    Geo.Congruent A C D F →
    TriangleCongruenceResult Geo A B C D E F := by
  exact SAS Geo A B C D E F
------------------------------------------------------------------------
-- Part IX. Parallelogram Theory
------------------------------------------------------------------------

/-!
A parallelogram is recognized from one pair of opposite sides that are
both parallel and congruent. Once recognized, the standard properties
of parallelograms become available as reusable geometric tools.
-/

------------------------------------------------------------------------
-- Recognition Criterion
------------------------------------------------------------------------

structure OnePairParallelCongruent
    (A B C D : Geo.Point) where
  parallel : Geo.Parallel A D B C
  congruent : Geo.Congruent A D B C
  /--
  The endpoint correspondence is not crossed: `A` and `B` lie on the
  same side of the line through `D` and `C`.

  Without this orientation condition the recognition statement is
  false even in the Euclidean plane (a bow-tie quadrilateral is a
  counterexample).
  -/
  oriented :
    ∃ l : Geo.Line,
      HilbertIncidence.OnLine D l ∧
      HilbertIncidence.OnLine C l ∧
      HilbertSameSide Geo A B l

/--
Build the correctly oriented recognition data from the crossing
configuration used in the Midsegment Theorem.

The points satisfy `A-D-P`, `P-Y-B`, and `D-Y-C`.  Thus the line `DC`
meets the interiors of two sides of triangle `PAB`; Pasch separation
puts `A` and `B` on the same side of that line.  The noncollinearity of
`Y,D,P` implies that `P,A,B` is a genuine triangle.
-/
theorem onePairParallelCongruent_of_crossing
    [HilbertOrder Geo]
    (A B C D P Y : Geo.Point)
    (hADP : Geo.Between A D P)
    (hPYB : Geo.Between P Y B)
    (hDYC : Geo.Between D Y C)
    (hYDP : ¬ Collinear Geo Y D P)
    (hParallel : Geo.Parallel A D B C)
    (hCongruent : Geo.Congruent A D B C) :
    OnePairParallelCongruent Geo A B C D := by
  have hPAB : ¬ Collinear Geo P A B := by
    rintro ⟨side, hPside, hAside, hBside⟩
    have hDside : HilbertIncidence.OnLine D side :=
      hilbert_between_on_line
        Geo A D P side hAside hPside hADP
    have hYside : HilbertIncidence.OnLine Y side :=
      hilbert_between_on_line
        Geo P Y B side hPside hBside hPYB
    exact hYDP ⟨side, hYside, hDside, hPside⟩
  have hDYCData := HilbertOrder.between_incidence D Y C hDYC
  rcases hDYCData.2.2.2.1 with ⟨cross, hDcross, hYcross, hCcross⟩
  have hPDA : Geo.Between P D A :=
    (HilbertOrder.between_incidence A D P hADP).2.2.2.2
  have hSameSide : HilbertSameSide Geo A B cross :=
    hilbert_third_side_endpoints_sameSide
      Geo P A B D Y cross
      hPAB hPDA hPYB hDcross hYcross
  exact
    { parallel := hParallel
      congruent := hCongruent
      oriented := ⟨cross, hDcross, hCcross, hSameSide⟩ }


/--
The diagonal-separation consequence of the corrected orientation.

For a correctly oriented pair of parallel congruent sides `AD` and
`BC`, the opposite vertices `A` and `C` lie on opposite sides of the
diagonal `DB`.  Otherwise copy `AD` to the ray opposite `DA`, obtaining
`A-D-A'`.  The Euclidean direction of Theorem 30 and SAS show that
`A'B ∥ DC`; hence `A'` and `B` lie on the same side of `DC`.  Together
with the recorded same-side relation between `A` and `B`, this
contradicts the fact that `A-D-A'` crosses `DC`.
-/
theorem onePair_diagonal_oppositeSide
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hData : OnePairParallelCongruent Geo A B C D) :
    ∃ diagonal : Geo.Line,
      HilbertIncidence.OnLine D diagonal ∧
      HilbertIncidence.OnLine B diagonal ∧
      HilbertOppositeSide Geo A C diagonal := by
  rcases hData.oriented with
    ⟨base, hDbase, hCbase, hABSame⟩
  have hAD : A ≠ D := hData.parallel.1
  have hBC : B ≠ C := hData.parallel.2.1
  rcases HilbertPlaneIncidence.line_through A D hAD with
    ⟨line₁, hA₁, hD₁⟩
  rcases HilbertPlaneIncidence.line_through B C hBC with
    ⟨line₂, hB₂, hC₂⟩
  have hLinesDisjoint :
      HilbertLinesDisjoint Geo line₁ line₂ := by
    rintro ⟨X, hX₁, hX₂⟩
    have hXAD : X ∈ Geo.PointLine A D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A D X line₁ hAD hA₁ hD₁).mpr hX₁
    have hXBC : X ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X line₂ hBC hB₂ hC₂).mpr hX₂
    exact Set.disjoint_left.mp hData.parallel.2.2 hXAD hXBC
  have hBline₁ : ¬ HilbertIncidence.OnLine B line₁ := by
    intro h
    exact hLinesDisjoint ⟨B, h, hB₂⟩
  have hCline₁ : ¬ HilbertIncidence.OnLine C line₁ := by
    intro h
    exact hLinesDisjoint ⟨C, h, hC₂⟩
  have hAline₂ : ¬ HilbertIncidence.OnLine A line₂ := by
    intro h
    exact hLinesDisjoint ⟨A, hA₁, h⟩
  have hDline₂ : ¬ HilbertIncidence.OnLine D line₂ := by
    intro h
    exact hLinesDisjoint ⟨D, hD₁, h⟩
  have hDB : D ≠ B := by
    intro h
    subst B
    exact hDline₂ hB₂
  have hDC : D ≠ C := by
    intro h
    subst C
    exact hDline₂ hC₂
  rcases HilbertPlaneIncidence.line_through D B hDB with
    ⟨diagonal, hDdiag, hBdiag⟩
  have hAdiag : ¬ HilbertIncidence.OnLine A diagonal := by
    intro hAdiag
    have hEq : line₁ = diagonal :=
      HilbertPlaneIncidence.line_unique
        A D hAD line₁ diagonal
        hA₁ hD₁ hAdiag hDdiag
    exact hBline₁ (hEq ▸ hBdiag)
  have hCdiag : ¬ HilbertIncidence.OnLine C diagonal := by
    intro hCdiag
    have hEq : line₂ = diagonal :=
      HilbertPlaneIncidence.line_unique
        B C hBC line₂ diagonal
        hB₂ hC₂ hBdiag hCdiag
    exact hDline₂ (hEq ▸ hDdiag)
  by_cases hACMeets :
      HilbertSegmentMeetsLine Geo A C diagonal
  · exact
      ⟨diagonal, hDdiag, hBdiag,
        hAdiag, hCdiag, hACMeets⟩
  · have hACSame :
        HilbertSameSide Geo A C diagonal :=
      ⟨hAdiag, hCdiag,
        Relation.ReflTransGen.single
          ⟨hAdiag, hCdiag, hACMeets⟩⟩
    rcases HilbertOrder.between_extension A D hAD with
      ⟨R, hADR⟩
    have hADRData := HilbertOrder.between_incidence A D R hADR
    rcases HilbertCongruence.segment_construction
        (Geo := Geo) A D D R hADRData.2.1 with
      ⟨A', hRA', hDA'_AD⟩
    have hAA :
        HilbertSameRay Geo D A A :=
      hilbert_sameRay_refl Geo D A hAD
    have hADA' : Geo.Between A D A' :=
      hilbert_between_transport_sameRays
        Geo A D R A A' hADR hAA hRA'
    have hADA'Data :=
      HilbertOrder.between_incidence A D A' hADA'
    have hDA' : D ≠ A' := hADA'Data.2.1
    have hA'₁ : HilbertIncidence.OnLine A' line₁ :=
      hilbert_collinear_on_line
        Geo A D A' line₁ hAD
        hA₁ hD₁ hADA'Data.2.2.2.1
    have hA'diag :
        ¬ HilbertIncidence.OnLine A' diagonal := by
      intro hA'diag
      have hEq : line₁ = diagonal :=
        HilbertPlaneIncidence.line_unique
          D A' hDA' line₁ diagonal
          hD₁ hA'₁ hDdiag hA'diag
      exact hBline₁ (hEq ▸ hBdiag)
    have hOppositeAA' :
        HilbertOppositeSide Geo A A' diagonal :=
      ⟨hAdiag, hA'diag, ⟨D, hADA', hDdiag⟩⟩
    have hOppositeA'A :
        HilbertOppositeSide Geo A' A diagonal :=
      hilbert_oppositeSide_symm
        Geo A A' diagonal hOppositeAA'
    have hOppositeA'C :
        HilbertOppositeSide Geo A' C diagonal :=
      hilbert_oppositeSide_transport_right
        Geo A' A C diagonal hOppositeA'A hACSame
    have hPointLine :
        Geo.PointLine A D = Geo.PointLine D A' :=
      hilbert_pointLine_eq_of_points_on_line
        Geo A D D A' line₁
        hAD hDA' hA₁ hD₁ hD₁ hA'₁
    have hParallelDA'_BC :
        Geo.Parallel D A' B C :=
      ⟨hDA', hBC, hPointLine ▸ hData.parallel.2.2⟩
    rcases hilbert_between_exists Geo D B hDB with
      ⟨E, hDEB⟩
    have hBED : Geo.Between B E D :=
      (HilbertOrder.between_incidence D E B hDEB).2.2.2.2
    have hAngleParallel :
        Geo.AngleCongruent E D A' E B C :=
      hilbert_alternate_angles_of_parallel_oppositeSide_lines
        Geo D A' B E C diagonal
        hDEB hDdiag hBdiag
        hOppositeA'C hParallelDA'_BC
    have hDESame : HilbertSameRay Geo D E B :=
      hilbert_sameRay_of_between Geo D E B hDEB
    have hBESame : HilbertSameRay Geo B E D :=
      hilbert_sameRay_of_between Geo B E D hBED
    have hFirstAngle :
        Geo.Angle E D A' = Geo.Angle B D A' :=
      hilbert_angle_eq_of_sameRay_first
        Geo D E B A' hDESame
    have hSecondAngle :
        Geo.Angle E B C = Geo.Angle D B C :=
      hilbert_angle_eq_of_sameRay_first
        Geo B E D C hBESame
    have hBDA'_DBC :
        Geo.AngleCongruent B D A' D B C := by
      unfold Geometry.Geo.AngleCongruent at hAngleParallel ⊢
      rw [← hFirstAngle, ← hSecondAngle]
      exact hAngleParallel
    have hA'DB_CBD :
        Geo.AngleCongruent A' D B C B D :=
      (Geo.angle_congruent_reverse_second
        A' D B D B C).mp
        ((Geo.angle_congruent_reverse_first
          B D A' D B C).mp hBDA'_DBC)
    have hDA'_BC :
        Geo.Congruent D A' B C :=
      hilbert_congruent_transitivity
        Geo D A' A D B C
        hDA'_AD hData.congruent
    have hDB_BD :
        Geo.Congruent D B B D :=
      (Geo.congruent_reverse_second
        D B D B).mp
        (hilbert_congruent_reflexive Geo D B)
    have hDA'B :
        ¬ Collinear Geo D A' B :=
      hilbert_not_collinear_of_off_line
        Geo D A' B line₁ hDA'
        hD₁ hA'₁ hBline₁
    have hBCD :
        ¬ Collinear Geo B C D :=
      hilbert_not_collinear_of_off_line
        Geo B C D line₂ hBC
        hB₂ hC₂ hDline₂
    have hTriangles :=
      hilbert_sas_remaining_angles
        Geo D A' B B C D
        hDA'B hBCD
        hDA'_BC hDB_BD hA'DB_CBD
    have hDBA'_BDC :
        Geo.AngleCongruent D B A' B D C :=
      hTriangles.2
    have hAtB :
        Geo.Angle E B A' = Geo.Angle D B A' :=
      hilbert_angle_eq_of_sameRay_first
        Geo B E D A' hBESame
    have hAtD :
        Geo.Angle E D C = Geo.Angle B D C :=
      hilbert_angle_eq_of_sameRay_first
        Geo D E B C hDESame
    have hAlternate :
        Geo.AngleCongruent E B A' E D C := by
      unfold Geometry.Geo.AngleCongruent
        at hDBA'_BDC ⊢
      rw [hAtB, hAtD]
      exact hDBA'_BDC
    have hParallelBA'_DC :
        Geo.Parallel B A' D C :=
      hilbert_parallel_of_alternate_angles_oppositeSide_lines
        Geo B A' D E C diagonal
        hBED hBdiag hDdiag
        hOppositeA'C hAlternate
    rcases HilbertPlaneIncidence.line_through B A'
        hParallelBA'_DC.1 with
      ⟨upper, hBupper, hA'upper⟩
    have hA'base :
        ¬ HilbertIncidence.OnLine A' base := by
      intro hA'base
      have hA'BA :
          A' ∈ Geo.PointLine B A' :=
        (hilbert_mem_pointLine_iff_onLine
          Geo B A' A' upper
          hParallelBA'_DC.1 hBupper hA'upper).mpr hA'upper
      have hA'DC :
          A' ∈ Geo.PointLine D C :=
        (hilbert_mem_pointLine_iff_onLine
          Geo D C A' base hDC
          hDbase hCbase).mpr hA'base
      exact
        Set.disjoint_left.mp hParallelBA'_DC.2.2
          hA'BA hA'DC
    have hBbase :
        ¬ HilbertIncidence.OnLine B base := by
      intro hBbase
      have hBBA :
          B ∈ Geo.PointLine B A' :=
        (hilbert_mem_pointLine_iff_onLine
          Geo B A' B upper
          hParallelBA'_DC.1 hBupper hA'upper).mpr hBupper
      have hBDC :
          B ∈ Geo.PointLine D C :=
        (hilbert_mem_pointLine_iff_onLine
          Geo D C B base hDC
          hDbase hCbase).mpr hBbase
      exact
        Set.disjoint_left.mp hParallelBA'_DC.2.2
          hBBA hBDC
    have hNoMeetA'B :
        ¬ HilbertSegmentMeetsLine Geo A' B base := by
      rintro ⟨X, hA'XB, hXbase⟩
      have hXupper :
          HilbertIncidence.OnLine X upper :=
        hilbert_between_on_line
          Geo A' X B upper hA'upper hBupper hA'XB
      have hXBA :
          X ∈ Geo.PointLine B A' :=
        (hilbert_mem_pointLine_iff_onLine
          Geo B A' X upper
          hParallelBA'_DC.1 hBupper hA'upper).mpr hXupper
      have hXDC :
          X ∈ Geo.PointLine D C :=
        (hilbert_mem_pointLine_iff_onLine
          Geo D C X base hDC
          hDbase hCbase).mpr hXbase
      exact
        Set.disjoint_left.mp hParallelBA'_DC.2.2
          hXBA hXDC
    have hA'BSame :
        HilbertSameSide Geo A' B base :=
      ⟨hA'base, hBbase,
        Relation.ReflTransGen.single
          ⟨hA'base, hBbase, hNoMeetA'B⟩⟩
    have hBA'Same :
        HilbertSameSide Geo B A' base :=
      hilbert_sameSide_symm
        Geo A' B base hA'BSame
    have hAA'Same :
        HilbertSameSide Geo A A' base :=
      hilbert_sameSide_trans
        Geo A B A' base hABSame hBA'Same
    have hOppositeAA'Base :
        HilbertOppositeSide Geo A A' base :=
      ⟨hABSame.1, hA'base,
        ⟨D, hADA', hDbase⟩⟩
    exact False.elim
      ((hilbert_oppositeSide_not_sameSide
        Geo A A' base hOppositeAA'Base) hAA'Same)


/-
Rejected under-specified version:

structure OnePairParallelCongruent
    (A B C D : Geo.Point) where
  parallel : Geo.Parallel A D B C
  congruent : Geo.Congruent A D B C

axiom OnePairParallelCongruentCriterion
    (A B C D : Geo.Point) :
    OnePairParallelCongruent Geo A B C D →
    IsParallelogram Geo A B C D
-/

/--
Recognition principle for a correctly oriented quadrilateral with one
pair of opposite sides parallel and congruent.

The orientation field excludes the crossed configuration admitted by
the former statement.  The proof first obtains the diagonal-side
orientation from `onePair_diagonal_oppositeSide`.  The Euclidean
direction of Theorem 30 and SAS then make the other pair of opposite
sides parallel.  This is a Euclidean Hilbert theorem and therefore
requires axiom IV explicitly through `HilbertEuclideanPlane`.
-/
theorem OnePairParallelCongruentCriterion
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point) :
    OnePairParallelCongruent Geo A B C D →
    IsParallelogram Geo A B C D := by
  intro hData
  rcases onePair_diagonal_oppositeSide
      Geo A B C D hData with
    ⟨diagonal, hDdiag, hBdiag, hOppositeAC⟩
  have hDB : D ≠ B := by
    intro h
    subst B
    have hDAD : D ∈ Geo.PointLine A D := by
      change Geometry.Geo.LineCollinear Geo A D D
      exact Or.inr (Or.inr (Or.inl rfl))
    have hDDC : D ∈ Geo.PointLine D C := by
      change Geometry.Geo.LineCollinear Geo D C D
      exact Or.inr (Or.inl rfl)
    exact
      Set.disjoint_left.mp hData.parallel.2.2
        hDAD hDDC
  rcases hilbert_between_exists Geo D B hDB with
    ⟨E, hDEB⟩
  have hBED : Geo.Between B E D :=
    (HilbertOrder.between_incidence D E B hDEB).2.2.2.2
  have hParallelDA_BC :
      Geo.Parallel D A B C :=
    ParallelSwapFirstLine
      Geo A D B C hData.parallel
  have hAngleParallel :
      Geo.AngleCongruent E D A E B C :=
    hilbert_alternate_angles_of_parallel_oppositeSide_lines
      Geo D A B E C diagonal
      hDEB hDdiag hBdiag
      hOppositeAC hParallelDA_BC
  have hDESame : HilbertSameRay Geo D E B :=
    hilbert_sameRay_of_between Geo D E B hDEB
  have hBESame : HilbertSameRay Geo B E D :=
    hilbert_sameRay_of_between Geo B E D hBED
  have hFirstAngle :
      Geo.Angle E D A = Geo.Angle B D A :=
    hilbert_angle_eq_of_sameRay_first
      Geo D E B A hDESame
  have hSecondAngle :
      Geo.Angle E B C = Geo.Angle D B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B E D C hBESame
  have hBDA_DBC :
      Geo.AngleCongruent B D A D B C := by
    unfold Geometry.Geo.AngleCongruent at hAngleParallel ⊢
    rw [← hFirstAngle, ← hSecondAngle]
    exact hAngleParallel
  have hADB_CBD :
      Geo.AngleCongruent A D B C B D :=
    (Geo.angle_congruent_reverse_second
      A D B D B C).mp
      ((Geo.angle_congruent_reverse_first
        B D A D B C).mp hBDA_DBC)
  have hDA_BC :
      Geo.Congruent D A B C :=
    (Geo.congruent_reverse_first
      A D B C).mp hData.congruent
  have hDB_BD :
      Geo.Congruent D B B D :=
    (Geo.congruent_reverse_second
      D B D B).mp
      (hilbert_congruent_reflexive Geo D B)
  have hDBA :
      ¬ Collinear Geo D B A :=
    hilbert_not_collinear_of_off_line
      Geo D B A diagonal hDB
      hDdiag hBdiag hOppositeAC.1
  have hDAB :
      ¬ Collinear Geo D A B :=
    fun h => hDBA (PrimCollinearRotate Geo D A B h)
  have hBDC :
      ¬ Collinear Geo B D C :=
    hilbert_not_collinear_of_off_line
      Geo B D C diagonal hDB.symm
      hBdiag hDdiag hOppositeAC.2.1
  have hBCD :
      ¬ Collinear Geo B C D :=
    fun h => hBDC (PrimCollinearRotate Geo B C D h)
  have hTriangles :=
    hilbert_sas_remaining_angles
      Geo D A B B C D
      hDAB hBCD
      hDA_BC hDB_BD hADB_CBD
  have hDBA_BDC :
      Geo.AngleCongruent D B A B D C :=
    hTriangles.2
  have hAtB :
      Geo.Angle E B A = Geo.Angle D B A :=
    hilbert_angle_eq_of_sameRay_first
      Geo B E D A hBESame
  have hAtD :
      Geo.Angle E D C = Geo.Angle B D C :=
    hilbert_angle_eq_of_sameRay_first
      Geo D E B C hDESame
  have hAlternate :
      Geo.AngleCongruent E B A E D C := by
    unfold Geometry.Geo.AngleCongruent at hDBA_BDC ⊢
    rw [hAtB, hAtD]
    exact hDBA_BDC
  have hParallelBA_DC :
      Geo.Parallel B A D C :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo B A D E C diagonal
      hBED hBdiag hDdiag
      hOppositeAC hAlternate
  have hParallelAB_CD :
      Geo.Parallel A B C D :=
    ParallelSwapSecondLine
      Geo A B D C
      (ParallelSwapFirstLine
        Geo B A D C hParallelBA_DC)
  have hParallelBC_DA :
      Geo.Parallel B C D A :=
    ParallelSwapSecondLine
      Geo B C A D
      (ParallelSymmetry
        Geo A D B C hData.parallel)
  exact ⟨hParallelAB_CD, hParallelBC_DA⟩


------------------------------------------------------------------------
-- Fundamental Properties
------------------------------------------------------------------------

/-
Previous provisional declaration:

axiom ParallelogramOppositeSidesParallel
    (A B C D : Geo.Point) :
    IsParallelogram Geo A B C D →
    OppositeSidesParallel Geo A B C D
-/

omit [HilbertIncidence Geo] in
/--
This former axiom unfolds immediately: `IsParallelogram` is currently
defined to mean `OppositeSidesParallel`.
-/
theorem ParallelogramOppositeSidesParallel
    (A B C D : Geo.Point) :
    IsParallelogram Geo A B C D →
    OppositeSidesParallel Geo A B C D := by
  intro h
  exact h


axiom ParallelogramOppositeSidesCongruent
    (A B C D : Geo.Point) :
    IsParallelogram Geo A B C D →
    OppositeSidesCongruent Geo A B C D


axiom ParallelogramDiagonals
    (A B C D M : Geo.Point) :
    IsParallelogram Geo A B C D →
    Collinear Geo A M C →
    Collinear Geo B M D →
    IsMidpoint Geo M A C


------------------------------------------------------------------------
-- Derived Results
------------------------------------------------------------------------

omit [HilbertIncidence Geo] in
theorem ParallelogramAdjacentParallel
    (A B C D : Geo.Point) :
    IsParallelogram Geo A B C D →
    Geo.Parallel D C A B := by
  intro h

  have hOpp :=
    ParallelogramOppositeSidesParallel Geo A B C D h

  rcases hOpp with ⟨h1, h2⟩

  exact
    ParallelSwapFirstLine
      Geo
      C D A B
      (ParallelSymmetry Geo A B C D h1)


theorem ParallelogramOfParallel
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel A D B C →
    IsParallelogram Geo A B C D := by
  intro h1 h2

  have h2' : Geo.Parallel B C D A := by
    exact
      ParallelSwapSecondLine
        Geo
        B C A D
        (ParallelSymmetry Geo A D B C h2)

  exact And.intro h1 h2'


------------------------------------------------------------------------
-- Helper Theorems
------------------------------------------------------------------------

omit [HilbertIncidence Geo] in
theorem ParallelSymmetrySwapSecond
    (A B C D : Geo.Point)
    (h : Geo.Parallel A D B C) :
    Geo.Parallel B C D A := by
  exact
    ParallelSwapSecondLine
      Geo
      B C A D
      (ParallelSymmetry Geo A D B C h)


omit [HilbertIncidence Geo] in
theorem CongruentReverseFirstSwapSecond
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent B A D C := by
  intro h
  exact
    CongruentSwapSecond
      Geo
      B A C D
      (CongruentReverseFirst Geo A B C D h)

end Geometry

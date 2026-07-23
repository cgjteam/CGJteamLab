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
Provisional recognition principle for a correctly oriented
quadrilateral with one pair of opposite sides parallel and congruent.

The orientation field excludes the crossed configuration admitted by
the former statement.  The declaration remains provisional until its
proof from Hilbert's Euclidean parallel theory is completed.
-/
axiom OnePairParallelCongruentCriterion
    (A B C D : Geo.Point) :
    OnePairParallelCongruent Geo A B C D →
    IsParallelogram Geo A B C D


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

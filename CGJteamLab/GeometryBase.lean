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
axioms.  See the project wiki page `Hilbert-Derivation-Ledger` for the
mathematical source, proof dependency, and downstream role of every
replacement.
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


/--
The two selected points on one of two parallel lines lie on the same
side of the other line.

Indeed, the whole first line is disjoint from the second one, so the
open segment joining its selected points cannot meet the second line.
This small plane-separation result supplies the orientation data needed
by the one-pair parallelogram criterion below.
-/
theorem parallel_endpoints_sameSide
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hParallel : Geo.Parallel A B C D) :
    ∃ l : Geo.Line,
      HilbertIncidence.OnLine C l ∧
      HilbertIncidence.OnLine D l ∧
      HilbertSameSide Geo A B l := by
  rcases HilbertPlaneIncidence.line_through
      A B hParallel.1 with
    ⟨line₁, hA₁, hB₁⟩
  rcases HilbertPlaneIncidence.line_through
      C D hParallel.2.1 with
    ⟨line₂, hC₂, hD₂⟩
  have hLinesDisjoint :
      HilbertLinesDisjoint Geo line₁ line₂ := by
    rintro ⟨X, hX₁, hX₂⟩
    have hXAB : X ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B X line₁ hParallel.1 hA₁ hB₁).mpr hX₁
    have hXCD : X ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D X line₂ hParallel.2.1 hC₂ hD₂).mpr hX₂
    exact
      Set.disjoint_left.mp hParallel.2.2 hXAB hXCD
  have hA₂ : ¬ HilbertIncidence.OnLine A line₂ := by
    intro hA₂
    exact hLinesDisjoint ⟨A, hA₁, hA₂⟩
  have hB₂ : ¬ HilbertIncidence.OnLine B line₂ := by
    intro hB₂
    exact hLinesDisjoint ⟨B, hB₁, hB₂⟩
  have hNoMeet :
      ¬ HilbertSegmentMeetsLine Geo A B line₂ := by
    rintro ⟨X, hAXB, hX₂⟩
    have hX₁ : HilbertIncidence.OnLine X line₁ :=
      hilbert_between_on_line
        Geo A X B line₁ hA₁ hB₁ hAXB
    exact hLinesDisjoint ⟨X, hX₁, hX₂⟩
  exact
    ⟨line₂, hC₂, hD₂,
      ⟨hA₂, hB₂,
        Relation.ReflTransGen.single
          ⟨hA₂, hB₂, hNoMeet⟩⟩⟩


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


/-
Previous provisional declaration:

axiom ParallelogramOppositeSidesCongruent
    (A B C D : Geo.Point) :
    IsParallelogram Geo A B C D →
    OppositeSidesCongruent Geo A B C D
-/

/--
The second named pair of opposite sides of a parallelogram is
congruent.

Lay off a copy `DX` of `BC` on the ray `DA`.  The lines `AB` and `CD`
are parallel, hence their selected endpoints are on the same side of
`CD`; moving from `A` to `X` along the ray from `D` preserves that
side.  Therefore the already proved one-pair criterion makes `XBCD` a
parallelogram, so `XB` is parallel to `CD`.  Hilbert IV identifies
`XB` with the original parallel `AB`.  Since `X` also lies on `DA`,
incidence uniqueness at the intersection of `AB` and `DA` gives
`X = A`, and consequently `BC ≅ DA`.
-/
theorem parallelogram_second_pair_congruent
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D) :
    Geo.Congruent B C D A := by
  have hAB_CD : Geo.Parallel A B C D :=
    hParallelogram.1
  have hBC_DA : Geo.Parallel B C D A :=
    hParallelogram.2
  have hDA_BC : Geo.Parallel D A B C :=
    ParallelSymmetry Geo B C D A hBC_DA
  have hAD_BC : Geo.Parallel A D B C :=
    ParallelSwapFirstLine Geo D A B C hDA_BC
  have hDA : D ≠ A := hDA_BC.1
  rcases HilbertCongruence.segment_construction
      (Geo := Geo) B C D A hDA with
    ⟨X, hRayDX, hDX_BC⟩
  have hXD : X ≠ D := hRayDX.2.1
  have hXAD : Collinear Geo X A D :=
    PrimCollinearSymm Geo D A X hRayDX.2.2.1
  have hXD_BC : Geo.Parallel X D B C :=
    ParallelCollinearLeft
      Geo A D X B C hXD hAD_BC hXAD
  have hXDcongruentBC : Geo.Congruent X D B C :=
    CongruentReverseFirst Geo D X B C hDX_BC

  rcases parallel_endpoints_sameSide
      Geo A B C D hAB_CD with
    ⟨lineCD, hCcd, hDcd, hABSame⟩
  rcases HilbertPlaneIncidence.line_through D A hDA with
    ⟨lineDA, hDda, hAda⟩
  rcases HilbertPlaneIncidence.line_through
      B C hDA_BC.2.1 with
    ⟨lineBC, hBbc, hCbc⟩
  have hLinesDA_BC :
      HilbertLinesDisjoint Geo lineDA lineBC := by
    rintro ⟨P, hPda, hPbc⟩
    have hPDA : P ∈ Geo.PointLine D A :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D A P lineDA hDA hDda hAda).mpr hPda
    have hPBC : P ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C P lineBC hDA_BC.2.1 hBbc hCbc).mpr hPbc
    exact
      Set.disjoint_left.mp hDA_BC.2.2 hPDA hPBC
  have hCda : ¬ HilbertIncidence.OnLine C lineDA := by
    intro hCda
    exact hLinesDA_BC ⟨C, hCda, hCbc⟩
  have hAA : HilbertSameRay Geo D A A :=
    hilbert_sameRay_refl Geo D A hDA.symm
  have hAXSame :
      HilbertSameSide Geo A X lineCD :=
    hilbert_sameRay_points_sameSide
      Geo D A A X C lineDA lineCD
      hDda hAda hDcd hCcd hCda hAA hRayDX
  have hXASame :
      HilbertSameSide Geo X A lineCD :=
    hilbert_sameSide_symm Geo A X lineCD hAXSame
  have hXBSame :
      HilbertSameSide Geo X B lineCD :=
    hilbert_sameSide_trans
      Geo X A B lineCD hXASame hABSame
  have hData : OnePairParallelCongruent Geo X B C D :=
    { parallel := hXD_BC
      congruent := hXDcongruentBC
      oriented := ⟨lineCD, hDcd, hCcd, hXBSame⟩ }
  have hAuxiliary :
      IsParallelogram Geo X B C D :=
    OnePairParallelCongruentCriterion
      Geo X B C D hData
  have hXB_CD : Geo.Parallel X B C D :=
    hAuxiliary.1

  rcases HilbertPlaneIncidence.line_through
      A B hAB_CD.1 with
    ⟨lineAB, hAab, hBab⟩
  rcases HilbertPlaneIncidence.line_through
      X B hXB_CD.1 with
    ⟨lineXB, hXxb, hBxb⟩
  have hLinesAB_CD :
      HilbertLinesDisjoint Geo lineAB lineCD := by
    rintro ⟨P, hPab, hPcd⟩
    have hPAB : P ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B P lineAB hAB_CD.1 hAab hBab).mpr hPab
    have hPCD : P ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D P lineCD hAB_CD.2.1 hCcd hDcd).mpr hPcd
    exact
      Set.disjoint_left.mp hAB_CD.2.2 hPAB hPCD
  have hLinesXB_CD :
      HilbertLinesDisjoint Geo lineXB lineCD := by
    rintro ⟨P, hPxb, hPcd⟩
    have hPXB : P ∈ Geo.PointLine X B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo X B P lineXB hXB_CD.1 hXxb hBxb).mpr hPxb
    have hPCD : P ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D P lineCD hXB_CD.2.1 hCcd hDcd).mpr hPcd
    exact
      Set.disjoint_left.mp hXB_CD.2.2 hPXB hPCD
  have hBcd : ¬ HilbertIncidence.OnLine B lineCD := by
    intro hBcd
    exact hLinesAB_CD ⟨B, hBab, hBcd⟩
  have hLineXB_AB : lineXB = lineAB :=
    HilbertEuclideanPlane.parallel_unique
      (Geo := Geo) lineCD B hBcd
      lineXB lineAB
      hBxb hLinesXB_CD
      hBab hLinesAB_CD
  have hXab : HilbertIncidence.OnLine X lineAB := by
    rw [← hLineXB_AB]
    exact hXxb
  have hXda : HilbertIncidence.OnLine X lineDA :=
    hilbert_collinear_on_line
      Geo D A X lineDA hDA hDda hAda hRayDX.2.2.1
  have hDab : ¬ HilbertIncidence.OnLine D lineAB := by
    intro hDab
    exact hLinesAB_CD ⟨D, hDab, hDcd⟩
  have hXA : X = A := by
    by_contra hXA
    have hLineDA_AB : lineDA = lineAB :=
      HilbertPlaneIncidence.line_unique
        X A hXA lineDA lineAB
        hXda hAda hXab hAab
    have hDab' : HilbertIncidence.OnLine D lineAB := by
      rw [← hLineDA_AB]
      exact hDda
    exact hDab hDab'
  subst X
  exact
    hilbert_congruent_symmetry
      Geo D A B C hDX_BC

/--
Opposite sides of a Hilbert parallelogram are congruent.

The preceding construction proves `BC ≅ DA`.  Applying it once more
to the cyclically relabelled parallelogram `BCDA` proves
`CD ≅ AB`, which is then reversed by symmetry of segment congruence.
No new axiom is introduced: the genuinely Euclidean step is exactly
the already explicit use of Hilbert IV.
-/
theorem ParallelogramOppositeSidesCongruent
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point) :
    IsParallelogram Geo A B C D →
    OppositeSidesCongruent Geo A B C D := by
  intro hParallelogram
  have hRotated :
      IsParallelogram Geo B C D A :=
    ⟨hParallelogram.2,
      ParallelSymmetry
        Geo A B C D hParallelogram.1⟩
  have hCD_AB :
      Geo.Congruent C D A B :=
    parallelogram_second_pair_congruent
      Geo B C D A hRotated
  exact
    ⟨hilbert_congruent_symmetry
        Geo C D A B hCD_AB,
      parallelogram_second_pair_congruent
        Geo A B C D hParallelogram⟩


/--
The diagonals of a Hilbert parallelogram have an interior intersection.

This is the missing existence statement behind the usual theorem that
the diagonals bisect each other.  Applied to the two cyclic orientations
of the parallelogram, `onePair_diagonal_oppositeSide` says that each
diagonal separates the endpoints of the other.  The two corresponding
crossing witnesses lie on both diagonal lines; incidence uniqueness
identifies them.

Unlike `ParallelogramDiagonals`, this theorem does not assume that a
common point of the diagonals has already been supplied.
-/
theorem ParallelogramDiagonalIntersectionExists
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D) :
    ∃ M : Geo.Point,
      Geo.Between A M C ∧
      Geo.Between B M D := by
  have hSides :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hParallelogram

  -- The diagonal `BD` crosses the segment `AC`.
  have hDA_BC : Geo.Parallel D A B C :=
    ParallelSymmetry
      Geo B C D A hParallelogram.2
  have hAD_BC : Geo.Parallel A D B C :=
    ParallelSwapFirstLine
      Geo D A B C hDA_BC
  have hADcongruentBC :
      Geo.Congruent A D B C :=
    CongruentReverseFirst
      Geo D A B C
      (hilbert_congruent_symmetry
        Geo B C D A hSides.2)
  rcases parallel_endpoints_sameSide
      Geo A B C D hParallelogram.1 with
    ⟨sideCD, hCcd, hDcd, hABSame⟩
  have hData : OnePairParallelCongruent Geo A B C D :=
    { parallel := hAD_BC
      congruent := hADcongruentBC
      oriented := ⟨sideCD, hDcd, hCcd, hABSame⟩ }
  rcases onePair_diagonal_oppositeSide
      Geo A B C D hData with
    ⟨diagonalBD, hDbd, hBbd, hOppositeAC⟩

  -- In the cyclic orientation, the diagonal `AC` crosses `BD`.
  have hBA_CD : Geo.Parallel B A C D :=
    ParallelSwapFirstLine
      Geo A B C D hParallelogram.1
  have hBAcongruentCD :
      Geo.Congruent B A C D :=
    CongruentReverseFirst
      Geo A B C D hSides.1
  rcases parallel_endpoints_sameSide
      Geo B C D A hParallelogram.2 with
    ⟨sideDA, hDda, hAda, hBCSame⟩
  have hRotatedData :
      OnePairParallelCongruent Geo B C D A :=
    { parallel := hBA_CD
      congruent := hBAcongruentCD
      oriented := ⟨sideDA, hAda, hDda, hBCSame⟩ }
  rcases onePair_diagonal_oppositeSide
      Geo B C D A hRotatedData with
    ⟨diagonalAC, hAac, hCac, hOppositeBD⟩

  rcases hOppositeAC.2.2 with
    ⟨X, hAXC, hXbd⟩
  rcases hOppositeBD.2.2 with
    ⟨Y, hBYD, hYac⟩
  have hXac : HilbertIncidence.OnLine X diagonalAC :=
    hilbert_between_on_line
      Geo A X C diagonalAC hAac hCac hAXC
  have hYbd : HilbertIncidence.OnLine Y diagonalBD :=
    hilbert_between_on_line
      Geo B Y D diagonalBD hBbd hDbd hBYD
  have hXY : X = Y := by
    by_contra hXY
    have hLinesEqual : diagonalAC = diagonalBD :=
      HilbertPlaneIncidence.line_unique
        X Y hXY diagonalAC diagonalBD
        hXac hYac hXbd hYbd
    have hAdiagonalBD :
        HilbertIncidence.OnLine A diagonalBD := by
      rw [← hLinesEqual]
      exact hAac
    exact hOppositeAC.1 hAdiagonalBD
  subst Y
  exact ⟨X, hAXC, hBYD⟩


/-
Previous provisional declaration:

axiom ParallelogramDiagonals
    (A B C D M : Geo.Point) :
    IsParallelogram Geo A B C D →
    Collinear Geo A M C →
    Collinear Geo B M D →
    IsMidpoint Geo M A C
-/

/--
The weak collinearity hypotheses naming the intersection of the two
diagonals actually place that point strictly inside both diagonals.

For each cyclic orientation, the congruent-and-parallel opposite side
pair satisfies `onePair_diagonal_oppositeSide`.  Its crossing witness
lies on both diagonal lines.  Incidence uniqueness identifies that
witness with the given common point `M`; otherwise the two diagonal
lines would coincide, contradicting the off-line part of the
opposite-side conclusion.
-/
theorem parallelogram_diagonal_crossing
    [HilbertEuclideanPlane Geo]
    (A B C D M : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D)
    (hAMC : Collinear Geo A M C)
    (hBMD : Collinear Geo B M D) :
    ∃ lineAC lineBD : Geo.Line,
      HilbertIncidence.OnLine A lineAC ∧
      HilbertIncidence.OnLine M lineAC ∧
      HilbertIncidence.OnLine C lineAC ∧
      HilbertIncidence.OnLine B lineBD ∧
      HilbertIncidence.OnLine M lineBD ∧
      HilbertIncidence.OnLine D lineBD ∧
      HilbertOppositeSide Geo A C lineBD ∧
      HilbertOppositeSide Geo B D lineAC ∧
      Geo.Between A M C ∧
      Geo.Between B M D := by
  have hSides :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hParallelogram
  have hDA_BC : Geo.Parallel D A B C :=
    ParallelSymmetry
      Geo B C D A hParallelogram.2
  have hAD_BC : Geo.Parallel A D B C :=
    ParallelSwapFirstLine
      Geo D A B C hDA_BC
  have hADcongruentBC :
      Geo.Congruent A D B C :=
    CongruentReverseFirst
      Geo D A B C
      (hilbert_congruent_symmetry
        Geo B C D A hSides.2)
  rcases parallel_endpoints_sameSide
      Geo A B C D hParallelogram.1 with
    ⟨sideCD, hCcd, hDcd, hABSame⟩
  have hData : OnePairParallelCongruent Geo A B C D :=
    { parallel := hAD_BC
      congruent := hADcongruentBC
      oriented := ⟨sideCD, hDcd, hCcd, hABSame⟩ }
  rcases onePair_diagonal_oppositeSide
      Geo A B C D hData with
    ⟨diagonalBD, hDbd, hBbd, hOppositeAC⟩

  have hBA_CD : Geo.Parallel B A C D :=
    ParallelSwapFirstLine
      Geo A B C D hParallelogram.1
  have hBAcongruentCD :
      Geo.Congruent B A C D :=
    CongruentReverseFirst
      Geo A B C D hSides.1
  rcases parallel_endpoints_sameSide
      Geo B C D A hParallelogram.2 with
    ⟨sideDA, hDda, hAda, hBCSame⟩
  have hRotatedData :
      OnePairParallelCongruent Geo B C D A :=
    { parallel := hBA_CD
      congruent := hBAcongruentCD
      oriented := ⟨sideDA, hAda, hDda, hBCSame⟩ }
  rcases onePair_diagonal_oppositeSide
      Geo B C D A hRotatedData with
    ⟨diagonalAC, hAac, hCac, hOppositeBD⟩

  rcases hAMC with
    ⟨lineAC, hAlineAC, hMlineAC, hClineAC⟩
  rcases hBMD with
    ⟨lineBD, hBlineBD, hMlineBD, hDlineBD⟩
  rcases hOppositeAC.2.2 with
    ⟨X, hAXC, hXdiagonalBD⟩
  rcases hOppositeBD.2.2 with
    ⟨Y, hBYD, hYdiagonalAC⟩
  have hAC : A ≠ C :=
    (HilbertOrder.between_incidence
      A X C hAXC).2.2.1
  have hBD : B ≠ D :=
    (HilbertOrder.between_incidence
      B Y D hBYD).2.2.1
  have hLineAC :
      lineAC = diagonalAC :=
    HilbertPlaneIncidence.line_unique
      A C hAC lineAC diagonalAC
      hAlineAC hClineAC hAac hCac
  have hLineBD :
      lineBD = diagonalBD :=
    HilbertPlaneIncidence.line_unique
      B D hBD lineBD diagonalBD
      hBlineBD hDlineBD hBbd hDbd
  have hOppositeAC' :
      HilbertOppositeSide Geo A C lineBD := by
    rw [hLineBD]
    exact
      ⟨hOppositeAC.1, hOppositeAC.2.1,
        ⟨X, hAXC, hXdiagonalBD⟩⟩
  have hOppositeBD' :
      HilbertOppositeSide Geo B D lineAC := by
    rw [hLineAC]
    exact
      ⟨hOppositeBD.1, hOppositeBD.2.1,
        ⟨Y, hBYD, hYdiagonalAC⟩⟩
  have hXlineAC :
      HilbertIncidence.OnLine X lineAC :=
    hilbert_between_on_line
      Geo A X C lineAC
      hAlineAC hClineAC hAXC
  have hXlineBD :
      HilbertIncidence.OnLine X lineBD := by
    rw [hLineBD]
    exact hXdiagonalBD
  have hMX : M = X := by
    by_contra hMX
    have hLinesEqual : lineAC = lineBD :=
      HilbertPlaneIncidence.line_unique
        M X hMX lineAC lineBD
        hMlineAC hXlineAC hMlineBD hXlineBD
    have hAlineBD :
        HilbertIncidence.OnLine A lineBD := by
      rw [← hLinesEqual]
      exact hAlineAC
    exact hOppositeAC'.1 hAlineBD
  have hYlineAC :
      HilbertIncidence.OnLine Y lineAC := by
    rw [hLineAC]
    exact hYdiagonalAC
  have hYlineBD :
      HilbertIncidence.OnLine Y lineBD :=
    hilbert_between_on_line
      Geo B Y D lineBD
      hBlineBD hDlineBD hBYD
  have hMY : M = Y := by
    by_contra hMY
    have hLinesEqual : lineAC = lineBD :=
      HilbertPlaneIncidence.line_unique
        M Y hMY lineAC lineBD
        hMlineAC hYlineAC hMlineBD hYlineBD
    have hBlineAC :
        HilbertIncidence.OnLine B lineAC := by
      rw [hLinesEqual]
      exact hBlineBD
    exact hOppositeBD'.1 hBlineAC
  subst X
  subst Y
  exact
    ⟨lineAC, lineBD,
      hAlineAC, hMlineAC, hClineAC,
      hBlineBD, hMlineBD, hDlineBD,
      hOppositeAC', hOppositeBD',
      hAXC, hBYD⟩

/--
The diagonals of a Hilbert parallelogram bisect each other.

The crossing lemma first recovers the strict orders `A-M-C` and
`B-M-D` from the weak collinearity hypotheses.  Hilbert's Theorem 30
then supplies the two pairs of alternate angles in triangles `ABM`
and `CDM`; opposite sides are congruent by the preceding theorem.
The angle-side-angle congruence theorem gives `AM ≅ CM`, which is
exactly the required midpoint statement after reversing the second
unoriented segment.
-/
theorem ParallelogramDiagonals
    [HilbertEuclideanPlane Geo]
    (A B C D M : Geo.Point) :
    IsParallelogram Geo A B C D →
    Collinear Geo A M C →
    Collinear Geo B M D →
    IsMidpoint Geo M A C := by
  intro hParallelogram hAMC hBMD
  rcases parallelogram_diagonal_crossing
      Geo A B C D M hParallelogram hAMC hBMD with
    ⟨lineAC, lineBD,
      hAac, hMac, hCac,
      hBbd, hMbd, hDbd,
      hOppositeAC, hOppositeBD,
      hAMCstrict, hBMDstrict⟩
  have hSides :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hParallelogram
  have hAngleAraw :
      Geo.AngleCongruent M A B M C D :=
    hilbert_alternate_angles_of_parallel_oppositeSide_lines
      Geo A B C M D lineAC
      hAMCstrict hAac hCac
      hOppositeBD hParallelogram.1
  have hAngleA :
      Geo.AngleCongruent B A M D C M :=
    (Geo.angle_congruent_reverse_second
      B A M M C D).mp
      ((Geo.angle_congruent_reverse_first
        M A B M C D).mp hAngleAraw)
  have hBA_DC : Geo.Parallel B A D C :=
    ParallelSwapSecondLine
      Geo B A C D
      (ParallelSwapFirstLine
        Geo A B C D hParallelogram.1)
  have hAngleBraw :
      Geo.AngleCongruent M B A M D C :=
    hilbert_alternate_angles_of_parallel_oppositeSide_lines
      Geo B A D M C lineBD
      hBMDstrict hBbd hDbd
      hOppositeAC hBA_DC
  have hAngleB :
      Geo.AngleCongruent A B M C D M :=
    (Geo.angle_congruent_reverse_second
      A B M M D C).mp
      ((Geo.angle_congruent_reverse_first
        M B A M D C).mp hAngleBraw)
  have hBM : B ≠ M :=
    (HilbertOrder.between_incidence
      B M D hBMDstrict).1
  have hDM : D ≠ M :=
    (HilbertOrder.between_incidence
      B M D hBMDstrict).2.1.symm
  have hBMA : ¬ Collinear Geo B M A :=
    hilbert_not_collinear_of_off_line
      Geo B M A lineBD hBM
      hBbd hMbd hOppositeAC.1
  have hDMC : ¬ Collinear Geo D M C :=
    hilbert_not_collinear_of_off_line
      Geo D M C lineBD hDM
      hDbd hMbd hOppositeAC.2.1
  have hABM : ¬ Collinear Geo A B M :=
    fun h => hBMA
      (PrimCollinearCycle Geo A B M h)
  have hCDM : ¬ Collinear Geo C D M :=
    fun h => hDMC
      (PrimCollinearCycle Geo C D M h)
  have hASA :=
    hilbert_asa_sides
      Geo A B M C D M
      hABM hCDM hSides.1 hAngleA hAngleB
  exact
    ⟨hAMC,
      (Geo.congruent_reverse_second
        A M C M).mp hASA.1⟩


/--
Stable `GeometryBase` wrapper for Hilbert's neutral Theorem 26.

The mathematical proof is `hilbert_midpoint_exists` in
`HilbertAxioms`; this declaration only packages its primitive
betweenness-and-congruence conclusion as `HilbertIsMidpoint`.
-/
theorem HilbertMidpointExists
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ M : Geo.Point,
      HilbertIsMidpoint Geo M A B := by
  exact hilbert_midpoint_exists Geo A B hAB


/-
Previous Euclidean construction through an auxiliary parallelogram.

It was mathematically valid but required the stronger axiom IV and
placed the proof of Hilbert's neutral Theorem 26 in the wrong layer.
It is retained here only as a historical implementation record.

/--
Every nondegenerate segment has a strict Hilbert midpoint.

For the present Euclidean layer, construct points `C` and `D` on
opposite sides of `AB` so that `AC ≅ BD` and the alternate angles made
with `AB` are congruent.  Theorem 30 gives `AC ∥ BD`; SAS supplies the
second pair of equal alternate angles and hence `CB ∥ DA`.  Thus
`ACBD` is a parallelogram.  Its diagonal-intersection point lies
strictly between `A` and `B`, and `ParallelogramDiagonals` makes the two
parts congruent.

Hilbert proves the stronger neutral result as Theorem 26.  This
construction deliberately uses the already available Euclidean
parallelogram theory because that is exactly the foundation assumed by
the Hilbert path of Finlay's proof.
-/
theorem HilbertMidpointExists
    [HilbertEuclideanPlane Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ M : Geo.Point,
      HilbertIsMidpoint Geo M A B := by
  rcases HilbertPlaneIncidence.line_through A B hAB with
    ⟨base, hAbase, hBbase⟩
  rcases hilbert_point_off_line Geo base with
    ⟨C, hCbase⟩
  have hABC : ¬ Collinear Geo A B C :=
    hilbert_not_collinear_of_off_line
      Geo A B C base hAB hAbase hBbase hCbase
  have hBAC : ¬ Collinear Geo B A C := by
    intro h
    exact hABC (PrimCollinearSwap Geo B A C h)
  have hCA : C ≠ A := by
    intro h
    subst C
    exact hCbase hAbase

  -- Select the side of `AB` opposite to `C`.
  rcases HilbertOrder.between_extension C A hCA with
    ⟨S, hCAS⟩
  have hCASData :=
    HilbertOrder.between_incidence C A S hCAS
  have hSA : S ≠ A := hCASData.2.1.symm
  have hSbase : ¬ HilbertIncidence.OnLine S base := by
    intro hSbase
    have hSAC : Collinear Geo S A C :=
      PrimCollinearSymm Geo C A S
        hCASData.2.2.2.1
    have hCbase' : HilbertIncidence.OnLine C base :=
      hilbert_collinear_on_line
        Geo S A C base hSA
        hSbase hAbase hSAC
    exact hCbase hCbase'
  have hOppositeCS :
      HilbertOppositeSide Geo C S base :=
    ⟨hCbase, hSbase, ⟨A, hCAS, hAbase⟩⟩

  -- Copy `∠BAC` at `B` on the opposite side of `AB`.
  rcases HilbertCongruence.angle_construction
      (Geo := Geo) B A C A B S
      hBAC hAB base hAbase hBbase hSbase with
    ⟨D₀, hD₀SSame, hAngleD₀, _⟩
  have hSD₀Same :
      HilbertSameSide Geo S D₀ base :=
    hilbert_sameSide_symm
      Geo D₀ S base hD₀SSame
  have hOppositeCD₀ :
      HilbertOppositeSide Geo C D₀ base :=
    hilbert_oppositeSide_transport_right
      Geo C S D₀ base hOppositeCS hSD₀Same
  have hBD₀ : B ≠ D₀ := by
    intro h
    subst D₀
    exact hOppositeCD₀.2.1 hBbase

  -- Lay off `BD ≅ AC` on the constructed ray.
  rcases HilbertCongruence.segment_construction
      (Geo := Geo) A C B D₀ hBD₀ with
    ⟨D, hRayD₀D, hBD_AC⟩
  rcases HilbertPlaneIncidence.line_through B D₀ hBD₀ with
    ⟨rayLine, hBray, hD₀ray⟩
  have hAray : ¬ HilbertIncidence.OnLine A rayLine := by
    intro hAray
    have hBaseRay : base = rayLine :=
      HilbertPlaneIncidence.line_unique
        A B hAB base rayLine
        hAbase hBbase hAray hBray
    exact hOppositeCD₀.2.1 (hBaseRay ▸ hD₀ray)
  have hD₀DSame :
      HilbertSameSide Geo D₀ D base :=
    hilbert_sameRay_points_sameSide
      Geo B D₀ D₀ D A rayLine base
      hBray hD₀ray hBbase hAbase hAray
      (hilbert_sameRay_refl Geo B D₀ hBD₀.symm)
      hRayD₀D
  have hSDsame :
      HilbertSameSide Geo S D base :=
    hilbert_sameSide_trans
      Geo S D₀ D base hSD₀Same hD₀DSame
  have hOppositeCD :
      HilbertOppositeSide Geo C D base :=
    hilbert_oppositeSide_transport_right
      Geo C S D base hOppositeCS hSDsame
  have hAngleD :
      Geo.AngleCongruent B A C A B D := by
    have hTarget :
        Geo.Angle A B D₀ = Geo.Angle A B D :=
      hilbert_angle_eq_of_sameRay_second
        Geo B A D₀ D hRayD₀D
    unfold Geometry.Geo.AngleCongruent at hAngleD₀ ⊢
    rw [← hTarget]
    exact hAngleD₀

  -- An interior point of `AB` names the transversal directions.
  rcases hilbert_between_exists Geo A B hAB with
    ⟨E, hAEB⟩
  have hAEBData :=
    HilbertOrder.between_incidence A E B hAEB
  have hBEA : Geo.Between B E A :=
    hAEBData.2.2.2.2
  have hAERay : HilbertSameRay Geo A E B :=
    hilbert_sameRay_of_between Geo A E B hAEB
  have hBERay : HilbertSameRay Geo B E A :=
    hilbert_sameRay_of_between Geo B E A hBEA
  have hFirstAlternate :
      Geo.AngleCongruent E A C E B D := by
    have hAtA :
        Geo.Angle E A C = Geo.Angle B A C :=
      hilbert_angle_eq_of_sameRay_first
        Geo A E B C hAERay
    have hAtB :
        Geo.Angle E B D = Geo.Angle A B D :=
      hilbert_angle_eq_of_sameRay_first
        Geo B E A D hBERay
    unfold Geometry.Geo.AngleCongruent at hAngleD ⊢
    rw [hAtA, hAtB]
    exact hAngleD
  have hAC_BD : Geo.Parallel A C B D :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo A C B E D base
      hAEB hAbase hBbase
      hOppositeCD hFirstAlternate

  -- SAS gives the alternate angles for the other pair of sides.
  have hACB : ¬ Collinear Geo A C B := by
    intro h
    exact hABC (PrimCollinearRotate Geo A C B h)
  have hBAD : ¬ Collinear Geo B A D :=
    hilbert_not_collinear_of_off_line
      Geo B A D base hAB.symm
      hBbase hAbase hOppositeCD.2.1
  have hBDA : ¬ Collinear Geo B D A := by
    intro h
    exact hBAD (PrimCollinearRotate Geo B D A h)
  have hACcongruentBD :
      Geo.Congruent A C B D :=
    hilbert_congruent_symmetry
      Geo B D A C hBD_AC
  have hABcongruentBA :
      Geo.Congruent A B B A :=
    (Geo.congruent_reverse_second
      A B A B).mp
      (hilbert_congruent_reflexive Geo A B)
  have hIncludedAngle :
      Geo.AngleCongruent C A B D B A :=
    (Geo.angle_congruent_reverse_second
      C A B A B D).mp
      ((Geo.angle_congruent_reverse_first
        B A C A B D).mp hAngleD)
  have hSAS :=
    hilbert_sas_remaining_angles
      Geo A C B B D A
      hACB hBDA
      hACcongruentBD hABcongruentBA
      hIncludedAngle
  have hSecondAlternate :
      Geo.AngleCongruent E B C E A D := by
    have hAtB :
        Geo.Angle E B C = Geo.Angle A B C :=
      hilbert_angle_eq_of_sameRay_first
        Geo B E A C hBERay
    have hAtA :
        Geo.Angle E A D = Geo.Angle B A D :=
      hilbert_angle_eq_of_sameRay_first
        Geo A E B D hAERay
    unfold Geometry.Geo.AngleCongruent at hSAS ⊢
    rw [hAtB, hAtA]
    exact hSAS.2
  have hBC_AD : Geo.Parallel B C A D :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo B C A E D base
      hBEA hBbase hAbase
      hOppositeCD hSecondAlternate
  have hCB_DA : Geo.Parallel C B D A :=
    ParallelSwapFirstLine
      Geo B C D A
      (ParallelSwapSecondLine
        Geo B C A D hBC_AD)
  have hParallelogram :
      IsParallelogram Geo A C B D :=
    ⟨hAC_BD, hCB_DA⟩

  rcases ParallelogramDiagonalIntersectionExists
      Geo A C B D hParallelogram with
    ⟨M, hAMB, hCMD⟩
  have hMidpoint :
      IsMidpoint Geo M A B :=
    ParallelogramDiagonals
      Geo A C B D M
      hParallelogram
      (HilbertOrder.between_incidence
        A M B hAMB).2.2.2.1
      (HilbertOrder.between_incidence
        C M D hCMD).2.2.2.1
  exact ⟨M, hAMB, hMidpoint.2⟩
-/


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

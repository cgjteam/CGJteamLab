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

The section map is compared against the Hilbert-style development in
Borsuk-Szmielew, Foundations of Geometry. This file does not reproduce
that book: the reference is used to identify local geometric theories,
their scope, and their dependency level.

Declarations headed `Previous provisional declaration` are retained
inside block comments as historical API records; they are not active
axioms.  See the project wiki page `Hilbert-Derivation-Ledger` for the
mathematical source, proof dependency, and downstream role of every
replacement.
-/

------------------------------------------------------------------------
-- Part I. Core Derived Notions
------------------------------------------------------------------------
-- Cross-cutting definitions used by several local theories.
-- Borsuk-Szmielew distribute the corresponding notions across:
-- Ch. I (collinearity/intersection), Ch. II sec. 11 (midpoint),
-- and Ch. V sec. 7 (parallelogram).
--

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

/--
BNW auxiliary axiom: nullsegment1

A segment congruent to a null segment is itself null.

This principle is not included explicitly in the historical Hilbert
axioms used by the project. It is added locally in Book Zero because
the BNW language permits degenerate segments.
-/
axiom bookZero_nullSegment1
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (h : Geo.Congruent A B C C) :
    A = B

/--
All null segments are congruent.
-/
axiom bookZero_nullSegment2
    (A B : Geo.Point) :
    Geo.Congruent A A B B

------------------------------------------------------------------------
-- Part II. Midpoints and Medians
------------------------------------------------------------------------
-- Reference point: Borsuk-Szmielew, Ch. II sec. 11, "Midpoint of a Segment".
-- `IsMedian` is the project-level triangle notion built from midpoint.
--

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
-- Reference point: Borsuk-Szmielew, Ch. I secs. 2-3,
-- non-collinearity together with the theory of lines and planes.
--



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
-- Part IV. Segment Congruence
------------------------------------------------------------------------
-- Reference point: Borsuk-Szmielew, Ch. II secs. 1-3,
-- congruence of segments and elementary relations between segments.
--



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

/--
Symmetry of the Hilbert midpoint relation with respect to the endpoints.

If `M` is the midpoint of `AB`, then `M` is also the midpoint of `BA`.
This follows from symmetry of betweenness and endpoint symmetries of
segment congruence.
-/

theorem MidpointSymmetry
    [HilbertCongruence Geo]
    (M A B : Geo.Point)
    (h : HilbertIsMidpoint Geo M A B) :
    HilbertIsMidpoint Geo M B A := by
  rcases h with ⟨hBetween, hCong⟩
  constructor
  · exact
      (HilbertOrder.between_incidence
        A M B hBetween).2.2.2.2
  ·
    have hReverse : Geo.Congruent M A B M :=
      CongruentReverseBoth Geo A M M B hCong
    exact
      CongruentSymmetry Geo M A B M hReverse




omit [HilbertIncidence Geo] in
/--
Endpoint reversal on the second segment.  This is representational,
not an additional congruence axiom.
-/
theorem CongruentSwapSecond
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent A B D C := by
  exact (Geometry.Geo.congruent_reverse_second Geo A B C D).mp


------------------------------------------------------------------------
-- Part V. Angle Congruence
------------------------------------------------------------------------
-- Reference point: Borsuk-Szmielew, Ch. II secs. 4-5,
-- "Congruence of Angles" and "Adjacent Angles. Vertical Angles".
--



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
-- Reference points: Borsuk-Szmielew, Ch. II secs. 35-37
-- (parallel half-lines, axes, lines) and Ch. V secs. 3-5
-- (Euclidean conclusions about parallels and parallel-sided angles).
--



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
-- Part VII. Segment and Intersection Constructions
------------------------------------------------------------------------
-- Cross-cutting construction infrastructure rather than one local theory.
-- Reference points include Borsuk-Szmielew, Ch. I secs. 4-5
-- (existence/intersection) and segment-construction results from Ch. II.
--



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
-- Reference point: Borsuk-Szmielew, Ch. II sec. 7,
-- "Relations Between Sides and Angles of Two Triangles".
--

structure TriangleCongruenceResult
    (A B C D E F : Geo.Point) where
  sideAB : Geo.Congruent A B D E
  sideBC : Geo.Congruent B C E F
  sideAC : Geo.Congruent A C D F
  angleA : Geo.AngleCongruent B A C E D F
  angleB : Geo.AngleCongruent A B C D E F
  angleC : Geo.AngleCongruent A C B D F E




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
-- Part IX. Parallelograms
------------------------------------------------------------------------
-- Reference point: Borsuk-Szmielew, Ch. V sec. 7, "Parallelograms".
-- Their local theory starts from two pairs of opposite parallel sides
-- and gives a recognition criterion using one oriented parallel pair
-- together with congruence. The diagonal results below are a natural
-- extension used by this library, not a transcription of sec. 7.
--

/-!
A parallelogram is recognized from one pair of opposite sides that are
both parallel and congruent. Once recognized, the standard properties
of parallelograms become available as reusable geometric tools.
-/

------------------------------------------------------------------------
-- Recognition of Parallelograms
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
-- Basic Properties of Parallelograms
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
-- Generic Relation Helpers
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

/-
Hilbert Theorem 11.

If AB is congruent to AC in a noncollinear triangle ABC,
then the base angles at B and C are congruent.
-/
/-
theorem hilbert_isosceles_base_angles
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hNC : ¬ Collinear Geo A B C)
    (hABAC : Geo.Congruent A B A C) :
    Geo.AngleCongruent A B C A C B := by

  have hNC' : ¬ Collinear Geo A C B := by
    intro hACB
    exact hNC (PrimCollinearRotate Geo A C B hACB)

  have hBAC : ¬ PrimCollinear Geo B A C := by
    intro hBAC
    apply hNC
    exact PrimCollinearSwap Geo B A C hBAC

  have hAngleA :
      Geo.AngleCongruent B A C C A B := by
    have hRefl :
        Geo.AngleCongruent B A C B A C :=
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo) B A C hBAC

    exact
      (Geo.angle_congruent_reverse_second
        B A C B A C).mp hRefl

  have hACAB : Geo.Congruent A C A B :=
    hilbert_congruent_symmetry Geo A B A C hABAC

  have hTriangles :=
    SAS
      Geo
      A B C
      A C B
      hNC
      hNC'
      hABAC
      hAngleA
      hACAB

  exact hTriangles.angleB
-/


/-
Temporary Hilbert Theorem 15: addition of adjacent congruent angles.

The outer rays OA and OC lie on opposite sides of the line OB,
and analogously OA' and OC' lie on opposite sides of O'B'.
Thus OB and O'B' are the interior dividing rays of the two angles.
-/

/--
Temporary Hilbert Theorem 15.

Let OA, OB, OC and O'A', O'B', O'C' determine two angle
configurations. The outer rays OA, OC and O'A', O'C' have the
same relative side configuration with respect to the lines OB
and O'B': in both configurations they lie on the same side, or
in both configurations they lie on different sides.

If the two component angles are pairwise congruent, then the
angles formed by the outer rays are congruent.

This is retained temporarily while the remaining Hilbert SSS
construction is verified.
-/

/-
The ray from O through R meets the open segment AB.

The witness X lies inside AB and on the ray OR.
-/
def HilbertRayMeetsSegment
    (O R A B : Geo.Point) : Prop :=
  ∃ X : Geo.Point,
    Geo.Between A X B ∧
    HilbertSameRay Geo O R X



/--
If A-B-D and C is not on line AD, then A and B lie on the same
side of line CD.

This is a pure incidence/order fact.
-/
theorem hilbert_between_points_sameSide_transversal
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABD : Geo.Between A B D)
    (hNC : ¬ PrimCollinear Geo A D C) :
    ∃ l : Geo.Line,
      HilbertIncidence.OnLine C l ∧
      HilbertIncidence.OnLine D l ∧
      HilbertSameSide Geo A B l := by

  have hAD : A ≠ D :=
    (HilbertOrder.between_incidence A B D hABD).2.2.1

  have hCD : C ≠ D := by
    intro hCD
    subst C
    apply hNC
    rcases HilbertPlaneIncidence.line_through A D hAD with
      ⟨l, hAl, hDl⟩
    exact PrimCollinear.mk (Geo := Geo) hAl hDl hDl

  rcases HilbertPlaneIncidence.line_through A D hAD with
    ⟨base, hAbase, hDbase⟩

  rcases HilbertPlaneIncidence.line_through C D hCD with
    ⟨cross, hCcross, hDcross⟩

  have hBbase : HilbertIncidence.OnLine B base :=
    hilbert_between_on_line
      Geo A B D base hAbase hDbase hABD

  have hLines : base ≠ cross := by
    intro hEq
    subst cross
    apply hNC
    exact PrimCollinear.mk
      (Geo := Geo) hAbase hDbase hCcross

  have hAnotcross :
      ¬ HilbertIncidence.OnLine A cross := by
    intro hAcross

    have hEq : base = cross :=
      HilbertPlaneIncidence.line_unique
        A D hAD
        base cross
        hAbase hDbase
        hAcross hDcross

    exact hLines hEq

  have hBD : B ≠ D :=
    (HilbertOrder.between_incidence A B D hABD).2.1

  have hBnotcross :
      ¬ HilbertIncidence.OnLine B cross := by
    intro hBcross

    have hEq : base = cross :=
      HilbertPlaneIncidence.line_unique
        B D hBD
        base cross
        hBbase hDbase
        hBcross hDcross

    exact hLines hEq

  have hABDcol : PrimCollinear Geo A B D :=
    (HilbertOrder.between_incidence
      A B D hABD).2.2.2.1

  have hNotBetween : ¬ Geo.Between A D B :=
    (HilbertOrder.between_unique
      A B D hABDcol hABD).2

  have hNoMeet :
      ¬ HilbertSegmentMeetsLine Geo A B cross :=
    hilbert_segment_not_meets_crossing_line
      Geo
      A B D
      base cross
      hLines
      hAbase
      hBbase
      hDbase
      hDcross
      hNotBetween

  have hSame : HilbertSameSide Geo A B cross := by
    exact
      ⟨hAnotcross,
       hBnotcross,
       Relation.ReflTransGen.single
         ⟨hAnotcross, hBnotcross, hNoMeet⟩⟩

  exact ⟨cross, hCcross, hDcross, hSame⟩

/--
The intersection point of CD with the base is B.

If A-O-D and C-B-D, then the ray OC meets the open segment AB,
provided A, D and B are noncollinear.
-/
theorem hilbert_sameSide_rays_order_case_eq
    [HilbertOrder Geo]
    (O A B C D : Geo.Point)
    (hADB : ¬ Collinear Geo A D B)
    (hAOD : Geo.Between A O D)
    (hCBD : Geo.Between C B D) :
    HilbertRayMeetsSegment Geo O C A B := by

  have hDBC :
      Geo.Between D B C :=
    (HilbertOrder.between_incidence
      C B D hCBD).2.2.2.2

  rcases
      hilbert_inner_pasch_strong
        Geo
        A D B C O
        hADB
        hDBC
        hAOD with
    ⟨F, hCFO, hAFB⟩

  have hOFC :
      Geo.Between O F C :=
    (HilbertOrder.between_incidence
      C F O hCFO).2.2.2.2

  have hRayOFC :
      HilbertSameRay Geo O F C :=
    hilbert_sameRay_of_between
      Geo O F C hOFC

  have hRayOCF :
      HilbertSameRay Geo O C F :=
    hilbert_sameRay_symm
      Geo O F C hRayOFC

  exact ⟨F, hAFB, hRayOCF⟩

/--
Two points lying on the same ray as a common reference point
lie on the same ray with each other.
-/



theorem hilbert_sameRay_of_common
    [HilbertOrder Geo]
    (O X P Q : Geo.Point)
    (hXP : HilbertSameRay Geo O X P)
    (hXQ : HilbertSameRay Geo O X Q) :
    HilbertSameRay Geo O P Q := by

  rcases hXP.2.2.1 with
    ⟨l, hOl, hXl, hPl⟩

  rcases hXQ.2.2.1 with
    ⟨m, hOm, hXm, hQm⟩

  have hlm : l = m :=
    HilbertPlaneIncidence.line_unique
      O X hXP.1.symm
      l m
      hOl hXl
      hOm hXm

  subst m

  refine
    ⟨hXP.2.1,
     hXQ.2.1,
     ⟨l, hOl, hPl, hQm⟩,
     ?_⟩

  intro hPOQ

  have hPX :
      HilbertSameRay Geo O P X :=
    hilbert_sameRay_symm
      Geo O X P hXP

  have hQX :
      HilbertSameRay Geo O Q X :=
    hilbert_sameRay_symm
      Geo O X Q hXQ

  have hXOX :
      Geo.Between X O X :=
    hilbert_between_transport_sameRays
      Geo
      P O Q
      X X
      hPOQ
      hPX
      hQX

  exact
    (HilbertOrder.between_incidence
      X O X hXOX).2.2.1 rfl

/--
The intersection point P lies beyond B on the ray OB.

If A-O-D, C-P-D and O-B-P, then ray OC meets the open
segment AB.
-/
theorem hilbert_sameSide_rays_order_case_OBP
    [HilbertOrder Geo]
    (O A B C D P : Geo.Point)
    (hADP : ¬ Collinear Geo A D P)
    (hAPB : ¬ Collinear Geo A P B)
    (hAOD : Geo.Between A O D)
    (hCPD : Geo.Between C P D)
    (hOBP : Geo.Between O B P) :
    HilbertRayMeetsSegment Geo O C A B := by

  --------------------------------------------------------------------
  -- First inner Pasch in triangle A-D-P:
  --
  -- D-P-C
  -- A-O-D
  --
  -- gives F with C-F-O and A-F-P.
  --------------------------------------------------------------------

  have hDPC :
      Geo.Between D P C :=
    (HilbertOrder.between_incidence
      C P D hCPD).2.2.2.2

  rcases
      hilbert_inner_pasch_strong
        Geo
        A D P
        C O
        hADP
        hDPC
        hAOD with
    ⟨F, hCFO, hAFP⟩

  --------------------------------------------------------------------
  -- Since O-B-P, also P-B-O.
  --
  -- A second inner Pasch in triangle A-P-B:
  --
  -- P-B-O
  -- A-F-P
  --
  -- gives G with O-G-F and A-G-B.
  --------------------------------------------------------------------

  have hPBO :
      Geo.Between P B O :=
    (HilbertOrder.between_incidence
      O B P hOBP).2.2.2.2

  rcases
      hilbert_inner_pasch_strong
        Geo
        A P B
        O F
        hAPB
        hPBO
        hAFP with
    ⟨G, hOGF, hAGB⟩

  --------------------------------------------------------------------
  -- F lies on ray OC.
  --------------------------------------------------------------------

  have hOFC :
      Geo.Between O F C :=
    (HilbertOrder.between_incidence
      C F O hCFO).2.2.2.2

  have hRayOFC :
      HilbertSameRay Geo O F C :=
    hilbert_sameRay_of_between
      Geo O F C hOFC

  --------------------------------------------------------------------
  -- G lies on the same ray as F, hence on ray OC.
  --------------------------------------------------------------------

  have hRayOGF :
      HilbertSameRay Geo O G F :=
    hilbert_sameRay_of_between
      Geo O G F hOGF

  have hRayOFG :
      HilbertSameRay Geo O F G :=
    hilbert_sameRay_symm
      Geo O G F hRayOGF

  have hRayOCG :
      HilbertSameRay Geo O C G :=
    hilbert_sameRay_of_common
      Geo
      O F C G
      hRayOFC
      hRayOFG

  exact ⟨G, hAGB, hRayOCG⟩

/--
The intersection point P lies beyond O on the ray BO.

If A-O-D, C-P-D and B-O-P, then ray OA meets the open
segment CB.
-/
theorem hilbert_sameSide_rays_order_case_BOP
    [HilbertOrder Geo]
    (O A B C D P : Geo.Point)
    (base : Geo.Line)
    (hOB : O ≠ B)
    (hObase : HilbertIncidence.OnLine O base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hPbase : HilbertIncidence.OnLine P base)
    (hAoff : ¬ HilbertIncidence.OnLine A base)
    (hCoff : ¬ HilbertIncidence.OnLine C base)
    (hSame : HilbertSameSide Geo A C base)
    (hAOC : ¬ Collinear Geo A O C)
    (hAOD : Geo.Between A O D)
    (hCPD : Geo.Between C P D)
    (hBOP : Geo.Between B O P) :
    HilbertRayMeetsSegment Geo O A C B := by

  have hAO : A ≠ O :=
    (HilbertOrder.between_incidence
      A O D hAOD).1

  have hOD : O ≠ D :=
    (HilbertOrder.between_incidence
      A O D hAOD).2.1

  have hOP : O ≠ P :=
    (HilbertOrder.between_incidence
      B O P hBOP).2.1

  have hPC : P ≠ C :=
    (HilbertOrder.between_incidence
      C P D hCPD).1.symm

  have hPD : P ≠ D :=
    (HilbertOrder.between_incidence
      C P D hCPD).2.1

  rcases
      (HilbertOrder.between_incidence
        A O D hAOD).2.2.2.1 with
    ⟨lineAD, hAlineAD, hOlineAD, hDlineAD⟩

  rcases
      (HilbertOrder.between_incidence
        C P D hCPD).2.2.2.1 with
    ⟨linePC, hClinePC, hPlinePC, hDlinePC⟩

  have hLines : linePC ≠ lineAD := by
    intro hEq

    have hClineAD :
        HilbertIncidence.OnLine C lineAD := by
      rw [← hEq]
      exact hClinePC

    exact hAOC
      ⟨lineAD, hAlineAD, hOlineAD, hClineAD⟩

  have hBoffAD :
      ¬ HilbertIncidence.OnLine B lineAD := by
    intro hBlineAD

    have hEq : lineAD = base :=
      HilbertPlaneIncidence.line_unique
        O B hOB
        lineAD base
        hOlineAD hBlineAD
        hObase hBbase

    have hAbase :
        HilbertIncidence.OnLine A base := by
      rw [← hEq]
      exact hAlineAD

    exact hAoff hAbase

  have hPoffAD :
      ¬ HilbertIncidence.OnLine P lineAD := by
    intro hPlineAD

    have hEq : lineAD = base :=
      HilbertPlaneIncidence.line_unique
        O P hOP
        lineAD base
        hOlineAD hPlineAD
        hObase hPbase

    have hAbase :
        HilbertIncidence.OnLine A base := by
      rw [← hEq]
      exact hAlineAD

    exact hAoff hAbase

  have hCoffAD :
      ¬ HilbertIncidence.OnLine C lineAD := by
    intro hClineAD
    exact hAOC
      ⟨lineAD, hAlineAD, hOlineAD, hClineAD⟩

  have hMeetsBP :
      HilbertSegmentMeetsLine Geo B P lineAD :=
    ⟨O, hBOP, hOlineAD⟩

  have hCPDcol :
      PrimCollinear Geo C P D :=
    (HilbertOrder.between_incidence
      C P D hCPD).2.2.2.1

  have hNotPDC :
      ¬ Geo.Between P D C := by
    intro hPDC

    have hCDP :
        Geo.Between C D P :=
      (HilbertOrder.between_incidence
        P D C hPDC).2.2.2.2

    exact
      (HilbertOrder.between_unique
        C P D hCPDcol hCPD).2
        hCDP

  have hNotMeetsPC :
      ¬ HilbertSegmentMeetsLine Geo P C lineAD :=
    hilbert_segment_not_meets_crossing_line
      Geo
      P C D
      linePC lineAD
      hLines
      hPlinePC
      hClinePC
      hDlinePC
      hDlineAD
      hNotPDC

  have hBPC :
      ¬ PrimCollinear Geo B P C := by
    rintro ⟨m, hBm, hPm, hCm⟩

    have hBP : B ≠ P :=
      (HilbertOrder.between_incidence
        B O P hBOP).2.2.1

    have hEq : m = base :=
      HilbertPlaneIncidence.line_unique
        B P hBP
        m base
        hBm hPm
        hBbase hPbase

    have hCbase :
        HilbertIncidence.OnLine C base := by
      rw [← hEq]
      exact hCm

    exact hCoff hCbase

  rcases
      hilbert_pasch_forced
        Geo
        B P C
        lineAD
        hBPC
        hBoffAD
        hPoffAD
        hCoffAD
        hMeetsBP
        hNotMeetsPC with
    ⟨F, hBFC, hFlineAD⟩

  have hCFB :
      Geo.Between C F B :=
    (HilbertOrder.between_incidence
      B F C hBFC).2.2.2.2

  have hCBO :
      ¬ PrimCollinear Geo C B O := by
    rintro ⟨m, hCm, hBm, hOm⟩

    have hEq : m = base :=
      HilbertPlaneIncidence.line_unique
        O B hOB
        m base
        hOm hBm
        hObase hBbase

    have hCbase :
        HilbertIncidence.OnLine C base := by
      rw [← hEq]
      exact hCm

    exact hCoff hCbase

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        C F O B
        hCFB
        hCBO with
    ⟨lineOB, hOlineOB, hBlineOB, hSameCFlineOB⟩

  have hEqOB : lineOB = base :=
    HilbertPlaneIncidence.line_unique
      O B hOB
      lineOB base
      hOlineOB hBlineOB
      hObase hBbase

  have hSameCF :
      HilbertSameSide Geo C F base := by
    rw [← hEqOB]
    exact hSameCFlineOB

  have hSameAF :
      HilbertSameSide Geo A F base :=
    hilbert_sameSide_trans
      Geo A C F base
      hSame hSameCF

  have hFO : F ≠ O := by
    intro hFO
    subst F
    exact hSameAF.2.1 hObase

  have hAOFcol :
      PrimCollinear Geo O A F :=
    ⟨lineAD, hOlineAD, hAlineAD, hFlineAD⟩

  have hNotAOF :
      ¬ Geo.Between A O F := by
    intro hAOF

    have hOppAF :
        HilbertOppositeSide Geo A F base :=
      ⟨hSameAF.1,
       hSameAF.2.1,
       ⟨O, hAOF, hObase⟩⟩

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo A F base hOppAF)
        hSameAF

  have hRayOAF :
      HilbertSameRay Geo O A F :=
    ⟨hAO, hFO, hAOFcol, hNotAOF⟩

  exact ⟨F, hCFB, hRayOAF⟩

/--
The intersection point P lies between O and B.

If A-O-D, C-P-D and O-P-B, then ray OC meets the open
segment AB.
-/
theorem hilbert_sameSide_rays_order_case_OPB
    [HilbertOrder Geo]
    (O A B C D P : Geo.Point)
    (base : Geo.Line)
    (hOB : O ≠ B)
    (hObase : HilbertIncidence.OnLine O base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hPbase : HilbertIncidence.OnLine P base)
    (hAoff : ¬ HilbertIncidence.OnLine A base)
    (hCoff : ¬ HilbertIncidence.OnLine C base)
    (hSame : HilbertSameSide Geo A C base)
    (hAOC : ¬ PrimCollinear Geo A O C)
    (hADP : ¬ PrimCollinear Geo A D P)
    (hAPB : ¬ PrimCollinear Geo A P B)
    (hAOD : Geo.Between A O D)
    (hCPD : Geo.Between C P D)
    (hOPB : Geo.Between O P B) :
    HilbertRayMeetsSegment Geo O C A B := by

  --------------------------------------------------------------------
  -- First inner Pasch in triangle A-D-P:
  --
  -- D-P-C
  -- A-O-D
  --
  -- gives F with C-F-O and A-F-P.
  --------------------------------------------------------------------

  have hDPC :
      Geo.Between D P C :=
    (HilbertOrder.between_incidence
      C P D hCPD).2.2.2.2

  rcases
      hilbert_inner_pasch_strong
        Geo
        A D P
        C O
        hADP
        hDPC
        hAOD with
    ⟨F, hCFO, hAFP⟩

  have hOFC :
      Geo.Between O F C :=
    (HilbertOrder.between_incidence
      C F O hCFO).2.2.2.2

  --------------------------------------------------------------------
  -- Let lineOC be the line through O, F and C.
  --------------------------------------------------------------------

  rcases
      (HilbertOrder.between_incidence
        O F C hOFC).2.2.2.1 with
    ⟨lineOC, hOlineOC, hFlineOC, hClineOC⟩

  have hOP : O ≠ P :=
    (HilbertOrder.between_incidence
      O P B hOPB).1

  --------------------------------------------------------------------
  -- lineOC differs from base because C lies off base.
  --------------------------------------------------------------------

  have hLines :
      base ≠ lineOC := by
    intro hEq

    have hCbase :
        HilbertIncidence.OnLine C base := by
      rw [hEq]
      exact hClineOC

    exact hCoff hCbase

  --------------------------------------------------------------------
  -- The vertices A, P and B are outside lineOC.
  --------------------------------------------------------------------

  have hAoffOC :
      ¬ HilbertIncidence.OnLine A lineOC := by
    intro hAlineOC

    exact hAOC
      ⟨lineOC,
       hAlineOC,
       hOlineOC,
       hClineOC⟩

  have hPoffOC :
      ¬ HilbertIncidence.OnLine P lineOC := by
    intro hPlineOC

    have hEq : base = lineOC :=
      HilbertPlaneIncidence.line_unique
        O P hOP
        base lineOC
        hObase hPbase
        hOlineOC hPlineOC

    have hCbase :
        HilbertIncidence.OnLine C base := by
      rw [hEq]
      exact hClineOC

    exact hCoff hCbase

  have hBoffOC :
      ¬ HilbertIncidence.OnLine B lineOC := by
    intro hBlineOC

    have hEq : base = lineOC :=
      HilbertPlaneIncidence.line_unique
        O B hOB
        base lineOC
        hObase hBbase
        hOlineOC hBlineOC

    have hCbase :
        HilbertIncidence.OnLine C base := by
      rw [hEq]
      exact hClineOC

    exact hCoff hCbase

  --------------------------------------------------------------------
  -- lineOC meets AP at F.
  --------------------------------------------------------------------

  have hMeetsAP :
      HilbertSegmentMeetsLine Geo A P lineOC :=
    ⟨F, hAFP, hFlineOC⟩

  --------------------------------------------------------------------
  -- lineOC cannot meet the open segment PB:
  -- its only intersection with base is O, and O lies outside PB.
  --------------------------------------------------------------------

  have hOPBcol :
      PrimCollinear Geo O P B :=
    (HilbertOrder.between_incidence
      O P B hOPB).2.2.2.1

  have hNotPOB :
      ¬ Geo.Between P O B :=
    (HilbertOrder.between_unique
      O P B hOPBcol hOPB).1

  have hNotMeetsPB :
      ¬ HilbertSegmentMeetsLine Geo P B lineOC :=
    hilbert_segment_not_meets_crossing_line
      Geo
      P B O
      base lineOC
      hLines
      hPbase
      hBbase
      hObase
      hOlineOC
      hNotPOB

  --------------------------------------------------------------------
  -- Forced Pasch now gives G on AB and on lineOC.
  --------------------------------------------------------------------

  rcases
      hilbert_pasch_forced
        Geo
        A P B
        lineOC
        hAPB
        hAoffOC
        hPoffOC
        hBoffOC
        hMeetsAP
        hNotMeetsPB with
    ⟨G, hAGB, hGlineOC⟩

  --------------------------------------------------------------------
  -- A and G lie on the same side of base.
  --------------------------------------------------------------------

  have hABO :
      ¬ PrimCollinear Geo A B O := by
    rintro ⟨m, hAm, hBm, hOm⟩

    have hEq : m = base :=
      HilbertPlaneIncidence.line_unique
        O B hOB
        m base
        hOm hBm
        hObase hBbase

    have hAbase :
        HilbertIncidence.OnLine A base := by
      rw [← hEq]
      exact hAm

    exact hAoff hAbase

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        A G O B
        hAGB
        hABO with
    ⟨lineOB, hOlineOB, hBlineOB, hSameAGlineOB⟩

  have hEqOB : lineOB = base :=
    HilbertPlaneIncidence.line_unique
      O B hOB
      lineOB base
      hOlineOB hBlineOB
      hObase hBbase

  have hSameAG :
      HilbertSameSide Geo A G base := by
    rw [← hEqOB]
    exact hSameAGlineOB

  have hSameCA :
      HilbertSameSide Geo C A base :=
    hilbert_sameSide_symm
      Geo A C base hSame

  have hSameCG :
      HilbertSameSide Geo C G base :=
    hilbert_sameSide_trans
      Geo C A G base
      hSameCA hSameAG

  --------------------------------------------------------------------
  -- Since C and G are collinear with O and lie on the same side of
  -- base, they determine the same ray from O.
  --------------------------------------------------------------------

  have hCO : C ≠ O := by
    intro h
    subst C
    exact hCoff hObase

  have hGO : G ≠ O := by
    intro h
    subst G
    exact hSameCG.2.1 hObase

  have hOCGcol :
      PrimCollinear Geo O C G :=
    ⟨lineOC, hOlineOC, hClineOC, hGlineOC⟩

  have hNotCOG :
      ¬ Geo.Between C O G := by
    intro hCOG

    have hOppCG :
        HilbertOppositeSide Geo C G base :=
      ⟨hSameCG.1,
       hSameCG.2.1,
       ⟨O, hCOG, hObase⟩⟩

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo C G base hOppCG)
        hSameCG

  have hRayOCG :
      HilbertSameRay Geo O C G :=
    ⟨hCO, hGO, hOCGcol, hNotCOG⟩

  exact ⟨G, hAGB, hRayOCG⟩

/--
Ray ordering in one half-plane.

If A and C lie in the same half-plane bounded by the line OB,
and A, O, C are noncollinear, then one of the rays OA and OC
meets the open segment joining the other point to B.
-/
theorem hilbert_sameSide_rays_order
    [HilbertOrder Geo]
    (O A B C : Geo.Point)
    (base : Geo.Line)
    (hOB : O ≠ B)
    (hObase : HilbertIncidence.OnLine O base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hAoff : ¬ HilbertIncidence.OnLine A base)
    (hCoff : ¬ HilbertIncidence.OnLine C base)
    (hSame : HilbertSameSide Geo A C base)
    (hAOC : ¬ Collinear Geo A O C) :
    HilbertRayMeetsSegment Geo O A C B ∨
    HilbertRayMeetsSegment Geo O C A B := by

  --------------------------------------------------------------------
  -- Extend AO beyond O:
  --
  --   A - O - D.
  --------------------------------------------------------------------

  have hAO : A ≠ O := by
    intro h
    subst A
    exact hAoff hObase

  rcases
      HilbertOrder.between_extension
        A O hAO with
    ⟨D, hAOD⟩

  have hAODData :=
    HilbertOrder.between_incidence
      A O D hAOD

  have hOD : O ≠ D :=
    hAODData.2.1

  --------------------------------------------------------------------
  -- D is outside base.
  --------------------------------------------------------------------

  have hDoff :
      ¬ HilbertIncidence.OnLine D base := by
    intro hDbase

    rcases hAODData.2.2.2.1 with
      ⟨lineAD, hAlineAD, hOlineAD, hDlineAD⟩

    have hEq : lineAD = base :=
      HilbertPlaneIncidence.line_unique
        O D hOD
        lineAD base
        hOlineAD hDlineAD
        hObase hDbase

    have hAbase :
        HilbertIncidence.OnLine A base := by
      rw [← hEq]
      exact hAlineAD

    exact hAoff hAbase

  --------------------------------------------------------------------
  -- A and D lie on opposite sides of base because segment AD
  -- meets base at O.
  --------------------------------------------------------------------

  have hOppAD :
      HilbertOppositeSide Geo A D base :=
    ⟨hAoff, hDoff, ⟨O, hAOD, hObase⟩⟩

  have hOppDA :
      HilbertOppositeSide Geo D A base :=
    hilbert_oppositeSide_symm
      Geo A D base hOppAD

  --------------------------------------------------------------------
  -- Transport the opposite-side relation from A to C.
  --------------------------------------------------------------------

  have hOppDC :
      HilbertOppositeSide Geo D C base :=
    hilbert_oppositeSide_transport_right
      Geo D A C base hOppDA hSame

  have hOppCD :
      HilbertOppositeSide Geo C D base :=
    hilbert_oppositeSide_symm
      Geo D C base hOppDC

  --------------------------------------------------------------------
  -- Let P be the intersection of the open segment CD with base.
  --------------------------------------------------------------------

  rcases hOppCD.2.2 with
    ⟨P, hCPD, hPbase⟩

  --------------------------------------------------------------------
  -- P cannot equal O. Otherwise A, O, C would be collinear.
  --------------------------------------------------------------------

  have hPO : P ≠ O := by
    intro hPOeq
    subst P

    have hAODcol :
        Collinear Geo A O D :=
      hAODData.2.2.2.1

    have hCODcol :
        Collinear Geo C O D :=
      (HilbertOrder.between_incidence
        C O D hCPD).2.2.2.1

    have hODCcol :
        Collinear Geo O D C :=
      PrimCollinearCycle
        Geo C O D hCODcol

    have hAOCcol :
        Collinear Geo A O C :=
      hilbert_primCollinear_trans
        Geo
        A O D C
        hOD
        hAODcol
        hODCcol

    exact hAOC hAOCcol

  --------------------------------------------------------------------
  -- O, B and P lie on base.
  --------------------------------------------------------------------

  have hOBP :
      Collinear Geo O B P :=
    ⟨base, hObase, hBbase, hPbase⟩

  --------------------------------------------------------------------
  -- Remaining step:
  -- analyze the order of O, B and P and apply Pasch to obtain
  -- one of the two required ray-segment intersections.
  --------------------------------------------------------------------

  have hPposition :
      P = B ∨
      Geo.Between O B P ∨
      Geo.Between B O P ∨
      Geo.Between O P B := by
    by_cases hPB : P = B
    · exact Or.inl hPB
    ·
      have hBP : B ≠ P := by
        intro hBP
        exact hPB hBP.symm

      have hOP : O ≠ P :=
        hPO.symm

      rcases
          hilbert_between_trichotomy
            Geo
            O B P
            hOB
            hBP
            hOP
            hOBP with
        hOBPbetween | hBOP | hOPB

      · exact Or.inr (Or.inl hOBPbetween)
      · exact Or.inr (Or.inr (Or.inl hBOP))
      · exact Or.inr (Or.inr (Or.inr hOPB))

  --------------------------------------------------------------------
  -- P is either B itself or occupies one of the three possible
  -- positions on the line OB.
  --------------------------------------------------------------------

  rcases hPposition with
    hPB | hOBPbetween | hBOP | hOPB

  ·
    subst P

    have hADB :
        ¬ Collinear Geo A D B := by
      rintro ⟨m, hAm, hDm, hBm⟩

      rcases hAODData.2.2.2.1 with
        ⟨n, hAn, hOn, hDn⟩

      have hAD : A ≠ D :=
        hAODData.2.2.1

      have hmn : m = n :=
        HilbertPlaneIncidence.line_unique
          A D hAD
          m n
          hAm hDm
          hAn hDn

      have hBOn :
          HilbertIncidence.OnLine B n := by
        rw [← hmn]
        exact hBm

      have hEq : n = base :=
        HilbertPlaneIncidence.line_unique
          O B hOB
          n base
          hOn hBOn
          hObase hBbase

      have hAbase :
          HilbertIncidence.OnLine A base := by
        rw [← hEq]
        exact hAn

      exact hAoff hAbase

    exact
      Or.inr
        (hilbert_sameSide_rays_order_case_eq
          Geo O A B C D
          hADB
          hAOD
          hCPD)

  ·
    have hADP :
        ¬ Collinear Geo A D P := by
      rintro ⟨m, hAm, hDm, hPm⟩

      rcases hAODData.2.2.2.1 with
        ⟨n, hAn, hOn, hDn⟩

      have hAD : A ≠ D :=
        hAODData.2.2.1

      have hmn : m = n :=
        HilbertPlaneIncidence.line_unique
          A D hAD
          m n
          hAm hDm
          hAn hDn

      have hPn :
          HilbertIncidence.OnLine P n := by
        rw [← hmn]
        exact hPm

      have hOP : O ≠ P :=
        (HilbertOrder.between_incidence
          O B P hOBPbetween).2.2.1

      have hEq : n = base :=
        HilbertPlaneIncidence.line_unique
          O P hOP
          n base
          hOn hPn
          hObase hPbase

      have hAbase :
          HilbertIncidence.OnLine A base := by
        rw [← hEq]
        exact hAn

      exact hAoff hAbase

    have hAPB :
        ¬ Collinear Geo A P B := by
      rintro ⟨m, hAm, hPm, hBm⟩

      have hBP : B ≠ P :=
        (HilbertOrder.between_incidence
          O B P hOBPbetween).2.1

      have hEq : m = base :=
        HilbertPlaneIncidence.line_unique
          B P hBP
          m base
          hBm hPm
          hBbase hPbase

      have hAbase :
          HilbertIncidence.OnLine A base := by
        rw [← hEq]
        exact hAm

      exact hAoff hAbase

    exact
      Or.inr
        (hilbert_sameSide_rays_order_case_OBP
          Geo
          O A B C D P
          hADP
          hAPB
          hAOD
          hCPD
          hOBPbetween)

  ·
    exact
      Or.inl
        (hilbert_sameSide_rays_order_case_BOP
          Geo
          O A B C D P
          base
          hOB
          hObase
          hBbase
          hPbase
          hAoff
          hCoff
          hSame
          hAOC
          hAOD
          hCPD
          hBOP)

  ·
    have hADP :
        ¬ PrimCollinear Geo A D P := by
      rintro ⟨m, hAm, hDm, hPm⟩

      rcases hAODData.2.2.2.1 with
        ⟨n, hAn, hOn, hDn⟩

      have hAD : A ≠ D :=
        hAODData.2.2.1

      have hmn : m = n :=
        HilbertPlaneIncidence.line_unique
          A D hAD
          m n
          hAm hDm
          hAn hDn

      have hPn :
          HilbertIncidence.OnLine P n := by
        rw [← hmn]
        exact hPm

      have hOP : O ≠ P :=
        (HilbertOrder.between_incidence
          O P B hOPB).1

      have hEq : n = base :=
        HilbertPlaneIncidence.line_unique
          O P hOP
          n base
          hOn hPn
          hObase hPbase

      have hAbase :
          HilbertIncidence.OnLine A base := by
        rw [← hEq]
        exact hAn

      exact hAoff hAbase

    have hAPB :
        ¬ PrimCollinear Geo A P B := by
      rintro ⟨m, hAm, hPm, hBm⟩

      have hPB : P ≠ B :=
        (HilbertOrder.between_incidence
          O P B hOPB).2.1

      have hEq : m = base :=
        HilbertPlaneIncidence.line_unique
          P B hPB
          m base
          hPm hBm
          hPbase hBbase

      have hAbase :
          HilbertIncidence.OnLine A base := by
        rw [← hEq]
        exact hAm

      exact hAoff hAbase

    exact
      Or.inr
        (hilbert_sameSide_rays_order_case_OPB
          Geo
          O A B C D P
          base
          hOB
          hObase
          hBbase
          hPbase
          hAoff
          hCoff
          hSame
          hAOC
          hADP
          hAPB
          hAOD
          hCPD
          hOPB)






/-
Uniqueness of angle construction on a prescribed side.

If H and K lie on the same side of the reference line OL and
the angles OLH and OLK are congruent, then both rays LH and LK
coincide with the unique ray obtained from Hilbert III.4.
-/
theorem hilbert_angle_unique_common_ray
    [HilbertCongruence Geo]
    (O L H K : Geo.Point)
    (line : Geo.Line)
    (hOL : O ≠ L)
    (hOline : HilbertIncidence.OnLine O line)
    (hLline : HilbertIncidence.OnLine L line)
    (hHoff : ¬ HilbertIncidence.OnLine H line)
    (hSameHK : HilbertSameSide Geo H K line)
    (hAngle :
      Geo.AngleCongruent O L H O L K) :
    ∃ X : Geo.Point,
      HilbertSameRay Geo L X H ∧
      HilbertSameRay Geo L X K := by

  have hOLH :
      ¬ Collinear Geo O L H := by
    rintro ⟨m, hOm, hLm, hHm⟩

    have hEq : m = line :=
      HilbertPlaneIncidence.line_unique
        O L hOL
        m line
        hOm hLm
        hOline hLline

    exact hHoff (hEq ▸ hHm)

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        O L H
        O L H
        hOLH
        hOL
        line
        hOline
        hLline
        hHoff with
    ⟨X, hXHSame, hAngleX, hUnique⟩

  have hHHSame :
      HilbertSameSide Geo H H line :=
    hilbert_sameSide_refl
      Geo H line hHoff

  have hRayXH :
      HilbertSameRay Geo L X H :=
    hUnique
      H
      hHHSame
      (HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo)
        O L H
        hOLH)

  have hKHSame :
      HilbertSameSide Geo K H line :=
    hilbert_sameSide_symm
      Geo H K line hSameHK

  have hRayXK :
      HilbertSameRay Geo L X K :=
    hUnique
      K
      hKHSame
      hAngle

  exact ⟨X, hRayXH, hRayXK⟩





/-
Hilbert Theorem 15, same-side case.

Case 1:
the ray OA meets the segment CB,
and the corresponding ray O'A' meets C'B'.

This theorem contains the geometric core of Hilbert's proof.
-/
theorem hilbert_angle_addition_sameSide_case1
    [HilbertCongruence Geo]
    (A O B C A' O' B' C' : Geo.Point)
    (l l' : Geo.Line)
    (hOB : O ≠ B)
    (hO'B' : O' ≠ B')
    (hOl : HilbertIncidence.OnLine O l)
    (hBl : HilbertIncidence.OnLine B l)
    (hO'l' : HilbertIncidence.OnLine O' l')
    (hB'l' : HilbertIncidence.OnLine B' l')
    (hAoff : ¬ HilbertIncidence.OnLine A l)
    (hCoff : ¬ HilbertIncidence.OnLine C l)
    (hA'off : ¬ HilbertIncidence.OnLine A' l')
    (hC'off : ¬ HilbertIncidence.OnLine C' l')
    (hSame' : HilbertSameSide Geo A' C' l')
    (hRay :
      HilbertRayMeetsSegment Geo O A C B)
    (hAB : Geo.AngleCongruent A O B A' O' B')
    (hBC : Geo.AngleCongruent B O C B' O' C') :
    Geo.AngleCongruent A O C A' O' C' := by

  --------------------------------------------------------------------
  -- H is the intersection of ray OA with segment CB.
  --------------------------------------------------------------------

  rcases hRay with
    ⟨H, hCHB, hRayAH⟩

  have hOC : O ≠ C := by
    intro hEq
    subst C
    exact hCoff hOl

  have hO'C' : O' ≠ C' := by
    intro hEq
    subst C'
    exact hC'off hO'l'

  have hO'A' : O' ≠ A' := by
    intro hEq
    subst A'
    exact hA'off hO'l'

  --------------------------------------------------------------------
  -- We take K = C and L = B.
  --
  -- Construct K' on ray O'C' so that
  --
  --   O'K' congruent OC.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O C
        O' C'
        hO'C' with
    ⟨K', hRayC'K', hO'K'_OC⟩

  have hOC_O'K' :
      Geo.Congruent O C O' K' :=
    hilbert_congruent_symmetry
      Geo O' K' O C hO'K'_OC

  --------------------------------------------------------------------
  -- Construct L' on ray O'B' so that
  --
  --   O'L' congruent OB.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O B
        O' B'
        hO'B' with
    ⟨L', hRayB'L', hO'L'_OB⟩

  have hOB_O'L' :
      Geo.Congruent O B O' L' :=
    hilbert_congruent_symmetry
      Geo O' L' O B hO'L'_OB

  --------------------------------------------------------------------
  -- Construct H' on ray O'A' so that
  --
  --   O'H' congruent OH.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O H
        O' A'
        hO'A' with
    ⟨H', hRayA'H', hO'H'_OH⟩

  have hOH_O'H' :
      Geo.Congruent O H O' H' :=
    hilbert_congruent_symmetry
      Geo O' H' O H hO'H'_OH

  --------------------------------------------------------------------
  -- Remaining Hilbert construction:
  --
  -- 1. transport the two assumed angle congruences from A,B,C,A',B',C'
  --    to H,B,C,H',L',K';
  -- 2. use SAS for triangles OBH / O'L'H' and OBC / O'L'K';
  -- 3. prove H' lies between K' and L' by angle-construction uniqueness;
  -- 4. derive HK congruent H'K';
  -- 5. finish by SAS.
  --------------------------------------------------------------------
  have hAngleHOB :
      Geo.AngleCongruent H O B H' O' L' := by

    have hLeft :
        Geo.Angle A O B =
        Geo.Angle H O B :=
      hilbert_angle_eq_of_sameRay_first
        Geo O A H B hRayAH

    have hRightFirst :
        Geo.Angle A' O' B' =
        Geo.Angle H' O' B' :=
      hilbert_angle_eq_of_sameRay_first
        Geo O' A' H' B' hRayA'H'

    have hRightSecond :
        Geo.Angle H' O' B' =
        Geo.Angle H' O' L' :=
      hilbert_angle_eq_of_sameRay_second
        Geo O' H' B' L' hRayB'L'

    have hRight :
        Geo.Angle A' O' B' =
        Geo.Angle H' O' L' :=
      hRightFirst.trans hRightSecond

    unfold Geometry.Geo.AngleCongruent at hAB ⊢
    rw [← hLeft, ← hRight]
    exact hAB

  have hAngleBOC :
      Geo.AngleCongruent B O C L' O' K' := by

    have hRightFirst :
        Geo.Angle B' O' C' =
        Geo.Angle L' O' C' :=
      hilbert_angle_eq_of_sameRay_first
        Geo O' B' L' C' hRayB'L'

    have hRightSecond :
        Geo.Angle L' O' C' =
        Geo.Angle L' O' K' :=
      hilbert_angle_eq_of_sameRay_second
        Geo O' L' C' K' hRayC'K'

    have hRight :
        Geo.Angle B' O' C' =
        Geo.Angle L' O' K' :=
      hRightFirst.trans hRightSecond

    unfold Geometry.Geo.AngleCongruent at hBC ⊢
    rw [← hRight]
    exact hBC

  --------------------------------------------------------------------
  -- The component-angle congruences now have the exact forms needed
  -- for the two applications of SAS:
  --
  --    angle HOB congruent angle H'O'L'
  --    angle BOC congruent angle L'O'K'.
  --------------------------------------------------------------------
    --------------------------------------------------------------------
  -- The constructed points L', H', K' lie respectively on or off l'.
  --------------------------------------------------------------------

  have hO'L' : O' ≠ L' :=
    hRayB'L'.2.1.symm

  have hO'H' : O' ≠ H' :=
    hRayA'H'.2.1.symm

  have hO'K' : O' ≠ K' :=
    hRayC'K'.2.1.symm

  have hL'line :
      HilbertIncidence.OnLine L' l' := by
    rcases hRayB'L'.2.2.1 with
      ⟨m, hO'm, hB'm, hL'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' B' hO'B'
        m l'
        hO'm hB'm
        hO'l' hB'l'

    rw [← hEq]
    exact hL'm

  have hH'off :
      ¬ HilbertIncidence.OnLine H' l' := by
    intro hH'line

    rcases hRayA'H'.2.2.1 with
      ⟨m, hO'm, hA'm, hH'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' H' hO'H'
        m l'
        hO'm hH'm
        hO'l' hH'line

    have hA'line :
        HilbertIncidence.OnLine A' l' := by
      rw [← hEq]
      exact hA'm

    exact hA'off hA'line

  have hK'off :
      ¬ HilbertIncidence.OnLine K' l' := by
    intro hK'line

    rcases hRayC'K'.2.2.1 with
      ⟨m, hO'm, hC'm, hK'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' K' hO'K'
        m l'
        hO'm hK'm
        hO'l' hK'line

    have hC'line :
        HilbertIncidence.OnLine C' l' := by
      rw [← hEq]
      exact hC'm

    exact hC'off hC'line

  --------------------------------------------------------------------
  -- H is off l because it lies on ray OA, while A is off l.
  --------------------------------------------------------------------

  have hOH : O ≠ H :=
    hRayAH.2.1.symm

  have hHoff :
      ¬ HilbertIncidence.OnLine H l := by
    intro hHline

    rcases hRayAH.2.2.1 with
      ⟨m, hOm, hAm, hHm⟩

    have hEq : m = l :=
      HilbertPlaneIncidence.line_unique
        O H hOH
        m l
        hOm hHm
        hOl hHline

    have hAline :
        HilbertIncidence.OnLine A l := by
      rw [← hEq]
      exact hAm

    exact hAoff hAline

  --------------------------------------------------------------------
  -- Noncollinearity of the four triangles used in SAS.
  --------------------------------------------------------------------

  have hOBH :
      ¬ Collinear Geo O B H := by
    rintro ⟨m, hOm, hBm, hHm⟩

    have hEq : m = l :=
      HilbertPlaneIncidence.line_unique
        O B hOB
        m l
        hOm hBm
        hOl hBl

    exact hHoff (hEq ▸ hHm)

  have hO'L'H' :
      ¬ Collinear Geo O' L' H' := by
    rintro ⟨m, hO'm, hL'm, hH'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' L' hO'L'
        m l'
        hO'm hL'm
        hO'l' hL'line

    exact hH'off (hEq ▸ hH'm)

  have hOBC :
      ¬ Collinear Geo O B C := by
    rintro ⟨m, hOm, hBm, hCm⟩

    have hEq : m = l :=
      HilbertPlaneIncidence.line_unique
        O B hOB
        m l
        hOm hBm
        hOl hBl

    exact hCoff (hEq ▸ hCm)

  have hO'L'K' :
      ¬ Collinear Geo O' L' K' := by
    rintro ⟨m, hO'm, hL'm, hK'm⟩

    have hEq : m = l' :=
      HilbertPlaneIncidence.line_unique
        O' L' hO'L'
        m l'
        hO'm hL'm
        hO'l' hL'line

    exact hK'off (hEq ▸ hK'm)

  --------------------------------------------------------------------
  -- Reverse the first transported angle to match the SAS orientation.
  --------------------------------------------------------------------

  have hAngleBOH :
      Geo.AngleCongruent B O H L' O' H' :=
    AngleCongruentReverse
      Geo
      H O B
      H' O' L'
      hAngleHOB

  --------------------------------------------------------------------
  -- Hilbert Theorem 12 for OBH / O'L'H'.
  --------------------------------------------------------------------

  have hTrianglesOBH :=
    SAS
      Geo
      O B H
      O' L' H'
      hOBH
      hO'L'H'
      hOB_O'L'
      hAngleBOH
      hOH_O'H'

  --------------------------------------------------------------------
  -- Hilbert Theorem 12 for OBC / O'L'K'.
  --------------------------------------------------------------------

  have hTrianglesOBC :=
    SAS
      Geo
      O B C
      O' L' K'
      hOBC
      hO'L'K'
      hOB_O'L'
      hAngleBOC
      hOC_O'K'

  have hBH_L'H' :
      Geo.Congruent B H L' H' :=
    hTrianglesOBH.sideBC

  have hBC_L'K' :
      Geo.Congruent B C L' K' :=
    hTrianglesOBC.sideBC

  have hAngleOBH :
      Geo.AngleCongruent O B H O' L' H' :=
    hTrianglesOBH.angleB

  have hAngleOBC :
      Geo.AngleCongruent O B C O' L' K' :=
    hTrianglesOBC.angleB

  --------------------------------------------------------------------
  -- Next:
  -- use H between C and B and angle-construction uniqueness to prove
  -- that H' lies on the segment K'L'.
  --------------------------------------------------------------------
  --------------------------------------------------------------------
  -- Since H lies between C and B, the rays BH and BC coincide.
  --------------------------------------------------------------------

  have hBHC :
      Geo.Between B H C :=
    (HilbertOrder.between_incidence
      C H B hCHB).2.2.2.2

  have hRayBHC :
      HilbertSameRay Geo B H C :=
    hilbert_sameRay_of_between
      Geo B H C hBHC

  have hAngleOBH_eq_OBC :
      Geo.Angle O B H =
      Geo.Angle O B C :=
    hilbert_angle_eq_of_sameRay_second
      Geo B O H C hRayBHC

  --------------------------------------------------------------------
  -- Replace BH by BC in the first SAS conclusion.
  --------------------------------------------------------------------

  have hAngleOBC_L'H' :
      Geo.AngleCongruent O B C O' L' H' := by
    unfold Geometry.Geo.AngleCongruent at hAngleOBH ⊢
    rw [← hAngleOBH_eq_OBC]
    exact hAngleOBH

  --------------------------------------------------------------------
  -- Therefore the two angles at L' are congruent:
  --
  --    angle O'L'H' congruent angle O'L'K'.
  --------------------------------------------------------------------

  have hAngleL'H'_L'K' :
      Geo.AngleCongruent O' L' H' O' L' K' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      O' L' H'
      O B C
      O' L' K'
      (by
        unfold Geometry.Geo.AngleCongruent at hAngleOBC_L'H' ⊢
        exact hAngleOBC_L'H'.symm)
      hAngleOBC

  --------------------------------------------------------------------
  -- The next step is the uniqueness clause of angle construction:
  -- H' and K' determine the same ray from L'.
  --------------------------------------------------------------------
  --------------------------------------------------------------------
  -- Transport the same-side relation from A', C' to H', K'.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        O' A' hO'A' with
    ⟨lineA', hO'lineA', hA'lineA'⟩

  have hB'notLineA' :
      ¬ HilbertIncidence.OnLine B' lineA' := by
    intro hB'lineA'

    have hEq : l' = lineA' :=
      HilbertPlaneIncidence.line_unique
        O' B' hO'B'
        l' lineA'
        hO'l' hB'l'
        hO'lineA' hB'lineA'

    have hA'line :
        HilbertIncidence.OnLine A' l' := by
      rw [hEq]
      exact hA'lineA'

    exact hA'off hA'line

  have hA'H'Same :
      HilbertSameSide Geo A' H' l' :=
    hilbert_sameRay_points_sameSide
      Geo
      O' A'
      A' H'
      B'
      lineA' l'
      hO'lineA' hA'lineA'
      hO'l' hB'l'
      hB'notLineA'
      (hilbert_sameRay_refl
        Geo O' A' hO'A'.symm)
      hRayA'H'

  rcases
      HilbertPlaneIncidence.line_through
        O' C' hO'C' with
    ⟨lineC', hO'lineC', hC'lineC'⟩

  have hB'notLineC' :
      ¬ HilbertIncidence.OnLine B' lineC' := by
    intro hB'lineC'

    have hEq : l' = lineC' :=
      HilbertPlaneIncidence.line_unique
        O' B' hO'B'
        l' lineC'
        hO'l' hB'l'
        hO'lineC' hB'lineC'

    have hC'line :
        HilbertIncidence.OnLine C' l' := by
      rw [hEq]
      exact hC'lineC'

    exact hC'off hC'line

  have hC'K'Same :
      HilbertSameSide Geo C' K' l' :=
    hilbert_sameRay_points_sameSide
      Geo
      O' C'
      C' K'
      B'
      lineC' l'
      hO'lineC' hC'lineC'
      hO'l' hB'l'
      hB'notLineC'
      (hilbert_sameRay_refl
        Geo O' C' hO'C'.symm)
      hRayC'K'

  have hH'A'Same :
      HilbertSameSide Geo H' A' l' :=
    hilbert_sameSide_symm
      Geo A' H' l' hA'H'Same

  have hH'C'Same :
      HilbertSameSide Geo H' C' l' :=
    hilbert_sameSide_trans
      Geo H' A' C' l'
      hH'A'Same hSame'

  have hH'K'Same :
      HilbertSameSide Geo H' K' l' :=
    hilbert_sameSide_trans
      Geo H' C' K' l'
      hH'C'Same hC'K'Same

  --------------------------------------------------------------------
  -- By uniqueness of angle construction, H' and K' belong to the
  -- same uniquely determined ray from L'.
  --------------------------------------------------------------------

  rcases
      hilbert_angle_unique_common_ray
        Geo
        O' L' H' K'
        l'
        hO'L'
        hO'l'
        hL'line
        hH'off
        hH'K'Same
        hAngleL'H'_L'K' with
    ⟨X, hRayXH', hRayXK'⟩

  --------------------------------------------------------------------
  -- Next: derive directly that H' and K' lie on the same ray from L'.
  --------------------------------------------------------------------

  have hRayH'K' :
      HilbertSameRay Geo L' H' K' :=
    hilbert_sameRay_of_common
      Geo
      L' X H' K'
      hRayXH'
      hRayXK'

  --------------------------------------------------------------------
  -- H' and K' now lie on the same ray from L'.
  -- The remaining task is to determine their order on that ray.
  --------------------------------------------------------------------
  have hRayH'K' :
      HilbertSameRay Geo L' H' K' :=
    hilbert_sameRay_of_common
      Geo
      L' X H' K'
      hRayXH'
      hRayXK'
  have hL'H' : L' ≠ H' :=
    hRayH'K'.1.symm

  rcases
      HilbertOrder.between_extension
        L' H' hL'H' with
    ⟨T', hL'H'T'⟩

  have hH'T' : H' ≠ T' :=
    (HilbertOrder.between_incidence
      L' H' T' hL'H'T').2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        H C
        H' T'
        hH'T' with
    ⟨J', hRayT'J', hH'J'_HC⟩

  have hRayL'L' :
      HilbertSameRay Geo H' L' L' :=
    hilbert_sameRay_refl
      Geo H' L' hL'H'

  have hL'H'J' :
      Geo.Between L' H' J' :=
    hilbert_between_transport_sameRays
      Geo
      L' H' T'
      L' J'
      hL'H'T'
      hRayL'L'
      hRayT'J'

  have hRayH'J' :
      HilbertSameRay Geo L' H' J' :=
    hilbert_sameRay_of_between
      Geo L' H' J' hL'H'J'
  have hBHC :
      Geo.Between B H C :=
    (HilbertOrder.between_incidence
      C H B hCHB).2.2.2.2

  have hHC_H'J' :
      Geo.Congruent H C H' J' :=
    hilbert_congruent_symmetry
      Geo H' J' H C hH'J'_HC

  have hBC_L'J' :
      Geo.Congruent B C L' J' :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      B H C
      L' H' J'
      hBHC
      hL'H'J'
      hBH_L'H'
      hHC_H'J'

  have hL'J'_BC :
      Geo.Congruent L' J' B C :=
    hilbert_congruent_symmetry
      Geo B C L' J' hBC_L'J'

  have hL'K'_BC :
      Geo.Congruent L' K' B C :=
    hilbert_congruent_symmetry
      Geo B C L' K' hBC_L'K'

  have hJ'K' : J' = K' :=
    hilbert_segment_construction_unique
      Geo
      B C
      L' H'
      J' K'
      hRayH'J'
      hRayH'K'
      hL'J'_BC
      hL'K'_BC

  subst K'

  have hL'H'K' :
      Geo.Between L' H' J' :=
    hL'H'J'
  have hBHO :
      ¬ Collinear Geo B H O := by
    rintro ⟨m, hBm, hHm, hOm⟩
    exact hOBH ⟨m, hOm, hBm, hHm⟩

  have hL'H'O' :
      ¬ Collinear Geo L' H' O' := by
    rintro ⟨m, hL'm, hH'm, hO'm⟩
    exact hO'L'H' ⟨m, hO'm, hL'm, hH'm⟩

  have hAngleBHO_L'H'O' :
      Geo.AngleCongruent B H O L' H' O' :=
    AngleCongruentReverse
      Geo
      O H B
      O' H' L'
      hTrianglesOBH.angleC

  have hAngleOHC :
      Geo.AngleCongruent O H C O' H' J' :=
    hilbert_adjacent_angles_congruent
      Geo
      B H O C
      L' H' O' J'
      hBHC
      hL'H'J'
      hBHO
      hL'H'O'
      hAngleBHO_L'H'O'

  have hHOC :
      ¬ Collinear Geo H O C := by
    rintro ⟨m, hHm, hOm, hCm⟩

    rcases
        (HilbertOrder.between_incidence
          B H C hBHC).2.2.2.1 with
      ⟨n, hBn, hHn, hCn⟩

    have hHC : H ≠ C :=
      (HilbertOrder.between_incidence
        B H C hBHC).2.1

    have hmn : m = n :=
      HilbertPlaneIncidence.line_unique
        H C hHC
        m n
        hHm hCm
        hHn hCn

    have hBm :
        HilbertIncidence.OnLine B m := by
      rw [hmn]
      exact hBn

    exact hOBH ⟨m, hOm, hBm, hHm⟩

  have hH'O'J' :
      ¬ Collinear Geo H' O' J' := by
    rintro ⟨m, hH'm, hO'm, hJ'm⟩

    rcases
        (HilbertOrder.between_incidence
          L' H' J' hL'H'J').2.2.2.1 with
      ⟨n, hL'n, hH'n, hJ'n⟩

    have hH'J' : H' ≠ J' :=
      (HilbertOrder.between_incidence
        L' H' J' hL'H'J').2.1

    have hmn : m = n :=
      HilbertPlaneIncidence.line_unique
        H' J' hH'J'
        m n
        hH'm hJ'm
        hH'n hJ'n

    have hL'm :
        HilbertIncidence.OnLine L' m := by
      rw [hmn]
      exact hL'n

    exact hO'L'H' ⟨m, hO'm, hL'm, hH'm⟩

  have hHO_H'O' :
      Geo.Congruent H O H' O' :=
    CongruentReverseBoth
      Geo
      O H
      O' H'
      hOH_O'H'

  have hFinal :=
    SAS
      Geo
      H O C
      H' O' J'
      hHOC
      hH'O'J'
      hHO_H'O'
      hAngleOHC
      hHC_H'J'

  have hAngleHOC_H'O'J' :
      Geo.AngleCongruent H O C H' O' J' :=
    hFinal.angleB

  have hLeft :
      Geo.Angle A O C =
      Geo.Angle H O C :=
    hilbert_angle_eq_of_sameRay_first
      Geo O A H C hRayAH

  have hRightFirst :
      Geo.Angle A' O' C' =
      Geo.Angle H' O' C' :=
    hilbert_angle_eq_of_sameRay_first
      Geo O' A' H' C' hRayA'H'

  have hRightSecond :
      Geo.Angle H' O' C' =
      Geo.Angle H' O' J' :=
    hilbert_angle_eq_of_sameRay_second
      Geo O' H' C' J' hRayC'K'

  have hRight :
      Geo.Angle A' O' C' =
      Geo.Angle H' O' J' :=
    hRightFirst.trans hRightSecond

  unfold Geometry.Geo.AngleCongruent at hAngleHOC_H'O'J' ⊢
  rw [hLeft, hRight]
  exact hAngleHOC_H'O'J'






/--
If C lies on the side of a line opposite to A, and D is obtained by
extending AO beyond O, then C and D lie on the same side of the line.

This is the half-plane reduction used in the opposite-side case of
Hilbert's Theorem 15.
-/
theorem hilbert_sameSide_after_opposite_extension
    [HilbertOrder Geo]
    (A O C D : Geo.Point)
    (l : Geo.Line)
    (hOl : HilbertIncidence.OnLine O l)
    (hAOC : ¬ PrimCollinear Geo A O C)
    (hAOD : Geo.Between A O D)
    (hOppAC : HilbertOppositeSide Geo A C l) :
    HilbertSameSide Geo C D l := by

  rcases hOppAC.2.2 with
    ⟨X, hAXC, hXl⟩

  have hACD :
      ¬ PrimCollinear Geo A C D := by
    rintro ⟨m, hAm, hCm, hDm⟩

    rcases
        (HilbertOrder.between_incidence
          A O D hAOD).2.2.2.1 with
      ⟨n, hAn, hOn, hDn⟩

    have hAD : A ≠ D :=
      (HilbertOrder.between_incidence
        A O D hAOD).2.2.1

    have hmn : m = n :=
      HilbertPlaneIncidence.line_unique
        A D hAD
        m n
        hAm hDm
        hAn hDn

    have hOm :
        HilbertIncidence.OnLine O m := by
      rw [hmn]
      exact hOn

    exact hAOC
      ⟨m, hAm, hOm, hCm⟩

  exact
    hilbert_third_side_endpoints_sameSide
      Geo
      A C D
      X O
      l
      hACD
      hAXC
      hAOD
      hXl
      hOl


/--
Hilbert Theorem 15, same-side case.

The outer rays OA and OC lie on the same side of the reference
line OB, and likewise O'A' and O'C' lie on the same side of O'B'.

If the two component angles with the reference rays are pairwise
congruent, then the angles formed by the outer rays are congruent.
-/

theorem hilbert_angle_addition_sameSide
    [HilbertCongruence Geo]
    (A O B C A' O' B' C' : Geo.Point)
    (l l' : Geo.Line)
    (hOB : O ≠ B)
    (hO'B' : O' ≠ B')
    (hOl : HilbertIncidence.OnLine O l)
    (hBl : HilbertIncidence.OnLine B l)
    (hO'l' : HilbertIncidence.OnLine O' l')
    (hB'l' : HilbertIncidence.OnLine B' l')
    (hAoff : ¬ HilbertIncidence.OnLine A l)
    (hCoff : ¬ HilbertIncidence.OnLine C l)
    (hA'off : ¬ HilbertIncidence.OnLine A' l')
    (hC'off : ¬ HilbertIncidence.OnLine C' l')
    (hSame : HilbertSameSide Geo A C l)
    (hSame' : HilbertSameSide Geo A' C' l')
    (hAOC : ¬ Collinear Geo A O C)
    (hAB : Geo.AngleCongruent A O B A' O' B')
    (hBC : Geo.AngleCongruent B O C B' O' C') :
    Geo.AngleCongruent A O C A' O' C' := by

  rcases
      hilbert_sameSide_rays_order
        Geo
        O A B C
        l
        hOB
        hOl
        hBl
        hAoff
        hCoff
        hSame
        hAOC with
    hRayA | hRayC

  ·
    exact
      hilbert_angle_addition_sameSide_case1
        Geo
        A O B C
        A' O' B' C'
        l l'
        hOB
        hO'B'
        hOl
        hBl
        hO'l'
        hB'l'
        hAoff
        hCoff
        hA'off
        hC'off
        hSame'
        hRayA
        hAB
        hBC

  ·
    have hSameRev' :
        HilbertSameSide Geo C' A' l' :=
      hilbert_sameSide_symm
        Geo A' C' l' hSame'

    have hCB :
        Geo.AngleCongruent C O B C' O' B' :=
      AngleCongruentReverse
        Geo
        B O C
        B' O' C'
        hBC

    have hBA :
        Geo.AngleCongruent B O A B' O' A' :=
      AngleCongruentReverse
        Geo
        A O B
        A' O' B'
        hAB

    have hCOA :
        Geo.AngleCongruent C O A C' O' A' :=
      hilbert_angle_addition_sameSide_case1
        Geo
        C O B A
        C' O' B' A'
        l l'
        hOB
        hO'B'
        hOl
        hBl
        hO'l'
        hB'l'
        hCoff
        hAoff
        hC'off
        hA'off
        hSameRev'
        hRayC
        hCB
        hBA

    exact
      AngleCongruentReverse
        Geo
        C O A
        C' O' A'
        hCOA

/--
Two points outside a line which are not on the same side of the line
lie on opposite sides of it.
-/
theorem hilbert_oppositeSide_of_not_sameSide
    [HilbertOrder Geo]
    (P Q : Geo.Point)
    (l : Geo.Line)
    (hPoff : ¬ HilbertIncidence.OnLine P l)
    (hQoff : ¬ HilbertIncidence.OnLine Q l)
    (hNotSame : ¬ HilbertSameSide Geo P Q l) :
    HilbertOppositeSide Geo P Q l := by

  refine ⟨hPoff, hQoff, ?_⟩

  by_contra hNoMeet

  apply hNotSame

  exact
    ⟨hPoff,
     hQoff,
     Relation.ReflTransGen.single
       ⟨hPoff, hQoff, hNoMeet⟩⟩


/--
Hilbert Theorem 15.

The rays OA, OC and O'A', O'C' have corresponding side
configurations with respect to the reference lines OB and O'B'.
If the two component angles are pairwise congruent, then the
angles formed by the outer rays are congruent.
-/
theorem hilbert_angle_addition
    [HilbertCongruence Geo]
    (A O B C A' O' B' C' : Geo.Point)
    (l l' : Geo.Line)
    (hOB : O ≠ B)
    (hO'B' : O' ≠ B')
    (hOl : HilbertIncidence.OnLine O l)
    (hBl : HilbertIncidence.OnLine B l)
    (hO'l' : HilbertIncidence.OnLine O' l')
    (hB'l' : HilbertIncidence.OnLine B' l')
    (hAoff : ¬ HilbertIncidence.OnLine A l)
    (hCoff : ¬ HilbertIncidence.OnLine C l)
    (hA'off : ¬ HilbertIncidence.OnLine A' l')
    (hC'off : ¬ HilbertIncidence.OnLine C' l')
    (hSideConfiguration :
      HilbertSameSide Geo A C l ↔
      HilbertSameSide Geo A' C' l')
    (hAOC : ¬ Collinear Geo A O C)
    (hA'O'C' : ¬ Collinear Geo A' O' C')
    (hAB : Geo.AngleCongruent A O B A' O' B')
    (hBC : Geo.AngleCongruent B O C B' O' C') :
    Geo.AngleCongruent A O C A' O' C' := by

  by_cases hSame :
      HilbertSameSide Geo A C l

  --------------------------------------------------------------------
  -- Same-side configuration.
  --------------------------------------------------------------------

  ·
    have hSame' :
        HilbertSameSide Geo A' C' l' :=
      hSideConfiguration.mp hSame

    exact
      hilbert_angle_addition_sameSide
        Geo
        A O B C
        A' O' B' C'
        l l'
        hOB
        hO'B'
        hOl
        hBl
        hO'l'
        hB'l'
        hAoff
        hCoff
        hA'off
        hC'off
        hSame
        hSame'
        hAOC
        hAB
        hBC

  --------------------------------------------------------------------
  -- Opposite-side configuration.
  --
  -- Extend OA and O'A' beyond O and O'. The opposite extensions
  -- lie on the same sides of the reference lines as C and C'.
  -- Theorem 14 transfers the component angle congruence to the
  -- supplementary angles, reducing the problem to the same-side case.
  --------------------------------------------------------------------

  ·
    have hNotSame' :
        ¬ HilbertSameSide Geo A' C' l' := by
      intro hSame'
      exact hSame (hSideConfiguration.mpr hSame')

    have hOppAC :
        HilbertOppositeSide Geo A C l :=
      hilbert_oppositeSide_of_not_sameSide
        Geo A C l
        hAoff hCoff hSame

    have hOppA'C' :
        HilbertOppositeSide Geo A' C' l' :=
      hilbert_oppositeSide_of_not_sameSide
        Geo A' C' l'
        hA'off hC'off hNotSame'

    have hAO : A ≠ O := by
      intro h
      subst A
      exact hAoff hOl

    have hA'O' : A' ≠ O' := by
      intro h
      subst A'
      exact hA'off hO'l'

    rcases
        HilbertOrder.between_extension
          A O hAO with
      ⟨D, hAOD⟩

    rcases
        HilbertOrder.between_extension
          A' O' hA'O' with
      ⟨D', hA'O'D'⟩

    have hSameCD :
        HilbertSameSide Geo C D l :=
      hilbert_sameSide_after_opposite_extension
        Geo
        A O C D
        l
        hOl
        hAOC
        hAOD
        hOppAC

    have hSameC'D' :
        HilbertSameSide Geo C' D' l' :=
      hilbert_sameSide_after_opposite_extension
        Geo
        A' O' C' D'
        l'
        hO'l'
        hA'O'C'
        hA'O'D'
        hOppA'C'

    have hSameDC :
        HilbertSameSide Geo D C l :=
      hilbert_sameSide_symm
        Geo C D l hSameCD

    have hSameD'C' :
        HilbertSameSide Geo D' C' l' :=
      hilbert_sameSide_symm
        Geo C' D' l' hSameC'D'

    ------------------------------------------------------------------
    -- Noncollinearity of the first component angles.
    ------------------------------------------------------------------

    have hAOB :
        ¬ Collinear Geo A O B := by
      rintro ⟨m, hAm, hOm, hBm⟩

      have hEq : m = l :=
        HilbertPlaneIncidence.line_unique
          O B hOB
          m l
          hOm hBm
          hOl hBl

      have hAl :
          HilbertIncidence.OnLine A l := by
        rw [← hEq]
        exact hAm

      exact hAoff hAl

    have hA'O'B' :
        ¬ Collinear Geo A' O' B' := by
      rintro ⟨m, hA'm, hO'm, hB'm⟩

      have hEq : m = l' :=
        HilbertPlaneIncidence.line_unique
          O' B' hO'B'
          m l'
          hO'm hB'm
          hO'l' hB'l'

      have hA'l' :
          HilbertIncidence.OnLine A' l' := by
        rw [← hEq]
        exact hA'm

      exact hA'off hA'l'

    ------------------------------------------------------------------
    -- Theorem 14: replace A and A' by their opposite extensions.
    ------------------------------------------------------------------

    have hBOD_B'O'D' :
        Geo.AngleCongruent B O D B' O' D' :=
      hilbert_adjacent_angles_congruent
        Geo
        A O B D
        A' O' B' D'
        hAOD
        hA'O'D'
        hAOB
        hA'O'B'
        hAB

    have hDOB_D'O'B' :
        Geo.AngleCongruent D O B D' O' B' :=
      AngleCongruentReverse
        Geo
        B O D
        B' O' D'
        hBOD_B'O'D'

    ------------------------------------------------------------------
    -- D,O,C and D',O',C' are noncollinear.
    ------------------------------------------------------------------

    have hDOC :
        ¬ Collinear Geo D O C := by
      intro hDOCcol

      have hAODcol :
          Collinear Geo A O D :=
        (HilbertOrder.between_incidence
          A O D hAOD).2.2.2.1

      have hODCcol :
          Collinear Geo O D C :=
        PrimCollinearSwap
          Geo D O C hDOCcol

      have hOD : O ≠ D :=
        (HilbertOrder.between_incidence
          A O D hAOD).2.1

      have hAOCcol :
          Collinear Geo A O C :=
        hilbert_primCollinear_trans
          Geo
          A O D C
          hOD
          hAODcol
          hODCcol

      exact hAOC hAOCcol

    have hD'O'C' :
        ¬ Collinear Geo D' O' C' := by
      intro hD'O'C'col

      have hA'O'D'col :
          Collinear Geo A' O' D' :=
        (HilbertOrder.between_incidence
          A' O' D' hA'O'D').2.2.2.1

      have hO'D'C'col :
          Collinear Geo O' D' C' :=
        PrimCollinearSwap
          Geo D' O' C' hD'O'C'col

      have hO'D' : O' ≠ D' :=
        (HilbertOrder.between_incidence
          A' O' D' hA'O'D').2.1

      have hA'O'C'col :
          Collinear Geo A' O' C' :=
        hilbert_primCollinear_trans
          Geo
          A' O' D' C'
          hO'D'
          hA'O'D'col
          hO'D'C'col

      exact hA'O'C' hA'O'C'col

    ------------------------------------------------------------------
    -- Apply the already proved same-side branch to D,O,B,C.
    ------------------------------------------------------------------

    have hDOC_D'O'C' :
        Geo.AngleCongruent D O C D' O' C' :=
      hilbert_angle_addition_sameSide
        Geo
        D O B C
        D' O' B' C'
        l l'
        hOB
        hO'B'
        hOl
        hBl
        hO'l'
        hB'l'
        hSameDC.1
        hCoff
        hSameD'C'.1
        hC'off
        hSameDC
        hSameD'C'
        hDOC
        hDOB_D'O'B'
        hBC

    ------------------------------------------------------------------
    -- Theorem 14 once more returns from D,D' to A,A'.
    ------------------------------------------------------------------

    have hDOA :
        Geo.Between D O A :=
      (HilbertOrder.between_incidence
        A O D hAOD).2.2.2.2

    have hD'O'A' :
        Geo.Between D' O' A' :=
      (HilbertOrder.between_incidence
        A' O' D' hA'O'D').2.2.2.2

    have hCOA_C'O'A' :
        Geo.AngleCongruent C O A C' O' A' :=
      hilbert_adjacent_angles_congruent
        Geo
        D O C A
        D' O' C' A'
        hDOA
        hD'O'A'
        hDOC
        hD'O'C'
        hDOC_D'O'C'

    exact
      AngleCongruentReverse
        Geo
        C O A
        C' O' A'
        hCOA_C'O'A'

/-
Temporary Hilbert SSS interface.

The target noncollinearity is included because `AngleCongruent`
does not itself encode angle nondegeneracy in this project.
-/








/-
Hilbert Theorem 11.

If AB is congruent to AC in a noncollinear triangle ABC,
then the base angles at B and C are congruent.
-/

theorem hilbert_isosceles_base_angles
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hNC : ¬ Collinear Geo A B C)
    (hABAC : Geo.Congruent A B A C) :
    Geo.AngleCongruent A B C A C B := by

  have hNC' : ¬ Collinear Geo A C B := by
    intro hACB
    exact hNC (PrimCollinearRotate Geo A C B hACB)

  have hBAC : ¬ PrimCollinear Geo B A C := by
    intro hBAC
    apply hNC
    exact PrimCollinearSwap Geo B A C hBAC

  have hAngleA :
      Geo.AngleCongruent B A C C A B := by
    have hRefl :
        Geo.AngleCongruent B A C B A C :=
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo) B A C hBAC

    exact
      (Geo.angle_congruent_reverse_second
        B A C B A C).mp hRefl

  have hACAB : Geo.Congruent A C A B :=
    hilbert_congruent_symmetry Geo A B A C hABAC

  have hTriangles :=
    SAS
      Geo
      A B C
      A C B
      hNC
      hNC'
      hABAC
      hAngleA
      hACAB

  exact hTriangles.angleB





/--
If A, M, B are three distinct collinear points and M is
equidistant from A and B, then M lies between A and B.

The two other possible orders would place A and B on the same
ray from M. Uniqueness of segment construction would then force
A = B.
-/
theorem hilbert_between_of_collinear_equidistant
    [HilbertCongruence Geo]
    (A M B : Geo.Point)
    (hMA : M ≠ A)
    (hMB : M ≠ B)
    (hAB : A ≠ B)
    (hCol : Collinear Geo A M B)
    (hCong : Geo.Congruent M A M B) :
    Geo.Between A M B := by

  rcases
      hilbert_between_trichotomy
        Geo A M B
        hMA.symm
        hMB
        hAB
        hCol with
    hAMB | hMAB | hABM

  · exact hAMB

  ·
    -- M-A-B: A and B lie on the same ray from M.
    have hRayAB : HilbertSameRay Geo M A B :=
      hilbert_sameRay_of_between
        Geo M A B hMAB

    have hRayAA : HilbertSameRay Geo M A A :=
      hilbert_sameRay_refl
        Geo M A hMA.symm

    have hMB_MA : Geo.Congruent M B M A :=
      hilbert_congruent_symmetry
        Geo M A M B hCong

    have hEq : A = B :=
      hilbert_segment_construction_unique
        Geo
        M A
        M A
        A B
        hRayAA
        hRayAB
        (hilbert_congruent_reflexive Geo M A)
        hMB_MA

    exact False.elim (hAB hEq)

  ·
    -- A-B-M, hence M-B-A: B and A lie on the same ray from M.
    have hMBA : Geo.Between M B A :=
      (HilbertOrder.between_incidence
        A B M hABM).2.2.2.2

    have hRayBA : HilbertSameRay Geo M B A :=
      hilbert_sameRay_of_between
        Geo M B A hMBA

    have hRayBB : HilbertSameRay Geo M B B :=
      hilbert_sameRay_refl
        Geo M B hMB.symm

    have hEq : B = A :=
      hilbert_segment_construction_unique
        Geo
        M B
        M B
        B A
        hRayBB
        hRayBA
        (hilbert_congruent_reflexive Geo M B)
        hCong

    exact False.elim (hAB hEq.symm)

/-
Hilbert Theorem 17, nondegenerate case.

The proof uses Hilbert Theorem 15 and two applications of the
isosceles base-angle theorem.
-/

theorem hilbert_theorem_17_nondegenerate
    [HilbertCongruence Geo]
    (X Y Z1 Z2 : Geo.Point)
    (lineXY lineZ : Geo.Line)
    (hXY : X ≠ Y)
    (hXxy : HilbertIncidence.OnLine X lineXY)
    (hYxy : HilbertIncidence.OnLine Y lineXY)
    (hOpp : HilbertOppositeSide Geo Z1 Z2 lineXY)
    (hZ1z : HilbertIncidence.OnLine Z1 lineZ)
    (hZ2z : HilbertIncidence.OnLine Z2 lineZ)
    (hXnotz : ¬ HilbertIncidence.OnLine X lineZ)
    (hYnotz : ¬ HilbertIncidence.OnLine Y lineZ)
    (hXZ : Geo.Congruent X Z1 X Z2)
    (hYZ : Geo.Congruent Y Z1 Y Z2) :
    Geo.AngleCongruent X Y Z1 X Y Z2 := by

  have hZ1Z2 : Z1 ≠ Z2 := by
    intro hEq
    subst Z2
    rcases hOpp.2.2 with ⟨P, hZ1PZ1, _⟩
    exact
      (HilbertOrder.between_incidence
        Z1 P Z1 hZ1PZ1).2.2.1 rfl

  have hXZ1Z2 :
      ¬ Collinear Geo X Z1 Z2 := by
    rintro ⟨line, hXline, hZ1line, hZ2line⟩

    have hLineEq : line = lineZ :=
      HilbertPlaneIncidence.line_unique
        Z1 Z2 hZ1Z2
        line lineZ
        hZ1line hZ2line
        hZ1z hZ2z

    exact hXnotz (hLineEq ▸ hXline)

  have hYZ1Z2 :
      ¬ Collinear Geo Y Z1 Z2 := by
    rintro ⟨line, hYline, hZ1line, hZ2line⟩

    have hLineEq : line = lineZ :=
      HilbertPlaneIncidence.line_unique
        Z1 Z2 hZ1Z2
        line lineZ
        hZ1line hZ2line
        hZ1z hZ2z

    exact hYnotz (hLineEq ▸ hYline)

  have hZ1XY :
      ¬ Collinear Geo Z1 X Y := by
    rintro ⟨line, hZ1line, hXline, hYline⟩

    have hLineEq : line = lineXY :=
      HilbertPlaneIncidence.line_unique
        X Y hXY
        line lineXY
        hXline hYline
        hXxy hYxy

    exact hOpp.1 (hLineEq ▸ hZ1line)

  have hZ2XY :
      ¬ Collinear Geo Z2 X Y := by
    rintro ⟨line, hZ2line, hXline, hYline⟩

    have hLineEq : line = lineXY :=
      HilbertPlaneIncidence.line_unique
        X Y hXY
        line lineXY
        hXline hYline
        hXxy hYxy

    exact hOpp.2.1 (hLineEq ▸ hZ2line)

  have hAngleX :
      Geo.AngleCongruent X Z1 Z2 X Z2 Z1 :=
    hilbert_isosceles_base_angles
      Geo
      X Z1 Z2
      hXZ1Z2
      hXZ

  have hAngleYraw :
      Geo.AngleCongruent Y Z1 Z2 Y Z2 Z1 :=
    hilbert_isosceles_base_angles
      Geo
      Y Z1 Z2
      hYZ1Z2
      hYZ

  have hAngleY :
      Geo.AngleCongruent Z2 Z1 Y Z1 Z2 Y := by
    exact
      (Geo.angle_congruent_reverse_second
        Z2 Z1 Y
        Y Z2 Z1).mp
        ((Geo.angle_congruent_reverse_first
          Y Z1 Z2
          Y Z2 Z1).mp
          hAngleYraw)

  have hXZ1Y :
      ¬ Collinear Geo X Z1 Y := by
    rintro ⟨line, hXline, hZ1line, hYline⟩
    exact hZ1XY ⟨line, hZ1line, hXline, hYline⟩

  have hXZ2Y :
      ¬ Collinear Geo X Z2 Y := by
    rintro ⟨line, hXline, hZ2line, hYline⟩
    exact hZ2XY ⟨line, hZ2line, hXline, hYline⟩

  have hAngleZ :
      Geo.AngleCongruent X Z1 Y X Z2 Y :=
    hilbert_angle_addition
      Geo
      X Z1 Z2 Y
      X Z2 Z1 Y
      lineZ lineZ
      hZ1Z2
      hZ1Z2.symm
      hZ1z
      hZ2z
      hZ2z
      hZ1z
      hXnotz
      hYnotz
      hXnotz
      hYnotz
      Iff.rfl
      hXZ1Y
      hXZ2Y
      hAngleX
      hAngleY

  have hZ1X_Z2X :
      Geo.Congruent Z1 X Z2 X :=
    CongruentReverseBoth
      Geo
      X Z1
      X Z2
      hXZ

  have hZ1Y_Z2Y :
      Geo.Congruent Z1 Y Z2 Y :=
    CongruentReverseBoth
      Geo
      Y Z1
      Y Z2
      hYZ

  have hTriangles :=
    SAS
      Geo
      Z1 X Y
      Z2 X Y
      hZ1XY
      hZ2XY
      hZ1X_Z2X
      hAngleZ
      hZ1Y_Z2Y

  exact
    (Geo.angle_congruent_reverse_second
      X Y Z1
      Z2 Y X).mp
      ((Geo.angle_congruent_reverse_first
        Z1 Y X
        Z2 Y X).mp
        hTriangles.angleC)



/--
Hilbert Theorem 17, special case X on Z1Z2.

If X lies on Z1Z2, the equality YZ1 = YZ2 makes triangle
YZ1Z2 isosceles. Its base-angle congruence, transported from
the rays Z1Z2 and Z2Z1 to the rays Z1X and Z2X, supplies the
included angle needed for SAS.
-/
theorem hilbert_theorem_17_case_X_on_Z
    [HilbertCongruence Geo]
    (X Y Z1 Z2 : Geo.Point)
    (lineXY lineZ : Geo.Line)
    (hXY : X ≠ Y)
    (hXxy : HilbertIncidence.OnLine X lineXY)
    (hYxy : HilbertIncidence.OnLine Y lineXY)
    (hOpp : HilbertOppositeSide Geo Z1 Z2 lineXY)
    (hZ1z : HilbertIncidence.OnLine Z1 lineZ)
    (hZ2z : HilbertIncidence.OnLine Z2 lineZ)
    (hXz : HilbertIncidence.OnLine X lineZ)
    (hXZ : Geo.Congruent X Z1 X Z2)
    (hYZ : Geo.Congruent Y Z1 Y Z2) :
    Geo.AngleCongruent X Y Z1 X Y Z2 := by

  have hZ1notXY :
      ¬ HilbertIncidence.OnLine Z1 lineXY :=
    hOpp.1

  have hZ2notXY :
      ¬ HilbertIncidence.OnLine Z2 lineXY :=
    hOpp.2.1

  have hXZ1 : X ≠ Z1 := by
    intro hEq
    subst Z1
    exact hZ1notXY hXxy

  have hXZ2 : X ≠ Z2 := by
    intro hEq
    subst Z2
    exact hZ2notXY hXxy

  have hZ1Z2 : Z1 ≠ Z2 := by
    intro hEq
    subst Z2
    rcases hOpp.2.2 with ⟨P, hZ1PZ1, _⟩
    exact
      (HilbertOrder.between_incidence
        Z1 P Z1 hZ1PZ1).2.2.1 rfl

  have hColZ1XZ2 :
      Collinear Geo Z1 X Z2 :=
    ⟨lineZ, hZ1z, hXz, hZ2z⟩

  have hBetween :
      Geo.Between Z1 X Z2 :=
    hilbert_between_of_collinear_equidistant
      Geo
      Z1 X Z2
      hXZ1
      hXZ2
      hZ1Z2
      hColZ1XZ2
      hXZ

  have hBetweenRev :
      Geo.Between Z2 X Z1 :=
    (HilbertOrder.between_incidence
      Z1 X Z2 hBetween).2.2.2.2

  have hRayZ1 :
      HilbertSameRay Geo Z1 X Z2 :=
    hilbert_sameRay_of_between
      Geo Z1 X Z2 hBetween

  have hRayZ2 :
      HilbertSameRay Geo Z2 X Z1 :=
    hilbert_sameRay_of_between
      Geo Z2 X Z1 hBetweenRev

  have hYnotz :
      ¬ HilbertIncidence.OnLine Y lineZ := by
    intro hYz

    have hLinesEqual : lineXY = lineZ :=
      HilbertPlaneIncidence.line_unique
        X Y hXY
        lineXY lineZ
        hXxy hYxy
        hXz hYz

    have hZ1xy :
        HilbertIncidence.OnLine Z1 lineXY := by
      rw [hLinesEqual]
      exact hZ1z

    exact hZ1notXY hZ1xy

  have hYZ1Z2 :
      ¬ Collinear Geo Y Z1 Z2 := by
    rintro ⟨line, hYline, hZ1line, hZ2line⟩

    have hLineEq : line = lineZ :=
      HilbertPlaneIncidence.line_unique
        Z1 Z2 hZ1Z2
        line lineZ
        hZ1line hZ2line
        hZ1z hZ2z

    exact hYnotz (hLineEq ▸ hYline)

  have hBaseRaw :
      Geo.AngleCongruent Y Z1 Z2 Y Z2 Z1 :=
    hilbert_isosceles_base_angles
      Geo Y Z1 Z2 hYZ1Z2 hYZ

  have hAngleAtZ :
      Geo.AngleCongruent X Z1 Y X Z2 Y := by

    have hLeft :
        Geo.Angle X Z1 Y =
        Geo.Angle Z2 Z1 Y :=
      hilbert_angle_eq_of_sameRay_first
        Geo Z1 X Z2 Y hRayZ1

    have hRight :
        Geo.Angle X Z2 Y =
        Geo.Angle Z1 Z2 Y :=
      hilbert_angle_eq_of_sameRay_first
        Geo Z2 X Z1 Y hRayZ2

    have hBase :
        Geo.AngleCongruent Z2 Z1 Y Z1 Z2 Y := by
      exact
        (Geo.angle_congruent_reverse_second
          Z2 Z1 Y Y Z2 Z1).mp
          ((Geo.angle_congruent_reverse_first
            Y Z1 Z2 Y Z2 Z1).mp hBaseRaw)

    unfold Geometry.Geo.AngleCongruent at hBase ⊢
    rw [hLeft, hRight]
    exact hBase

  have hZ1XY :
      ¬ Collinear Geo Z1 X Y := by
    rintro ⟨line, hZ1line, hXline, hYline⟩

    have hLineEq : line = lineXY :=
      HilbertPlaneIncidence.line_unique
        X Y hXY
        line lineXY
        hXline hYline
        hXxy hYxy

    exact hZ1notXY (hLineEq ▸ hZ1line)

  have hZ2XY :
      ¬ Collinear Geo Z2 X Y := by
    rintro ⟨line, hZ2line, hXline, hYline⟩

    have hLineEq : line = lineXY :=
      HilbertPlaneIncidence.line_unique
        X Y hXY
        line lineXY
        hXline hYline
        hXxy hYxy

    exact hZ2notXY (hLineEq ▸ hZ2line)

  have hZ1X_Z2X :
      Geo.Congruent Z1 X Z2 X :=
    CongruentReverseBoth
      Geo X Z1 X Z2 hXZ

  have hZ1Y_Z2Y :
      Geo.Congruent Z1 Y Z2 Y :=
    CongruentReverseBoth
      Geo Y Z1 Y Z2 hYZ

  have hTriangles :=
    SAS
      Geo
      Z1 X Y
      Z2 X Y
      hZ1XY
      hZ2XY
      hZ1X_Z2X
      hAngleAtZ
      hZ1Y_Z2Y

  exact
    (Geo.angle_congruent_reverse_second
      X Y Z1 Z2 Y X).mp
      ((Geo.angle_congruent_reverse_first
        Z1 Y X Z2 Y X).mp hTriangles.angleC)

/--
Hilbert Theorem 17, special case Y on Z1Z2.

If Y lies on Z1Z2, equidistance YZ1 = YZ2 forces Y to lie
between Z1 and Z2. The equality XZ1 = XZ2 makes triangle
XZ1Z2 isosceles. Transporting its base angles to the rays
Z1Y and Z2Y supplies the included angles for SAS.
-/
theorem hilbert_theorem_17_case_Y_on_Z
    [HilbertCongruence Geo]
    (X Y Z1 Z2 : Geo.Point)
    (lineXY lineZ : Geo.Line)
    (hXY : X ≠ Y)
    (hXxy : HilbertIncidence.OnLine X lineXY)
    (hYxy : HilbertIncidence.OnLine Y lineXY)
    (hOpp : HilbertOppositeSide Geo Z1 Z2 lineXY)
    (hZ1z : HilbertIncidence.OnLine Z1 lineZ)
    (hZ2z : HilbertIncidence.OnLine Z2 lineZ)
    (hYz : HilbertIncidence.OnLine Y lineZ)
    (hXZ : Geo.Congruent X Z1 X Z2)
    (hYZ : Geo.Congruent Y Z1 Y Z2) :
    Geo.AngleCongruent X Y Z1 X Y Z2 := by

  have hZ1notXY :
      ¬ HilbertIncidence.OnLine Z1 lineXY :=
    hOpp.1

  have hZ2notXY :
      ¬ HilbertIncidence.OnLine Z2 lineXY :=
    hOpp.2.1

  have hYZ1 : Y ≠ Z1 := by
    intro hEq
    subst Z1
    exact hZ1notXY hYxy

  have hYZ2 : Y ≠ Z2 := by
    intro hEq
    subst Z2
    exact hZ2notXY hYxy

  have hZ1Z2 : Z1 ≠ Z2 := by
    intro hEq
    subst Z2
    rcases hOpp.2.2 with ⟨P, hZ1PZ1, _⟩
    exact
      (HilbertOrder.between_incidence
        Z1 P Z1 hZ1PZ1).2.2.1 rfl

  have hColZ1YZ2 :
      Collinear Geo Z1 Y Z2 :=
    ⟨lineZ, hZ1z, hYz, hZ2z⟩

  have hBetween :
      Geo.Between Z1 Y Z2 :=
    hilbert_between_of_collinear_equidistant
      Geo
      Z1 Y Z2
      hYZ1
      hYZ2
      hZ1Z2
      hColZ1YZ2
      hYZ

  have hBetweenRev :
      Geo.Between Z2 Y Z1 :=
    (HilbertOrder.between_incidence
      Z1 Y Z2 hBetween).2.2.2.2

  have hRayZ1 :
      HilbertSameRay Geo Z1 Y Z2 :=
    hilbert_sameRay_of_between
      Geo Z1 Y Z2 hBetween

  have hRayZ2 :
      HilbertSameRay Geo Z2 Y Z1 :=
    hilbert_sameRay_of_between
      Geo Z2 Y Z1 hBetweenRev

  have hXnotz :
      ¬ HilbertIncidence.OnLine X lineZ := by
    intro hXz

    have hLinesEqual : lineXY = lineZ :=
      HilbertPlaneIncidence.line_unique
        X Y hXY
        lineXY lineZ
        hXxy hYxy
        hXz hYz

    have hZ1xy :
        HilbertIncidence.OnLine Z1 lineXY := by
      rw [hLinesEqual]
      exact hZ1z

    exact hZ1notXY hZ1xy

  have hXZ1Z2 :
      ¬ Collinear Geo X Z1 Z2 := by
    rintro ⟨line, hXline, hZ1line, hZ2line⟩

    have hLineEq : line = lineZ :=
      HilbertPlaneIncidence.line_unique
        Z1 Z2 hZ1Z2
        line lineZ
        hZ1line hZ2line
        hZ1z hZ2z

    exact hXnotz (hLineEq ▸ hXline)

  have hBaseRaw :
      Geo.AngleCongruent X Z1 Z2 X Z2 Z1 :=
    hilbert_isosceles_base_angles
      Geo X Z1 Z2 hXZ1Z2 hXZ

  have hBase :
      Geo.AngleCongruent Z2 Z1 X Z1 Z2 X := by
    exact
      (Geo.angle_congruent_reverse_second
        Z2 Z1 X X Z2 Z1).mp
        ((Geo.angle_congruent_reverse_first
          X Z1 Z2 X Z2 Z1).mp hBaseRaw)

  have hAngleAtZ :
      Geo.AngleCongruent Y Z1 X Y Z2 X := by

    have hLeft :
        Geo.Angle Y Z1 X =
        Geo.Angle Z2 Z1 X :=
      hilbert_angle_eq_of_sameRay_first
        Geo Z1 Y Z2 X hRayZ1

    have hRight :
        Geo.Angle Y Z2 X =
        Geo.Angle Z1 Z2 X :=
      hilbert_angle_eq_of_sameRay_first
        Geo Z2 Y Z1 X hRayZ2

    unfold Geometry.Geo.AngleCongruent at hBase ⊢
    rw [hLeft, hRight]
    exact hBase

  have hZ1YX :
      ¬ Collinear Geo Z1 Y X := by
    rintro ⟨line, hZ1line, hYline, hXline⟩

    have hLineEq : line = lineXY :=
      HilbertPlaneIncidence.line_unique
        X Y hXY
        line lineXY
        hXline hYline
        hXxy hYxy

    exact hZ1notXY (hLineEq ▸ hZ1line)

  have hZ2YX :
      ¬ Collinear Geo Z2 Y X := by
    rintro ⟨line, hZ2line, hYline, hXline⟩

    have hLineEq : line = lineXY :=
      HilbertPlaneIncidence.line_unique
        X Y hXY
        line lineXY
        hXline hYline
        hXxy hYxy

    exact hZ2notXY (hLineEq ▸ hZ2line)

  have hZ1Y_Z2Y :
      Geo.Congruent Z1 Y Z2 Y :=
    CongruentReverseBoth
      Geo Y Z1 Y Z2 hYZ

  have hZ1X_Z2X :
      Geo.Congruent Z1 X Z2 X :=
    CongruentReverseBoth
      Geo X Z1 X Z2 hXZ

  have hTriangles :=
    SAS
      Geo
      Z1 Y X
      Z2 Y X
      hZ1YX
      hZ2YX
      hZ1Y_Z2Y
      hAngleAtZ
      hZ1X_Z2X

  exact
    (Geo.angle_congruent_reverse_second
      X Y Z1 Z2 Y X).mp
      ((Geo.angle_congruent_reverse_first
        Z1 Y X Z2 Y X).mp hTriangles.angleB)

/--
Hilbert Theorem 17.

Let Z1 and Z2 lie on opposite sides of the line XY.
If XZ1 is congruent to XZ2 and YZ1 is congruent to YZ2,
then the angles XYZ1 and XYZ2 are congruent.

The proof splits according to whether X or Y lies on the
line Z1Z2. The two special cases and the general case have
already been established separately.
-/
theorem hilbert_theorem_17
    [HilbertCongruence Geo]
    (X Y Z1 Z2 : Geo.Point)
    (lineXY lineZ : Geo.Line)
    (hXY : X ≠ Y)
    (hXxy : HilbertIncidence.OnLine X lineXY)
    (hYxy : HilbertIncidence.OnLine Y lineXY)
    (hOpp : HilbertOppositeSide Geo Z1 Z2 lineXY)
    (hZ1z : HilbertIncidence.OnLine Z1 lineZ)
    (hZ2z : HilbertIncidence.OnLine Z2 lineZ)
    (hXZ : Geo.Congruent X Z1 X Z2)
    (hYZ : Geo.Congruent Y Z1 Y Z2) :
    Geo.AngleCongruent X Y Z1 X Y Z2 := by

  by_cases hXz : HilbertIncidence.OnLine X lineZ

  · exact
      hilbert_theorem_17_case_X_on_Z
        Geo
        X Y Z1 Z2
        lineXY lineZ
        hXY
        hXxy hYxy
        hOpp
        hZ1z hZ2z
        hXz
        hXZ hYZ

  · by_cases hYz : HilbertIncidence.OnLine Y lineZ

    · exact
        hilbert_theorem_17_case_Y_on_Z
          Geo
          X Y Z1 Z2
          lineXY lineZ
          hXY
          hXxy hYxy
          hOpp
          hZ1z hZ2z
          hYz
          hXZ hYZ

    · exact
        hilbert_theorem_17_nondegenerate
          Geo
          X Y Z1 Z2
          lineXY lineZ
          hXY
          hXxy hYxy
          hOpp
          hZ1z hZ2z
          hXz hYz
          hXZ hYZ

/--
Auxiliary construction for Hilbert Theorem 18 (SSS).

Given two nondegenerate triangles ABC and A'B'C', construct a point G
on the side of AB opposite to C such that

  AG ≅ A'C'
  ∠BAG ≅ ∠B'A'C'.

This is the auxiliary construction used in Hilbert's proof of SSS.
-/
theorem hilbert_sss_auxiliary_point
    [HilbertCongruence Geo]
    (A B C A' B' C' : Geo.Point)
    (base : Geo.Line)
    (hABC : ¬ Collinear Geo A B C)
    (hA'B'C' : ¬ Collinear Geo A' B' C')
    (hAB : A ≠ B)
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base) :
    ∃ G : Geo.Point,
      HilbertOppositeSide Geo C G base ∧
      Geo.Congruent A G A' C' ∧
      Geo.AngleCongruent B A G B' A' C' := by

  have hCbase :
      ¬ HilbertIncidence.OnLine C base := by
    intro hCbase
    exact hABC ⟨base, hAbase, hBbase, hCbase⟩

  have hCA : C ≠ A := by
    intro h
    subst C
    exact hCbase hAbase

  have hB'A'C' :
      ¬ Collinear Geo B' A' C' := by
    intro h
    exact hA'B'C' (PrimCollinearSwap Geo B' A' C' h)

  have hBA : B ≠ A :=
    hAB.symm

  -- Choose a point S on the side of AB opposite to C.
  rcases HilbertOrder.between_extension C A hCA with
    ⟨S, hCAS⟩

  have hCASData :=
    HilbertOrder.between_incidence C A S hCAS

  have hSA : S ≠ A :=
    hCASData.2.1.symm

  have hSbase :
      ¬ HilbertIncidence.OnLine S base := by
    intro hSbase

    have hSAC : Collinear Geo S A C :=
      PrimCollinearSymm Geo C A S
        hCASData.2.2.2.1

    have hCbase' :
        HilbertIncidence.OnLine C base :=
      hilbert_collinear_on_line
        Geo S A C base hSA
        hSbase hAbase hSAC

    exact hCbase hCbase'

  have hOppositeCS :
      HilbertOppositeSide Geo C S base :=
    ⟨hCbase, hSbase, ⟨A, hCAS, hAbase⟩⟩

  -- Copy angle B'A'C' at A, with AB as the first ray,
  -- on the side selected by S.
  rcases HilbertCongruence.angle_construction
      (Geo := Geo)
      B' A' C'
      B A S
      hB'A'C'
      hBA
      base
      hBbase hAbase hSbase with
    ⟨R, hRSSame, hAngleR, _⟩

  have hSRSame :
      HilbertSameSide Geo S R base :=
    hilbert_sameSide_symm
      Geo R S base hRSSame

  have hOppositeCR :
      HilbertOppositeSide Geo C R base :=
    hilbert_oppositeSide_transport_right
      Geo C S R base hOppositeCS hSRSame

  have hAR : A ≠ R := by
    intro h
    subst R
    exact hOppositeCR.2.1 hAbase

  -- Lay off AG ≅ A'C' on ray AR.
  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      A' C'
      A R
      hAR with
    ⟨G, hRayRG, hAG_A'C'⟩

  -- R and G are on the same side of AB.
  rcases HilbertPlaneIncidence.line_through
      A R hAR with
    ⟨rayLine, hAray, hRray⟩

  have hBray :
      ¬ HilbertIncidence.OnLine B rayLine := by
    intro hBray

    have hBaseRay : base = rayLine :=
      HilbertPlaneIncidence.line_unique
        A B hAB
        base rayLine
        hAbase hBbase
        hAray hBray

    exact hOppositeCR.2.1 (hBaseRay ▸ hRray)

  have hRGSame :
      HilbertSameSide Geo R G base :=
    hilbert_sameRay_points_sameSide
      Geo
      A R R G B
      rayLine base
      hAray hRray
      hAbase hBbase hBray
      (hilbert_sameRay_refl Geo A R hAR.symm)
      hRayRG

  have hSGSame :
      HilbertSameSide Geo S G base :=
    hilbert_sameSide_trans
      Geo S R G base
      hSRSame hRGSame

  have hOppositeCG :
      HilbertOppositeSide Geo C G base :=
    hilbert_oppositeSide_transport_right
      Geo C S G base
      hOppositeCS hSGSame

  -- Replace the constructed ray AR by the same ray AG.
  have hAngleG :
      Geo.AngleCongruent B A G B' A' C' := by

    have hTarget :
        Geo.Angle B A R =
        Geo.Angle B A G :=
      hilbert_angle_eq_of_sameRay_second
        Geo A B R G hRayRG

    unfold Geometry.Geo.AngleCongruent at hAngleR ⊢
    rw [← hTarget]

    exact hAngleR.symm

  exact
    ⟨G, hOppositeCG, hAG_A'C', hAngleG⟩


/--
In the auxiliary construction for Hilbert Theorem 18,
triangle ABG is congruent by SAS to triangle A'B'C'.
In particular, BG is congruent to B'C'.
-/
theorem hilbert_sss_auxiliary_BG
    [HilbertCongruence Geo]
    (A B G A' B' C' : Geo.Point)
    (hABG : ¬ Collinear Geo A B G)
    (hA'B'C' : ¬ Collinear Geo A' B' C')
    (hAB : Geo.Congruent A B A' B')
    (hAG : Geo.Congruent A G A' C')
    (hAngle :
      Geo.AngleCongruent B A G B' A' C') :
    Geo.Congruent B G B' C' := by

  have hTriangles :=
    SAS
      Geo
      A B G
      A' B' C'
      hABG
      hA'B'C'
      hAB
      hAngle
      hAG

  exact hTriangles.sideBC




theorem hilbert_two_centers_equal_distances_collinear
    [HilbertCongruence Geo]
    (a b c d : Geo.Point)
    (habd : Geo.Between a b d)
    (hadac : Geo.Congruent a d a c)
    (hbdbc : Geo.Congruent b d b c) :
    Collinear Geo a b c := by

  by_contra habc

  have habdCol : PrimCollinear Geo a b d :=
    (HilbertOrder.between_incidence a b d habd).2.2.2.1

  have hab : a ≠ b :=
    (HilbertOrder.between_incidence a b d habd).1

  have hbd : b ≠ d :=
    (HilbertOrder.between_incidence a b d habd).2.1

  have had : a ≠ d :=
    (HilbertOrder.between_incidence a b d habd).2.2.1

  have hADC : ¬ Collinear Geo a d c := by
    intro hADC

    have hBAD : PrimCollinear Geo b a d :=
      PrimCollinearSwap Geo a b d habdCol

    have hBAC : PrimCollinear Geo b a c :=
      hilbert_primCollinear_trans
        Geo b a d c had
        hBAD
        hADC

    exact habc (PrimCollinearSwap Geo b a c hBAC)

  have hBDC : ¬ Collinear Geo b d c := by
    intro hBDC

    have hABC : PrimCollinear Geo a b c :=
      hilbert_primCollinear_trans
        Geo a b d c hbd
        habdCol
        hBDC

    exact habc hABC

  have hIsoA :
      Geo.AngleCongruent a d c a c d :=
    hilbert_isosceles_base_angles
      Geo a d c hADC hadac

  have hIsoB :
      Geo.AngleCongruent b d c b c d :=
    hilbert_isosceles_base_angles
      Geo b d c hBDC hbdbc

  have hdba : Geo.Between d b a :=
    (HilbertOrder.between_incidence a b d habd).2.2.2.2

  have hRayDBA : HilbertSameRay Geo d b a :=
    hilbert_sameRay_of_between Geo d b a hdba

  have hBDC_ACD :
      Geo.AngleCongruent b d c a c d := by
    unfold Geometry.Geo.AngleCongruent at hIsoA ⊢
    rw [hilbert_angle_eq_of_sameRay_first
      Geo d b a c hRayDBA]
    exact hIsoA

  have hACD_BCD :
      Geo.AngleCongruent a c d b c d :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      a c d
      b d c
      b c d
      (Geometry.Geo.angle_congruent_symmetry
        Geo b d c a c d hBDC_ACD)
      hIsoB

  have hDCA_DCB :
      Geo.AngleCongruent d c a d c b :=
    (Geo.angle_congruent_reverse_second
      d c a b c d).mp
      ((Geo.angle_congruent_reverse_first
        a c d b c d).mp hACD_BCD)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo a b c d habd hADC with
    ⟨l, hCl, hDl, hSameAB⟩

  have hdc : d ≠ c := by
    intro hdc
    subst d
    apply hADC
    rcases HilbertPlaneIncidence.line_through a c had with
      ⟨m, ham, hcm⟩
    exact PrimCollinear.mk
      (Geo := Geo) ham hcm hcm

  have hDCA : ¬ PrimCollinear Geo d c a := by
    intro hDCA'
    apply hADC
    exact
      PrimCollinearRotate Geo a c d
        (PrimCollinearSymm Geo d c a hDCA')

  rcases HilbertCongruence.angle_construction
      (Geo := Geo)
      d c a
      d c b
      hDCA
      hdc
      l
      hDl
      hCl
      hSameAB.2.1 with
    ⟨x, hSameXB, hAngleX, hUnique⟩

  have hSameAA : HilbertSameSide Geo a a l :=
    hilbert_sameSide_refl
      Geo a l hSameAB.1

  have hRayXA : HilbertSameRay Geo c x a :=
    hUnique
      a
      hSameAB
      (HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo) d c a hDCA)

  have hSameBB : HilbertSameSide Geo b b l :=
    hilbert_sameSide_refl
      Geo b l hSameAB.2.1

  have hRayXB : HilbertSameRay Geo c x b :=
    hUnique b hSameBB hDCA_DCB

  have hCXA : PrimCollinear Geo c x a :=
    hilbert_sameRay_collinear Geo c x a hRayXA

  have hCXB : PrimCollinear Geo c x b :=
    hilbert_sameRay_collinear Geo c x b hRayXB

  have hACX : PrimCollinear Geo a c x :=
    PrimCollinearRotate Geo a x c
      (PrimCollinearSymm Geo c x a hCXA)

  have hACB : PrimCollinear Geo a c b :=
    hilbert_primCollinear_trans
      Geo a c x b
      hRayXA.1.symm
      hACX
      hCXB

  exact habc (PrimCollinearRotate Geo a c b hACB)


theorem hilbert_congruent_triple_collinear
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (hab : a ≠ b)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hBCbc : Geo.Congruent B C b c) :
    Collinear Geo a b c := by

  rcases HilbertOrder.between_extension a b hab with
    ⟨R, habR⟩

  have hbR : b ≠ R :=
    (HilbertOrder.between_incidence a b R habR).2.1

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      B C
      b R
      hbR with
    ⟨d, hRayd, hbdBC⟩

  have hRayA : HilbertSameRay Geo b a a :=
    hilbert_sameRay_refl Geo b a hab

  have habd : Geo.Between a b d :=
    hilbert_between_transport_sameRays
      Geo
      a b R
      a d
      habR
      hRayA
      hRayd

  have hBCbd : Geo.Congruent B C b d :=
    hilbert_congruent_symmetry
      Geo b d B C hbdBC

  have hACad : Geo.Congruent A C a d :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A B C
      a b d
      hABC
      habd
      hABab
      hBCbd

  have hadAC : Geo.Congruent a d A C :=
    hilbert_congruent_symmetry
      Geo A C a d hACad

  have hadac : Geo.Congruent a d a c :=
    hilbert_congruent_transitivity
      Geo
      a d
      A C
      a c
      hadAC
      hACac

  have hbdbc : Geo.Congruent b d b c :=
    hilbert_congruent_transitivity
      Geo
      b d
      B C
      b c
      hbdBC
      hBCbc

  exact
    hilbert_two_centers_equal_distances_collinear
      Geo
      a b c d
      habd
      hadac
      hbdbc


theorem hilbert_part_not_congruent_whole
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    ¬ Geo.Congruent A B A C := by
  intro hABAC

  have hAB : A ≠ B :=
    (HilbertOrder.between_incidence A B C hABC).1

  have hRayB : HilbertSameRay Geo A B B :=
    hilbert_sameRay_refl Geo A B hAB.symm

  have hRayC : HilbertSameRay Geo A B C :=
    hilbert_sameRay_of_between Geo A B C hABC

  have hACAB : Geo.Congruent A C A B :=
    hilbert_congruent_symmetry Geo A B A C hABAC

  have hBC : B = C :=
    hilbert_segment_construction_unique
      Geo
      A B
      A B
      B C
      hRayB
      hRayC
      (hilbert_congruent_reflexive Geo A B)
      hACAB

  have hBneC : B ≠ C :=
    (HilbertOrder.between_incidence A B C hABC).2.1

  exact hBneC hBC

def HilbertSegmentLess
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point) : Prop :=
  ∃ P : Geo.Point,
    Geo.Between C P D ∧
    Geo.Congruent A B C P



theorem hilbert_segmentLess_congruent_left
    [HilbertCongruence Geo]
    (A B A' B' C D : Geo.Point)
    (hLess : HilbertSegmentLess Geo A B C D)
    (hCong : Geo.Congruent A' B' A B) :
    HilbertSegmentLess Geo A' B' C D := by

  rcases hLess with ⟨P, hCPD, hABCP⟩

  have hA'B'CP : Geo.Congruent A' B' C P :=
    hilbert_congruent_transitivity
      Geo
      A' B'
      A B
      C P
      hCong
      hABCP

  exact ⟨P, hCPD, hA'B'CP⟩


theorem hilbert_segmentLess_not_congruent
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hLess : HilbertSegmentLess Geo A B C D) :
    ¬ Geo.Congruent A B C D := by

  intro hABCD

  rcases hLess with ⟨P, hCPD, hABCP⟩

  have hCPAB : Geo.Congruent C P A B :=
    hilbert_congruent_symmetry
      Geo A B C P hABCP

  have hCPCD : Geo.Congruent C P C D :=
    hilbert_congruent_transitivity
      Geo
      C P
      A B
      C D
      hCPAB
      hABCD

  exact
    hilbert_part_not_congruent_whole
      Geo C P D hCPD hCPCD


theorem hilbert_segmentLess_of_between
    [HilbertCongruence Geo]
    (C P D : Geo.Point)
    (hCPD : Geo.Between C P D) :
    HilbertSegmentLess Geo C P C D := by

  exact
    ⟨P,
     hCPD,
     hilbert_congruent_reflexive Geo C P⟩


theorem hilbert_segmentLess_asymm
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABCD : HilbertSegmentLess Geo A B C D) :
    ¬ HilbertSegmentLess Geo C D A B := by

  intro hCDAB

  rcases hABCD with ⟨P, hCPD, hABCP⟩
  rcases hCDAB with ⟨Q, hAQB, hCDAQ⟩

  have hAB : A ≠ B :=
    (HilbertOrder.between_incidence A Q B hAQB).2.2.1

  rcases HilbertOrder.between_extension A B hAB with
    ⟨S, hABS⟩

  have hBS : B ≠ S :=
    (HilbertOrder.between_incidence A B S hABS).2.1

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      P D
      B S
      hBS with
    ⟨R, hRayR, hBRPD⟩

  have hRayA : HilbertSameRay Geo B A A :=
    hilbert_sameRay_refl Geo B A hAB

  have hABR : Geo.Between A B R :=
    hilbert_between_transport_sameRays
      Geo
      A B S
      A R
      hABS
      hRayA
      hRayR

  have hCPAB : Geo.Congruent C P A B :=
    hilbert_congruent_symmetry
      Geo A B C P hABCP

  have hPDBR : Geo.Congruent P D B R :=
    hilbert_congruent_symmetry
      Geo B R P D hBRPD

  have hCDAR : Geo.Congruent C D A R :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      C P D
      A B R
      hCPD
      hABR
      hCPAB
      hPDBR

  have hARCD : Geo.Congruent A R C D :=
    hilbert_congruent_symmetry
      Geo C D A R hCDAR

  have hAQCD : Geo.Congruent A Q C D :=
    hilbert_congruent_symmetry
      Geo C D A Q hCDAQ

  have hRayQ0 : HilbertSameRay Geo A Q B :=
    hilbert_sameRay_of_between Geo A Q B hAQB

  have hRayQ : HilbertSameRay Geo A B Q :=
    hilbert_sameRay_symm Geo A Q B hRayQ0

  have hRayR' : HilbertSameRay Geo A B R :=
    hilbert_sameRay_of_between Geo A B R hABR

  have hRQ : R = Q :=
    hilbert_segment_construction_unique
      Geo
      C D
      A B
      R Q
      hRayR'
      hRayQ
      hARCD
      hAQCD

  subst R

  have hAQBcol : PrimCollinear Geo A Q B :=
    (HilbertOrder.between_incidence A Q B hAQB).2.2.2.1

  have hNotABQ : ¬ Geo.Between A B Q :=
    (HilbertOrder.between_unique
      A Q B hAQBcol hAQB).2

  exact hNotABQ hABR


theorem hilbert_congruent_collinear_triple_preserves_between
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Collinear Geo a b c)
    (hab : a ≠ b)
    (hbc : b ≠ c)
    (hac : a ≠ c)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hBCbc : Geo.Congruent B C b c) :
    Geo.Between a b c := by

  rcases
      hilbert_between_trichotomy
        Geo a b c hab hbc hac habc with
    habcOrder | hbacOrder | hacbOrder

  · exact habcOrder

  · exfalso

    have hcabOrder : Geo.Between c a b :=
      (HilbertOrder.between_incidence
        b a c hbacOrder).2.2.2.2

    have hcaltcb :
        HilbertSegmentLess Geo c a c b :=
      hilbert_segmentLess_of_between
        Geo c a b hcabOrder

    have hCAca : Geo.Congruent C A c a :=
      CongruentReverseBoth Geo A C a c hACac

    have hCAltcb :
        HilbertSegmentLess Geo C A c b :=
      hilbert_segmentLess_congruent_left
        Geo
        c a
        C A
        c b
        hcaltcb
        hCAca

    have hCBA : Geo.Between C B A :=
      (HilbertOrder.between_incidence
        A B C hABC).2.2.2.2

    have hCBltCA :
        HilbertSegmentLess Geo C B C A :=
      hilbert_segmentLess_of_between
        Geo C B A hCBA

    have hCBcb : Geo.Congruent C B c b :=
      CongruentReverseBoth Geo B C b c hBCbc

    have hcbCB : Geo.Congruent c b C B :=
      hilbert_congruent_symmetry
        Geo C B c b hCBcb

    have hcbltCA :
        HilbertSegmentLess Geo c b C A :=
      hilbert_segmentLess_congruent_left
        Geo
        C B
        c b
        C A
        hCBltCA
        hcbCB

    exact
      (hilbert_segmentLess_asymm
        Geo C A c b hCAltcb)
        hcbltCA

  · exfalso

    have hacltab :
        HilbertSegmentLess Geo a c a b :=
      hilbert_segmentLess_of_between
        Geo a c b hacbOrder

    have hACltab :
        HilbertSegmentLess Geo A C a b :=
      hilbert_segmentLess_congruent_left
        Geo
        a c
        A C
        a b
        hacltab
        hACac

    have hABltAC :
        HilbertSegmentLess Geo A B A C :=
      hilbert_segmentLess_of_between
        Geo A B C hABC

    have habAB : Geo.Congruent a b A B :=
      hilbert_congruent_symmetry
        Geo A B a b hABab

    have habltAC :
        HilbertSegmentLess Geo a b A C :=
      hilbert_segmentLess_congruent_left
        Geo
        A B
        a b
        A C
        hABltAC
        habAB

    exact
      (hilbert_segmentLess_asymm
        Geo A C a b hACltab)
        habltAC


theorem hilbert_theorem27_three_points
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (hab : a ≠ b)
    (hbc : b ≠ c)
    (hac : a ≠ c)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hBCbc : Geo.Congruent B C b c) :
    Geo.Between a b c := by

  have habc : Collinear Geo a b c :=
    hilbert_congruent_triple_collinear
      Geo
      A B C
      a b c
      hABC
      hab
      hABab
      hACac
      hBCbc

  exact
    hilbert_congruent_collinear_triple_preserves_between
      Geo
      A B C
      a b c
      hABC
      habc
      hab
      hbc
      hac
      hABab
      hACac
      hBCbc

/--
Collinearity is preserved by congruence of the three corresponding
segments.

Interface-level form of Book Zero #46.
-/
theorem hilbert_collinearity_preserved_by_three_congruences
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABCcol : PrimCollinear Geo A B C)
    (hAB : Geo.Congruent A B a b)
    (hAC : Geo.Congruent A C a c)
    (hBC : Geo.Congruent B C b c) :
    PrimCollinear Geo a b c := by

  have collinear_of_eq12 :
      ∀ X Y Z : Geo.Point,
        X = Y →
        PrimCollinear Geo X Y Z := by
    intro X Y Z hXY
    subst Y

    by_cases hXZ : X = Z

    · subst Z

      rcases hilbert_line_through_point Geo X with
        ⟨l, hXl⟩

      exact ⟨l, hXl, hXl, hXl⟩

    · rcases
        HilbertPlaneIncidence.line_through
          X Z hXZ with
        ⟨l, hXl, hZl⟩

      exact ⟨l, hXl, hXl, hZl⟩

  by_cases hABeq : A = B

  · subst B

    have hab : a = b :=
      bookZero_nullSegment1
        Geo a b A
        (hilbert_congruent_symmetry
          Geo A A a b hAB)

    exact collinear_of_eq12 a b c hab

  · by_cases hACeq : A = C

    · subst C

      have hac : a = c :=
        bookZero_nullSegment1
          Geo a c A
          (hilbert_congruent_symmetry
            Geo A A a c hAC)

      have hacb : PrimCollinear Geo a c b :=
        collinear_of_eq12 a c b hac

      exact
        PrimCollinearRotate
          Geo a c b hacb

    · by_cases hBCeq : B = C

      · subst C

        have hbc : b = c :=
          bookZero_nullSegment1
            Geo b c B
            (hilbert_congruent_symmetry
              Geo B B b c hBC)

        subst c

        by_cases hab : a = b

        · subst b

          rcases hilbert_line_through_point Geo a with
            ⟨l, hal⟩

          exact ⟨l, hal, hal, hal⟩

        · rcases
            HilbertPlaneIncidence.line_through
              a b hab with
            ⟨l, hal, hbl⟩

          exact ⟨l, hal, hbl, hbl⟩

      ·
        have hBAba : Geo.Congruent B A b a :=
          CongruentReverseBoth
            Geo A B a b hAB

        have hCAca : Geo.Congruent C A c a :=
          CongruentReverseBoth
            Geo A C a c hAC

        have hCBcb : Geo.Congruent C B c b :=
          CongruentReverseBoth
            Geo B C b c hBC

        have hab : a ≠ b := by
          intro habEq
          subst b

          have hNull : Geo.Congruent A B a a := by
            simpa using hAB

          have hEq : A = B :=
            bookZero_nullSegment1
              Geo A B a hNull

          exact hABeq hEq

        have hac : a ≠ c := by
          intro hacEq
          subst c

          have hNull : Geo.Congruent A C a a := by
            simpa using hAC

          have hEq : A = C :=
            bookZero_nullSegment1
              Geo A C a hNull

          exact hACeq hEq

        have hbc : b ≠ c := by
          intro hbcEq
          subst c

          have hNull : Geo.Congruent B C b b := by
            simpa using hBC

          have hEq : B = C :=
            bookZero_nullSegment1
              Geo B C b hNull

          exact hBCeq hEq

        rcases
            hilbert_between_trichotomy
              Geo
              A B C
              hABeq
              hBCeq
              hACeq
              hABCcol with
          hABC | hBAC | hACB

        · have habc : Geo.Between a b c :=
            hilbert_theorem27_three_points
              Geo
              A B C
              a b c
              hABC
              hab
              hbc
              hac
              hAB
              hAC
              hBC

          exact
            (HilbertOrder.between_incidence
              a b c habc).2.2.2.1

        · have hbac : Geo.Between b a c :=
            hilbert_theorem27_three_points
              Geo
              B A C
              b a c
              hBAC
              hab.symm
              hac
              hbc
              hBAba
              hBC
              hAC

          have hbacCol : PrimCollinear Geo b a c :=
            (HilbertOrder.between_incidence
              b a c hbac).2.2.2.1

          rcases hbacCol with
            ⟨l, hbl, hal, hcl⟩

          exact ⟨l, hal, hbl, hcl⟩

        · have hacb : Geo.Between a c b :=
            hilbert_theorem27_three_points
              Geo
              A C B
              a c b
              hACB
              hac
              hbc.symm
              hab
              hAC
              hAB
              hCBcb

          have hacbCol : PrimCollinear Geo a c b :=
            (HilbertOrder.between_incidence
              a c b hacb).2.2.2.1

          rcases hacbCol with
            ⟨l, hal, hcl, hbl⟩

          exact ⟨l, hal, hbl, hcl⟩

/--
Noncollinearity is preserved by congruence of the three corresponding
segments.
-/
theorem hilbert_noncollinear_of_three_congruences
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABC : ¬ Collinear Geo A B C)
    (hAB : Geo.Congruent A B D E)
    (hAC : Geo.Congruent A C D F)
    (hBC : Geo.Congruent B C E F) :
    ¬ Collinear Geo D E F := by

  intro hDEF

  have hDEAB : Geo.Congruent D E A B :=
    hilbert_congruent_symmetry
      Geo A B D E hAB

  have hDFAC : Geo.Congruent D F A C :=
    hilbert_congruent_symmetry
      Geo A C D F hAC

  have hEFBC : Geo.Congruent E F B C :=
    hilbert_congruent_symmetry
      Geo B C E F hBC

  have hABCcol : Collinear Geo A B C :=
    hilbert_collinearity_preserved_by_three_congruences
      Geo
      D E F
      A B C
      hDEF
      hDEAB
      hDFAC
      hEFBC

  exact hABC hABCcol

/-
Hilbert Theorem 18 (SSS).

If the three corresponding sides of two triangles are congruent,
then the triangles are congruent.

The noncollinearity of the second triple is derived from the three
side congruences.
-/

theorem HilbertSSS
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABC : ¬ Collinear Geo A B C)
    (hAB : Geo.Congruent A B D E)
    (hBC : Geo.Congruent B C E F)
    (hAC : Geo.Congruent A C D F) :
    (¬ Collinear Geo D E F) ∧
    TriangleCongruenceResult Geo A B C D E F := by

  have hDEF : ¬ Collinear Geo D E F :=
    hilbert_noncollinear_of_three_congruences
      Geo
      A B C
      D E F
      hABC
      hAB
      hAC
      hBC

  have hABne : A ≠ B := by
    intro hEq
    subst B

    by_cases hACeq : A = C

    · subst C

      rcases hilbert_line_through_point Geo A with
        ⟨l, hAl⟩

      exact hABC ⟨l, hAl, hAl, hAl⟩

    · rcases
        HilbertPlaneIncidence.line_through
          A C hACeq with
        ⟨l, hAl, hCl⟩

      exact hABC ⟨l, hAl, hAl, hCl⟩

  rcases
      HilbertPlaneIncidence.line_through
        A B hABne with
    ⟨lineAB, hAline, hBline⟩

  rcases
      hilbert_sss_auxiliary_point
        Geo
        A B C
        D E F
        lineAB
        hABC
        hDEF
        hABne
        hAline
        hBline with
    ⟨G, hOppCG, hAG, hBAG_EDF⟩

  have hABG : ¬ Collinear Geo A B G := by
    intro hABG

    rcases hABG with
      ⟨l, hAl, hBl, hGl⟩

    have hEq : l = lineAB :=
      HilbertPlaneIncidence.line_unique
        A B hABne
        l lineAB
        hAl hBl
        hAline hBline

    have hGline :
        HilbertIncidence.OnLine G lineAB := by
      rw [← hEq]
      exact hGl

    exact hOppCG.2.1 hGline

  have hBG :
      Geo.Congruent B G E F :=
    hilbert_sss_auxiliary_BG
      Geo
      A B G
      D E F
      hABG
      hDEF
      hAB
      hAG
      hBAG_EDF

  have hACAG :
      Geo.Congruent A C A G :=
    hilbert_congruent_transitivity
      Geo
      A C
      D F
      A G
      hAC
      (hilbert_congruent_symmetry
        Geo A G D F hAG)

  have hBCBG :
      Geo.Congruent B C B G :=
    hilbert_congruent_transitivity
      Geo
      B C
      E F
      B G
      hBC
      (hilbert_congruent_symmetry
        Geo B G E F hBG)

  have hCG : C ≠ G := by
    intro hEq
    subst G

    rcases hOppCG.2.2 with
      ⟨P, hCPC, _⟩

    exact
      (HilbertOrder.between_incidence
        C P C hCPC).2.2.1 rfl

  rcases
      HilbertPlaneIncidence.line_through
        C G hCG with
    ⟨lineCG, hCcg, hGcg⟩

  have hABC_ABG :
      Geo.AngleCongruent A B C A B G :=
    hilbert_theorem_17
      Geo
      A B C G
      lineAB lineCG
      hABne
      hAline hBline
      hOppCG
      hCcg hGcg
      hACAG
      hBCBG

  have hTrianglesABG :=
    SAS
      Geo
      A B G
      D E F
      hABG
      hDEF
      hAB
      hBAG_EDF
      hAG

  have hABG_DEF :
      Geo.AngleCongruent A B G D E F :=
    hTrianglesABG.angleB

  have hABC_DEF :
      Geo.AngleCongruent A B C D E F :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A B C
      A B G
      D E F
      hABC_ABG
      hABG_DEF

  have hBAC : ¬ Collinear Geo B A C := by
    intro h
    exact hABC
      (PrimCollinearSwap Geo B A C h)

  have hEDF : ¬ Collinear Geo E D F := by
    intro h
    exact hDEF
      (PrimCollinearSwap Geo E D F h)

  have hBA_ED :
      Geo.Congruent B A E D :=
    CongruentReverseBoth
      Geo A B D E hAB

  have hTrianglesRotated :
      TriangleCongruenceResult Geo B A C E D F :=
    SAS
      Geo
      B A C
      E D F
      hBAC
      hEDF
      hBA_ED
      hABC_DEF
      hBC

  have hAngleC :
      Geo.AngleCongruent A C B D F E :=
    AngleCongruentReverse
      Geo
      B C A
      E F D
      hTrianglesRotated.angleC

  have hTriangles :
      TriangleCongruenceResult Geo A B C D E F :=
    {
      sideAB := hAB
      sideBC := hBC
      sideAC := hAC
      angleA := hTrianglesRotated.angleB
      angleB := hTrianglesRotated.angleA
      angleC := hAngleC
    }

  exact ⟨hDEF, hTriangles⟩

/-
Existence of an angle bisector in Hilbert geometry.

For every nondegenerate angle BAC there exists a point M such that
the angles BAM and CAM are congruent.
-/

theorem hilbert_angle_bisector_exists
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ Collinear Geo A B C) :
    ∃ M : Geo.Point,
      Geo.AngleCongruent B A M C A M := by

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        A C
        A B
        hAB with
    ⟨D, hRayBD, hAD_AC⟩

  have hAD : A ≠ D :=
    hRayBD.2.1.symm

  have hABD :
      Collinear Geo A B D :=
    hRayBD.2.2.1

  have hADC :
      ¬ Collinear Geo A D C := by

    intro hADC

    have hBAD :
        Collinear Geo B A D :=
      PrimCollinearSwap Geo A B D hABD

    have hBAC :
        Collinear Geo B A C :=
      hilbert_primCollinear_trans
        Geo
        B A D C
        hAD
        hBAD
        hADC

    exact
      hABC
        (PrimCollinearSwap Geo B A C hBAC)

  have hDC : D ≠ C := by
    intro hDC
    subst D
    exact hABC hABD

  rcases
      HilbertMidpointExists
        Geo D C hDC with
    ⟨M, hMid⟩

  have hDMC :
      Geo.Between D M C :=
    hMid.1

  have hDM_MC :
      Geo.Congruent D M M C :=
    hMid.2

  have hDM : D ≠ M :=
    (HilbertOrder.between_incidence
      D M C hDMC).1

  have hDMCcol :
      Collinear Geo D M C :=
    (HilbertOrder.between_incidence
      D M C hDMC).2.2.2.1

  have hADM :
      ¬ Collinear Geo A D M := by

    intro hADM

    have hADC' :
        Collinear Geo A D C :=
      hilbert_primCollinear_trans
        Geo
        A D M C
        hDM
        hADM
        hDMCcol

    exact hADC hADC'

  have hDM_CM :
      Geo.Congruent D M C M :=
    (Geo.congruent_reverse_second
      D M M C).mp hDM_MC

  have hAM :
      Geo.Congruent A M A M :=
    hilbert_congruent_reflexive
      Geo A M

  have hSSS :=
    HilbertSSS
      Geo
      A D M
      A C M
      hADM
      hAD_AC
      hDM_CM
      hAM

  have hAngle :
      Geo.AngleCongruent D A M C A M :=
    hSSS.2.angleA

  have hRayDB :
      HilbertSameRay Geo A D B :=
    hilbert_sameRay_symm
      Geo A B D hRayBD

  have hEq :
      Geo.Angle D A M =
      Geo.Angle B A M :=
    hilbert_angle_eq_of_sameRay_first
      Geo A D B M hRayDB

  refine ⟨M, ?_⟩

  unfold Geometry.Geo.AngleCongruent at hAngle ⊢
  rw [← hEq]
  exact hAngle

/--
Strict comparison of Hilbert angles.

`HilbertAngleLess Geo A O B C P D` means that the angle `AOB`
is congruent to an angle obtained inside the angle `CPD`.
-/
def HilbertAngleLess
    (A O B C P D : Geo.Point) : Prop :=
  ¬ PrimCollinear Geo A O B ∧
  ¬ PrimCollinear Geo C P D ∧
  ∃ X : Geo.Point,
    HilbertRayMeetsSegment Geo P X C D ∧
    Geo.AngleCongruent A O B C P X

theorem hilbert_angleLess_intro
    (A O B C P D X : Geo.Point)
    (hAOB : ¬ PrimCollinear Geo A O B)
    (hCPD : ¬ PrimCollinear Geo C P D)
    (hInside : HilbertRayMeetsSegment Geo P X C D)
    (hAngle : Geo.AngleCongruent A O B C P X) :
    HilbertAngleLess Geo A O B C P D := by
  exact ⟨hAOB, hCPD, X, hInside, hAngle⟩

theorem hilbert_interior_subangle_not_congruent_whole
    [HilbertCongruence Geo]
    (O D X C : Geo.Point)
    (hXOC : ¬ PrimCollinear Geo X O C)
    (hInside : HilbertRayMeetsSegment Geo O D X C) :
    ¬ Geo.AngleCongruent C O D X O C := by

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  --------------------------------------------------------------------
  -- Base line OC.
  --------------------------------------------------------------------

  have hOC : O ≠ C :=
    hilbert_noncollinear_ne_first
      Geo O C X
      (fun h =>
        hXOC
          (PrimCollinearRotate Geo X C O
            (PrimCollinearSymm Geo O C X h)))

  rcases HilbertPlaneIncidence.line_through O C hOC with
    ⟨base, hObase, hCbase⟩

  --------------------------------------------------------------------
  -- X and H are on the same side of OC, since X-H-C.
  --------------------------------------------------------------------

  have hXCO : ¬ PrimCollinear Geo X C O := by
    intro h
    exact hXOC
      (PrimCollinearRotate Geo X C O h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo X H O C hXHC hXCO with
    ⟨l, hOl, hCl, hXHsame_l⟩

  have hlbase : l = base :=
    HilbertPlaneIncidence.line_unique
      O C hOC
      l base
      hOl hCl
      hObase hCbase

  have hXHsame :
      HilbertSameSide Geo X H base := by
    rw [← hlbase]
    exact hXHsame_l

  --------------------------------------------------------------------
  -- D and H are on the same ray from O, hence on the same side of OC.
  --------------------------------------------------------------------

  rcases hRayODH.2.2.1 with
    ⟨rayLine, hOray, hDray, hHray⟩

  have hHC : H ≠ C :=
    (HilbertOrder.between_incidence
      X H C hXHC).2.1

  have hCoff :
      ¬ HilbertIncidence.OnLine C rayLine := by
    intro hCray

    have hXHCcol :
        PrimCollinear Geo X H C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.2.2.1

    have hHCX :
        PrimCollinear Geo H C X :=
      PrimCollinearCycle Geo X H C hXHCcol

    have hXray :
        HilbertIncidence.OnLine X rayLine :=
      hilbert_collinear_on_line
        Geo H C X
        rayLine
        hHC
        hHray
        hCray
        hHCX

    exact hXOC
      ⟨rayLine, hXray, hOray, hCray⟩

  have hDD :
      HilbertSameRay Geo O D D :=
    hilbert_sameRay_refl
      Geo O D hRayODH.1

  have hDHsame :
      HilbertSameSide Geo D H base :=
    hilbert_sameRay_points_sameSide
      Geo
      O D D H C
      rayLine base
      hOray hDray
      hObase hCbase
      hCoff
      hDD
      hRayODH

  have hHXsame :
      HilbertSameSide Geo H X base :=
    hilbert_sameSide_symm
      Geo X H base hXHsame

  have hDXsame :
      HilbertSameSide Geo D X base :=
    hilbert_sameSide_trans
      Geo D H X base
      hDHsame
      hHXsame

  --------------------------------------------------------------------
  -- Assume the proper subangle COD is congruent to the whole angle XOC.
  --------------------------------------------------------------------

  intro hCong

  have hCong' :
      Geo.AngleCongruent C O D C O X := by
    unfold Geometry.Geo.AngleCongruent at hCong ⊢
    rw [← Geo.angle_swap X O C]
    exact hCong

  --------------------------------------------------------------------
  -- Uniqueness of angle construction forces OD and OX to be the same ray.
  --------------------------------------------------------------------

  have hCO : C ≠ O :=
    hOC.symm

  rcases
      hilbert_angle_unique_common_ray
        Geo
        C O D X
        base
        hCO
        hCbase
        hObase
        hDXsame.1
        hDXsame
        hCong' with
    ⟨Z, hZD, hZX⟩

  have hDX :
      HilbertSameRay Geo O D X :=
    hilbert_sameRay_of_common
      Geo O Z D X
      hZD
      hZX

  --------------------------------------------------------------------
  -- But OD is an interior ray meeting XC at H.
  -- If OD = OX, then O,X,H are collinear.
  -- Together with X-H-C this makes X,O,C collinear: contradiction.
  --------------------------------------------------------------------

  have hXHray :
      HilbertSameRay Geo O X H :=
    hilbert_sameRay_of_common
      Geo O D X H
      hDX
      hRayODH

  have hOXH :
      PrimCollinear Geo O X H :=
    hXHray.2.2.1

  have hXHCcol :
      PrimCollinear Geo X H C :=
    (HilbertOrder.between_incidence
      X H C hXHC).2.2.2.1

  have hXH : X ≠ H :=
    (HilbertOrder.between_incidence
      X H C hXHC).1

  have hOXC :
      PrimCollinear Geo O X C :=
    hilbert_primCollinear_trans
      Geo O X H C
      hXH
      hOXH
      hXHCcol

  exact hXOC
    (PrimCollinearSwap Geo O X C hOXC)

theorem hilbert_ray_order_exclusive
    [HilbertOrder Geo]
    (O D X C : Geo.Point)
    (hXOC : ¬ PrimCollinear Geo X O C)
    (hDXC : HilbertRayMeetsSegment Geo O D X C) :
    ¬ HilbertRayMeetsSegment Geo O X D C := by

  --------------------------------------------------------------------
  -- First ordering: ray OD meets XC.
  --------------------------------------------------------------------

  rcases hDXC with
    ⟨H, hXHC, hRayODH⟩

  have hXHCdata :=
    HilbertOrder.between_incidence X H C hXHC

  have hXH : X ≠ H :=
    hXHCdata.1

  have hHC : H ≠ C :=
    hXHCdata.2.1

  have hXC : X ≠ C :=
    hXHCdata.2.2.1

  --------------------------------------------------------------------
  -- Base line OX.
  --------------------------------------------------------------------

  have hOX : O ≠ X :=
    hilbert_noncollinear_ne_first
      Geo O X C
      (fun h =>
        hXOC
          (PrimCollinearSwap Geo O X C h))

  rcases HilbertPlaneIncidence.line_through O X hOX with
    ⟨lineOX, hOox, hXox⟩

  --------------------------------------------------------------------
  -- Line XC.
  --------------------------------------------------------------------

  rcases HilbertPlaneIncidence.line_through X C hXC with
    ⟨lineXC, hXxc, hCxc⟩

  have hHxc :
      HilbertIncidence.OnLine H lineXC :=
    hilbert_between_on_line
      Geo X H C lineXC
      hXxc hCxc hXHC

  have hOoffXC :
      ¬ HilbertIncidence.OnLine O lineXC := by
    intro hOxc
    exact hXOC
      ⟨lineXC, hXxc, hOxc, hCxc⟩

  --------------------------------------------------------------------
  -- H and C lie on the same ray from X.
  -- Hence H and C are on the same side of OX.
  --------------------------------------------------------------------

  have hRayXHC :
      HilbertSameRay Geo X H C :=
    hilbert_sameRay_of_between
      Geo X H C hXHC

  have hRayXHH :
      HilbertSameRay Geo X H H :=
    hilbert_sameRay_refl
      Geo X H hXH.symm

  have hHCsame :
      HilbertSameSide Geo H C lineOX :=
    hilbert_sameRay_points_sameSide
      Geo
      X H H C O
      lineXC lineOX
      hXxc hHxc
      hXox hOox
      hOoffXC
      hRayXHH
      hRayXHC

  --------------------------------------------------------------------
  -- Line OD.
  --------------------------------------------------------------------

  have hOD : O ≠ D :=
    hRayODH.1.symm

  rcases HilbertPlaneIncidence.line_through O D hOD with
    ⟨lineOD, hOod, hDod⟩

  have hHod :
      HilbertIncidence.OnLine H lineOD :=
    hilbert_collinear_on_line
      Geo O D H lineOD
      hOD
      hOod hDod
      hRayODH.2.2.1

  --------------------------------------------------------------------
  -- X is not on OD.
  --------------------------------------------------------------------

  have hXoffOD :
      ¬ HilbertIncidence.OnLine X lineOD := by
    intro hXod

    have hXHCcol :
        PrimCollinear Geo X H C :=
      hXHCdata.2.2.2.1

    have hCod :
        HilbertIncidence.OnLine C lineOD :=
      hilbert_collinear_on_line
        Geo X H C lineOD
        hXH
        hXod hHod
        hXHCcol

    exact hXOC
      ⟨lineOD, hXod, hOod, hCod⟩

  --------------------------------------------------------------------
  -- D and H lie on the same ray from O.
  -- Hence D and H are on the same side of OX.
  --------------------------------------------------------------------

  have hRayODD :
      HilbertSameRay Geo O D D :=
    hilbert_sameRay_refl
      Geo O D hRayODH.1

  have hDHsame :
      HilbertSameSide Geo D H lineOX :=
    hilbert_sameRay_points_sameSide
      Geo
      O D D H X
      lineOD lineOX
      hOod hDod
      hOox hXox
      hXoffOD
      hRayODD
      hRayODH

  --------------------------------------------------------------------
  -- Therefore D and C are on the same side of OX.
  --------------------------------------------------------------------

  have hDCsame :
      HilbertSameSide Geo D C lineOX :=
    hilbert_sameSide_trans
      Geo D H C lineOX
      hDHsame
      hHCsame

  --------------------------------------------------------------------
  -- Assume the reverse ordering:
  -- ray OX meets DC.
  --------------------------------------------------------------------

  intro hReverse

  rcases hReverse with
    ⟨K, hDKC, hRayOXK⟩

  have hKox :
      HilbertIncidence.OnLine K lineOX :=
    hilbert_collinear_on_line
      Geo O X K lineOX
      hOX
      hOox hXox
      hRayOXK.2.2.1

  --------------------------------------------------------------------
  -- Then D and C are on opposite sides of OX.
  --------------------------------------------------------------------

  have hOpp :
      HilbertOppositeSide Geo D C lineOX :=
    ⟨hDCsame.1,
      hDCsame.2.1,
      ⟨K, hDKC, hKox⟩⟩

  --------------------------------------------------------------------
  -- Contradiction.
  --------------------------------------------------------------------

  exact
    (hilbert_oppositeSide_not_sameSide
      Geo D C lineOX hOpp)
      hDCsame

/--
Segment subtraction.

If `B` lies between `A` and `C`, `b` lies between `a` and `c`,
and the whole segments and the first parts are respectively congruent,
then the remaining parts are congruent.
-/
theorem hilbert_segment_subtraction
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c) :
    Geo.Congruent B C b c := by

  have habcData :=
    HilbertOrder.between_incidence a b c habc

  have hab : a ≠ b :=
    habcData.1

  have hbc : b ≠ c :=
    habcData.2.1

  ----------------------------------------------------------------------
  -- Lay off a copy of BC on ray bc.
  ----------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        B C
        b c
        hbc with
    ⟨d, hRaycd, hbd_BC⟩

  ----------------------------------------------------------------------
  -- Since d lies on ray bc and a-b-c, we also have a-b-d.
  ----------------------------------------------------------------------

  have hRayaa :
      HilbertSameRay Geo b a a :=
    hilbert_sameRay_refl
      Geo b a hab

  have habd :
      Geo.Between a b d :=
    hilbert_between_transport_sameRays
      Geo
      a b c
      a d
      habc
      hRayaa
      hRaycd

  ----------------------------------------------------------------------
  -- AB = ab and BC = bd imply AC = ad.
  ----------------------------------------------------------------------

  have hBCbd :
      Geo.Congruent B C b d :=
    hilbert_congruent_symmetry
      Geo b d B C hbd_BC

  have hACad :
      Geo.Congruent A C a d :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A B C
      a b d
      hABC
      habd
      hABab
      hBCbd

  ----------------------------------------------------------------------
  -- Both c and d lie on ray ab at distance AC from a.
  -- Uniqueness of segment construction gives d = c.
  ----------------------------------------------------------------------

  have hRayabd :
      HilbertSameRay Geo a b d :=
    hilbert_sameRay_of_between
      Geo a b d habd

  have hRayabc :
      HilbertSameRay Geo a b c :=
    hilbert_sameRay_of_between
      Geo a b c habc

  have hadAC :
      Geo.Congruent a d A C :=
    hilbert_congruent_symmetry
      Geo A C a d hACad

  have hacAC :
      Geo.Congruent a c A C :=
    hilbert_congruent_symmetry
      Geo A C a c hACac

  have hdc : d = c :=
    hilbert_segment_construction_unique
      Geo
      A C
      a b
      d c
      hRayabd
      hRayabc
      hadAC
      hacAC

  subst d

  exact
    hilbert_congruent_symmetry
      Geo b c B C hbd_BC

/--
If `B` lies between `A` and `C`, and segments congruent to `AB`
and `AC` are laid off on the same ray from `O`, then the endpoint
of the shorter segment lies between `O` and the endpoint of the
longer segment.
-/
theorem hilbert_layoff_shorter_between
    [HilbertCongruence Geo]
    (A B C O R P Q : Geo.Point)
    (hABC : Geo.Between A B C)
    (hRayP : HilbertSameRay Geo O R P)
    (hRayQ : HilbertSameRay Geo O R Q)
    (hOP_AB : Geo.Congruent O P A B)
    (hOQ_AC : Geo.Congruent O Q A C) :
    Geo.Between O P Q := by

  have hABCdata :=
    HilbertOrder.between_incidence A B C hABC

  have hBC : B ≠ C :=
    hABCdata.2.1

  have hOP : O ≠ P :=
    hRayP.2.1.symm

  rcases HilbertOrder.between_extension O P hOP with
    ⟨T, hOPT⟩

  have hPT : P ≠ T :=
    (HilbertOrder.between_incidence
      O P T hOPT).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        B C
        P T
        hPT with
    ⟨S, hRayTS, hPS_BC⟩

  have hRayPOO :
      HilbertSameRay Geo P O O :=
    hilbert_sameRay_refl
      Geo P O hOP

  have hOPS :
      Geo.Between O P S :=
    hilbert_between_transport_sameRays
      Geo
      O P T
      O S
      hOPT
      hRayPOO
      hRayTS

  have hOS_AC :
      Geo.Congruent O S A C :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      O P S
      A B C
      hOPS
      hABC
      hOP_AB
      hPS_BC

  have hRayOPS :
      HilbertSameRay Geo O P S :=
    hilbert_sameRay_of_between
      Geo O P S hOPS

  have hRayOPR :
      HilbertSameRay Geo O P R :=
    hilbert_sameRay_symm
      Geo O R P hRayP

  have hRayORS :
      HilbertSameRay Geo O R S :=
    hilbert_sameRay_of_common
      Geo
      O P R S
      hRayOPR
      hRayOPS

  have hSQ : S = Q :=
    hilbert_segment_construction_unique
      Geo
      A C
      O R
      S Q
      hRayORS
      hRayQ
      hOS_AC
      hOQ_AC

  subst S

  exact hOPS

/--
Right transport of strict segment comparison through congruence.

If `AB < CD` and `CD ≅ C'D'`, then `AB < C'D'`.
-/
theorem hilbert_segmentLess_congruent_right
    [HilbertCongruence Geo]
    (A B C D C' D' : Geo.Point)
    (hLess : HilbertSegmentLess Geo A B C D)
    (hCong : Geo.Congruent C D C' D') :
    HilbertSegmentLess Geo A B C' D' := by

  rcases hLess with
    ⟨P, hCPD, hABCP⟩

  have hCPDdata :=
    HilbertOrder.between_incidence C P D hCPD

  have hCD : C ≠ D :=
    hCPDdata.2.2.1

  have hC'D' : C' ≠ D' := by
    intro hEq
    subst D'

    exact hCD
      (bookZero_nullSegment1
        Geo C D C'
        hCong)

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        C P
        C' D'
        hC'D' with
    ⟨P', hRayP', hC'P'_CP⟩

  have hRayD' :
      HilbertSameRay Geo C' D' D' :=
    hilbert_sameRay_refl
      Geo C' D' hC'D'.symm

  have hCP_C'P' :
      Geo.Congruent C P C' P' :=
    hilbert_congruent_symmetry
      Geo C' P' C P hC'P'_CP

  have hC'D'_CD :
      Geo.Congruent C' D' C D :=
    hilbert_congruent_symmetry
      Geo C D C' D' hCong

  have hC'P'D' :
      Geo.Between C' P' D' :=
    hilbert_layoff_shorter_between
      Geo
      C P D
      C' D'
      P' D'
      hCPD
      hRayP'
      hRayD'
      hC'P'_CP
      hC'D'_CD

  have hAB_C'P' :
      Geo.Congruent A B C' P' :=
    hilbert_congruent_transitivity
      Geo
      A B
      C P
      C' P'
      hABCP
      hCP_C'P'

  exact
    ⟨P',
      hC'P'D',
      hAB_C'P'⟩

/--
Transport of an interior point between congruent segments.

If `H` lies between `X` and `C` and `XC ≅ UV`, then there is a point
`H'` between `U` and `V` such that the two component segments correspond:
`XH ≅ UH'` and `HC ≅ H'V`.
-/
theorem hilbert_between_point_transport
    [HilbertCongruence Geo]
    (X H C U V : Geo.Point)
    (hXHC : Geo.Between X H C)
    (hXC_UV : Geo.Congruent X C U V) :
    ∃ H' : Geo.Point,
      Geo.Between U H' V ∧
      Geo.Congruent X H U H' ∧
      Geo.Congruent H C H' V := by

  have hXH_lt_XC :
      HilbertSegmentLess Geo X H X C :=
    hilbert_segmentLess_of_between
      Geo X H C hXHC

  have hXH_lt_UV :
      HilbertSegmentLess Geo X H U V :=
    hilbert_segmentLess_congruent_right
      Geo
      X H
      X C
      U V
      hXH_lt_XC
      hXC_UV

  rcases hXH_lt_UV with
    ⟨H', hUH'V, hXH_UH'⟩

  have hHC_H'V :
      Geo.Congruent H C H' V :=
    hilbert_segment_subtraction
      Geo
      X H C
      U H' V
      hXHC
      hUH'V
      hXH_UH'
      hXC_UV

  exact
    ⟨H',
      hUH'V,
      hXH_UH',
      hHC_H'V⟩

/--
A ray meeting a segment continues to meet any segment whose endpoints
are moved along the same two rays from the vertex.

This is the crossbar invariance needed for the transport of an
interior ray between congruent angles.
-/
theorem hilbert_ray_meets_segment_sameRays
    [HilbertOrder Geo]
    (O R A B A' B' : Geo.Point)
    (hMeet :
      HilbertRayMeetsSegment Geo O R A B)
    (hAA' :
      HilbertSameRay Geo O A A')
    (hBB' :
      HilbertSameRay Geo O B B')
    (hAOB :
      ¬ PrimCollinear Geo A O B)
    (hA'OB' :
      ¬ PrimCollinear Geo A' O B') :
    HilbertRayMeetsSegment Geo O R A' B' := by

  rcases hMeet with
    ⟨X, hAXB, hRayORX⟩

  have hAXBdata :=
    HilbertOrder.between_incidence A X B hAXB

  have hAX : A ≠ X :=
    hAXBdata.1

  have hXB : X ≠ B :=
    hAXBdata.2.1

  have hOX : O ≠ X :=
    hRayORX.2.1.symm

  have hOA : O ≠ A :=
    hAA'.1.symm

  have hOB : O ≠ B :=
    hBB'.1.symm

  have hOA' : O ≠ A' :=
    hAA'.2.1.symm

  have hOB' : O ≠ B' :=
    hBB'.2.1.symm

  --------------------------------------------------------------------
  -- The line OX crosses AB at X.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        O X hOX with
    ⟨lineOX, hOlineOX, hXlineOX⟩

  have hAXBcol :
      PrimCollinear Geo A X B :=
    hAXBdata.2.2.2.1

  have hAoffOX :
      ¬ HilbertIncidence.OnLine A lineOX := by
    intro hAline

    have hBline :
        HilbertIncidence.OnLine B lineOX :=
      hilbert_collinear_on_line
        Geo A X B lineOX
        hAX
        hAline
        hXlineOX
        hAXBcol

    exact hAOB
      ⟨lineOX,
        hAline,
        hOlineOX,
        hBline⟩

  have hBoffOX :
      ¬ HilbertIncidence.OnLine B lineOX := by
    intro hBline

    have hXBA :
        PrimCollinear Geo X B A :=
      PrimCollinearCycle
        Geo A X B hAXBcol

    have hAline :
        HilbertIncidence.OnLine A lineOX :=
      hilbert_collinear_on_line
        Geo X B A lineOX
        hXB
        hXlineOX
        hBline
        hXBA

    exact hAOB
      ⟨lineOX,
        hAline,
        hOlineOX,
        hBline⟩

  have hOppAB :
      HilbertOppositeSide Geo A B lineOX :=
    ⟨hAoffOX,
      hBoffOX,
      ⟨X, hAXB, hXlineOX⟩⟩

  --------------------------------------------------------------------
  -- Moving A to A' on ray OA preserves its side of OX.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        O A hOA with
    ⟨lineOA, hOlineOA, hAlineOA⟩

  have hXoffOA :
      ¬ HilbertIncidence.OnLine X lineOA := by
    intro hXline

    have hBline :
        HilbertIncidence.OnLine B lineOA :=
      hilbert_collinear_on_line
        Geo A X B lineOA
        hAX
        hAlineOA
        hXline
        hAXBcol

    exact hAOB
      ⟨lineOA,
        hAlineOA,
        hOlineOA,
        hBline⟩

  have hRayOAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hOA.symm

  have hAA'SameOX :
      HilbertSameSide Geo A A' lineOX :=
    hilbert_sameRay_points_sameSide
      Geo
      O A
      A A'
      X
      lineOA lineOX
      hOlineOA
      hAlineOA
      hOlineOX
      hXlineOX
      hXoffOA
      hRayOAA
      hAA'

  --------------------------------------------------------------------
  -- Moving B to B' on ray OB preserves its side of OX.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        O B hOB with
    ⟨lineOB, hOlineOB, hBlineOB⟩

  have hXoffOB :
      ¬ HilbertIncidence.OnLine X lineOB := by
    intro hXline

    have hXBA :
        PrimCollinear Geo X B A :=
      PrimCollinearCycle
        Geo A X B hAXBcol

    have hAline :
        HilbertIncidence.OnLine A lineOB :=
      hilbert_collinear_on_line
        Geo X B A lineOB
        hXB
        hXline
        hBlineOB
        hXBA

    exact hAOB
      ⟨lineOB,
        hAline,
        hOlineOB,
        hBlineOB⟩

  have hRayOBB :
      HilbertSameRay Geo O B B :=
    hilbert_sameRay_refl
      Geo O B hOB.symm

  have hBB'SameOX :
      HilbertSameSide Geo B B' lineOX :=
    hilbert_sameRay_points_sameSide
      Geo
      O B
      B B'
      X
      lineOB lineOX
      hOlineOB
      hBlineOB
      hOlineOX
      hXlineOX
      hXoffOB
      hRayOBB
      hBB'

  --------------------------------------------------------------------
  -- Hence A' and B' are still on opposite sides of OX.
  --------------------------------------------------------------------

  have hOppBA :
      HilbertOppositeSide Geo B A lineOX :=
    hilbert_oppositeSide_symm
      Geo A B lineOX hOppAB

  have hOppBA' :
      HilbertOppositeSide Geo B A' lineOX :=
    hilbert_oppositeSide_transport_right
      Geo
      B A A'
      lineOX
      hOppBA
      hAA'SameOX

  have hOppA'B :
      HilbertOppositeSide Geo A' B lineOX :=
    hilbert_oppositeSide_symm
      Geo B A' lineOX hOppBA'

  have hOppA'B' :
      HilbertOppositeSide Geo A' B' lineOX :=
    hilbert_oppositeSide_transport_right
      Geo
      A' B B'
      lineOX
      hOppA'B
      hBB'SameOX

  rcases hOppA'B'.2.2 with
    ⟨Y, hA'YB', hYlineOX⟩

  --------------------------------------------------------------------
  -- X and A lie on the same side of OB.
  --------------------------------------------------------------------

  have hABO :
      ¬ PrimCollinear Geo A B O := by
    intro h
    exact hAOB
      (PrimCollinearRotate Geo A B O h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        A X O B
        hAXB
        hABO with
    ⟨lineOB₁, hOlineOB₁, hBlineOB₁, hAXSame₁⟩

  have hLineOB :
      lineOB₁ = lineOB :=
    HilbertPlaneIncidence.line_unique
      O B hOB
      lineOB₁ lineOB
      hOlineOB₁ hBlineOB₁
      hOlineOB hBlineOB

  have hAXSameOB :
      HilbertSameSide Geo A X lineOB := by
    rw [← hLineOB]
    exact hAXSame₁

  --------------------------------------------------------------------
  -- A and A' are also on the same side of OB.
  --------------------------------------------------------------------

  have hBoffOA :
      ¬ HilbertIncidence.OnLine B lineOA := by
    intro hBline
    exact hAOB
      ⟨lineOA,
        hAlineOA,
        hOlineOA,
        hBline⟩

  have hAA'SameOB :
      HilbertSameSide Geo A A' lineOB :=
    hilbert_sameRay_points_sameSide
      Geo
      O A
      A A'
      B
      lineOA lineOB
      hOlineOA
      hAlineOA
      hOlineOB
      hBlineOB
      hBoffOA
      hRayOAA
      hAA'

  have hXASameOB :
      HilbertSameSide Geo X A lineOB :=
    hilbert_sameSide_symm
      Geo A X lineOB hAXSameOB

  have hXA'SameOB :
      HilbertSameSide Geo X A' lineOB :=
    hilbert_sameSide_trans
      Geo X A A' lineOB
      hXASameOB
      hAA'SameOB

  --------------------------------------------------------------------
  -- The point Y between A' and B' lies on the same side of OB
  -- as A'.
  --------------------------------------------------------------------

  have hA'B'O :
      ¬ PrimCollinear Geo A' B' O := by
    intro h
    exact hA'OB'
      (PrimCollinearRotate Geo A' B' O h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        A' Y O B'
        hA'YB'
        hA'B'O with
    ⟨lineOB', hOlineOB', hB'lineOB', hA'YSame'⟩

  have hB'lineOB :
      HilbertIncidence.OnLine B' lineOB :=
    hilbert_collinear_on_line
      Geo O B B'
      lineOB
      hOB
      hOlineOB
      hBlineOB
      hBB'.2.2.1

  have hLineOB' :
      lineOB' = lineOB :=
    HilbertPlaneIncidence.line_unique
      O B' hOB'
      lineOB' lineOB
      hOlineOB' hB'lineOB'
      hOlineOB hB'lineOB

  have hA'YSameOB :
      HilbertSameSide Geo A' Y lineOB := by
    rw [← hLineOB']
    exact hA'YSame'

  have hXYSameOB :
      HilbertSameSide Geo X Y lineOB :=
    hilbert_sameSide_trans
      Geo X A' Y lineOB
      hXA'SameOB
      hA'YSameOB

  --------------------------------------------------------------------
  -- Since X and Y lie on OX and on the same side of OB,
  -- they determine the same ray from O.
  --------------------------------------------------------------------

  have hOY : O ≠ Y := by
    intro h
    subst Y
    exact hXYSameOB.2.1 hOlineOB

  have hOXYcol :
      PrimCollinear Geo O X Y :=
    ⟨lineOX,
      hOlineOX,
      hXlineOX,
      hYlineOX⟩

  have hNotXOY :
      ¬ Geo.Between X O Y := by
    intro hXOY

    have hOppXY :
        HilbertOppositeSide Geo X Y lineOB :=
      ⟨hXYSameOB.1,
        hXYSameOB.2.1,
        ⟨O, hXOY, hOlineOB⟩⟩

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo X Y lineOB hOppXY)
        hXYSameOB

  have hRayOXY :
      HilbertSameRay Geo O X Y :=
    ⟨hOX.symm,
      hOY.symm,
      hOXYcol,
      hNotXOY⟩

  have hRayOXR :
      HilbertSameRay Geo O X R :=
    hilbert_sameRay_symm
      Geo O R X hRayORX

  have hRayORY :
      HilbertSameRay Geo O R Y :=
    hilbert_sameRay_of_common
      Geo
      O X R Y
      hRayOXR
      hRayOXY

  exact
    ⟨Y,
      hA'YB',
      hRayORY⟩

/--
Hilbert Theorem 16, existence part.

An interior ray of one angle can be transported to an interior ray
of a congruent angle so that the corresponding component angles are
congruent.
-/
theorem hilbert_interior_subangle_transport
    [HilbertCongruence Geo]
    (O X C D A' O' B' : Geo.Point)
    (hXOC : ¬ PrimCollinear Geo X O C)
    (hAOB : ¬ PrimCollinear Geo A' O' B')
    (hInside : HilbertRayMeetsSegment Geo O D X C)
    (hWhole :
      Geo.AngleCongruent X O C A' O' B') :
    ∃ D' : Geo.Point,
      HilbertRayMeetsSegment Geo O' D' A' B' ∧
      Geo.AngleCongruent C O D B' O' D' := by

  have hXO : X ≠ O :=
    hilbert_noncollinear_ne_first
      Geo X O C hXOC

  have hOX : O ≠ X :=
    hXO.symm

  have hOCX :
      ¬ Collinear Geo O C X := by
    intro h
    exact hXOC
      (PrimCollinearRotate
        Geo X C O
        (PrimCollinearSymm Geo O C X h))

  have hOC : O ≠ C :=
    hilbert_noncollinear_ne_first
      Geo O C X hOCX

  have hA'O' : A' ≠ O' :=
    hilbert_noncollinear_ne_first
      Geo A' O' B' hAOB

  have hO'A' : O' ≠ A' :=
    hA'O'.symm

  have hO'B'A' :
      ¬ Collinear Geo O' B' A' := by
    intro h
    exact hAOB
      (PrimCollinearRotate
        Geo A' B' O'
        (PrimCollinearSymm Geo O' B' A' h))

  have hO'B' : O' ≠ B' :=
    hilbert_noncollinear_ne_first
      Geo O' B' A' hO'B'A'

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O' A'
        O X
        hOX with
    ⟨X₀, hRayX₀, hOX₀_O'A'⟩

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O' B'
        O C
        hOC with
    ⟨C₀, hRayC₀, hOC₀_O'B'⟩

  have hOX₀ : O ≠ X₀ :=
    hRayX₀.2.1.symm

  have hOC₀ : O ≠ C₀ :=
    hRayC₀.2.1.symm

  have hX₀OC₀ :
      ¬ PrimCollinear Geo X₀ O C₀ := by
    intro hCol

    have hOC₀C :
        PrimCollinear Geo O C₀ C :=
      PrimCollinearRotate
        Geo O C C₀ hRayC₀.2.2.1

    have hX₀OC :
        PrimCollinear Geo X₀ O C :=
      hilbert_primCollinear_trans
        Geo
        X₀ O C₀ C
        hOC₀
        hCol
        hOC₀C

    have hOX₀C :
        PrimCollinear Geo O X₀ C :=
      PrimCollinearSwap
        Geo X₀ O C hX₀OC

    have hXOX₀ :
        PrimCollinear Geo X O X₀ :=
      PrimCollinearSwap
        Geo O X X₀ hRayX₀.2.2.1

    have hXOCcol :
        PrimCollinear Geo X O C :=
      hilbert_primCollinear_trans
        Geo
        X O X₀ C
        hOX₀
        hXOX₀
        hOX₀C

    exact hXOC hXOCcol

  have hAngleFirst :
      Geo.Angle X O C₀ =
      Geo.Angle X₀ O C₀ :=
    hilbert_angle_eq_of_sameRay_first
      Geo O X X₀ C₀ hRayX₀

  have hAngleSecond :
      Geo.Angle X O C =
      Geo.Angle X O C₀ :=
    hilbert_angle_eq_of_sameRay_second
      Geo O X C C₀ hRayC₀

  have hAngleX₀OC₀ :
      Geo.Angle X₀ O C₀ =
      Geo.Angle X O C := by
    calc
      Geo.Angle X₀ O C₀
          = Geo.Angle X O C₀ := hAngleFirst.symm
      _ = Geo.Angle X O C := hAngleSecond.symm

  have hWhole₀ :
      Geo.AngleCongruent X₀ O C₀ A' O' B' := by
    unfold Geometry.Geo.AngleCongruent at hWhole ⊢
    rw [hAngleX₀OC₀]
    exact hWhole

  have hOX₀C₀ :
      ¬ Collinear Geo O X₀ C₀ := by
    intro h
    exact hX₀OC₀
      (PrimCollinearSwap Geo O X₀ C₀ h)

  have hO'A'B' :
      ¬ Collinear Geo O' A' B' := by
    intro h
    exact hAOB
      (PrimCollinearSwap Geo O' A' B' h)

  have hBig :=
    SAS
      Geo
      O X₀ C₀
      O' A' B'
      hOX₀C₀
      hO'A'B'
      hOX₀_O'A'
      hWhole₀
      hOC₀_O'B'

  have hX₀C₀_A'B' :
      Geo.Congruent X₀ C₀ A' B' :=
    hBig.sideBC

  have hInside₀ :
      HilbertRayMeetsSegment Geo O D X₀ C₀ :=
    hilbert_ray_meets_segment_sameRays
      Geo
      O D
      X C
      X₀ C₀
      hInside
      hRayX₀
      hRayC₀
      hXOC
      hX₀OC₀

  rcases hInside₀ with
    ⟨H₀, hX₀H₀C₀, hRayODH₀⟩

  rcases
      hilbert_between_point_transport
        Geo
        X₀ H₀ C₀
        A' B'
        hX₀H₀C₀
        hX₀C₀_A'B' with
    ⟨H', hA'H'B', hX₀H₀_A'H', hH₀C₀_H'B'⟩

  refine ⟨H', ?_, ?_⟩

  have hO'H' : O' ≠ H' := by
    intro hEq
    subst H'

    have hA'O'B'col :
        PrimCollinear Geo A' O' B' :=
      (HilbertOrder.between_incidence
        A' O' B' hA'H'B').2.2.2.1

    exact hAOB hA'O'B'col

  have hRayO'H'H' :
      HilbertSameRay Geo O' H' H' :=
    hilbert_sameRay_refl
      Geo O' H' hO'H'.symm

  · exact
      ⟨H',
        hA'H'B',
        hRayO'H'H'⟩

  have hX₀H₀ :
      X₀ ≠ H₀ :=
    (HilbertOrder.between_incidence
      X₀ H₀ C₀ hX₀H₀C₀).1

  have hA'H' :
      A' ≠ H' :=
    (HilbertOrder.between_incidence
      A' H' B' hA'H'B').1

  have hOX₀H₀ :
      ¬ PrimCollinear Geo O X₀ H₀ := by
    intro hCol

    have hX₀H₀C₀col :
        PrimCollinear Geo X₀ H₀ C₀ :=
      (HilbertOrder.between_incidence
        X₀ H₀ C₀ hX₀H₀C₀).2.2.2.1

    have hOX₀C₀col :
        PrimCollinear Geo O X₀ C₀ :=
      hilbert_primCollinear_trans
        Geo
        O X₀ H₀ C₀
        hX₀H₀
        hCol
        hX₀H₀C₀col

    exact hX₀OC₀
      (PrimCollinearSwap Geo O X₀ C₀ hOX₀C₀col)

  have hO'A'H' :
      ¬ PrimCollinear Geo O' A' H' := by
    intro hCol

    have hA'H'B'col :
        PrimCollinear Geo A' H' B' :=
      (HilbertOrder.between_incidence
        A' H' B' hA'H'B').2.2.2.1

    have hO'A'B'col :
        PrimCollinear Geo O' A' B' :=
      hilbert_primCollinear_trans
        Geo
        O' A' H' B'
        hA'H'
        hCol
        hA'H'B'col

    exact hAOB
      (PrimCollinearSwap Geo O' A' B' hO'A'B'col)

  have hRayX₀H₀C₀ :
      HilbertSameRay Geo X₀ H₀ C₀ :=
    hilbert_sameRay_of_between
      Geo X₀ H₀ C₀ hX₀H₀C₀

  have hRayA'H'B' :
      HilbertSameRay Geo A' H' B' :=
    hilbert_sameRay_of_between
      Geo A' H' B' hA'H'B'

  have hAngleAtX₀ :
      Geo.Angle O X₀ H₀ =
      Geo.Angle O X₀ C₀ :=
    hilbert_angle_eq_of_sameRay_second
      Geo X₀ O H₀ C₀
      hRayX₀H₀C₀

  have hAngleAtA' :
      Geo.Angle O' A' H' =
      Geo.Angle O' A' B' :=
    hilbert_angle_eq_of_sameRay_second
      Geo A' O' H' B'
      hRayA'H'B'

  have hBigAngleB :
      Geo.AngleCongruent O X₀ C₀ O' A' B' :=
    hBig.angleB

  have hSmallAngle :
      Geo.AngleCongruent O X₀ H₀ O' A' H' := by
    unfold Geometry.Geo.AngleCongruent at hBigAngleB ⊢
    rw [hAngleAtX₀, hAngleAtA']
    exact hBigAngleB

  have hX₀OH₀ :
      ¬ Collinear Geo X₀ O H₀ := by
    intro h
    exact hOX₀H₀
      (PrimCollinearSwap Geo X₀ O H₀ h)

  have hA'O'H' :
      ¬ Collinear Geo A' O' H' := by
    intro h
    exact hO'A'H'
      (PrimCollinearSwap Geo A' O' H' h)

  have hX₀O_A'O' :
      Geo.Congruent X₀ O A' O' :=
    CongruentReverseBoth
      Geo
      O X₀
      O' A'
      hOX₀_O'A'

  have hSmall :=
    SAS
      Geo
      X₀ O H₀
      A' O' H'
      hX₀OH₀
      hA'O'H'
      hX₀O_A'O'
      hSmallAngle
      hX₀H₀_A'H'

  have hOH₀_O'H' :
      Geo.Congruent O H₀ O' H' :=
    hSmall.sideBC

  have hC₀H₀ :
      C₀ ≠ H₀ :=
    (HilbertOrder.between_incidence
      X₀ H₀ C₀ hX₀H₀C₀).2.1.symm

  have hOC₀H₀ :
      ¬ PrimCollinear Geo O C₀ H₀ := by
    intro hCol

    have hC₀H₀X₀ :
        PrimCollinear Geo C₀ H₀ X₀ :=
      PrimCollinearSymm
        Geo X₀ H₀ C₀
        (HilbertOrder.between_incidence
          X₀ H₀ C₀ hX₀H₀C₀).2.2.2.1

    have hOC₀X₀ :
        PrimCollinear Geo O C₀ X₀ :=
      hilbert_primCollinear_trans
        Geo
        O C₀ H₀ X₀
        hC₀H₀
        hCol
        hC₀H₀X₀

    have hX₀OC₀col :
        PrimCollinear Geo X₀ O C₀ :=
      PrimCollinearRotate
        Geo X₀ C₀ O
        (PrimCollinearSymm
          Geo O C₀ X₀ hOC₀X₀)

    exact hX₀OC₀ hX₀OC₀col

  have hC₀H₀_B'H' :
      Geo.Congruent C₀ H₀ B' H' :=
    CongruentReverseBoth
      Geo
      H₀ C₀
      H' B'
      hH₀C₀_H'B'

  have hOC₀H₀' :
      ¬ Collinear Geo O C₀ H₀ := by
    intro h
    exact hOC₀H₀ h

  have hSSS :=
    HilbertSSS
      Geo
      O C₀ H₀
      O' B' H'
      hOC₀H₀'
      hOC₀_O'B'
      hC₀H₀_B'H'
      hOH₀_O'H'

  have hSub₀ :
      Geo.AngleCongruent C₀ O H₀ B' O' H' :=
    hSSS.2.angleA

  have hAngleC :
      Geo.Angle C O D =
      Geo.Angle C₀ O D :=
    hilbert_angle_eq_of_sameRay_first
      Geo O C C₀ D hRayC₀

  have hAngleD :
      Geo.Angle C₀ O D =
      Geo.Angle C₀ O H₀ :=
    hilbert_angle_eq_of_sameRay_second
      Geo O C₀ D H₀ hRayODH₀

  have hAngleCOD :
      Geo.Angle C O D =
      Geo.Angle C₀ O H₀ := by
    calc
      Geo.Angle C O D
          = Geo.Angle C₀ O D := hAngleC
      _ = Geo.Angle C₀ O H₀ := hAngleD

  unfold Geometry.Geo.AngleCongruent at hSub₀ ⊢
  rw [hAngleCOD]
  exact hSub₀

theorem hilbert_exterior_angle_aux
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C) :
    ∃ M E : Geo.Point,
      Geo.Between A M C ∧
      Geo.Congruent A M M C ∧
      Geo.Between B M E ∧
      Geo.Congruent B M M E ∧
      Geo.AngleCongruent B A C M C E := by

  ----------------------------------------------------------------------
  -- Midpoint M of AC.
  ----------------------------------------------------------------------

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (fun h =>
        hABC
          (PrimCollinearRotate Geo A C B h))

  rcases HilbertMidpointExists Geo A C hAC with
    ⟨M, hMid⟩

  rcases hMid with
    ⟨hAMC, hAMMC⟩

  ----------------------------------------------------------------------
  -- B is not M.
  ----------------------------------------------------------------------

  have hBM : B ≠ M := by
    intro hBM
    subst M

    have hABCcol :
        PrimCollinear Geo A B C :=
      (HilbertOrder.between_incidence
        A B C hAMC).2.2.2.1

    exact hABC hABCcol

  ----------------------------------------------------------------------
  -- Extend BM beyond M to E with BM ≅ ME.
  ----------------------------------------------------------------------

  rcases ExtendSegmentBeyond Geo B M hBM with
    ⟨E, hBME, hBMME⟩

  ----------------------------------------------------------------------
  -- Basic incidence data from A-M-C.
  ----------------------------------------------------------------------

  have hAMCdata :=
    HilbertOrder.between_incidence A M C hAMC

  have hAM : A ≠ M :=
    hAMCdata.1

  have hMC : M ≠ C :=
    hAMCdata.2.1

  have hAMCcol : PrimCollinear Geo A M C :=
    hAMCdata.2.2.2.1

  ----------------------------------------------------------------------
  -- Triangle AMB is noncollinear.
  ----------------------------------------------------------------------

  have hAMBnc : ¬ PrimCollinear Geo A M B := by
    intro hAMB

    have hCMA : PrimCollinear Geo C M A :=
      PrimCollinearSymm Geo A M C hAMCcol

    have hMAB : PrimCollinear Geo M A B :=
      PrimCollinearSwap Geo A M B hAMB

    have hCMB : PrimCollinear Geo C M B :=
      hilbert_primCollinear_trans
        Geo C M A B
        hAM.symm
        hCMA
        hMAB

    have hACM : PrimCollinear Geo A C M :=
      PrimCollinearRotate Geo A M C hAMCcol

    have hACB : PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo A C M B
        hMC.symm
        hACM
        hCMB

    exact hABC
      (PrimCollinearRotate Geo A C B hACB)

  ----------------------------------------------------------------------
  -- Vertical angles at M.
  ----------------------------------------------------------------------

  have hVertical :
      Geo.AngleCongruent A M B C M E :=
    hilbert_vertical_angles
      Geo A M B C E
      hAMC
      hBME
      hAMBnc

  ----------------------------------------------------------------------
  -- Triangle CME is also noncollinear.
  ----------------------------------------------------------------------

  have hBMEdata :=
    HilbertOrder.between_incidence B M E hBME

  have hME : M ≠ E :=
    hBMEdata.2.1

  have hBMEcol : PrimCollinear Geo B M E :=
    hBMEdata.2.2.2.1

  have hCME_nc : ¬ PrimCollinear Geo C M E := by
    intro hCME

    have hMEB : PrimCollinear Geo M E B :=
      PrimCollinearCycle Geo B M E hBMEcol

    have hCMB : PrimCollinear Geo C M B :=
      hilbert_primCollinear_trans
        Geo C M E B
        hME
        hCME
        hMEB

    have hMCB : PrimCollinear Geo M C B :=
      PrimCollinearSwap Geo C M B hCMB

    have hAMB : PrimCollinear Geo A M B :=
      hilbert_primCollinear_trans
        Geo A M C B
        hMC
        hAMCcol
        hMCB

    exact hAMBnc hAMB

  ----------------------------------------------------------------------
  -- Put the side congruences in the orientation required by SAS:
  --
  -- MA ≅ MC
  -- MB ≅ ME
  ----------------------------------------------------------------------

  have hMAMC : Geo.Congruent M A M C :=
    (Geo.congruent_reverse_first
      A M M C).mp hAMMC

  have hMBME : Geo.Congruent M B M E :=
    (Geo.congruent_reverse_first
      B M M E).mp hBMME

  ----------------------------------------------------------------------
  -- Reorient noncollinearity for triangles MAB and MCE.
  ----------------------------------------------------------------------

  have hMABnc : ¬ PrimCollinear Geo M A B := by
    intro h
    exact hAMBnc
      (PrimCollinearSwap Geo M A B h)

  have hMCEnc : ¬ PrimCollinear Geo M C E := by
    intro h
    exact hCME_nc
      (PrimCollinearSwap Geo M C E h)

  ----------------------------------------------------------------------
  -- SAS:
  --
  -- triangle MAB ≅ triangle MCE
  --
  -- hence angle MAB ≅ angle MCE.
  ----------------------------------------------------------------------

  have hSAS :=
    hilbert_sas_remaining_angles
      Geo
      M A B
      M C E
      hMABnc
      hMCEnc
      hMAMC
      hMBME
      hVertical

  have hMAB_MCE :
      Geo.AngleCongruent M A B M C E :=
    hSAS.1

  ----------------------------------------------------------------------
  -- Since A-M-C, rays AM and AC are the same.
  -- Therefore angle MAB = angle CAB = angle BAC.
  ----------------------------------------------------------------------

  have hRayAMC : HilbertSameRay Geo A M C :=
    hilbert_sameRay_of_between
      Geo A M C hAMC

  have hMAB_CAB :
      Geo.Angle M A B = Geo.Angle C A B :=
    hilbert_angle_eq_of_sameRay_first
      Geo A M C B hRayAMC

  have hBAC_MAB :
      Geo.Angle B A C = Geo.Angle M A B := by
    calc
      Geo.Angle B A C = Geo.Angle C A B :=
        Geo.angle_swap B A C
      _ = Geo.Angle M A B :=
        hMAB_CAB.symm

  ----------------------------------------------------------------------
  -- Transport the SAS angle equality to BAC.
  ----------------------------------------------------------------------

  have hBAC_MCE :
      Geo.AngleCongruent B A C M C E := by
    unfold Geometry.Geo.AngleCongruent at hMAB_MCE ⊢
    rw [hBAC_MAB]
    exact hMAB_MCE

 --xact ⟨M, E, hAMC, hBME, hBAC_MCE⟩
  exact
  ⟨M, E,
    hAMC,
    hAMMC,
    hBME,
    hBMME,
    hBAC_MCE⟩

theorem hilbert_exterior_angle_meets_AD
    [HilbertCongruence Geo]
    (A B C D E : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hBCD : Geo.Between B C D)
    (hParallel : Geo.Parallel A B C E) :
    ∃ H : Geo.Point,
      Geo.Between A H D ∧
      PrimCollinear Geo C E H := by

  have hBCDdata :=
    HilbertOrder.between_incidence B C D hBCD

  have hBC : B ≠ C :=
    hBCDdata.1

  have hCD : C ≠ D :=
    hBCDdata.2.1

  have hBD : B ≠ D :=
    hBCDdata.2.2.1

  have hBCDcol : PrimCollinear Geo B C D :=
    hBCDdata.2.2.2.1

  have hAB : A ≠ B :=
    hParallel.1

  have hCE : C ≠ E :=
    hParallel.2.1

  ----------------------------------------------------------------------
  -- ABD is a genuine triangle.
  ----------------------------------------------------------------------

  have hBDA : ¬ PrimCollinear Geo B D A := by
    intro hBDAcol

    have hCDB : PrimCollinear Geo C D B :=
      PrimCollinearCycle Geo B C D hBCDcol

    have hDBA : PrimCollinear Geo D B A :=
      PrimCollinearSwap Geo B D A hBDAcol

    have hCDA : PrimCollinear Geo C D A :=
      hilbert_primCollinear_trans
        Geo C D B A
        hBD.symm
        hCDB
        hDBA

    have hBCA : PrimCollinear Geo B C A :=
      hilbert_primCollinear_trans
        Geo B C D A
        hCD
        hBCDcol
        hCDA

    have hCAB : PrimCollinear Geo C A B :=
      PrimCollinearCycle Geo B C A hBCA

    have hABCcol : PrimCollinear Geo A B C :=
      PrimCollinearCycle Geo C A B hCAB

    exact hABC hABCcol

  ----------------------------------------------------------------------
  -- Lines AB and CE.
  ----------------------------------------------------------------------

  rcases HilbertPlaneIncidence.line_through A B hAB with
    ⟨lineAB, hAab, hBab⟩

  rcases HilbertPlaneIncidence.line_through C E hCE with
    ⟨lineCE, hCce, hEce⟩

  ----------------------------------------------------------------------
  -- A and B cannot lie on CE because AB || CE.
  ----------------------------------------------------------------------

  have hAce : ¬ HilbertIncidence.OnLine A lineCE := by
    intro hAce

    have hAinAB : A ∈ Geo.PointLine A B := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo A B A lineAB
          hAB hAab hBab).2 hAab

    have hAinCE : A ∈ Geo.PointLine C E := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo C E A lineCE
          hCE hCce hEce).2 hAce

    exact
      Set.disjoint_left.mp hParallel.2.2
        hAinAB hAinCE

  have hBce : ¬ HilbertIncidence.OnLine B lineCE := by
    intro hBce

    have hBinAB : B ∈ Geo.PointLine A B := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo A B B lineAB
          hAB hAab hBab).2 hBab

    have hBinCE : B ∈ Geo.PointLine C E := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo C E B lineCE
          hCE hCce hEce).2 hBce

    exact
      Set.disjoint_left.mp hParallel.2.2
        hBinAB hBinCE

  ----------------------------------------------------------------------
  -- D is not on CE either.
  ----------------------------------------------------------------------

  have hDce : ¬ HilbertIncidence.OnLine D lineCE := by
    intro hDce

    have hCDB : PrimCollinear Geo C D B :=
      PrimCollinearCycle Geo B C D hBCDcol

    have hBce' : HilbertIncidence.OnLine B lineCE :=
      hilbert_collinear_on_line
        Geo C D B
        lineCE
        hCD
        hCce
        hDce
        hCDB

    exact hBce hBce'

  ----------------------------------------------------------------------
  -- CE meets side BD at C.
  ----------------------------------------------------------------------

  have hMeetsBD :
      HilbertSegmentMeetsLine Geo B D lineCE :=
    ⟨C, hBCD, hCce⟩

  ----------------------------------------------------------------------
  -- Pasch in triangle BDA.
  --
  -- Since CE enters through BD, it must leave through BA or DA.
  ----------------------------------------------------------------------

  rcases HilbertOrder.pasch
      (Geo := Geo)
      B D A
      hBDA
      lineCE
      hBce
      hDce
      hAce
      hMeetsBD with
    hMeetsBA | hMeetsDA

  ----------------------------------------------------------------------
  -- The BA alternative contradicts AB || CE.
  ----------------------------------------------------------------------

  · rcases hMeetsBA with
      ⟨X, hBXA, hXce⟩

    have hXab :
        HilbertIncidence.OnLine X lineAB :=
      hilbert_between_on_line
        Geo B X A
        lineAB
        hBab hAab
        hBXA

    have hXinAB : X ∈ Geo.PointLine A B := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo A B X lineAB
          hAB hAab hBab).2 hXab

    have hXinCE : X ∈ Geo.PointLine C E := by
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo C E X lineCE
          hCE hCce hEce).2 hXce

    exact
      False.elim
        (Set.disjoint_left.mp hParallel.2.2
          hXinAB hXinCE)

  ----------------------------------------------------------------------
  -- Therefore CE meets DA.
  ----------------------------------------------------------------------

  · rcases hMeetsDA with
      ⟨H, hDHA, hHce⟩

    have hAHD : Geo.Between A H D :=
      (HilbertOrder.between_incidence
        D H A hDHA).2.2.2.2

    have hCEH : PrimCollinear Geo C E H :=
      ⟨lineCE, hCce, hEce, hHce⟩

    exact ⟨H, hAHD, hCEH⟩


theorem hilbert_exterior_angle_sameRay
    [HilbertCongruence Geo]
    (A B C D M E H : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hAMC : Geo.Between A M C)
    (hBME : Geo.Between B M E)
    (hBCD : Geo.Between B C D)
    (hAHD : Geo.Between A H D)
    (hCEH : PrimCollinear Geo C E H) :
    HilbertSameRay Geo C E H := by

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (fun h =>
        hABC
          (PrimCollinearRotate Geo A C B h))

  rcases HilbertPlaneIncidence.line_through A C hAC with
    ⟨lineAC, hAac, hCac⟩

  have hMac : HilbertIncidence.OnLine M lineAC :=
    hilbert_between_on_line
      Geo A M C lineAC
      hAac hCac hAMC

  ----------------------------------------------------------------------
  -- Triangle BED is noncollinear.
  ----------------------------------------------------------------------

  have hBED : ¬ PrimCollinear Geo B E D := by
    rintro ⟨l, hBl, hEl, hDl⟩

    have hMl : HilbertIncidence.OnLine M l :=
      hilbert_between_on_line
        Geo B M E l
        hBl hEl hBME

    have hCl : HilbertIncidence.OnLine C l :=
      hilbert_between_on_line
        Geo B C D l
        hBl hDl hBCD

    have hMC : M ≠ C :=
      (HilbertOrder.between_incidence
        A M C hAMC).2.1

    have hAl : HilbertIncidence.OnLine A l :=
      hilbert_collinear_on_line
        Geo M C A l
        hMC
        hMl hCl
        (PrimCollinearCycle Geo A M C
          (HilbertOrder.between_incidence
            A M C hAMC).2.2.2.1)

    exact hABC ⟨l, hAl, hBl, hCl⟩

  ----------------------------------------------------------------------
  -- AC meets BE at M and BD at C.
  -- Hence E and D lie on the same side of AC.
  ----------------------------------------------------------------------

  have hEDsame :
      HilbertSameSide Geo E D lineAC :=
    hilbert_third_side_endpoints_sameSide
      Geo
      B E D
      M C
      lineAC
      hBED
      hBME
      hBCD
      hMac
      hCac

  ----------------------------------------------------------------------
  -- D is off AC.
  ----------------------------------------------------------------------

  have hDac : ¬ HilbertIncidence.OnLine D lineAC := by
    intro hDac

    have hBCDcol :
        PrimCollinear Geo B C D :=
      (HilbertOrder.between_incidence
        B C D hBCD).2.2.2.1

    have hCD : C ≠ D :=
      (HilbertOrder.between_incidence
        B C D hBCD).2.1

    have hBac : HilbertIncidence.OnLine B lineAC :=
      hilbert_collinear_on_line
        Geo C D B lineAC
        hCD
        hCac hDac
        (PrimCollinearCycle Geo B C D hBCDcol)

    exact hABC ⟨lineAC, hAac, hBac, hCac⟩

  ----------------------------------------------------------------------
  -- H and D are on the same side of AC.
  ----------------------------------------------------------------------

  have hAD : A ≠ D :=
    (HilbertOrder.between_incidence
      A H D hAHD).2.2.1

  rcases HilbertPlaneIncidence.line_through A D hAD with
    ⟨lineAD, hAad, hDad⟩

  have hHad : HilbertIncidence.OnLine H lineAD :=
    hilbert_between_on_line
      Geo A H D lineAD
      hAad hDad hAHD

  have hHac : ¬ HilbertIncidence.OnLine H lineAC := by
    intro hHac

    have hAH : A ≠ H :=
      (HilbertOrder.between_incidence
        A H D hAHD).1

    have hEq : lineAD = lineAC :=
      HilbertPlaneIncidence.line_unique
        A H hAH
        lineAD lineAC
        hAad hHad
        hAac hHac

    exact hDac (hEq ▸ hDad)

  have hAHDsame : HilbertSameRay Geo A H D :=
    hilbert_sameRay_of_between
      Geo A H D hAHD

  have hADHsame : HilbertSameRay Geo A D H :=
    hilbert_sameRay_symm
      Geo A H D hAHDsame

  have hADDsame : HilbertSameRay Geo A D D :=
    hilbert_sameRay_refl
      Geo A D hAD.symm

  have hHDsame :
      HilbertSameSide Geo H D lineAC :=
    hilbert_sameRay_points_sameSide
      Geo
      A D H D C
      lineAD lineAC
      hAad hDad
      hAac hCac
      (by
        intro hCad
        have hEq : lineAD = lineAC :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            lineAD lineAC
            hAad hCad
            hAac hCac
        exact hDac (hEq ▸ hDad))
      hADHsame
      hADDsame

  ----------------------------------------------------------------------
  -- E and H are therefore on the same side of AC.
  ----------------------------------------------------------------------

  have hDHsame :
      HilbertSameSide Geo D H lineAC :=
    hilbert_sameSide_symm
      Geo H D lineAC hHDsame

  have hEHsame :
      HilbertSameSide Geo E H lineAC :=
    hilbert_sameSide_trans
      Geo E D H lineAC
      hEDsame
      hDHsame

  ----------------------------------------------------------------------
  -- Build SameRay(C,E,H).
  ----------------------------------------------------------------------

  have hEC : E ≠ C := by
    intro h
    subst E
    exact hEHsame.1 hCac

  have hHC : H ≠ C := by
    intro h
    subst H
    exact hEHsame.2.1 hCac

  refine
    ⟨hEC,
      hHC,
      hCEH,
      ?_⟩

  intro hECH

  have hOpp :
      HilbertOppositeSide Geo E H lineAC :=
    ⟨hEHsame.1,
      hEHsame.2.1,
      ⟨C, hECH, hCac⟩⟩

  exact
    (hilbert_oppositeSide_not_sameSide
      Geo E H lineAC hOpp)
      hEHsame

theorem hilbert_exterior_angle_inside
    [HilbertCongruence Geo]
    (A B C D M E : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hAMC : Geo.Between A M C)
    (hBME : Geo.Between B M E)
    (hBCD : Geo.Between B C D)
    (hParallel : Geo.Parallel A B C E) :
    HilbertRayMeetsSegment Geo C E A D := by

  rcases hilbert_exterior_angle_meets_AD
      Geo A B C D E
      hABC
      hBCD
      hParallel with
    ⟨H, hAHD, hCEH⟩

  have hRay :
      HilbertSameRay Geo C E H :=
    hilbert_exterior_angle_sameRay
      Geo A B C D M E H
      hABC
      hAMC
      hBME
      hBCD
      hAHD
      hCEH

  exact ⟨H, hAHD, hRay⟩

theorem hilbert_exterior_angle_aux_parallel
    [HilbertCongruence Geo]
    (A B C M E : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hAMC : Geo.Between A M C)
    (hBME : Geo.Between B M E)
    (hAngle : Geo.AngleCongruent B A C M C E) :
    Geo.Parallel A B C E := by

  ----------------------------------------------------------------------
  -- The transversal AC.
  ----------------------------------------------------------------------

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (fun h =>
        hABC
          (PrimCollinearRotate Geo A C B h))

  rcases HilbertPlaneIncidence.line_through A C hAC with
    ⟨lineAC, hAac, hCac⟩

  have hMac :
      HilbertIncidence.OnLine M lineAC :=
    hilbert_between_on_line
      Geo A M C lineAC
      hAac hCac hAMC

  ----------------------------------------------------------------------
  -- B is off AC.
  ----------------------------------------------------------------------

  have hBoff :
      ¬ HilbertIncidence.OnLine B lineAC := by
    intro hBac
    exact hABC
      ⟨lineAC, hAac, hBac, hCac⟩

  ----------------------------------------------------------------------
  -- E is off AC.
  ----------------------------------------------------------------------

  have hBMEdata :=
    HilbertOrder.between_incidence B M E hBME

  have hME : M ≠ E :=
    hBMEdata.2.1

  have hEoff :
      ¬ HilbertIncidence.OnLine E lineAC := by
    intro hEac

    have hBac :
        HilbertIncidence.OnLine B lineAC :=
      hilbert_collinear_on_line
        Geo M E B
        lineAC
        hME
        hMac hEac
        (PrimCollinearCycle Geo B M E
          hBMEdata.2.2.2.1)

    exact hBoff hBac

  ----------------------------------------------------------------------
  -- Since B-M-E, B and E lie on opposite sides of AC.
  ----------------------------------------------------------------------

  have hOppBE :
      HilbertOppositeSide Geo B E lineAC :=
    ⟨hBoff,
      hEoff,
      ⟨M, hBME, hMac⟩⟩

  ----------------------------------------------------------------------
  -- Convert angle BAC to angle MAB.
  --
  -- A-M-C means rays AM and AC coincide.
  ----------------------------------------------------------------------

  have hRayAMC :
      HilbertSameRay Geo A M C :=
    hilbert_sameRay_of_between
      Geo A M C hAMC

  have hMAB_BAC :
      Geo.Angle M A B = Geo.Angle B A C := by
    calc
      Geo.Angle M A B = Geo.Angle B A M := by
        exact Geo.angle_swap M A B
      _ = Geo.Angle B A C :=
        hilbert_angle_eq_of_sameRay_second
          Geo A B M C hRayAMC

  have hAlternate :
      Geo.AngleCongruent M A B M C E := by
    unfold Geometry.Geo.AngleCongruent at hAngle ⊢
    rw [hMAB_BAC]
    exact hAngle

  ----------------------------------------------------------------------
  -- Equal alternate angles imply parallel lines.
  -- This is the neutral direction of Hilbert Theorem 30.
  ----------------------------------------------------------------------

  exact
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo A B C M E lineAC
      hAMC
      hAac hCac
      hOppBE
      hAlternate

/--
Full quantitative form of Hilbert's exterior-angle theorem
(Theorem 22), first remote interior angle.

If `A` lies between `B` and `D`, then `CAD` is an exterior
angle of triangle `ABC`.  The theorem states that the remote
interior angle `ACB` is strictly smaller than `CAD`.

The earlier theorem

`hilbert_exterior_angle_not_congruent`

was intentionally proved only in the weaker form needed for the
alternate-angle criterion.  It is retained unchanged.  The present
theorem restores the strict angle comparison required by Euclid I.16.

In the notation of `HilbertAngleLess`, the conclusion is

    angle ACB < angle CAD.
-/
theorem hilbert_exterior_angle_less
    [HilbertCongruence Geo]
    (A B C D M E : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hAMC : Geo.Between A M C)
    (hBME : Geo.Between B M E)
    (hBCD : Geo.Between B C D)
    (hAngle : Geo.AngleCongruent B A C M C E)
    (hParallel : Geo.Parallel A B C E) :
    HilbertAngleLess Geo B A C A C D := by

  ----------------------------------------------------------------------
  -- First angle BAC is nondegenerate in the required orientation.
  ----------------------------------------------------------------------

  have hBACnc : ¬ PrimCollinear Geo B A C := by
    intro h
    exact hABC
      (PrimCollinearSwap Geo B A C h)

  ----------------------------------------------------------------------
  -- Exterior angle ACD is nondegenerate.
  ----------------------------------------------------------------------

  have hBCDdata :=
    HilbertOrder.between_incidence B C D hBCD

  have hCD : C ≠ D :=
    hBCDdata.2.1

  have hBCDcol : PrimCollinear Geo B C D :=
    hBCDdata.2.2.2.1

  have hACDnc : ¬ PrimCollinear Geo A C D := by
    intro hACD

    have hCDB : PrimCollinear Geo C D B :=
      PrimCollinearCycle Geo B C D hBCDcol

    have hACB : PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo A C D B
        hCD
        hACD
        hCDB

    exact hABC
      (PrimCollinearRotate Geo A C B hACB)

  ----------------------------------------------------------------------
  -- Since A-M-C, rays CM and CA coincide.
  -- Hence angle MCE = angle ACE.
  ----------------------------------------------------------------------

  have hCMA : Geo.Between C M A :=
    (HilbertOrder.between_incidence
      A M C hAMC).2.2.2.2

  have hRayCMA : HilbertSameRay Geo C M A :=
    hilbert_sameRay_of_between
      Geo C M A hCMA

  have hMCE_ACE :
      Geo.Angle M C E = Geo.Angle A C E :=
    hilbert_angle_eq_of_sameRay_first
      Geo C M A E hRayCMA

  have hBAC_ACE :
      Geo.AngleCongruent B A C A C E := by
    unfold Geometry.Geo.AngleCongruent at hAngle ⊢
    rw [← hMCE_ACE]
    exact hAngle

  ----------------------------------------------------------------------
  -- Ray CE meets the open segment AD.
  ----------------------------------------------------------------------

  have hInside :
      HilbertRayMeetsSegment Geo C E A D :=
    hilbert_exterior_angle_inside
      Geo A B C D M E
      hABC
      hAMC
      hBME
      hBCD
      hParallel

  ----------------------------------------------------------------------
  -- Definition of HilbertAngleLess.
  -- Witness X = E.
  ----------------------------------------------------------------------

  exact
    ⟨hBACnc,
      hACDnc,
      ⟨E,
        hInside,
        hBAC_ACE⟩⟩

theorem hilbert_angleLess_transport_right
    [HilbertCongruence Geo]
    (A O B C P D C' P' D' : Geo.Point)
    (hLess :
      HilbertAngleLess Geo A O B C P D)
    (hTarget :
      ¬ PrimCollinear Geo C' P' D')
    (hWhole :
      Geo.AngleCongruent C P D C' P' D') :
    HilbertAngleLess Geo A O B C' P' D' := by

  rcases hLess with
    ⟨hAOB, hCPD, X, hInside, hAngle⟩

  ----------------------------------------------------------------------
  -- Reverse the source and target whole angles.
  ----------------------------------------------------------------------

  have hWholeRev :
      Geo.AngleCongruent D P C D' P' C' :=
    (Geo.angle_congruent_reverse_second
      D P C C' P' D').mp
      ((Geo.angle_congruent_reverse_first
        C P D C' P' D').mp hWhole)

  ----------------------------------------------------------------------
  -- Reverse the open segment CD.
  ----------------------------------------------------------------------

  rcases hInside with
    ⟨H, hCHD, hRayPXH⟩

  have hDHC :
      Geo.Between D H C :=
    (HilbertOrder.between_incidence
      C H D hCHD).2.2.2.2

  have hInsideRev :
      HilbertRayMeetsSegment Geo P X D C :=
    ⟨H, hDHC, hRayPXH⟩

  ----------------------------------------------------------------------
  -- Transport the interior ray to the congruent target angle.
  ----------------------------------------------------------------------

  rcases
      hilbert_interior_subangle_transport
        Geo
        P D C X
        D' P' C'
        (by
          intro h
          exact hCPD
            (PrimCollinearSymm Geo D P C h))
        (by
          intro h
          exact hTarget
            (PrimCollinearSymm Geo D' P' C' h))
        hInsideRev
        hWholeRev with
    ⟨Y, hInsideTargetRev, hSubAngle⟩

  ----------------------------------------------------------------------
  -- Reverse target segment D'C'.
  ----------------------------------------------------------------------

  rcases hInsideTargetRev with
    ⟨K, hD'KC', hRayP'YK⟩

  have hC'KD' :
      Geo.Between C' K D' :=
    (HilbertOrder.between_incidence
      D' K C' hD'KC').2.2.2.2

  have hInsideTarget :
      HilbertRayMeetsSegment Geo P' Y C' D' :=
    ⟨K, hC'KD', hRayP'YK⟩

  ----------------------------------------------------------------------
  -- The transported subangle already has the required orientation.
  ----------------------------------------------------------------------

  have hSubAngle' :
      Geo.AngleCongruent C P X C' P' Y :=
    hSubAngle

  ----------------------------------------------------------------------
  -- Compose with the original witness angle.
  ----------------------------------------------------------------------

  have hFinal :
      Geo.AngleCongruent A O B C' P' Y :=
    Geo.angle_congruent_transitivity
      A O B
      C P X
      C' P' Y
      hAngle
      hSubAngle'

  ----------------------------------------------------------------------
  -- Definition of HilbertAngleLess.
  ----------------------------------------------------------------------

  exact
    ⟨hAOB,
      hTarget,
      ⟨Y,
        hInsideTarget,
        hFinal⟩⟩


/--
An interior ray determines a proper subangle of the whole angle.

If ray OD meets the open segment XC, then angle XOD is strictly
smaller than angle XOC.
-/
theorem hilbert_interior_angle_less
    [HilbertCongruence Geo]
    (O D X C : Geo.Point)
    (hXOC : ¬ PrimCollinear Geo X O C)
    (hInside : HilbertRayMeetsSegment Geo O D X C) :
    HilbertAngleLess Geo X O D X O C := by

  rcases hInside with
    ⟨H, hXHC, hRayODH⟩

  have hXOD :
      ¬ PrimCollinear Geo X O D := by
    intro hCol

    rcases hCol with
      ⟨lineXOD, hXline, hOline, hDline⟩

    rcases hRayODH.2.2.1 with
      ⟨lineODH, hOline', hDline', hHline'⟩

    have hOD : O ≠ D :=
      hRayODH.1.symm

    have hLines :
        lineXOD = lineODH :=
      HilbertPlaneIncidence.line_unique
        O D hOD
        lineXOD lineODH
        hOline hDline
        hOline' hDline'

    have hHline :
        HilbertIncidence.OnLine H lineXOD := by
      rw [hLines]
      exact hHline'

    have hXH : X ≠ H :=
      (HilbertOrder.between_incidence
        X H C hXHC).1

    have hXHCcol :
        PrimCollinear Geo X H C :=
      (HilbertOrder.between_incidence
        X H C hXHC).2.2.2.1

    have hCline :
        HilbertIncidence.OnLine C lineXOD :=
      hilbert_collinear_on_line
        Geo
        X H C
        lineXOD
        hXH
        hXline
        hHline
        hXHCcol

    exact hXOC
      ⟨lineXOD, hXline, hOline, hCline⟩

  have hRefl :
      Geo.AngleCongruent X O D X O D :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      X O D hXOD

  exact
    hilbert_angleLess_intro
      Geo
      X O D
      X O C
      D
      hXOD
      hXOC
      ⟨H, hXHC, hRayODH⟩
      hRefl

/--
Strict angle comparison is transitive.
-/
theorem hilbert_angleLess_trans
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (h₁ :
      HilbertAngleLess Geo A O B C P D)
    (h₂ :
      HilbertAngleLess Geo C P D E Q F) :
    HilbertAngleLess Geo A O B E Q F := by

  rcases h₂ with
    ⟨hCPD, hEQF, Y, hInsideY, hCPD_EQY⟩

  ----------------------------------------------------------------------
  -- Since QY is an interior ray of angle EQF,
  -- the subangle EQY is nondegenerate.
  ----------------------------------------------------------------------

  have hEQYLess :
      HilbertAngleLess Geo E Q Y E Q F :=
    hilbert_interior_angle_less
      Geo Q Y E F hEQF hInsideY

  have hEQY :
      ¬ PrimCollinear Geo E Q Y :=
    hEQYLess.1

  ----------------------------------------------------------------------
  -- Transport h₁ from the whole angle CPD to the congruent
  -- interior angle EQY.
  ----------------------------------------------------------------------

  have h₁' :
      HilbertAngleLess Geo A O B E Q Y :=
    hilbert_angleLess_transport_right
      Geo
      A O B
      C P D
      E Q Y
      h₁
      hEQY
      hCPD_EQY

  rcases h₁' with
    ⟨hAOB, hEQY', Z, hInsideZ, hAngle⟩

  ----------------------------------------------------------------------
  -- The ray QY meets EF at H.
  ----------------------------------------------------------------------

  rcases hInsideY with
    ⟨H, hEHF, hRayQYH⟩

  ----------------------------------------------------------------------
  -- E,Q,H is noncollinear because H lies on the same ray as Y.
  ----------------------------------------------------------------------

  have hEQH :
      ¬ PrimCollinear Geo E Q H := by
    intro hCol

    have hQH : Q ≠ H :=
      hRayQYH.2.1.symm

    have hQHY :
        PrimCollinear Geo Q H Y := by
      rcases hRayQYH.2.2.1 with
        ⟨l, hQl, hYl, hHl⟩
      exact ⟨l, hQl, hHl, hYl⟩

    have hEQYcol :
        PrimCollinear Geo E Q Y :=
      hilbert_primCollinear_trans
        Geo
        E Q H Y
        hQH
        hCol
        hQHY

    exact hEQY hEQYcol

  ----------------------------------------------------------------------
  -- Move the second endpoint of segment EY from Y to H.
  -- Since Y and H lie on the same ray from Q, ray QZ still
  -- meets the corresponding segment EH.
  ----------------------------------------------------------------------

  have hEQ : E ≠ Q :=
    hilbert_noncollinear_ne_first
      Geo E Q F hEQF

  have hRayQEE :
      HilbertSameRay Geo Q E E :=
    hilbert_sameRay_refl
      Geo Q E hEQ

  have hInsideEH :
      HilbertRayMeetsSegment Geo Q Z E H :=
    hilbert_ray_meets_segment_sameRays
      Geo
      Q Z
      E Y
      E H
      hInsideZ
      hRayQEE
      hRayQYH
      hEQY'
      hEQH

  ----------------------------------------------------------------------
  -- If K lies between E and H, and H lies between E and F,
  -- then K lies between E and F.
  ----------------------------------------------------------------------

  rcases hInsideEH with
    ⟨K, hEKH, hRayQZK⟩

  have hEKF :
      Geo.Between E K F :=
    (hilbert_between_inner_trans
      Geo E K H F hEKH hEHF).2

  have hInsideFinal :
      HilbertRayMeetsSegment Geo Q Z E F :=
    ⟨K, hEKF, hRayQZK⟩

  ----------------------------------------------------------------------
  -- The same witness angle now lies inside the whole angle EQF.
  ----------------------------------------------------------------------

  exact
    hilbert_angleLess_intro
      Geo
      A O B
      E Q F
      Z
      hAOB
      hEQF
      hInsideFinal
      hAngle

theorem hilbert_segment_trichotomy
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hCD : C ≠ D) :
    Geo.Congruent A B C D ∨
    HilbertSegmentLess Geo A B C D ∨
    HilbertSegmentLess Geo C D A B := by

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        A B
        C D
        hCD with
    ⟨X, hRayCDX, hCX_AB⟩

  have hCX : C ≠ X :=
    hRayCDX.2.1.symm

  have hCDX :
      Collinear Geo C D X :=
    hRayCDX.2.2.1

  by_cases hDX : D = X

  · subst X

    left

    exact
      hilbert_congruent_symmetry
        Geo C D A B hCX_AB

  · rcases
        hilbert_between_trichotomy
          Geo C D X
          hCD
          hDX
          hCX
          hCDX with
      hCDXbetween | hDCX | hCXD

    ·
      -- C-D-X, so CD < CX, and CX ≅ AB.
      right
      right

      have hCD_CX :
          HilbertSegmentLess Geo C D C X :=
        hilbert_segmentLess_of_between
          Geo C D X hCDXbetween

      exact
        hilbert_segmentLess_congruent_right
          Geo
          C D
          C X
          A B
          hCD_CX
          hCX_AB

    ·
      -- D-C-X contradicts X lying on ray CD.
      exfalso
      exact hRayCDX.2.2.2 hDCX

    ·
      -- C-X-D, so CX < CD, and AB ≅ CX.
      right
      left

      have hCX_CD :
          HilbertSegmentLess Geo C X C D :=
        hilbert_segmentLess_of_between
          Geo C X D hCXD

      have hAB_CX :
          Geo.Congruent A B C X :=
        hilbert_congruent_symmetry
          Geo C X A B hCX_AB

      exact
        hilbert_segmentLess_congruent_left
          Geo
          C X
          A B
          C D
          hCX_CD
          hAB_CX

theorem hilbert_angleLess_irrefl
    [HilbertCongruence Geo]
    (A O B : Geo.Point) :
    ¬ HilbertAngleLess Geo A O B A O B := by

  intro hLess

  rcases hLess with
    ⟨hAOB, _, X, hInside, hAngle⟩

  rcases hInside with
    ⟨H, hAHB, hRayOXH⟩

  have hBHA :
      Geo.Between B H A :=
    (HilbertOrder.between_incidence
      A H B hAHB).2.2.2.2

  have hInsideRev :
      HilbertRayMeetsSegment Geo O X B A :=
    ⟨H, hBHA, hRayOXH⟩

  have hBOA :
      ¬ PrimCollinear Geo B O A := by
    intro h
    exact hAOB
      (PrimCollinearSymm Geo B O A h)

  have hNot :
      ¬ Geo.AngleCongruent A O X B O A :=
    hilbert_interior_subangle_not_congruent_whole
      Geo
      O X
      B A
      hBOA
      hInsideRev

  have hSubWhole :
      Geo.AngleCongruent A O X B O A :=
    (Geo.angle_congruent_reverse_second
      A O X
      A O B).mp
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        A O B
        A O X
        hAngle)

  exact hNot hSubWhole

theorem hilbert_angleLess_transport_left
    [HilbertCongruence Geo]
    (A O B A' O' B' C P D : Geo.Point)
    (hLess :
      HilbertAngleLess Geo A O B C P D)
    (hSource :
      ¬ PrimCollinear Geo A' O' B')
    (hCong :
      Geo.AngleCongruent A' O' B' A O B) :
    HilbertAngleLess Geo A' O' B' C P D := by

  rcases hLess with
    ⟨hAOB, hCPD, X, hInside, hAngle⟩

  have hAngle' :
      Geo.AngleCongruent A' O' B' C P X :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A' O' B'
      A O B
      C P X
      hCong
      hAngle

  exact
    ⟨hSource,
      hCPD,
      X,
      hInside,
      hAngle'⟩

/-
General circle-circle continuity.

The circle with center `O2` and radius `O2R2` contains two points
`X` and `Y`.  The point `X` is inside the circle with center `O1`
and radius `O1R1`, while `Y` is outside it.  Then the two circles
have a common point.
-/
omit [HilbertIncidence Geo] in
axiom hilbert_circle_circle_intersection
    [HilbertCongruence Geo]
    (O1 R1 O2 R2 X Y : Geo.Point)
    (hO1R1 : O1 ≠ R1)
    (hO2R2 : O2 ≠ R2)
    (hXon2 : Geo.Congruent O2 X O2 R2)
    (hYon2 : Geo.Congruent O2 Y O2 R2)
    (hXinside1 :
      X = O1 ∨
      HilbertSegmentLess Geo O1 X O1 R1)
    (hYoutside1 :
      HilbertSegmentLess Geo O1 R1 O1 Y) :
    ∃ P : Geo.Point,
      Geo.Congruent O1 P O1 R1 ∧
      Geo.Congruent O2 P O2 R2

/-
Existence principle for Euclid Book I, Proposition 1,
derived from general circle-circle continuity.

For every nondegenerate segment `AB` there exists a point `C`
equidistant from both endpoints:

* `AC ≅ AB`
* `BC ≅ AB`

The noncollinearity of `A`, `B`, and `C` is proved separately
in `euclid_proposition_1`.
-/
omit [HilbertIncidence Geo] in
theorem hilbert_equidistant_point_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ C : Geo.Point,
      Geo.Congruent A C A B ∧
      Geo.Congruent B C A B := by

  rcases
      HilbertOrder.between_extension
        A B hAB with
    ⟨R, hABR⟩

  have hBR : B ≠ R :=
    (HilbertOrder.between_incidence
      A B R hABR).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        B A
        B R
        hBR with
    ⟨Y, hRayBRY, hBY_BA⟩

  have hRayBAA :
      HilbertSameRay Geo B A A :=
    hilbert_sameRay_refl
      Geo B A hAB

  have hABY :
      Geo.Between A B Y :=
    hilbert_between_transport_sameRays
      Geo
      A B R
      A Y
      hABR
      hRayBAA
      hRayBRY

  have hAon2 :
      Geo.Congruent B A B A :=
    hilbert_congruent_reflexive
      Geo B A

  have hYon2 :
      Geo.Congruent B Y B A :=
    hBY_BA

  have hAinside1 :
      A = A ∨
      HilbertSegmentLess Geo A A A B := by
    left
    rfl

  have hYoutside1 :
      HilbertSegmentLess Geo A B A Y := by
    exact
      ⟨B,
       hABY,
       hilbert_congruent_reflexive Geo A B⟩

  rcases
      hilbert_circle_circle_intersection
        Geo
        A B
        B A
        A Y
        hAB
        hAB.symm
        hAon2
        hYon2
        hAinside1
        hYoutside1 with
    ⟨C, hAC_AB, hBC_BA⟩

  have hBC_AB :
      Geo.Congruent B C A B :=
    (Geometry.Geo.congruent_reverse_second
      Geo B C B A).mp hBC_BA

  exact
    ⟨C, hAC_AB, hBC_AB⟩

/--
The sum of two segments AB and CD is strictly greater than EF.

The point P realizes the sum on the ray from A through B:
A-B-P and BP ~= CD, so AP represents AB + CD.
The final condition says EF < AP.
-/
def HilbertSegmentSumGreater
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point) : Prop :=
  ∃ P : Geo.Point,
    Geo.Between A B P ∧
    Geo.Congruent B P C D ∧
    HilbertSegmentLess Geo E F A P

end Geometry

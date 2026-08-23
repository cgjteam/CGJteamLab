import CGJteamLab.HilbertGrundlagen

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

variable [HilbertIncidence Geo]

/-!
# HilbertInterface

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

/-
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
theorem hilbert_interior_subangle_transport_both
    [HilbertCongruence Geo]
    (O X C D A' O' B' : Geo.Point)
    (hXOC : ¬ PrimCollinear Geo X O C)
    (hAOB : ¬ PrimCollinear Geo A' O' B')
    (hInside : HilbertRayMeetsSegment Geo O D X C)
    (hWhole :
      Geo.AngleCongruent X O C A' O' B') :
    ∃ D' : Geo.Point,
      HilbertRayMeetsSegment Geo O' D' A' B' ∧
      (
        Geo.AngleCongruent C O D B' O' D' ∧
        Geo.AngleCongruent X O D A' O' D'
      ) := by

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

  have hRight :
      Geo.AngleCongruent
        C O D
        B' O' H' := by
    unfold Geometry.Geo.AngleCongruent at hSub₀ ⊢
    rw [hAngleCOD]
    exact hSub₀

  --------------------------------------------------------------------
  -- The other component was already obtained by the small SAS.
  --------------------------------------------------------------------

  have hLeft₀ :
      Geo.AngleCongruent
        X₀ O H₀
        A' O' H' :=
    hSmall.angleB

  have hAngleX :
      Geo.Angle X O H₀ =
      Geo.Angle X₀ O H₀ :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      O X X₀ H₀
      hRayX₀

  have hAngleDLeft :
      Geo.Angle X O D =
      Geo.Angle X O H₀ :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      O X D H₀
      hRayODH₀

  have hAngleXOD :
      Geo.Angle X O D =
      Geo.Angle X₀ O H₀ := by
    calc
      Geo.Angle X O D
          = Geo.Angle X O H₀ :=
        hAngleDLeft
      _ = Geo.Angle X₀ O H₀ :=
        hAngleX

  have hLeft :
      Geo.AngleCongruent
        X O D
        A' O' H' := by
    unfold Geometry.Geo.AngleCongruent
      at hLeft₀ ⊢
    rw [hAngleXOD]
    exact hLeft₀

  exact
    ⟨hRight, hLeft⟩

theorem hilbert_interior_subangle_transport
    [HilbertCongruence Geo]
    (O X C D A' O' B' : Geo.Point)
    (hXOC : ¬ PrimCollinear Geo X O C)
    (hAOB : ¬ PrimCollinear Geo A' O' B')
    (hInside :
      HilbertRayMeetsSegment Geo O D X C)
    (hWhole :
      Geo.AngleCongruent X O C A' O' B') :
    ∃ D' : Geo.Point,
      HilbertRayMeetsSegment Geo O' D' A' B' ∧
      Geo.AngleCongruent C O D B' O' D' := by

  rcases
      hilbert_interior_subangle_transport_both
        Geo
        O X C D
        A' O' B'
        hXOC
        hAOB
        hInside
        hWhole
    with
    ⟨D', hInside', hBoth⟩

  exact
    ⟨D',
      hInside',
      hBoth.1⟩


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



theorem angle_trichotomy
    [HilbertCongruence Geo]
    (A O B C P D : Geo.Point)
    (hAOB : ¬ PrimCollinear Geo A O B)
    (hCPD : ¬ PrimCollinear Geo C P D) :
    Geo.AngleCongruent A O B C P D ∨
    HilbertAngleLess Geo A O B C P D ∨
    HilbertAngleLess Geo C P D A O B := by

  --------------------------------------------------------------------
  -- Base line OA.
  --------------------------------------------------------------------

  have hAO : A ≠ O :=
    hilbert_noncollinear_ne_first
      Geo A O B hAOB

  rcases
      HilbertPlaneIncidence.line_through
        O A hAO.symm with
    ⟨base, hObase, hAbase⟩

  have hBoff :
      ¬ HilbertIncidence.OnLine B base := by
    intro hBbase
    apply hAOB
    exact
      PrimCollinear.mk
        (Geo := Geo)
        hAbase hObase hBbase

  --------------------------------------------------------------------
  -- Copy angle CPD at O, with OA as first ray,
  -- on the side of OA containing B.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        C P D
        A O B
        hCPD
        hAO
        base
        hAbase hObase hBoff with
    ⟨X, hXBSame, hAngleX, _hUnique⟩

  -- angle CPD is congruent to angle AOX
  --
  -- hAngleX :
  --   AngleCongruent C P D A O X

  have hBXSame :
      HilbertSameSide Geo B X base :=
    hilbert_sameSide_symm
      Geo X B base hXBSame

  have hXoff :
      ¬ HilbertIncidence.OnLine X base :=
    hBXSame.2.1

  have hAOX :
      ¬ PrimCollinear Geo A O X :=
    hilbert_not_collinear_of_off_line
      Geo
      A O X
      base
      hAO
      hAbase hObase hXoff

  --------------------------------------------------------------------
  -- Compare the two second rays OB and OX.
  --------------------------------------------------------------------

  by_cases hBOX :
      PrimCollinear Geo B O X

  ·
    ------------------------------------------------------------------
    -- Collinear case:
    -- B and X lie on the same side of OA, hence on the same ray.
    ------------------------------------------------------------------

    have hRayBX :
        HilbertSameRay Geo O B X :=
      sameRay_of_collinear_sameSide
        (Geo := Geo)
        (O := O)
        (B := B)
        (X := X)
        (base := base)
        hObase
        hBoff
        hXoff
        hBXSame
        hBOX

    have hAngleEq :
        Geo.Angle A O B =
        Geo.Angle A O X :=
      hilbert_angle_eq_of_sameRay_second
        Geo O A B X hRayBX


    have hAOB_AOX :
        Geo.AngleCongruent A O B A O X := by
      unfold Geometry.Geo.AngleCongruent
      rw [hAngleEq]

      exact
        HilbertCongruence.angle_congruence_reflexive
          (Geo := Geo)
          A O X
          hAOX

    have hAOX_CPD :
        Geo.AngleCongruent A O X C P D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        C P D
        A O X
        hAngleX

    have hAOB_CPD :
        Geo.AngleCongruent A O B C P D :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        A O B
        A O X
        C P D
        hAOB_AOX
        hAOX_CPD

    exact Or.inl hAOB_CPD

  ·
    ------------------------------------------------------------------
    -- Noncollinear case:
    -- compare rays OB and OX in the same half-plane bounded by OA.
    ------------------------------------------------------------------

    have hOA : O ≠ A :=
      hAO.symm

    rcases
        hilbert_sameSide_rays_order
          Geo
          O B A X
          base
          hOA
          hObase
          hAbase
          hBoff
          hXoff
          hBXSame
          hBOX with
      hRayBInside | hRayXInside

    ·
      ----------------------------------------------------------------
      -- ray OB meets segment XA:
      -- angle AOB < angle AOX.
      ----------------------------------------------------------------

      rcases hRayBInside with
        ⟨H, hXHA, hRayOBH⟩

      have hAHX :
          Geo.Between A H X :=
        (HilbertOrder.between_incidence
          X H A hXHA).2.2.2.2

      have hInside :
          HilbertRayMeetsSegment Geo O B A X :=
        ⟨H, hAHX, hRayOBH⟩

      have hAOB_AOX :
          HilbertAngleLess Geo A O B A O X :=
        hilbert_angleLess_intro
          Geo
          A O B
          A O X
          B
          hAOB
          hAOX
          hInside
          (HilbertCongruence.angle_congruence_reflexive
            (Geo := Geo)
            A O B
            hAOB)

      have hAOX_CPD :
          Geo.AngleCongruent A O X C P D :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          C P D
          A O X
          hAngleX

      have hAOB_CPD :
          HilbertAngleLess Geo A O B C P D :=
        hilbert_angleLess_transport_right
          Geo
          A O B
          A O X
          C P D
          hAOB_AOX
          hCPD
          hAOX_CPD

      exact Or.inr (Or.inl hAOB_CPD)

    ·
      ----------------------------------------------------------------
      -- ray OX meets segment BA:
      -- angle AOX < angle AOB.
      ----------------------------------------------------------------

      rcases hRayXInside with
        ⟨H, hBHA, hRayOXH⟩

      have hAHB :
          Geo.Between A H B :=
        (HilbertOrder.between_incidence
          B H A hBHA).2.2.2.2

      have hInside :
          HilbertRayMeetsSegment Geo O X A B :=
        ⟨H, hAHB, hRayOXH⟩

      have hAOX_AOB :
          HilbertAngleLess Geo A O X A O B :=
        hilbert_angleLess_intro
          Geo
          A O X
          A O B
          X
          hAOX
          hAOB
          hInside
          (HilbertCongruence.angle_congruence_reflexive
            (Geo := Geo)
            A O X
            hAOX)

      have hCPD_AOB :
          HilbertAngleLess Geo C P D A O B :=
        hilbert_angleLess_transport_left
          Geo
          A O X
          C P D
          A O B
          hAOX_AOB
          hCPD
          hAngleX

      exact Or.inr (Or.inr hCPD_AOB)

def HilbertAnglesEqualTwoRightAnglesWithSupplement
    [HilbertOrder Geo]
    (A O B C P D E : Geo.Point) : Prop :=
  Geo.Between D P E /\
  Geo.AngleCongruent A O B C P E

theorem hilbert_parallel_transitive_distinct
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hAB_EF : Geo.Parallel A B E F)
    (hCD_EF : Geo.Parallel C D E F)
    (hDistinct :
      Geo.PointLine A B ≠ Geo.PointLine C D) :
    Geo.Parallel A B C D := by

  have hAB : A ≠ B :=
    hAB_EF.1

  have hCD : C ≠ D :=
    hCD_EF.1

  have hEF : E ≠ F :=
    hAB_EF.2.1

  rcases HilbertPlaneIncidence.line_through A B hAB with
    ⟨lineAB, hAab, hBab⟩

  rcases HilbertPlaneIncidence.line_through C D hCD with
    ⟨lineCD, hCcd, hDcd⟩

  rcases HilbertPlaneIncidence.line_through E F hEF with
    ⟨lineEF, hEef, hFef⟩

  have hLinesAB_EF :
      HilbertLinesDisjoint Geo lineAB lineEF := by
    rintro ⟨P, hPab, hPef⟩

    have hPAB :
        P ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B P lineAB
        hAB hAab hBab).mpr hPab

    have hPEF :
        P ∈ Geo.PointLine E F :=
      (hilbert_mem_pointLine_iff_onLine
        Geo E F P lineEF
        hEF hEef hFef).mpr hPef

    exact
      Set.disjoint_left.mp hAB_EF.2.2
        hPAB hPEF

  have hLinesCD_EF :
      HilbertLinesDisjoint Geo lineCD lineEF := by
    rintro ⟨P, hPcd, hPef⟩

    have hPCD :
        P ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D P lineCD
        hCD hCcd hDcd).mpr hPcd

    have hPEF :
        P ∈ Geo.PointLine E F :=
      (hilbert_mem_pointLine_iff_onLine
        Geo E F P lineEF
        hEF hEef hFef).mpr hPef

    exact
      Set.disjoint_left.mp hCD_EF.2.2
        hPCD hPEF

  refine ⟨hAB, hCD, ?_⟩

  apply Set.disjoint_left.mpr
  intro P hPAB hPCD

  have hPab :
      HilbertIncidence.OnLine P lineAB :=
    (hilbert_mem_pointLine_iff_onLine
      Geo A B P lineAB
      hAB hAab hBab).mp hPAB

  have hPcd :
      HilbertIncidence.OnLine P lineCD :=
    (hilbert_mem_pointLine_iff_onLine
      Geo C D P lineCD
      hCD hCcd hDcd).mp hPCD

  have hPef :
      ¬ HilbertIncidence.OnLine P lineEF := by
    intro hPef

    exact
      hLinesAB_EF ⟨P, hPab, hPef⟩

  have hLineEq :
      lineAB = lineCD :=
    HilbertEuclideanPlane.parallel_unique
      (Geo := Geo)
      lineEF P hPef
      lineAB lineCD
      hPab hLinesAB_EF
      hPcd hLinesCD_EF

  have hC_ab :
      HilbertIncidence.OnLine C lineAB := by
    rw [hLineEq]
    exact hCcd

  have hD_ab :
      HilbertIncidence.OnLine D lineAB := by
    rw [hLineEq]
    exact hDcd

  have hPointLineEq :
      Geo.PointLine A B = Geo.PointLine C D :=
    hilbert_pointLine_eq_of_points_on_line
      Geo
      A B C D
      lineAB
      hAB hCD
      hAab hBab
      hC_ab hD_ab

  exact hDistinct hPointLineEq

theorem hilbert_parallel_through_point_exists
    [HilbertCongruence Geo]
    (A B P : Geo.Point)
    (hAB : A ≠ B)
    (hABP : ¬ Collinear Geo A B P) :
    ∃ Q : Geo.Point,
      P ≠ Q ∧
      Geo.Parallel A B P Q := by

  -- The given line AB.
  rcases HilbertPlaneIncidence.line_through A B hAB with
    ⟨base, hAbase, hBbase⟩

  have hPbase :
      ¬ HilbertIncidence.OnLine P base := by
    intro hPbase
    exact hABP
      ⟨base, hAbase, hBbase, hPbase⟩

  have hAP : A ≠ P := by
    intro h
    subst P
    exact hPbase hAbase

  -- AP will be the transversal.
  rcases HilbertPlaneIncidence.line_through A P hAP with
    ⟨trans, hAtrans, hPtrans⟩

  have hBtrans :
      ¬ HilbertIncidence.OnLine B trans := by
    intro hBtrans
    exact hABP
      ⟨trans, hAtrans, hBtrans, hPtrans⟩

  -- Choose an interior point E of AP.
  rcases hilbert_between_exists Geo A P hAP with
    ⟨E, hAEP⟩

  have hAEPData :=
    HilbertOrder.between_incidence A E P hAEP

  have hEA : E ≠ A :=
    hAEPData.1.symm

  have hEP : E ≠ P :=
    hAEPData.2.1

  have hEtrans :
      HilbertIncidence.OnLine E trans :=
    hilbert_between_on_line
      Geo A E P trans
      hAtrans hPtrans hAEP

  -- EAB is a genuine angle because B is outside AP.
  have hEAB :
      ¬ Collinear Geo E A B :=
    hilbert_not_collinear_of_off_line
      Geo E A B trans
      hEA
      hEtrans
      hAtrans
      hBtrans

  -- Select a point S on the opposite side of AP from B.
  rcases HilbertOrder.between_extension B A hAB.symm with
    ⟨S, hBAS⟩

  have hBASData :=
    HilbertOrder.between_incidence B A S hBAS

  have hSA : S ≠ A :=
    hBASData.2.1.symm

  have hStrans :
      ¬ HilbertIncidence.OnLine S trans := by
    intro hStrans

    have hSAB :
        Collinear Geo S A B :=
      PrimCollinearSymm Geo B A S
        hBASData.2.2.2.1

    have hBtrans' :
        HilbertIncidence.OnLine B trans :=
      hilbert_collinear_on_line
        Geo S A B trans
        hSA
        hStrans
        hAtrans
        hSAB

    exact hBtrans hBtrans'

  have hOppositeBS :
      HilbertOppositeSide Geo B S trans :=
    ⟨hBtrans, hStrans,
      ⟨A, hBAS, hAtrans⟩⟩

  -- Copy angle EAB at P, with PE as the first ray,
  -- on the side opposite B.
  rcases HilbertCongruence.angle_construction
      (Geo := Geo)
      E A B
      E P S
      hEAB
      hEP
      trans
      hEtrans
      hPtrans
      hStrans with
    ⟨Q, hQSSame, hAngle, _⟩

  have hSQSame :
      HilbertSameSide Geo S Q trans :=
    hilbert_sameSide_symm
      Geo Q S trans hQSSame

  have hOppositeBQ :
      HilbertOppositeSide Geo B Q trans :=
    hilbert_oppositeSide_transport_right
      Geo B S Q trans
      hOppositeBS
      hSQSame

  have hPQ : P ≠ Q := by
    intro h
    subst Q
    exact hOppositeBQ.2.1 hPtrans

  -- EAB and EPQ are alternate angles.
  have hParallel :
      Geo.Parallel A B P Q :=
    hilbert_parallel_of_alternate_angles_oppositeSide_lines
      Geo
      A B
      P E Q
      trans
      hAEP
      hAtrans
      hPtrans
      hOppositeBQ
      hAngle

  exact ⟨Q, hPQ, hParallel⟩

/--
Opposite angles of a Euclidean parallelogram are congruent.

For the parallelogram `ABCD`, the triangles `ABC` and `CDA`
have three corresponding congruent sides:

  AB ~= CD,
  BC ~= DA,
  AC ~= CA.

Hence SSS gives the congruence of the opposite angles at `B` and `D`.
-/
theorem ParallelogramOppositeAngleCongruent
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D) :
    Geo.AngleCongruent A B C C D A := by

  have hParallel :
      Geo.Parallel A B C D :=
    hParallelogram.1

  have hAB : A ≠ B :=
    hParallel.1

  have hCD : C ≠ D :=
    hParallel.2.1

  ------------------------------------------------------------
  -- ABC is a genuine triangle.
  ------------------------------------------------------------

  have hABC :
      ¬ Collinear Geo A B C := by
    intro hCol

    rcases hCol with
      ⟨lineAB, hAab, hBab, hCab⟩

    rcases HilbertPlaneIncidence.line_through
        C D hCD with
      ⟨lineCD, hCcd, hDcd⟩

    have hC_AB :
        C ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B C lineAB
        hAB hAab hBab).mpr hCab

    have hC_CD :
        C ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D C lineCD
        hCD hCcd hDcd).mpr hCcd

    exact
      Set.disjoint_left.mp hParallel.2.2
        hC_AB hC_CD

  ------------------------------------------------------------
  -- Opposite sides are congruent.
  ------------------------------------------------------------

  have hSides :
      OppositeSidesCongruent Geo A B C D :=
    ParallelogramOppositeSidesCongruent
      Geo A B C D hParallelogram

  have hAB_CD :
      Geo.Congruent A B C D :=
    hSides.1

  have hBC_DA :
      Geo.Congruent B C D A :=
    hSides.2

  ------------------------------------------------------------
  -- The diagonal AC is common to the two triangles.
  ------------------------------------------------------------

  have hAC_CA :
      Geo.Congruent A C C A :=
    CongruentSwapSecond
      Geo A C A C
      (hilbert_congruent_reflexive Geo A C)

  ------------------------------------------------------------
  -- SSS for ABC and CDA.
  ------------------------------------------------------------

  have hSSS :=
    HilbertSSS
      Geo
      A B C
      C D A
      hABC
      hAB_CD
      hBC_DA
      hAC_CA

  exact hSSS.2.angleB

def OppositeAnglesCongruent
    (A B C D : Geo.Point) : Prop :=
  Geo.AngleCongruent D A B B C D ∧
  Geo.AngleCongruent A B C C D A


/--
Both pairs of opposite angles of a Euclidean parallelogram
are congruent.
-/
theorem ParallelogramOppositeAnglesCongruent
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D) :
    OppositeAnglesCongruent Geo A B C D := by

  have hAngleB_D :
      Geo.AngleCongruent A B C C D A :=
    ParallelogramOppositeAngleCongruent
      Geo A B C D hParallelogram

  have hBC_DA :
      Geo.Parallel B C D A :=
    hParallelogram.2

  have hCD_AB :
      Geo.Parallel C D A B :=
    ParallelSymmetry
      Geo A B C D hParallelogram.1

  have hRotated :
      IsParallelogram Geo B C D A :=
    ⟨hBC_DA, hCD_AB⟩

  have hAngleC_A :
      Geo.AngleCongruent B C D D A B :=
    ParallelogramOppositeAngleCongruent
      Geo B C D A hRotated

  have hAngleA_C :
      Geo.AngleCongruent D A B B C D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B C D
      D A B
      hAngleC_A

  exact
    ⟨hAngleA_C, hAngleB_D⟩


omit [HilbertIncidence Geo] in
theorem ParallelogramReverse
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D) :
    IsParallelogram Geo B A D C := by

  constructor

  · exact
      ParallelSwapSecondLine
        Geo B A C D
        (ParallelSwapFirstLine
          Geo A B C D
          hParallelogram.1)

  · exact
      ParallelSwapSecondLine
        Geo A D B C
        (ParallelSwapFirstLine
          Geo D A B C
          (ParallelSymmetry
            Geo B C D A
            hParallelogram.2))

omit [HilbertIncidence Geo] in
theorem ParallelogramRotateTwo
    (A B C D : Geo.Point)
    (hParallelogram : IsParallelogram Geo A B C D) :
    IsParallelogram Geo C D A B := by

  constructor

  · exact
      ParallelSymmetry
        Geo A B C D
        hParallelogram.1

  · exact
      ParallelSymmetry
        Geo B C D A
        hParallelogram.2

/--
Hilbert Theorem 45: geometric construction behind the
triangle-to-parallelogram equidecomposition.

D is the midpoint of AC and E is the midpoint of BC.
Extend DE beyond E to F with DE congruent EF.

Then triangles EDC and EFB are congruent and ABFD
is a parallelogram.

The scissors-equivalence statement is proved separately
in HilbertScissors.
-/
theorem hilbert_triangle_parallelogram_data
    [HilbertEuclideanPlane Geo]
    (A B C D E : Geo.Point)
    (hD : HilbertIsMidpoint Geo D A C)
    (hE : HilbertIsMidpoint Geo E B C)
    (hTri : Not (Collinear Geo E D C)) :
    exists F : Geo.Point,
      Geo.Between D E F /\
      TriangleCongruenceResult Geo E D C E F B /\
      IsParallelogram Geo A B F D := by

  --------------------------------------------------------------------
  -- Step 1. Extend DE beyond E.
  --------------------------------------------------------------------

  have hED : Not (E = D) :=
    hilbert_noncollinear_ne_first
      Geo E D C hTri

  have hDE : Not (D = E) := by
    intro h
    exact hED h.symm

  rcases
    ExtendSegmentBeyond
      Geo D E hDE with
  ⟨F, hDEF, hDEEF⟩

  have hDEFData :=
    HilbertOrder.between_incidence
      D E F hDEF

  have hDEFcol :
      Collinear Geo D E F :=
    hDEFData.2.2.2.1

  have hEF : Not (E = F) :=
    hDEFData.2.1

  --------------------------------------------------------------------
  -- Step 2. Midpoint data.
  --------------------------------------------------------------------

  have hDGeometry :
      IsMidpoint Geo D A C :=
    midpoint_of_hilbert
      Geo D A C hD

  have hEGeometry :
      IsMidpoint Geo E B C :=
    midpoint_of_hilbert
      Geo E B C hE

  have hCEB :
      Geo.Between C E B :=
    (HilbertOrder.between_incidence
      B E C hE.left).2.2.2.2

  have hCEBcol :
      Collinear Geo C E B :=
    CollinearSymmetry
      Geo B E C hEGeometry.left

  have hBE : Not (B = E) :=
    (HilbertOrder.between_incidence
      B E C hE.left).1

  have hEB : Not (E = B) := by
    intro h
    exact hBE h.symm

  --------------------------------------------------------------------
  -- Step 3. EFB is noncollinear.
  --------------------------------------------------------------------

  have hTri2 :
      Not (Collinear Geo E F B) := by

    intro hEFB

    have hDEB :
        Collinear Geo D E B :=
      hilbert_primCollinear_trans
        Geo D E F B
        hEF
        hDEFcol
        hEFB

    have hEBC :
        Collinear Geo E B C :=
      PrimCollinearCycle
        Geo C E B hCEBcol

    have hDEC :
        Collinear Geo D E C :=
      hilbert_primCollinear_trans
        Geo D E B C
        hEB
        hDEB
        hEBC

    exact
      hTri
        (PrimCollinearSwap
          Geo D E C hDEC)

  --------------------------------------------------------------------
  -- Step 4. Vertical angles at E.
  --------------------------------------------------------------------

  have hVert :=
    VerticalAngles
      Geo C E D B F
      hCEB
      hDEF
      (fun h =>
        hTri
          (PrimCollinearCycle
            Geo C E D h))

  have hVert' :=
    AngleCongruentReverse
      Geo C E D B E F hVert

  --------------------------------------------------------------------
  -- Step 5. SAS: EDC congruent EFB.
  --------------------------------------------------------------------

  have hSideED_EF :=
    CongruentReverseFirst
      Geo D E E F hDEEF

  have hSideEB_CE :=
    CongruentReverseBoth
      Geo B E E C hEGeometry.right

  have hSideEC_EB :=
    CongruentReverseFirst
      Geo C E E B
      (CongruentSymmetry
        Geo E B C E hSideEB_CE)

  have hCong :=
    TriangleCongruentFromSAS
      Geo E D C E F B
      hTri
      hTri2
      hSideED_EF
      hVert'
      hSideEC_EB

  --------------------------------------------------------------------
  -- Step 6. AD parallel BF.
  --------------------------------------------------------------------

  have hAD_BF :=
    parallel_from_equal_angles
      Geo A C D B E F
      hD.left
      hCEB
      hDEF
      (fun h =>
        hTri
          (PrimCollinearCycle
            Geo C E D h))
      hCong.angleC

  --------------------------------------------------------------------
  -- Step 7. AD congruent BF.
  --
  -- AD ~= DC from the midpoint.
  -- CD ~= BF from the SAS result.
  --------------------------------------------------------------------

  have hSideCD_BF :=
    CongruentReverseFirstSwapSecond
      Geo
      D C F B
      hCong.sideBC

  have hSideAD_BF :=
    congruent_transitivity
      Geo A D C B F
      hDGeometry.right
      hSideCD_BF

  --------------------------------------------------------------------
  -- Step 8. Recognize ABFD as a parallelogram.
  --------------------------------------------------------------------

  have hOnePair :
      OnePairParallelCongruent Geo A B F D :=
    onePairParallelCongruent_of_crossing
      Geo A B F D C E
      hD.left
      hCEB
      hDEF
      hTri
      hAD_BF
      hSideAD_BF

  have hParallelogram :
      IsParallelogram Geo A B F D :=
    OnePairParallelCongruentCriterion
      Geo A B F D hOnePair

  exact
  ⟨F, hDEF, hCong, hParallelogram⟩

/--
The midpoints of two sides of a nondegenerate triangle do not lie
with their common vertex on one line.

If M is the midpoint of AB and N is the midpoint of AC, then
N, M, A are noncollinear whenever A, B, C are noncollinear.
-/
theorem hilbert_midpoints_noncollinear
    [HilbertOrder Geo]
    (A B C M N : Geo.Point)
    (hM : HilbertIsMidpoint Geo M A B)
    (hN : HilbertIsMidpoint Geo N A C)
    (hABC : Not (Collinear Geo A B C)) :
    Not (Collinear Geo N M A) := by

  intro hNMA

  have hAM :
      Not (A = M) :=
    (HilbertOrder.between_incidence
      A M B hM.left).1

  have hAN :
      Not (A = N) :=
    (HilbertOrder.between_incidence
      A N C hN.left).1

  have hAMB :
      Collinear Geo A M B :=
    (HilbertOrder.between_incidence
      A M B hM.left).2.2.2.1

  have hANC :
      Collinear Geo A N C :=
    (HilbertOrder.between_incidence
      A N C hN.left).2.2.2.1

  have hBAM :
      Collinear Geo B A M :=
    PrimCollinearCycle
      Geo M B A
      (PrimCollinearCycle
        Geo A M B hAMB)

  have hAMN :
      Collinear Geo A M N :=
    PrimCollinearSymm
      Geo N M A hNMA

  have hBAN :
      Collinear Geo B A N :=
    hilbert_primCollinear_trans
      Geo B A M N
      hAM
      hBAM
      hAMN

  have hBAC :
      Collinear Geo B A C :=
    hilbert_primCollinear_trans
      Geo B A N C
      hAN
      hBAN
      hANC

  exact
    hABC
      (PrimCollinearSwap
        Geo B A C hBAC)

omit [HilbertIncidence Geo] in
theorem ParallelogramRotateOne
    (A B C D : Geo.Point)
    (h : IsParallelogram Geo A B C D) :
    IsParallelogram Geo D A B C := by
  exact
    ⟨ParallelSymmetry Geo B C D A h.2,
     h.1⟩

/--
A parallelogram is uniquely determined by three consecutive vertices.

If `ABCD` and `ABCE` are parallelograms, then `D = E`.
-/
theorem ParallelogramFourthVertexUnique
    [HilbertEuclideanPlane Geo]
    (A B C D E : Geo.Point)
    (hABCD : IsParallelogram Geo A B C D)
    (hABCE : IsParallelogram Geo A B C E) :
    D = E := by

  --------------------------------------------------------------------
  -- The upper sides AD and AE are both parallel to BC.
  --------------------------------------------------------------------

  have hAD_BC :
      Geo.Parallel A D B C :=
    ParallelSwapFirstLine
      Geo D A B C
      (ParallelSymmetry
        Geo B C D A hABCD.2)

  have hAE_BC :
      Geo.Parallel A E B C :=
    ParallelSwapFirstLine
      Geo E A B C
      (ParallelSymmetry
        Geo B C E A hABCE.2)

  have hBC :
      B ≠ C :=
    hAD_BC.2.1

  rcases
      HilbertPlaneIncidence.line_through
        B C hBC
    with
    ⟨lineBC, hBbc, hCbc⟩

  rcases
      HilbertPlaneIncidence.line_through
        A D hAD_BC.1
    with
    ⟨lineAD, hAad, hDad⟩

  rcases
      HilbertPlaneIncidence.line_through
        A E hAE_BC.1
    with
    ⟨lineAE, hAae, hEae⟩

  have hLinesAD_BC :
      HilbertLinesDisjoint Geo lineAD lineBC := by
    rintro ⟨X, hXad, hXbc⟩

    have hXAD :
        X ∈ Geo.PointLine A D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A D X lineAD
        hAD_BC.1 hAad hDad).mpr hXad

    have hXBC :
        X ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X lineBC
        hBC hBbc hCbc).mpr hXbc

    exact
      Set.disjoint_left.mp
        hAD_BC.2.2
        hXAD hXBC

  have hLinesAE_BC :
      HilbertLinesDisjoint Geo lineAE lineBC := by
    rintro ⟨X, hXae, hXbc⟩

    have hXAE :
        X ∈ Geo.PointLine A E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A E X lineAE
        hAE_BC.1 hAae hEae).mpr hXae

    have hXBC :
        X ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X lineBC
        hBC hBbc hCbc).mpr hXbc

    exact
      Set.disjoint_left.mp
        hAE_BC.2.2
        hXAE hXBC

  have hAoffBC :
      ¬ HilbertIncidence.OnLine A lineBC := by
    intro hAbc
    exact
      hLinesAD_BC
        ⟨A, hAad, hAbc⟩

  have hUpper :
      lineAD = lineAE :=
    HilbertEuclideanPlane.parallel_unique
      (Geo := Geo)
      lineBC A hAoffBC
      lineAD lineAE
      hAad hLinesAD_BC
      hAae hLinesAE_BC

  --------------------------------------------------------------------
  -- Likewise CD and CE are the unique parallels to AB through C.
  --------------------------------------------------------------------

  have hAB_CD :
      Geo.Parallel A B C D :=
    hABCD.1

  have hAB_CE :
      Geo.Parallel A B C E :=
    hABCE.1

  rcases
      HilbertPlaneIncidence.line_through
        A B hAB_CD.1
    with
    ⟨lineAB, hAab, hBab⟩

  rcases
      HilbertPlaneIncidence.line_through
        C D hAB_CD.2.1
    with
    ⟨lineCD, hCcd, hDcd⟩

  rcases
      HilbertPlaneIncidence.line_through
        C E hAB_CE.2.1
    with
    ⟨lineCE, hCce, hEce⟩

  have hLinesAB_CD :
      HilbertLinesDisjoint Geo lineAB lineCD := by
    rintro ⟨X, hXab, hXcd⟩

    have hXAB :
        X ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B X lineAB
        hAB_CD.1 hAab hBab).mpr hXab

    have hXCD :
        X ∈ Geo.PointLine C D :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C D X lineCD
        hAB_CD.2.1 hCcd hDcd).mpr hXcd

    exact
      Set.disjoint_left.mp
        hAB_CD.2.2
        hXAB hXCD

  have hLinesAB_CE :
      HilbertLinesDisjoint Geo lineAB lineCE := by
    rintro ⟨X, hXab, hXce⟩

    have hXAB :
        X ∈ Geo.PointLine A B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A B X lineAB
        hAB_CE.1 hAab hBab).mpr hXab

    have hXCE :
        X ∈ Geo.PointLine C E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo C E X lineCE
        hAB_CE.2.1 hCce hEce).mpr hXce

    exact
      Set.disjoint_left.mp
        hAB_CE.2.2
        hXAB hXCE

  have hCoffAB :
      ¬ HilbertIncidence.OnLine C lineAB := by
    intro hCab
    exact
      hLinesAB_CD
        ⟨C, hCab, hCcd⟩

  have hLinesCD_AB :
      HilbertLinesDisjoint Geo lineCD lineAB := by
    rintro ⟨X, hXcd, hXab⟩
    exact
      hLinesAB_CD
        ⟨X, hXab, hXcd⟩

  have hLinesCE_AB :
      HilbertLinesDisjoint Geo lineCE lineAB := by
    rintro ⟨X, hXce, hXab⟩
    exact
      hLinesAB_CE
        ⟨X, hXab, hXce⟩

  have hRight :
      lineCD = lineCE :=
    HilbertEuclideanPlane.parallel_unique
      (Geo := Geo)
      lineAB C hCoffAB
      lineCD lineCE
      hCcd hLinesCD_AB
      hCce hLinesCE_AB


  --------------------------------------------------------------------
  -- D and E are intersections of the same two distinct lines.
  --------------------------------------------------------------------

  by_contra hDE

  have hEad :
      HilbertIncidence.OnLine E lineAD := by
    rw [hUpper]
    exact hEae

  have hEcd :
      HilbertIncidence.OnLine E lineCD := by
    rw [hRight]
    exact hEce

  have hAD_CD :
      lineAD = lineCD :=
    HilbertPlaneIncidence.line_unique
      D E hDE
      lineAD lineCD
      hDad hEad
      hDcd hEcd

  have hCad :
      HilbertIncidence.OnLine C lineAD := by
    rw [hAD_CD]
    exact hCcd

  exact
    hLinesAD_BC
      ⟨C, hCad, hCbc⟩

-----------------------------------------------------------------------
-- Intersection of two constructed lines
--
-- Target: eliminate `i46_complete_parallelogram` (and, with it, the
-- corresponding half of `i42_construct_parallelogram` and the Pasch
-- point `N` inside `i47_diagram`) by proving outright that the
-- parallelogram on a given base and a given third vertex can be
-- completed.
--
-- The observation that makes this cheap is that in this library
-- `Geo.Parallel` is *defined* as disjointness of the two extensional
-- point-line carriers.  So "two non-parallel lines meet" is not a new
-- axiom at all; it is the definition read backwards.  All the real
-- content sits in one step:
--
--   the line through `B` parallel to `AD` and the line through `D`
--   parallel to `AB` are not parallel to each other.
--
-- For if they were, `hilbert_parallel_transitive_distinct` (which is
-- where Hilbert's axiom IV is actually used) would force the line `AD`
-- either to be parallel to the line `DR` -- impossible, they share `D`
-- -- or to coincide with it, in which case `AB` would be parallel to a
-- line through `A`, again impossible.
--
-- Naming convention: auxiliary results carry the `intersection_test_`
-- prefix; the target theorem already carries the name it should have
-- once it is moved into `HilbertInterface.lean`, so that promotion is
-- a copy rather than a rename.
------------------------------------------------------------------------

/-
The first determining point of a point-line lies on it.
-/
omit [HilbertIncidence Geo] in
theorem intersection_test_left_mem
    (A B : Geo.Point) :
    A ∈ Geo.PointLine A B := by
  change Geometry.Geo.LineCollinear Geo A B A
  exact Or.inr (Or.inl rfl)

/-
The second determining point of a point-line lies on it.
-/
omit [HilbertIncidence Geo] in
theorem intersection_test_right_mem
    (A B : Geo.Point) :
    B ∈ Geo.PointLine A B := by
  change Geometry.Geo.LineCollinear Geo A B B
  exact Or.inr (Or.inr (Or.inl rfl))

/-
Two lines with a common point are not parallel.

Immediate from the definition of `Geo.Parallel` as disjointness of the
two carriers; stated separately because it is used three times below
and reads better than an inlined `Set.disjoint_left`.
-/
omit [HilbertIncidence Geo] in
theorem intersection_test_not_parallel_of_common_point
    (A B C D P : Geo.Point)
    (hP₁ : P ∈ Geo.PointLine A B)
    (hP₂ : P ∈ Geo.PointLine C D) :
    ¬ Geo.Parallel A B C D := by
  intro hParallel
  exact
    Set.disjoint_left.mp hParallel.2.2
      hP₁ hP₂

/--
Disjoint incidence lines carry parallel point-lines.

This is the bridge between the incidence-level notion
`HilbertLinesDisjoint` and the extensional notion `Geo.Parallel`.
-/
theorem intersection_test_parallel_of_lines_disjoint
    [HilbertOrder Geo]
    (B Q D R : Geo.Point)
    (l m : Geo.Line)
    (hBQ : B ≠ Q)
    (hDR : D ≠ R)
    (hBl : HilbertIncidence.OnLine B l)
    (hQl : HilbertIncidence.OnLine Q l)
    (hDm : HilbertIncidence.OnLine D m)
    (hRm : HilbertIncidence.OnLine R m)
    (hDisjoint : HilbertLinesDisjoint Geo l m) :
    Geo.Parallel B Q D R := by

  refine ⟨hBQ, hDR, Set.disjoint_left.mpr ?_⟩

  intro X hXBQ hXDR

  have hXl :
      HilbertIncidence.OnLine X l :=
    (hilbert_mem_pointLine_iff_onLine
      Geo B Q X l hBQ hBl hQl).mp hXBQ

  have hXm :
      HilbertIncidence.OnLine X m :=
    (hilbert_mem_pointLine_iff_onLine
      Geo D R X m hDR hDm hRm).mp hXDR

  exact hDisjoint ⟨X, hXl, hXm⟩

------------------------------------------------------------------------
-- Target theorem
------------------------------------------------------------------------

/--
A parallelogram can be completed from three of its vertices.

Given a base `AB` and a point `D` off the line `AB`, there is a fourth
vertex `C` making `A B C D` a parallelogram.

`C` is the intersection of the line through `B` parallel to `AD` with
the line through `D` parallel to `AB`; both lines exist by I.31
(`hilbert_parallel_through_point_exists`), and the argument that they
are not parallel to each other is where Hilbert's axiom IV enters, via
`hilbert_parallel_transitive_distinct`.

This is the statement currently assumed as `i46_complete_parallelogram`
in `Proposition46.lean`.
-/
theorem hilbert_parallelogram_fourth_vertex_exists
    [HilbertEuclideanPlane Geo]
    (A B D : Geo.Point)
    (hABD : Not (Collinear Geo A B D)) :
    ∃ C : Geo.Point,
      IsParallelogram Geo A B C D := by

  --------------------------------------------------------------------
  -- Nondegeneracy.
  --------------------------------------------------------------------

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B D hABD

  have hADB :
      Not (Collinear Geo A D B) := by
    intro hCol
    exact
      hABD
        (PrimCollinearRotate Geo A D B hCol)

  have hAD : A ≠ D :=
    hilbert_noncollinear_ne_first
      Geo A D B hADB

  --------------------------------------------------------------------
  -- Step 1 [I.31]: the two constructed parallels.
  --------------------------------------------------------------------

  rcases
      hilbert_parallel_through_point_exists
        Geo A D B hAD hADB with
    ⟨Q, hBQ, hParAD_BQ⟩

  rcases
      hilbert_parallel_through_point_exists
        Geo A B D hAB hABD with
    ⟨R, hDR, hParAB_DR⟩

  rcases
      HilbertPlaneIncidence.line_through
        B Q hBQ with
    ⟨l, hBl, hQl⟩

  rcases
      HilbertPlaneIncidence.line_through
        D R hDR with
    ⟨m, hDm, hRm⟩

  --------------------------------------------------------------------
  -- Step 2: the two lines are not parallel, hence they meet.
  --------------------------------------------------------------------

  have hMeet :
      HilbertLinesMeet Geo l m := by

    by_contra hDisjoint

    have hParBQ_DR :
        Geo.Parallel B Q D R :=
      intersection_test_parallel_of_lines_disjoint
        Geo B Q D R l m
        hBQ hDR hBl hQl hDm hRm
        hDisjoint

    by_cases hSameCarrier :
        Geo.PointLine A D = Geo.PointLine D R

    ----------------------------------------------------------------
    -- If `AD` and `DR` are the same line, then `AB` is parallel to a
    -- line through `A`.
    ----------------------------------------------------------------

    · have hA_DR :
          A ∈ Geo.PointLine D R := by
        rw [← hSameCarrier]
        exact intersection_test_left_mem Geo A D

      exact
        intersection_test_not_parallel_of_common_point
          Geo A B D R A
          (intersection_test_left_mem Geo A B)
          hA_DR
          hParAB_DR

    ----------------------------------------------------------------
    -- Otherwise transitivity of parallelism makes `AD` parallel to
    -- `DR`, though they share `D`.
    ----------------------------------------------------------------

    · have hParDR_BQ :
          Geo.Parallel D R B Q :=
        ParallelSymmetry
          Geo B Q D R hParBQ_DR

      have hParAD_DR :
          Geo.Parallel A D D R :=
        hilbert_parallel_transitive_distinct
          Geo A D D R B Q
          hParAD_BQ
          hParDR_BQ
          hSameCarrier

      exact
        intersection_test_not_parallel_of_common_point
          Geo A D D R D
          (intersection_test_right_mem Geo A D)
          (intersection_test_left_mem Geo D R)
          hParAD_DR

  rcases hMeet with ⟨C, hCl, hCm⟩

  --------------------------------------------------------------------
  -- Step 3: the intersection point is distinct from `B` and from `D`.
  --------------------------------------------------------------------

  have hCB : C ≠ B := by
    intro hEq

    have hBm :
        HilbertIncidence.OnLine B m := by
      rw [← hEq]
      exact hCm

    have hB_DR :
        B ∈ Geo.PointLine D R :=
      (hilbert_mem_pointLine_iff_onLine
        Geo D R B m hDR hDm hRm).mpr hBm

    exact
      intersection_test_not_parallel_of_common_point
        Geo A B D R B
        (intersection_test_right_mem Geo A B)
        hB_DR
        hParAB_DR

  have hCD : C ≠ D := by
    intro hEq

    have hDl :
        HilbertIncidence.OnLine D l := by
      rw [← hEq]
      exact hCl

    have hD_BQ :
        D ∈ Geo.PointLine B Q :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B Q D l hBQ hBl hQl).mpr hDl

    exact
      intersection_test_not_parallel_of_common_point
        Geo A D B Q D
        (intersection_test_right_mem Geo A D)
        hD_BQ
        hParAD_BQ

  --------------------------------------------------------------------
  -- Step 4: transport both parallels onto the sides `BC` and `DC`.
  --------------------------------------------------------------------

  have hColBCQ :
      Collinear Geo B C Q :=
    ⟨l, hBl, hCl, hQl⟩

  have hColDCR :
      Collinear Geo D C R :=
    ⟨m, hDm, hCm, hRm⟩

  have hParBC_DA :
      Geo.Parallel B C D A := by
    have hParBQ_AD :
        Geo.Parallel B Q A D :=
      ParallelSymmetry
        Geo A D B Q hParAD_BQ

    have hParBC_AD :
        Geo.Parallel B C A D :=
      collinear_parallel_trans
        Geo B C Q A D
        (Ne.symm hCB)
        hColBCQ
        hParBQ_AD

    exact
      ParallelSwapSecondLine
        Geo B C A D hParBC_AD

  have hParAB_CD :
      Geo.Parallel A B C D := by
    have hParDR_AB :
        Geo.Parallel D R A B :=
      ParallelSymmetry
        Geo A B D R hParAB_DR

    have hParDC_AB :
        Geo.Parallel D C A B :=
      collinear_parallel_trans
        Geo D C R A B
        (Ne.symm hCD)
        hColDCR
        hParDR_AB

    have hParAB_DC :
        Geo.Parallel A B D C :=
      ParallelSymmetry
        Geo D C A B hParDC_AB

    exact
      ParallelSwapSecondLine
        Geo A B D C hParAB_DC

  exact ⟨C, hParAB_CD, hParBC_DA⟩

------------------------------------------------------------------------
-- Follow-up targets for this file
--
-- 1. `i42_construct_parallelogram` (Proposition42.lean) asks for a
--    parallelogram on a given base with a prescribed angle at one
--    vertex.  With the theorem above, what remains of that axiom is
--    only the angle-construction part (III,4), not the intersection.
--
-- 2. The Pasch point `N` of `i47_diagram` -- the meeting of the
--    diagonal `DC` of the square with the cut `ML` -- should follow
--    from `HilbertOrder.pasch` applied to the triangle cut by the line
--    `ML`, not from the diagram axiom.
------------------------------------------------------------------------

end Geometry

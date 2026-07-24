# Hilbert derivation ledger

This document records why provisional declarations in
`CGJteamLab/GeometryBase.lean` can be replaced by definitions or proved
theorems.  It is the durable mathematical memory of the Hilbert branch:
the comments left during an interactive proof session are useful while
working, but this file and the Lean docstrings are the permanent record.

The ledger describes the state at commit `eb3bd04` and should be updated
whenever another provisional axiom is removed.

## Source and page convention

The mathematical reference is:

> David Hilbert, *Foundations of Geometry*, second English edition,
> translated by Leo Unger from the tenth German edition, revised and
> enlarged by Paul Bernays, Open Court.

Page numbers below are the printed book pages.  The corresponding page
number in `foundations-of-geometry-2ed.pdf` is included in parentheses,
because the PDF has twelve pages of front matter before printed page 1.

The principal references are:

| Material | Printed page | PDF page |
| --- | ---: | ---: |
| Incidence axioms I.1-I.3 | 3-4 | 15-16 |
| Order axioms II.1-II.4 | 5 | 17 |
| Theorems 3 and 4 | 6 | 18 |
| Theorem 5 | 6-7 | 18-19 |
| Congruence axioms III.1-III.5 | 10-12 | 22-24 |
| Theorem 12 (first triangle congruence theorem) | 14 | 26 |
| Theorem 14 (supplementary angles) | 14-15 | 26-27 |
| Theorem 19 (transitivity and symmetry of angle congruence) | 18-19 | 30-31 |
| Theorem 22 (exterior-angle theorem) | 21-22 | 33-34 |
| Theorem 25 (extended triangle congruence theorem) | 22-23 | 34-35 |
| Theorem 26 (bisection of every segment) | 23 | 35 |
| Definition of parallel lines and Theorem 30 | 25 | 37 |

The proof comments are independent paraphrases of the mathematical
dependencies.  They do not copy or translate formal code from another
geometry library.

## Architectural rule

The four relevant layers have different jobs:

1. `GeometryCore` defines the shared objects and representation-level
   identities.  It does not contain Hilbert axioms.
2. `HilbertAxioms` contains exactly Hilbert's axiom hierarchy and
   theorems derived from it.
3. `GeometryBase` provides the stable project-facing API.  Its public
   theorems delegate either to a representation fact in `GeometryCore`
   or to a proved result in `HilbertAxioms`.
4. `MidsegmentParallel` and `FinlayProof` consume that API.  The Suppes
   and Tarski paths may reuse it only through their explicit bridges.

An occurrence of `axiom` inside a `Previous provisional declaration`
block comment is historical text, not an active Lean axiom.

## What counts as a reduction

Not every removed axiom needs a long geometric proof.

- A **representation reduction** follows because an object was modeled
  correctly: segments are unordered endpoint pairs, angles are
  unordered ray pairs, and parallelism is disjointness of extensional
  point-lines.
- A **Hilbert derivation** uses fields of the Hilbert classes and
  previously proved consequences of those fields.
- A **definition unfolding** follows immediately from a project
  definition and carries no new mathematical content.

Keeping these cases separate prevents us from claiming that a
definitional identity is an axiom or that a substantial Hilbert theorem
is "obvious".

## Completed replacements in `GeometryBase`

### Incidence and collinearity

| Former provisional declaration | Active result | Reason and proof root |
| --- | --- | --- |
| `CollinearSymmetry` | theorem of the same name | Permutes the three witnesses in `PrimCollinear`.  This is representational. |
| `CollinearTrans` | theorem of the same name | `hilbert_primCollinear_trans`; axiom I.2 makes the two lines through the distinct common points `G` and `P` equal.  The new hypothesis `G != P` is mathematically necessary. |
| `IntersectionOnSameLine` | theorem of the same name | Axiom I.2 identifies the two lines through distinct `A` and `P`; the intersection witness is then transported along that equality. |

### Segment congruence

| Former provisional declaration | Active result | Reason and proof root |
| --- | --- | --- |
| `CongruentSymmetry` | theorem of the same name | `hilbert_congruent_symmetry`; reflexivity, symmetry, and transitivity of segment congruence are derived from III.1-III.2 on printed pages 10-11. |
| `CongruentReverseFirst` | theorem of the same name | `Geo.congruent_reverse_first`; `Geo.Segment A B` is the unordered pair `s(A, B)`. |
| `CongruentReverseBoth` | theorem of the same name | Two endpoint reversals of unordered segments. |
| `CongruentSwapSecond` | theorem of the same name | Endpoint reversal on the second unordered segment. |
| `congruent_transitivity` | theorem of the same name | `hilbert_congruent_transitivity` after normalizing the endpoint order.  Ultimately derived from III.1-III.2. |

The endpoint-reversal theorems require no Hilbert class.  This matches
Hilbert's statement on printed page 10 that `AB` and `BA` denote the
same segment.

### Angles and triangle congruence

| Former provisional declaration | Active result | Reason and proof root |
| --- | --- | --- |
| `AngleCongruentReverse` | theorem of the same name | `Geo.Angle` is an unordered pair of rays, so swapping both sides preserves the represented angle. |
| `SAS` | theorem of the same name | Formal form of Theorem 12.  `hilbert_sas_remaining_angles` uses III.5; `hilbert_sas_third_side_and_angle` adds segment construction and the uniqueness clause of III.4 to obtain the third side. |
| `TriangleCongruentFromSAS` | theorem of the same name | Compatibility wrapper around `SAS`; the added noncollinearity hypotheses make Hilbert's standing convention for triangles explicit. |
| `VerticalAngles` | theorem of the same name | `hilbert_vertical_angles`, the immediate vertical-angle corollary of Theorem 14.  Strict betweenness identifies both pairs of opposite rays and noncollinearity excludes degenerate angles. |

`Geo.AngleCongruent` is the equivalence closure of the primitive
`Geo.UnorientedAngleCongruent` relation.  Consequently reflexivity,
symmetry, and transitivity are properties of the public representation,
not extra fields of a Hilbert class.  In Hilbert's development the
corresponding mathematical transitivity result is Theorem 19.  The
choice of equivalence closure is therefore a modeling decision that
builds the expected equality-like behavior into the public relation.

### Parallelism

| Former provisional declaration | Active result | Reason and proof root |
| --- | --- | --- |
| `ParallelSymmetry` | theorem of the same name | Symmetry of `Set.Disjoint` in the definition of `Geo.Parallel`. |
| `ParallelSwapFirstLine` | theorem of the same name | `Geo.pointLine_swap` shows that reversing a determining pair preserves the first point-line. |
| `ParallelSwapSecondLine` | theorem of the same name | The analogous representation fact for the second point-line. |
| `ParallelCollinearLeft` | theorem of the same name | `hilbert_pointLine_eq_of_points_on_line` identifies two nondegenerate point pairs on one incidence line, using I.2 and Theorem 4. |
| `collinear_parallel_trans` | theorem of the same name | The companion point-line transport in the other argument position. |
| `parallel_from_equal_angles` | theorem of the same name | `hilbert_parallel_of_alternate_angles`, the equal-alternate-angles implication in Theorem 30.  It is proved from the non-equality part of Theorem 22 and does not use Euclid's axiom IV. |
| Parallel lines imply equal alternate angles | `equal_angles_from_parallel` | `hilbert_alternate_angles_of_parallel`, the Euclidean implication in Theorem 30.  Angle construction III.4 and the neutral implication produce a second parallel through the same point; axiom IV identifies it with the given parallel. |

Hilbert defines two plane lines to be parallel when they do not
intersect (printed page 25).  Since the project is planar,
`Geo.Parallel A B C D` is exactly nondegeneracy of `AB` and `CD`
together with disjointness of their extensional `PointLine` carriers.

The converse direction of Theorem 30 - parallel lines cut by a
transversal produce congruent alternate angles - is now formalized as
`equal_angles_from_parallel`.  It explicitly requires
`HilbertEuclideanPlane`; the Euclidean parallel axiom is therefore not
silently used by the neutral `parallel_from_equal_angles`.

### Construction and parallelogram API

| Former provisional declaration | Active result | Reason and proof root |
| --- | --- | --- |
| `ExtendSegment` | theorem of the same name | `hilbert_extend_segment`; for `A != B`, II.2 supplies a ray beyond `B` and III.1 lays off a congruent copy of `AB` on it.  The degenerate case uses derived reflexivity. |
| `OnePairParallelCongruentCriterion` | theorem of the same name | The corrected same-side orientation excludes the bow-tie case. `onePair_diagonal_oppositeSide` derives the required diagonal orientation using plane separation, the Euclidean direction of Theorem 30, and SAS; a second SAS application and the neutral direction of Theorem 30 yield the missing parallel pair. |
| `ParallelogramOppositeSidesParallel` | theorem of the same name | Direct unfolding: `IsParallelogram` is currently defined as `OppositeSidesParallel`. |
| `ParallelogramOppositeSidesCongruent` | theorem of the same name | Lay off a copy of one side on the ray containing its opposite side.  Same-side transport supplies the orientation for `OnePairParallelCongruentCriterion`; Hilbert IV then identifies the constructed parallel with the original side, and incidence uniqueness identifies the constructed endpoint.  Cyclic relabelling gives the other pair. |
| Existence of a diagonal intersection | `ParallelogramDiagonalIntersectionExists` | The two cyclic applications of `onePair_diagonal_oppositeSide` construct crossing witnesses on the diagonals.  Incidence uniqueness identifies the witnesses, yielding a point strictly between both pairs of opposite vertices. |
| `ParallelogramDiagonals` | theorem of the same name | The one-pair orientation lemma first proves that the named common point lies strictly inside both diagonals.  Theorem 30 gives two alternate-angle congruences, opposite sides are congruent by the preceding theorem, and angle-side-angle congruence gives equality of the two diagonal halves. |
| Existence of a strict midpoint | `HilbertMidpointExists` | Thin `GeometryBase` wrapper around `hilbert_midpoint_exists`.  The mathematical proof is Hilbert's neutral Theorem 26 in `HilbertAxioms`: opposite-side angle construction, Theorem 4, Pasch/Theorem 22 exclusion of exterior orders, vertical angles, and Theorem 25.  The result is `Between A M B ∧ AM ≅ MB` and needs only Groups I-III. |

## The nontrivial proof chain

The following chain is the reason the latest reductions are maintainable
rather than isolated tactics:

```text
I.1-I.2 and II.1-II.4
  -> Theorem 3 and Theorem 4
  -> strengthened inner and outer Pasch
  -> the required transitivity clauses of Theorem 5
  -> transport of Between along rays

III.1-III.5
  -> uniqueness of segment construction
  -> Theorem 12 (SAS)

Theorem 5 + Theorem 12
  -> Theorem 14 (supplementary angles)
  -> vertical angles

Pasch side separation + Theorem 12 + Theorem 14
  -> non-equality part of Theorem 22
  -> equal alternate angles imply disjoint lines
  -> neutral direction of Theorem 30
  -> GeometryBase.parallel_from_equal_angles

Pasch side/opposite-side transport + III.4
  -> construct the equal-angle parallel through a prescribed point
Hilbert IV (uniqueness of the parallel)
  -> identify the constructed line with the given parallel
  -> Euclidean direction of Theorem 30
  -> GeometryBase.equal_angles_from_parallel
```

The principal Lean names in this chain are:

- `hilbert_between_exists` - Theorem 3;
- `hilbert_between_trichotomy` - Theorem 4;
- `hilbert_inner_pasch_strong` and `hilbert_outer_pasch_strong`;
- `hilbert_between_outer_trans_right`,
  `hilbert_between_outer_trans`, and `hilbert_between_inner_trans` -
  the clauses of Theorem 5 needed by the project;
- `hilbert_between_transport_sameRays`;
- `hilbert_sas_remaining_angles` and
  `hilbert_sas_third_side_and_angle` - Theorem 12;
- `hilbert_adjacent_angles_congruent` - Theorem 14;
- `hilbert_vertical_angles`;
- `hilbert_line_avoids_third_triangle_side` and
  `hilbert_outer_endpoints_sameSide` - the required side-separation
  lemmas;
- `hilbert_exterior_angle_not_congruent` - only the non-equality
  consequence of Theorem 22 needed here;
- `hilbert_exterior_angle_not_congruent_other` - the companion remote
  interior-angle form of Theorem 22;
- `hilbert_aas_sides` - Theorem 25;
- `hilbert_midpoint_exists` - Theorem 26;
- `hilbert_parallel_of_alternate_angles` - the neutral implication used
  from Theorem 30;
- `hilbert_oppositeSide_transport_right` - Pasch plane-separation
  transport needed to preserve the selected side of the transversal;
- `hilbert_parallel_of_alternate_angles_oppositeSide` - the general
  neutral alternate-angle criterion used by the Euclidean construction;
- `hilbert_alternate_angles_of_parallel` - the direction of Theorem 30
  that uses axiom IV;
- `hilbert_parallel_of_alternate_angles_oppositeSide_lines` and
  `hilbert_alternate_angles_of_parallel_oppositeSide_lines` - the
  line-level forms used by parallelogram recognition;
- `onePair_diagonal_oppositeSide` - the order-and-orientation lemma
  which eliminates the crossed endpoint correspondence.

## Downstream purpose

The reductions are not merely library cleanup:

- `MidsegmentParallel` uses segment extension, vertical angles, SAS,
  congruence transitivity, the alternate-angle parallel criterion, and
  the Euclidean one-pair parallelogram recognition theorem to prove the
  midsegment result.
- `FinlayProof` is the canonical formal pseudocode of Finlay's
  mathematical proof.  Starting only from the assertion that `ABC` is
  a triangle, it constructs the two initial midpoints, their
  intersection `G`, the auxiliary point `P`, and the intersection
  `D = AP ∩ BC`.  It then keeps Steps 1--5, their explanatory comments,
  and the complete dependency graph directly in the file.
- `FinlayCommon` currently contains the shared upper part used by the
  Suppes and Tarski integration routes: the two parallel transports,
  parallelogram recognition, incidence transport, diagonal bisection,
  and final collinearity transitivity.
- `FinlayProofSuppes` and `FinlayProofTarski` obtain `FG ∥ BP` and
  `EG ∥ CP` from their imported Midsegment Theorems and currently call
  `FinlayFromMidsegmentParallels`.
- The three foundation-specific final theorems are expected to have the
  same mathematical conclusion but not necessarily identical
  hypotheses.  Their headers and construction preludes must expose
  exactly what Hilbert, Suppes, or Tarski supplies.  Only the visible
  five-step Finlay argument after those constructions should retain the
  same mathematical shape.
- The Tarski adapter additionally converts primitive Tarski
  collinearity and midpoint data through the explicit bridge.  The
  Suppes adapter obtains its midsegment parallelisms through its
  declared bridge.  Neither adapter repeats Finlay's five-step
  mathematical argument.

The current Tarski adapter is an integration route through
`GeometryBase`, not yet a derivation of Hilbert's parallel interface
from `TarskiEuclideanPlane`.  It therefore states
`HilbertEuclideanPlane` explicitly where the shared one-pair theorem is
used.  No Hilbert parallel axiom is inserted into `TarskiAxioms`.
The current Suppes adapter has the same integration character in the
shared upper step: `SuppesGeometry` and `SuppesMidsegmentBridge`
provide the midsegment theorem, while `HilbertEuclideanPlane` is
stated explicitly for the derived Euclidean parallelogram results.
No Hilbert axiom is inserted into `SuppesAxioms` or `SuppesBase`.

Thus a theorem in `HilbertAxioms` should record the mathematical
dependency, while its wrapper in `GeometryBase` should explain which
stable project operation it replaces.

## Remaining active axioms

There are no active `axiom` declarations left in
`GeometryBase.lean`.

The former declarations remain only inside labelled block comments as
historical API records.

The original `OnePairParallelCongruentCriterion` said only that one
pair of named opposite sides was parallel and congruent.  That statement
was false for a crossed bow-tie configuration.  The structure now also
records that the corresponding outer endpoints lie on the same side
of the other side-line.  In the Midsegment proof this orientation is
derived from the three strict betweenness hypotheses by
`hilbert_third_side_endpoints_sameSide`, a Pasch separation theorem.
The corrected criterion is now a theorem.  Its proof constructs the
alternative endpoint on the opposite ray to rule out the crossed
correspondence, derives the diagonal-side orientation, and then uses
Theorem 30 and SAS to obtain the second pair of parallel sides.

`ParallelogramOppositeSidesCongruent` is the standard Euclidean
parallelogram theorem derived from segment construction, plane-side
transport, the one-pair recognition theorem, and uniqueness of the
parallel.  `ParallelogramDiagonals` is derived from it, strict
diagonal-side separation, Theorem 30, and angle-side-angle
congruence.  Neither statement is a new field of
`HilbertAxioms`; every genuinely Euclidean step instead uses
`HilbertEuclideanPlane`, whose only new field is Hilbert's axiom IV.

## History of the reduction work

The following commits are useful reconstruction points:

| Commit | Main mathematical change |
| --- | --- |
| `68d17be` | First representation and definition reductions in `GeometryBase`. |
| `0b8f7cd` | Segment congruence symmetry and transitivity derived from Hilbert congruence. |
| `4d5d83b` | Endpoint reversal moved to the unordered segment representation in `GeometryCore`. |
| `fa98f17` | Angle reversal moved to the unordered angle representation. |
| `7136268` | Basic parallel symmetry and endpoint swaps reduced to core representation. |
| `3c99fea` | `ExtendSegment` derived from Hilbert order and congruence. |
| `f3da8f8` | `CollinearTrans` proved with the necessary distinctness hypothesis. |
| `b0737a3` | Strict Hilbert midpoint data separated from weak project collinearity. |
| `1463f59` | `IntersectionOnSameLine` derived from incidence uniqueness. |
| `509827a`, `599528f` | SAS reduced to Hilbert's Theorem 12 and propagated to callers. |
| `933fa68` | `VerticalAngles` derived through Theorems 5, 12, and 14. |
| `67ea0f2` | Parallel transports proved using extensional point-lines. |
| `eb3bd04` | Equal alternate angles reduced through Theorems 22 and 30. |

## Documentation protocol for the next reduction

Every future replacement should leave four durable records:

1. Keep the old signature in a `Previous provisional declaration`
   block comment until the public migration is complete.
2. Put a docstring above the active `GeometryBase` theorem stating
   whether the result is representational, definitional, neutral
   Hilbert geometry, or Euclidean Hilbert geometry.
3. Put a mathematical docstring above every nontrivial helper in
   `HilbertAxioms`, including the book theorem or axiom numbers, the
   precise local consequence formalized, and a short proof outline.
4. Update this ledger with the new dependency and the statement of any
   hypothesis added during the replacement.

Before a commit, compile the modified leaf modules and run a full
`lake build`.  Also verify that no `sorry` or `admit` was introduced and
that the count of active `axiom` declarations changed as expected.

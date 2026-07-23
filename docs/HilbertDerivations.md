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

Hilbert defines two plane lines to be parallel when they do not
intersect (printed page 25).  Since the project is planar,
`Geo.Parallel A B C D` is exactly nondegeneracy of `AB` and `CD`
together with disjointness of their extensional `PointLine` carriers.

The converse direction of Theorem 30 - parallel lines cut by a
transversal produce congruent alternate angles - does require the
Euclidean parallel axiom.  It is not being silently used by
`parallel_from_equal_angles`.

### Construction and parallelogram API

| Former provisional declaration | Active result | Reason and proof root |
| --- | --- | --- |
| `ExtendSegment` | theorem of the same name | `hilbert_extend_segment`; for `A != B`, II.2 supplies a ray beyond `B` and III.1 lays off a congruent copy of `AB` on it.  The degenerate case uses derived reflexivity. |
| `ParallelogramOppositeSidesParallel` | theorem of the same name | Direct unfolding: `IsParallelogram` is currently defined as `OppositeSidesParallel`. |

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
- `hilbert_parallel_of_alternate_angles` - the neutral implication used
  from Theorem 30.

## Downstream purpose

The reductions are not merely library cleanup:

- `MidsegmentParallel` uses segment extension, vertical angles, SAS,
  congruence transitivity, and the alternate-angle parallel criterion
  to prove the midsegment result.
- `FinlayProof` uses the two parallel transports, incidence
  transport, and collinearity transitivity to move from the
  midsegment theorem to the final concurrency configuration.
- `MidsegmentParallelTarski` and `FinlayProofTarski` reuse the same
  stable API after explicit conversion of Tarski betweenness and
  midpoint data.
- The Suppes path likewise reuses only the common interfaces made
  available through its declared dependency path.

Thus a theorem in `HilbertAxioms` should record the mathematical
dependency, while its wrapper in `GeometryBase` should explain which
stable project operation it replaces.

## Remaining active axioms

Exactly three active `axiom` declarations remain in
`GeometryBase.lean`:

1. `OnePairParallelCongruentCriterion`;
2. `ParallelogramOppositeSidesCongruent`;
3. `ParallelogramDiagonals`.

They are all in the parallelogram section and should be treated as one
design problem rather than three unrelated proofs.

`OnePairParallelCongruentCriterion` currently says only that one pair
of named opposite sides is parallel and congruent.  In an informal
textbook the word "quadrilateral" supplies distinctness, cyclic order,
and simplicity conditions.  The current Lean structure does not yet
encode those conditions, so a proof attempt must first decide which
orientation or same-side hypotheses make the recognition statement
correct.

After the quadrilateral notion is made precise,
`ParallelogramOppositeSidesCongruent` is the standard Euclidean
parallelogram theorem.  `ParallelogramDiagonals` should then be derived
from it together with the hypotheses identifying the diagonal
intersection.  Neither statement belongs as a new field of
`HilbertAxioms`; any genuinely Euclidean step must instead use
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


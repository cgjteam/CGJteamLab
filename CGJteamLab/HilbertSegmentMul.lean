/-
HilbertSegmentMul.lean -- SKELETON

Every declaration below is stated but not proved.  The file is not
meant to be reachable from the build root until the `sorry`s are
discharged; add it to CGJteamLab.lean only at that point.

Purpose: close the last assumption of Euclid I.39,

    hilbert_scissors_triangle_positive
      (HilbertScissorsPositivity.lean)

by constructing the area valuation of Hilbert, Foundations sec. 20,
equivalently Hartshorne, Theorem 23.2.

Each block is tagged

    [ELEM]    provable from Groups I-III, the parallel axiom, and the
              segment arithmetic already in HilbertSegmentArithmetic
    [PASCAL]  needs proposition39_test_special_pascal
              (HilbertPascal.lean:15745), i.e. Hilbert sec. 14

The tags are the point of this file: only four statements are
[PASCAL], and all four are about multiplication, none about the
geometry of triangles.
-/

import CGJteamLab.HilbertSegmentArithmetic
import CGJteamLab.HilbertScissorsInvariant

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Part 0.  A unit segment
------------------------------------------------------------------------

/--
An arbitrary but fixed positive segment class, used as the unit of
multiplication.

Nothing depends on the choice: a different unit rescales every area by
a fixed factor, and positivity is unaffected.
-/
noncomputable def hilbertUnitSegment
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    HilbertPositiveSegmentClass Geo := by

  let h :=
    HilbertPlaneIncidence.two_points_on_line
      (Geo := Geo)

  let l : Geo.Line :=
    Classical.choose h

  have hl :
      ∃ A B : Geo.Point,
        A ≠ B ∧
        HilbertIncidence.OnLine A l ∧
        HilbertIncidence.OnLine B l :=
    Classical.choose_spec h

  let A : Geo.Point :=
    Classical.choose hl

  have hA :
      ∃ B : Geo.Point,
        A ≠ B ∧
        HilbertIncidence.OnLine A l ∧
        HilbertIncidence.OnLine B l :=
    Classical.choose_spec hl

  let B : Geo.Point :=
    Classical.choose hA

  have hB :
      A ≠ B ∧
      HilbertIncidence.OnLine A l ∧
      HilbertIncidence.OnLine B l :=
    Classical.choose_spec hA

  exact
    hilbertPositiveSegmentClassOf
      Geo A B hB.1


------------------------------------------------------------------------
-- Part 1.  Multiplication
--
-- Hilbert sec. 15.  In the language of the ratio witnesses already
-- present in HilbertSegmentArithmetic, the product a * b is the unique
-- x with
--
--     1 : a  =  b : x.
------------------------------------------------------------------------

/-- [ELEM] The fourth proportional exists. -/
theorem hilbertPositiveSegmentMul_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    ∃ x : HilbertPositiveSegmentClass Geo,
      HilbertPositiveSegmentProportion Geo
        (hilbertUnitSegment Geo) a b x :=
  sorry

/--
[ELEM] The fourth proportional is unique.

Two right triangles with congruent acute angles and congruent adjacent
legs are congruent, so the opposite leg is determined.  This is
segment-construction uniqueness plus ASA, not proportion theory.
-/
theorem hilbertPositiveSegmentMul_unique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b x y : HilbertPositiveSegmentClass Geo)
    (hx : HilbertPositiveSegmentProportion Geo
            (hilbertUnitSegment Geo) a b x)
    (hy : HilbertPositiveSegmentProportion Geo
            (hilbertUnitSegment Geo) a b y) :
    x = y :=
  sorry

/-- The product of two positive segment classes. -/
noncomputable def hilbertPositiveSegmentMul
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentClass Geo :=
  Classical.choose
    (hilbertPositiveSegmentMul_exists Geo a b)

theorem hilbertPositiveSegmentMul_spec
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentProportion Geo
      (hilbertUnitSegment Geo) a b
      (hilbertPositiveSegmentMul Geo a b) :=
  Classical.choose_spec
    (hilbertPositiveSegmentMul_exists Geo a b)

------------------------------------------------------------------------
-- Part 2.  The laws
------------------------------------------------------------------------

/-- [ELEM] -/
theorem hilbertPositiveSegmentMul_one
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMul Geo a (hilbertUnitSegment Geo) = a :=
  sorry

/--
[PASCAL] Commutativity.

Hilbert, Theorem 42.  This is the point where sec. 14 is consumed:
the two right triangles realizing a * b and b * a share a vertex, and
special Pascal supplies the missing parallel.
-/
theorem hilbertPositiveSegmentMul_comm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMul Geo a b =
      hilbertPositiveSegmentMul Geo b a :=
  sorry

/-- [PASCAL] Associativity.  Hilbert, Theorem 42. -/
theorem hilbertPositiveSegmentMul_assoc
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b c : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMul Geo
        (hilbertPositiveSegmentMul Geo a b) c =
      hilbertPositiveSegmentMul Geo a
        (hilbertPositiveSegmentMul Geo b c) :=
  sorry

/--
[ELEM] Distributivity.

Laying off b and c consecutively on one leg and cutting by parallels.
No Pascal: only the parallel axiom and additivity of segment laying
off.  This is the law the `split` field of HilbertTriangleWeight needs.
-/
theorem hilbertPositiveSegmentMul_add
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b c : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMul Geo a
        (hilbertPositiveSegmentAdd Geo b c) =
      hilbertPositiveSegmentAdd Geo
        (hilbertPositiveSegmentMul Geo a b)
        (hilbertPositiveSegmentMul Geo a c) :=
  sorry

/-- [PASCAL] Cancellation, via commutativity and the order on segments. -/
theorem hilbertPositiveSegmentMul_left_cancel
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (a b c : HilbertPositiveSegmentClass Geo)
    (h : hilbertPositiveSegmentMul Geo a b =
           hilbertPositiveSegmentMul Geo a c) :
    b = c :=
  sorry

------------------------------------------------------------------------
-- Part 3.  The valuation target
--
-- HilbertScissorsValuation needs an AddCommMonoid, and
-- eq_of_equicomplementable needs cancellation.  Positive segment
-- classes have no zero, so one is adjoined.  The empty scissors term
-- maps to `none`.
------------------------------------------------------------------------

/-- Positive segment classes with a formal zero. -/
abbrev HilbertArea
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :=
  Option (HilbertPositiveSegmentClass Geo)

/--
[ELEM] The three laws are already available:
`hilbertPositiveSegmentAdd_comm`, `hilbertPositiveSegment_add_assoc`,
`hilbertPositiveSegment_add_right_cancel`.  Only the plumbing through
`Option` is new.
-/
noncomputable instance
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    AddCancelCommMonoid (HilbertArea Geo) :=
  sorry

------------------------------------------------------------------------
-- Part 4.  Base and altitude
------------------------------------------------------------------------

/--
`b` is the class of the side `B C` and `h` the class of the
perpendicular dropped from `A` to the line `B C`.
-/
def HilbertTriangleBaseAltitude
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (b h : HilbertPositiveSegmentClass Geo) : Prop :=
  sorry

/-- [ELEM] Every nondegenerate triangle has a base and an altitude. -/
theorem hilbertTriangleBaseAltitude_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hNoncol : ¬ Collinear Geo A B C) :
    ∃ b h : HilbertPositiveSegmentClass Geo,
      HilbertTriangleBaseAltitude Geo A B C b h :=
  sorry

/--
[PASCAL] The product of a base and its altitude does not depend on
which side is taken as base.

Hilbert, sec. 20, from the similarity of the two triangles cut off by
the altitudes, i.e. Theorem 41.  This is the second and last essential
use of proportion theory.
-/
theorem hilbertTriangleBaseAltitude_independent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (b h b' h' : HilbertPositiveSegmentClass Geo)
    (hbh : HilbertTriangleBaseAltitude Geo A B C b h)
    (hbh' : HilbertTriangleBaseAltitude Geo B C A b' h') :
    hilbertPositiveSegmentMul Geo b h =
      hilbertPositiveSegmentMul Geo b' h' :=
  sorry

------------------------------------------------------------------------
-- Part 5.  The area weight
--
-- Note: no halving.  Hilbert's 1/2 is needed only to compare triangles
-- with rectangles; for I.39 the product itself is enough.
------------------------------------------------------------------------

/--
The area of a formal triangle term: the product of a base and the
corresponding altitude, and `none` on degenerate terms.
-/
noncomputable def hilbertAreaOfTriangleTerm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (T : HilbertTriangleTerm Geo) :
    HilbertArea Geo :=
  sorry

/--
The area weight.

`split` reduces to `hilbertPositiveSegmentMul_add`, because the three
triangles share the altitude from `A` to the line `B C`.

`congruent` reduces to congruence of bases together with uniqueness of
the perpendicular, so congruent triangles have congruent altitudes.

Neither field needs Pascal directly; both consume Part 2.
-/
noncomputable def hilbertAreaWeight
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo] :
    HilbertTriangleWeight Geo (HilbertArea Geo) :=
  sorry

/-- [ELEM] A nondegenerate triangle has nonzero area. -/
theorem hilbertAreaWeight_pos
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C : Geo.Point)
    (hNoncol : ¬ Collinear Geo A B C) :
    (hilbertAreaWeight Geo).weight
        (hilbertTriangleTerm Geo A B C) ≠ 0 :=
  sorry

------------------------------------------------------------------------
-- Part 6.  Discharge
--
-- Replaces the axiom in HilbertScissorsPositivity.lean.  Once Parts
-- 1-5 are in place this proof is complete as written; nothing further
-- about triangles is required.
------------------------------------------------------------------------

theorem hilbert_scissors_triangle_positive'
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertEuclideanPlane Geo]
    (P : HilbertScissorsTerm Geo)
    (A B C : Geo.Point)
    (hNoncol : ¬ Collinear Geo A B C) :
    ¬ HilbertScissorsEquicomplementable Geo
        (P + hilbertScissorsTriangle Geo A B C)
        P := by

  intro hEq

  have hVal :=
    HilbertScissorsValuation.eq_of_equicomplementable
      Geo
      (HilbertTriangleWeight.toValuation Geo (hilbertAreaWeight Geo))
      hEq

  rw [(HilbertTriangleWeight.toValuation
        Geo (hilbertAreaWeight Geo)).map_add] at hVal

  have hZero :
      (HilbertTriangleWeight.toValuation
          Geo (hilbertAreaWeight Geo)).value
        (hilbertScissorsTriangle Geo A B C) = 0 := by
    have := hVal.trans (add_zero _).symm
    exact add_left_cancel this

  exact
    hilbertAreaWeight_pos Geo A B C hNoncol
      (by simpa [HilbertTriangleWeight.toValuation,
                 hilbertScissorsTriangle] using hZero)

#print axioms hilbert_scissors_triangle_positive'

end Geometry

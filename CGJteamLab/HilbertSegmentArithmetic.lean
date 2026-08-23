import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
An oriented pair of endpoints used only as a representative
of a segment congruence class.

Endpoint orientation disappears after quotienting by congruence.
-/
abbrev HilbertSegmentRep :=
  Geo.Point × Geo.Point


/--
Congruence of segments defines an equivalence relation on endpoint pairs.
-/
def hilbertSegmentSetoid
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    Setoid (HilbertSegmentRep Geo) where

  r := fun s t =>
    Geo.Congruent s.1 s.2 t.1 t.2

  iseqv := by
    constructor

    · intro s
      exact
        hilbert_congruent_reflexive
          Geo s.1 s.2

    · intro s t h
      exact
        hilbert_congruent_symmetry
          Geo
          s.1 s.2
          t.1 t.2
          h

    · intro s t q hst htq
      exact
        hilbert_congruent_transitivity
          Geo
          s.1 s.2
          t.1 t.2
          q.1 q.2
          hst
          htq


/--
A Hilbert segment length is a congruence class of segments.
-/
abbrev HilbertSegmentClass
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :=
  Quotient (hilbertSegmentSetoid Geo)


/--
The congruence class represented by the segment AB.
-/
def hilbertSegmentClassOf
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point) :
    HilbertSegmentClass Geo :=
  Quotient.mk
    (hilbertSegmentSetoid Geo)
    (A, B)

/--
Two segments determine the same Hilbert segment class
iff they are congruent.
-/
theorem hilbertSegmentClassOf_eq_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point) :
    hilbertSegmentClassOf Geo A B =
        hilbertSegmentClassOf Geo C D
      <->
    Geo.Congruent A B C D := by

  constructor

  · intro h
    exact
      Quotient.exact h

  · intro h
    exact
      Quotient.sound h

/--
Reversing the endpoints does not change a Hilbert segment class.
-/
theorem hilbertSegmentClassOf_swap
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point) :
    hilbertSegmentClassOf Geo A B =
      hilbertSegmentClassOf Geo B A := by

  apply
    (hilbertSegmentClassOf_eq_iff
      Geo A B B A).2

  exact
    (Geo.congruent_reverse_second
      A B A B).mp
      (hilbert_congruent_reflexive Geo A B)

/--
All degenerate segments determine the same segment class.
-/
theorem hilbertSegmentClassOf_null_eq
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point) :
    hilbertSegmentClassOf Geo A A =
      hilbertSegmentClassOf Geo B B := by

  apply
    (hilbertSegmentClassOf_eq_iff
      Geo A A B B).2

  exact
    bookZero_nullSegment2
      Geo A B

/--
A nondegenerate segment representative.
-/
abbrev HilbertPositiveSegmentRep :=
  {s : HilbertSegmentRep Geo // Ne s.1 s.2}


/--
Congruence restricted to nondegenerate segment representatives.
-/
def hilbertPositiveSegmentSetoid
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    Setoid (HilbertPositiveSegmentRep Geo) where

  r := fun s t =>
    Geo.Congruent
      s.val.1 s.val.2
      t.val.1 t.val.2

  iseqv := by
    constructor

    · intro s
      exact
        hilbert_congruent_reflexive
          Geo s.val.1 s.val.2

    · intro s t h
      exact
        hilbert_congruent_symmetry
          Geo
          s.val.1 s.val.2
          t.val.1 t.val.2
          h

    · intro s t q hst htq
      exact
        hilbert_congruent_transitivity
          Geo
          s.val.1 s.val.2
          t.val.1 t.val.2
          q.val.1 q.val.2
          hst
          htq


/--
A positive Hilbert segment length is a congruence class
of nondegenerate segments.
-/
abbrev HilbertPositiveSegmentClass
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :=
  Quotient (hilbertPositiveSegmentSetoid Geo)


/--
The positive segment class represented by AB.
-/
def hilbertPositiveSegmentClassOf
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    HilbertPositiveSegmentClass Geo :=
  Quotient.mk
    (hilbertPositiveSegmentSetoid Geo)
    ⟨(A, B), hAB⟩

/--
Geometric addition of positive segment classes.

The relation `HilbertPositiveSegmentSum Geo a b c` means that
there is a collinear configuration A-B-C such that

  AB represents a,
  BC represents b,
  AC represents c.
-/
def HilbertPositiveSegmentSum
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo) : Prop :=
  ∃ A B C : Geo.Point,
    ∃ hABC : Geo.Between A B C,
      hilbertPositiveSegmentClassOf
          Geo A B
          (HilbertOrder.between_incidence A B C hABC).1 =
        a ∧
      hilbertPositiveSegmentClassOf
          Geo B C
          (HilbertOrder.between_incidence A B C hABC).2.1 =
        b ∧
      hilbertPositiveSegmentClassOf
          Geo A C
          (HilbertOrder.between_incidence A B C hABC).2.2.1 =
        c

/--
Every strict betweenness configuration realizes addition
of the two adjacent positive segment classes.
-/
theorem hilbertPositiveSegmentSum_of_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    HilbertPositiveSegmentSum
      Geo
      (hilbertPositiveSegmentClassOf
        Geo A B
        (HilbertOrder.between_incidence A B C hABC).1)
      (hilbertPositiveSegmentClassOf
        Geo B C
        (HilbertOrder.between_incidence A B C hABC).2.1)
      (hilbertPositiveSegmentClassOf
        Geo A C
        (HilbertOrder.between_incidence A B C hABC).2.2.1) := by

  exact
    ⟨A, B, C, hABC, rfl, rfl, rfl⟩

/--
The sum relation is single-valued in its third argument.
-/
theorem hilbertPositiveSegmentSum_unique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hc : HilbertPositiveSegmentSum Geo a b c)
    (hd : HilbertPositiveSegmentSum Geo a b d) :
    c = d := by

  rcases hc with
    ⟨A, B, C, hABC, hABa, hBCb, hACc⟩

  rcases hd with
    ⟨A', B', C', hA'B'C',
      hA'B'a, hB'C'b, hA'C'd⟩

  have hAB :
      Ne A B :=
    (HilbertOrder.between_incidence
      A B C hABC).1

  have hBC :
      Ne B C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.1

  have hAC :
      Ne A C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.2.1

  have hA'B' :
      Ne A' B' :=
    (HilbertOrder.between_incidence
      A' B' C' hA'B'C').1

  have hB'C' :
      Ne B' C' :=
    (HilbertOrder.between_incidence
      A' B' C' hA'B'C').2.1

  have hA'C' :
      Ne A' C' :=
    (HilbertOrder.between_incidence
      A' B' C' hA'B'C').2.2.1

  have hABeq :
      hilbertPositiveSegmentClassOf Geo A B hAB =
        hilbertPositiveSegmentClassOf Geo A' B' hA'B' :=
    hABa.trans hA'B'a.symm

  have hBCeq :
      hilbertPositiveSegmentClassOf Geo B C hBC =
        hilbertPositiveSegmentClassOf Geo B' C' hB'C' :=
    hBCb.trans hB'C'b.symm

  have hABcong :
      Geo.Congruent A B A' B' := by
    exact Quotient.exact hABeq

  have hBCcong :
      Geo.Congruent B C B' C' := by
    exact Quotient.exact hBCeq

  have hACcong :
      Geo.Congruent A C A' C' :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A B C
      A' B' C'
      hABC
      hA'B'C'
      hABcong
      hBCcong

  have hACeq :
      hilbertPositiveSegmentClassOf Geo A C hAC =
        hilbertPositiveSegmentClassOf Geo A' C' hA'C' := by
    exact Quotient.sound hACcong

  calc
    c =
        hilbertPositiveSegmentClassOf Geo A C hAC :=
      hACc.symm
    _ =
        hilbertPositiveSegmentClassOf Geo A' C' hA'C' :=
      hACeq
    _ = d :=
      hA'C'd

end Geometry

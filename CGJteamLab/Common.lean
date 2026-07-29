import Std

universe u

/--
Two ordered pairs represent the same unordered pair when they are equal
or differ only by swapping their entries.
-/
inductive UnorderedPairRel {alpha : Type u} :
    (alpha × alpha) -> (alpha × alpha) -> Prop where
  | direct (a b : alpha) :
      UnorderedPairRel (a, b) (a, b)
  | swapped (a b : alpha) :
      UnorderedPairRel (a, b) (b, a)

instance unorderedPairSetoid (alpha : Type u) :
    Setoid (alpha × alpha) where
  r := UnorderedPairRel
  iseqv := by
    constructor
    · intro p
      rcases p with ⟨a, b⟩
      exact UnorderedPairRel.direct a b
    · intro p q h
      cases h with
      | direct a b =>
          exact UnorderedPairRel.direct a b
      | swapped a b =>
          exact UnorderedPairRel.swapped b a
    · intro p q r hpq hqr
      cases hpq with
      | direct _ _ =>
          exact hqr
      | swapped a b =>
          cases hqr with
          | direct _ _ =>
              exact UnorderedPairRel.swapped a b
          | swapped _ _ =>
              exact UnorderedPairRel.direct a b

/-- An unordered pair, implemented as ordered pairs modulo swapping. -/
def UnorderedPair (alpha : Type u) : Type u :=
  Quotient (unorderedPairSetoid alpha)

namespace UnorderedPair

/-- Construct an unordered pair from two elements. -/
def mk {alpha : Type u} (a b : alpha) : UnorderedPair alpha :=
  Quotient.mk' (a, b)

/-- Swapping the two entries does not change an unordered pair. -/
theorem eq_swap {alpha : Type u} (a b : alpha) :
    mk a b = mk b a := by
  apply Quotient.sound
  exact UnorderedPairRel.swapped a b

end UnorderedPair

namespace Common

universe v

/-- The unordered pair determined by two elements. -/
def Segment {Point : Type v} (A B : Point) : UnorderedPair Point :=
  UnorderedPair.mk A B

/-- Lift a binary relation on unordered pairs to a four-point relation. -/
def PairRelation
    {Point : Type v}
    (R : UnorderedPair Point -> UnorderedPair Point -> Prop)
    (A B C D : Point) : Prop :=
  R (Segment A B) (Segment C D)

theorem segment_swap
    {Point : Type v}
    (A B : Point) :
    Segment A B = Segment B A :=
  UnorderedPair.eq_swap A B

theorem pairRelation_reverse_first
    {Point : Type v}
    (R : UnorderedPair Point -> UnorderedPair Point -> Prop)
    (A B C D : Point) :
    PairRelation R A B C D <->
    PairRelation R B A C D := by
  unfold PairRelation Segment
  rw [UnorderedPair.eq_swap A B]

theorem pairRelation_reverse_second
    {Point : Type v}
    (R : UnorderedPair Point -> UnorderedPair Point -> Prop)
    (A B C D : Point) :
    PairRelation R A B C D <->
    PairRelation R A B D C := by
  unfold PairRelation Segment
  rw [UnorderedPair.eq_swap C D]

end Common

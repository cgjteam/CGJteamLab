namespace Geometry

universe u

inductive UnorderedPairRel {α : Type u} :
    (α × α) → (α × α) → Prop
  | direct (a b : α) :
      UnorderedPairRel (a, b) (a, b)
  | swapped (a b : α) :
      UnorderedPairRel (a, b) (b, a)

instance unorderedPairSetoid (α : Type u) :
    Setoid (α × α) where
  r := UnorderedPairRel
  iseqv := by
    constructor
    · intro x
      cases x with
      | mk a b =>
          exact UnorderedPairRel.direct a b
    · intro x y h
      cases h with
      | direct a b =>
          exact UnorderedPairRel.direct a b
      | swapped a b =>
          exact UnorderedPairRel.swapped b a
    · intro x y z hxy hyz
      cases hxy <;> cases hyz
      · exact UnorderedPairRel.direct _ _
      · exact UnorderedPairRel.swapped _ _
      · exact UnorderedPairRel.swapped _ _
      · exact UnorderedPairRel.direct _ _

def UnorderedPair (α : Type u) :=
  Quotient (unorderedPairSetoid α)
def UnorderedPair.mk {α : Type u} (a b : α) :
    UnorderedPair α :=
  Quotient.mk _ (a, b)

theorem UnorderedPair.eq_swap {α : Type u}
    (a b : α) :
    UnorderedPair.mk a b =
    UnorderedPair.mk b a :=
  Quotient.sound (UnorderedPairRel.swapped a b)

end Geometry

import CGJteamLab.HilbertInterfaceV

namespace Geometry

universe u v w

/-!
# Generic Eudoxus magnitude layer

This file extracts the logical core of Euclid V.Def.5 from the
segment-specific implementation in `HilbertInterfaceV`.

The key point is that equality of ratios may compare two different
kinds of magnitudes:

    a : b = c : d

where `a,b` belong to one magnitude kind and `c,d` belong to another.

For Euclid XI.25 the intended specialization is:

    base magnitude : base magnitude
      =
    solid magnitude : solid magnitude.

No numerical measure, area function, volume function, coordinates,
real numbers, or field structure is introduced here.

Only the data actually used by V.Def.5 are retained:

1. strict comparison inside each magnitude kind;
2. positive natural multiples inside each magnitude kind.

The natural-number convention is intentionally the same as in
`HilbertInterfaceV`: index `n` denotes the `(n+1)`-fold positive
multiple. Thus zero magnitudes are not needed.
-/

/--
Minimal data needed to state Euclid V.Def.5 for one kind of positive
magnitude.

No algebraic laws are imposed here. Those belong to the concrete
magnitude implementation. This structure is only the comparison
interface consumed by the Eudoxus definition.
-/
structure EudoxusMagnitude (M : Type u) where
  less : M -> M -> Prop
  multiple : Nat -> M -> M

/--
Heterogeneous Eudoxus equality of ratios.

The first ratio `a:b` lives in magnitude system `A`.
The second ratio `c:d` lives in magnitude system `B`.

For every pair of positive natural multiples, the three possible
comparisons agree:

    m*a < n*b,
    m*a = n*b,
    n*b < m*a.

This is the direct abstract form of Euclid V.Def.5.
-/
def EudoxusProportionBetween
    {M : Type u}
    {N : Type v}
    (A : EudoxusMagnitude M)
    (B : EudoxusMagnitude N)
    (a b : M)
    (c d : N) : Prop :=
  forall m n : Nat,
    (A.less
        (A.multiple m a)
        (A.multiple n b)
      <->
     B.less
        (B.multiple m c)
        (B.multiple n d))
    /\
    (A.multiple m a = A.multiple n b
      <->
     B.multiple m c = B.multiple n d)
    /\
    (A.less
        (A.multiple n b)
        (A.multiple m a)
      <->
     B.less
        (B.multiple n d)
        (B.multiple m c))

/--
Reflexivity for a ratio inside one magnitude system.
-/
theorem eudoxusProportionBetween_refl
    {M : Type u}
    (A : EudoxusMagnitude M)
    (a b : M) :
    EudoxusProportionBetween A A a b a b := by
  intro m n
  exact
    And.intro Iff.rfl
      (And.intro Iff.rfl Iff.rfl)

/--
Symmetry of heterogeneous Eudoxus proportion.
-/
theorem eudoxusProportionBetween_symm
    {M : Type u}
    {N : Type v}
    (A : EudoxusMagnitude M)
    (B : EudoxusMagnitude N)
    (a b : M)
    (c d : N)
    (h :
      EudoxusProportionBetween A B a b c d) :
    EudoxusProportionBetween B A c d a b := by
  intro m n
  have hmn := h m n
  exact
    And.intro hmn.1.symm
      (And.intro hmn.2.1.symm hmn.2.2.symm)

/--
Transitivity through a third magnitude kind.

This is the fully heterogeneous analogue of Euclid V.11 at the level
of ratio equality.
-/
theorem eudoxusProportionBetween_trans
    {M : Type u}
    {N : Type v}
    {P : Type w}
    (A : EudoxusMagnitude M)
    (B : EudoxusMagnitude N)
    (C : EudoxusMagnitude P)
    (a b : M)
    (c d : N)
    (e f : P)
    (hAB :
      EudoxusProportionBetween A B a b c d)
    (hBC :
      EudoxusProportionBetween B C c d e f) :
    EudoxusProportionBetween A C a b e f := by
  intro m n

  have h1 := hAB m n
  have h2 := hBC m n

  exact
    And.intro
      (Iff.trans h1.1 h2.1)
      (And.intro
        (Iff.trans h1.2.1 h2.2.1)
        (Iff.trans h1.2.2 h2.2.2))

/--
A generic transport criterion for Eudoxus proportion.

Suppose `f` sends magnitudes of kind `A` to magnitudes of kind `B`,
commutes with positive natural multiples, preserves and reflects strict
comparison, and is injective. Then

    a : b = f(a) : f(b)

in the Eudoxus sense.

This is the abstract pattern expected in Euclid XI.25: a base
magnitude and the corresponding solid magnitude have matching
multiple-comparison behavior.
-/
theorem eudoxusProportionBetween_of_transport
    {M : Type u}
    {N : Type v}
    (A : EudoxusMagnitude M)
    (B : EudoxusMagnitude N)
    (f : M -> N)
    (hMultiple :
      forall n x,
        f (A.multiple n x) =
          B.multiple n (f x))
    (hLess :
      forall x y,
        A.less x y <-> B.less (f x) (f y))
    (hInjective : Function.Injective f)
    (a b : M) :
    EudoxusProportionBetween
      A B
      a b
      (f a) (f b) := by

  intro m n

  have hLessForward :
      A.less
          (A.multiple m a)
          (A.multiple n b)
        <->
      B.less
          (B.multiple m (f a))
          (B.multiple n (f b)) := by

    calc
      A.less
          (A.multiple m a)
          (A.multiple n b)
        <->
      B.less
          (f (A.multiple m a))
          (f (A.multiple n b)) := by
            exact hLess
              (A.multiple m a)
              (A.multiple n b)

      _ <->
      B.less
          (B.multiple m (f a))
          (B.multiple n (f b)) := by
            rw [
              hMultiple m a,
              hMultiple n b
            ]

  have hEq :
      A.multiple m a =
          A.multiple n b
        <->
      B.multiple m (f a) =
          B.multiple n (f b) := by

    constructor

    case mp =>
      intro h
      have hf :
          f (A.multiple m a) =
            f (A.multiple n b) :=
        congrArg f h
      simpa [
        hMultiple m a,
        hMultiple n b
      ] using hf

    case mpr =>
      intro h
      apply hInjective
      simpa [
        hMultiple m a,
        hMultiple n b
      ] using h

  have hLessReverse :
      A.less
          (A.multiple n b)
          (A.multiple m a)
        <->
      B.less
          (B.multiple n (f b))
          (B.multiple m (f a)) := by

    calc
      A.less
          (A.multiple n b)
          (A.multiple m a)
        <->
      B.less
          (f (A.multiple n b))
          (f (A.multiple m a)) := by
            exact hLess
              (A.multiple n b)
              (A.multiple m a)

      _ <->
      B.less
          (B.multiple n (f b))
          (B.multiple m (f a)) := by
            rw [
              hMultiple n b,
              hMultiple m a
            ]

  exact
    And.intro hLessForward
      (And.intro hEq hLessReverse)

------------------------------------------------------------------------
-- Bridge to the existing segment-specific Book V implementation
------------------------------------------------------------------------

universe z

variable (Geo : Geometry.Geo.{z})

/--
The existing positive Hilbert segment classes, viewed as one generic
Eudoxus magnitude kind.

This is only a wrapper around the already established definitions in
`HilbertInterfaceV`.
-/
noncomputable def hilbertPositiveSegmentEudoxusMagnitude
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    EudoxusMagnitude
      (HilbertPositiveSegmentClass Geo) where
  less :=
    HilbertPositiveSegmentLess Geo
  multiple :=
    hilbertPositiveSegmentMultiple Geo

/--
The existing segment-specific `HilbertEudoxusProportion` is definitionally
the homogeneous specialization of the generic heterogeneous definition.

This theorem is the compatibility bridge: no old Book V theorem needs to
be rewritten in order to use the new generic layer.
-/
theorem hilbertEudoxusProportion_iff_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo) :
    HilbertEudoxusProportion Geo a b c d
      <->
    EudoxusProportionBetween
      (hilbertPositiveSegmentEudoxusMagnitude
        (Geo := Geo))
      (hilbertPositiveSegmentEudoxusMagnitude
        (Geo := Geo))
      a b c d := by
  rfl

end Geometry

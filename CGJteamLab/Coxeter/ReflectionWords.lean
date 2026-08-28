import CGJteamLab.Coxeter.Reflection

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
The product of two Hilbert line-reflection generators.

Our convention is:

    reflectionProduct axis1 axis2 P
      = r_axis2 (r_axis1 P).

Thus `axis1` acts first and `axis2` acts second.
-/
noncomputable def reflectionProduct
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo) :
    Equiv Geo.Point Geo.Point :=
  (lineReflectEquiv Geo axis1).trans
    (lineReflectEquiv Geo axis2)


@[simp]
theorem reflectionProduct_apply
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (P : Geo.Point) :
    reflectionProduct Geo axis1 axis2 P =
      lineReflect Geo axis2
        (lineReflect Geo axis1 P) := by
  rfl


/--
The product of a reflection generator with itself is the identity
on points.
-/
@[simp]
theorem reflectionProduct_self_apply
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point) :
    reflectionProduct Geo axis axis P = P := by
  exact lineReflect_involutive Geo axis P

/--
The inverse of a product of two reflection generators acts by reversing
the order of the generators.
-/
@[simp]
theorem reflectionProduct_symm_apply
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (P : Geo.Point) :
    (reflectionProduct Geo axis1 axis2).symm P =
      reflectionProduct Geo axis2 axis1 P := by
  rfl


/--
As permutations, the inverse of `r_axis2 r_axis1` is
`r_axis1 r_axis2`.
-/
theorem reflectionProduct_symm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo) :
    (reflectionProduct Geo axis1 axis2).symm =
      reflectionProduct Geo axis2 axis1 := by
  apply Equiv.ext
  intro P
  rfl

/--
The n-fold iterate of the product of two reflection generators.

This is the word

    (r_axis2 r_axis1)^n

with the convention fixed by `reflectionProduct`.
-/
noncomputable def reflectionProductPow
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (n : Nat) :
    Equiv Geo.Point Geo.Point :=
  Nat.rec
    (Equiv.refl Geo.Point)
    (fun _ w =>
      w.trans
        (reflectionProduct Geo axis1 axis2))
    n


@[simp]
theorem reflectionProductPow_zero
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo) :
    reflectionProductPow Geo axis1 axis2 0 =
      Equiv.refl Geo.Point := by
  rfl


@[simp]
theorem reflectionProductPow_succ
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (n : Nat) :
    reflectionProductPow Geo axis1 axis2 (Nat.succ n) =
      (reflectionProductPow Geo axis1 axis2 n).trans
        (reflectionProduct Geo axis1 axis2) := by
  rfl


@[simp]
theorem reflectionProductPow_one
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo) :
    reflectionProductPow Geo axis1 axis2 1 =
      reflectionProduct Geo axis1 axis2 := by
  apply Equiv.ext
  intro P
  rfl


/--
The pair of reflection generators satisfies the Coxeter relation
of exponent p:

    (r_axis2 r_axis1)^p = 1.
-/
def ReflectionPairRelation
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (p : Nat) : Prop :=
  reflectionProductPow Geo axis1 axis2 p =
    Equiv.refl Geo.Point


/--
`ReflectionPairExactPeriod Geo axis1 axis2 p` means that `p` is the
least positive exponent for which the reflection product is the identity.

This is stronger than `ReflectionPairRelation`, which only states that
the displayed exponent is satisfied.
-/
def ReflectionPairExactPeriod
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (p : Nat) : Prop :=
  0 < p /\
  ReflectionPairRelation Geo axis1 axis2 p /\
  forall q : Nat,
    0 < q ->
    q < p ->
    Not (ReflectionPairRelation Geo axis1 axis2 q)


/--
Swapping the two reflection axes conjugates every power of their product
by reflection in `axis1`.

With the convention

    reflectionProduct axis1 axis2 = r_axis2 r_axis1,

the statement is

    (r_axis1 r_axis2)^n
      = r_axis1 (r_axis2 r_axis1)^n r_axis1

pointwise.
-/
theorem reflectionProductPow_swap_apply
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (n : Nat)
    (P : Geo.Point) :
    reflectionProductPow Geo axis2 axis1 n P =
      lineReflect Geo axis1
        (reflectionProductPow Geo axis1 axis2 n
          (lineReflect Geo axis1 P)) := by

  induction n with

  | zero =>
      change
        P =
          lineReflect Geo axis1
            (lineReflect Geo axis1 P)
      exact
        (lineReflect_involutive
          Geo axis1 P).symm

  | succ n ih =>
      change
        lineReflect Geo axis1
          (lineReflect Geo axis2
            (reflectionProductPow Geo axis2 axis1 n P)) =
        lineReflect Geo axis1
          (lineReflect Geo axis2
            (lineReflect Geo axis1
              (reflectionProductPow Geo axis1 axis2 n
                (lineReflect Geo axis1 P))))

      rw [ih]


/--
The satisfied pair relation is symmetric in the two reflection axes.

Thus

    (r_axis2 r_axis1)^p = 1

implies

    (r_axis1 r_axis2)^p = 1.

The proof uses the conjugacy formula above, not a numerical angle argument.
-/
theorem reflectionPairRelation_symm
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (p : Nat)
    (hRel :
      ReflectionPairRelation Geo axis1 axis2 p) :
    ReflectionPairRelation Geo axis2 axis1 p := by

  unfold ReflectionPairRelation at hRel
  unfold ReflectionPairRelation

  apply Equiv.ext
  intro P

  rw [
    reflectionProductPow_swap_apply
      Geo axis1 axis2 p P
  ]

  have hAtReflected :
      reflectionProductPow Geo axis1 axis2 p
          (lineReflect Geo axis1 P) =
        lineReflect Geo axis1 P := by

    have hAt :=
      congrArg
        (fun f : Equiv Geo.Point Geo.Point =>
          f (lineReflect Geo axis1 P))
        hRel

    simpa using hAt

  rw [hAtReflected]

  exact
    lineReflect_involutive
      Geo axis1 P


/--
Exact period is symmetric in the two reflection axes.

This removes the orientation artifact caused by the implementation
convention for `reflectionProduct`.
-/
theorem reflectionPairExactPeriod_symm
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (p : Nat)
    (hExact :
      ReflectionPairExactPeriod Geo axis1 axis2 p) :
    ReflectionPairExactPeriod Geo axis2 axis1 p := by

  refine
    And.intro
      hExact.1
      ?_

  refine
    And.intro
      (reflectionPairRelation_symm
        Geo
        axis1 axis2
        p
        hExact.2.1)
      ?_

  intro q hqPos hqLt hRelSwap

  have hRelOriginal :
      ReflectionPairRelation Geo axis1 axis2 q :=
    reflectionPairRelation_symm
      Geo
      axis2 axis1
      q
      hRelSwap

  exact
    hExact.2.2
      q
      hqPos
      hqLt
      hRelOriginal

end Geometry

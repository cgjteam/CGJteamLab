import CGJteamLab.Coxeter.CoxeterRelations

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Helper for arbitrary finite Coxeter period.

If the pair relation of exponent p holds, then the p-th power of the
reflection product fixes every point.

This is only a bridge from the equality of permutations stored in
ReflectionPairRelation to its pointwise form.
-/
theorem coxeter_general_relation_fixes_point
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (p : Nat)
    (hRel :
      ReflectionPairRelation Geo axis1 axis2 p)
    (P : Geo.Point) :
    reflectionProductPow Geo axis1 axis2 p P = P := by

  unfold ReflectionPairRelation at hRel

  have hAtP :=
    congrArg
      (fun f : Equiv Geo.Point Geo.Point => f P)
      hRel

  simpa using hAtP

/--
Helper for arbitrary finite Coxeter period.

If reflection in `middle` transports the carrier of `left` exactly onto
the carrier of `right`, then the products attached to the two consecutive
pairs are equal:

    r_middle r_left = r_right r_middle.

In the implementation convention this is

    reflectionProduct left middle =
      reflectionProduct middle right.

This is the local telescoping identity needed for a general finite
carrier chain.
-/
theorem coxeter_general_adjacent_products_of_carrier_transport
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (left middle right : ReflectionAxis Geo)
    (hMap :
      ReflectionMapsLine
        Geo
        middle
        left.carrier
        right.carrier) :
    reflectionProduct Geo left middle =
      reflectionProduct Geo middle right := by

  apply Equiv.ext
  intro P

  rw [
    reflectionProduct_apply,
    reflectionProduct_apply
  ]

  have hConj :=
    lineReflect_conjugation_pointwise
      Geo
      middle
      left
      right
      hMap
      (lineReflect Geo middle P)

  rw [
    lineReflect_involutive
      Geo
      middle
      P
  ] at hConj

  exact hConj

/--
Helper for arbitrary finite Coxeter period.

This is the local telescoping step for powers of a fixed reflection
product.

Assume that the fixed product

    r_axis1 r_axis0

is also the adjacent product

    r_next r_current,

and that its n-th power has already telescoped to

    r_current r_axis0.

Then the (n+1)-st power telescopes to

    r_next r_axis0.

No geometry is used here beyond involutivity of reflection.
-/
theorem coxeter_general_power_telescope_step
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis0 axis1 current next : ReflectionAxis Geo)
    (n : Nat)
    (hPair :
      reflectionProduct Geo axis0 axis1 =
        reflectionProduct Geo current next)
    (P : Geo.Point)
    (hPow :
      reflectionProductPow Geo axis0 axis1 n P =
        lineReflect Geo current
          (lineReflect Geo axis0 P)) :
    reflectionProductPow
        Geo axis0 axis1 (Nat.succ n) P =
      lineReflect Geo next
        (lineReflect Geo axis0 P) := by

  rw [reflectionProductPow_succ]

  change
    reflectionProduct Geo axis0 axis1
        (reflectionProductPow Geo axis0 axis1 n P) =
      lineReflect Geo next
        (lineReflect Geo axis0 P)

  rw [hPair, hPow]

  change
    lineReflect Geo next
        (lineReflect Geo current
          (lineReflect Geo current
            (lineReflect Geo axis0 P))) =
      lineReflect Geo next
        (lineReflect Geo axis0 P)

  rw [
    lineReflect_involutive
      Geo
      current
      (lineReflect Geo axis0 P)
  ]

/--
Helper for arbitrary finite Coxeter period.

Suppose reflection in each axis of a sequence transports the preceding
carrier exactly onto the following carrier:

    r_axis_(n+1)(axis_n) = axis_(n+2).

Then all consecutive reflection products are equal to the initial one.

This converts the geometric carrier-transport recurrence into the
algebraic hypothesis used by the telescoping argument.
-/
theorem coxeter_general_products_constant_of_carrier_chain
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (hMap :
      forall n : Nat,
        ReflectionMapsLine
          Geo
          (axis (Nat.succ n))
          (axis n).carrier
          (axis (Nat.succ (Nat.succ n))).carrier) :
    forall n : Nat,
      reflectionProduct Geo (axis 0) (axis 1) =
        reflectionProduct
          Geo
          (axis n)
          (axis (Nat.succ n)) := by

  intro n

  induction n with

  | zero =>
      rfl

  | succ n ih =>
      calc
        reflectionProduct Geo (axis 0) (axis 1) =
            reflectionProduct
              Geo
              (axis n)
              (axis (Nat.succ n)) := ih

        _ =
            reflectionProduct
              Geo
              (axis (Nat.succ n))
              (axis (Nat.succ (Nat.succ n))) :=
          coxeter_general_adjacent_products_of_carrier_transport
            Geo
            (axis n)
            (axis (Nat.succ n))
            (axis (Nat.succ (Nat.succ n)))
            (hMap n)

/--
Helper for arbitrary finite Coxeter period.

If two canonical line reflections agree pointwise, then their carriers
are the same line.

The proof uses two distinct points stored in the first reflection axis.
They are fixed by the first reflection, hence also by the second one.
Therefore both lie on the second carrier, and line uniqueness identifies
the two carriers.
-/
theorem coxeter_general_carriers_eq_of_reflections_pointwise_eq
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hEq :
      forall P : Geo.Point,
        lineReflect Geo axis1 P =
          lineReflect Geo axis2 P) :
    axis1.carrier = axis2.carrier := by

  have hFixA1 :
      lineReflect Geo axis1 axis1.A =
        axis1.A :=
    lineReflect_fixed_of_on_axis
      Geo
      axis1
      axis1.A
      axis1.hA

  have hFixA2 :
      lineReflect Geo axis2 axis1.A =
        axis1.A := by
    rw [<- hEq axis1.A]
    exact hFixA1

  have hSpecA2 :
      IsLineReflection
        Geo
        axis2
        axis1.A
        axis1.A := by
    have hSpec :=
      lineReflect_spec
        Geo
        axis2
        axis1.A

    rw [hFixA2] at hSpec
    exact hSpec

  have hA2 :
      HilbertIncidence.OnLine
        axis1.A
        axis2.carrier :=
    (line_reflection_fixed_iff_on_axis
      Geo
      axis2
      axis1.A).1
      hSpecA2

  have hFixB1 :
      lineReflect Geo axis1 axis1.B =
        axis1.B :=
    lineReflect_fixed_of_on_axis
      Geo
      axis1
      axis1.B
      axis1.hB

  have hFixB2 :
      lineReflect Geo axis2 axis1.B =
        axis1.B := by
    rw [<- hEq axis1.B]
    exact hFixB1

  have hSpecB2 :
      IsLineReflection
        Geo
        axis2
        axis1.B
        axis1.B := by
    have hSpec :=
      lineReflect_spec
        Geo
        axis2
        axis1.B

    rw [hFixB2] at hSpec
    exact hSpec

  have hB2 :
      HilbertIncidence.OnLine
        axis1.B
        axis2.carrier :=
    (line_reflection_fixed_iff_on_axis
      Geo
      axis2
      axis1.B).1
      hSpecB2

  exact
    HilbertPlaneIncidence.line_unique
      axis1.A
      axis1.B
      axis1.hAB
      axis1.carrier
      axis2.carrier
      axis1.hA
      axis1.hB
      hA2
      hB2

/--
Helper for arbitrary finite Coxeter period.

To telescope powers only up to p, it is enough to know equality of the
consecutive reflection products only below p.

This is the finite telescoping version needed below a fixed bound p.
-/
theorem coxeter_general_power_telescope_up_to
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (hPair :
      forall n : Nat,
        n < p ->
        reflectionProduct Geo (axis 0) (axis 1) =
          reflectionProduct
            Geo
            (axis n)
            (axis (Nat.succ n)))
    (n : Nat)
    (P : Geo.Point) :
    n <= p ->
    reflectionProductPow
        Geo
        (axis 0)
        (axis 1)
        n
        P =
      lineReflect Geo (axis n)
        (lineReflect Geo (axis 0) P) := by

  induction n with

  | zero =>
      intro hn

      change
        P =
          lineReflect Geo (axis 0)
            (lineReflect Geo (axis 0) P)

      exact
        (lineReflect_involutive
          Geo
          (axis 0)
          P).symm

  | succ n ih =>
      intro hn

      have hnLt :
          n < p :=
        Nat.lt_of_succ_le hn

      have hnLe :
          n <= p :=
        Nat.le_trans
          (Nat.le_succ n)
          hn

      exact
        coxeter_general_power_telescope_step
          Geo
          (axis 0)
          (axis 1)
          (axis n)
          (axis (Nat.succ n))
          n
          (hPair n hnLt)
          P
          (ih hnLe)

/--
Helper for arbitrary finite Coxeter period.

This is the finite carrier-return version needed below a fixed bound p.

Assume equality of consecutive reflection products only below p. If
q <= p and the q-th power of the initial product is the identity, then
the q-th axis has the same carrier as the initial axis.
-/
theorem coxeter_general_carrier_returns_of_relation_up_to
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (hPair :
      forall n : Nat,
        n < p ->
        reflectionProduct Geo (axis 0) (axis 1) =
          reflectionProduct
            Geo
            (axis n)
            (axis (Nat.succ n)))
    (q : Nat)
    (hq :
      q <= p)
    (hRel :
      ReflectionPairRelation
        Geo
        (axis 0)
        (axis 1)
        q) :
    (axis q).carrier = (axis 0).carrier := by

  apply
    coxeter_general_carriers_eq_of_reflections_pointwise_eq
      Geo
      (axis q)
      (axis 0)

  intro X

  let P : Geo.Point :=
    lineReflect Geo (axis 0) X

  have hPow :
      reflectionProductPow
          Geo
          (axis 0)
          (axis 1)
          q
          P =
        lineReflect Geo (axis q)
          (lineReflect Geo (axis 0) P) :=
    coxeter_general_power_telescope_up_to
      Geo
      axis
      p
      hPair
      q
      P
      hq

  have hFix :
      reflectionProductPow
          Geo
          (axis 0)
          (axis 1)
          q
          P =
        P :=
    coxeter_general_relation_fixes_point
      Geo
      (axis 0)
      (axis 1)
      q
      hRel
      P

  have hInv :
      lineReflect Geo (axis 0) P =
        X := by
    dsimp [P]
    exact
      lineReflect_involutive
        Geo
        (axis 0)
        X

  rw [hInv] at hPow

  have hEq :
      lineReflect Geo (axis q) X =
        P := by
    exact hPow.symm.trans hFix

  dsimp [P] at hEq

  exact hEq

/--
Helper for the geometric construction of arbitrary finite period.

For three reflection axes through a common center O, one additional
reflected point is enough to prove exact transport of the preceding
carrier onto the following carrier.

The center O is fixed by reflection in the middle axis. Together with
a second point P on the preceding carrier whose image Q lies on the
following carrier, the two-point line transport criterion applies.
-/
theorem coxeter_general_common_center_point_transport
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (previous middle next : ReflectionAxis Geo)
    (O P Q : Geo.Point)
    (hOprevious :
      HilbertIncidence.OnLine
        O
        previous.carrier)
    (hPprevious :
      HilbertIncidence.OnLine
        P
        previous.carrier)
    (hOP :
      Not (O = P))
    (hOmiddle :
      HilbertIncidence.OnLine
        O
        middle.carrier)
    (hOnext :
      HilbertIncidence.OnLine
        O
        next.carrier)
    (hQnext :
      HilbertIncidence.OnLine
        Q
        next.carrier)
    (hImage :
      lineReflect Geo middle P = Q) :
    ReflectionMapsLine
      Geo
      middle
      previous.carrier
      next.carrier := by

  have hFixO :
      lineReflect Geo middle O = O :=
    lineReflect_fixed_of_on_axis
      Geo
      middle
      O
      hOmiddle

  have hImageOonNext :
      HilbertIncidence.OnLine
        (lineReflect Geo middle O)
        next.carrier := by
    rw [hFixO]
    exact hOnext

  have hImagePonNext :
      HilbertIncidence.OnLine
        (lineReflect Geo middle P)
        next.carrier := by
    rw [hImage]
    exact hQnext

  exact
    reflectionMapsLine_of_two_points
      Geo
      middle
      previous.carrier
      next.carrier
      O
      P
      hOprevious
      hPprevious
      hOP
      hImageOonNext
      hImagePonNext

/--
Helper for the geometric construction of arbitrary finite period.

A point Q is the canonical reflection of P across an axis whenever P is
off the axis, H is a perpendicular foot from P to the axis, and H is the
midpoint of P and Q.

This is a direct bridge from the synthetic geometric definition
IsLineReflection to the canonical map lineReflect.
-/
theorem coxeter_general_lineReflect_eq_of_perpendicular_midpoint
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPoff :
      Not
        (HilbertIncidence.OnLine
          P
          axis.carrier))
    (hPerp :
      PerpendicularToAxis
        Geo
        axis
        H
        P)
    (hMid :
      HilbertIsMidpoint
        Geo
        H
        P
        Q) :
    lineReflect Geo axis P = Q := by

  apply
    line_reflection_unique
      Geo
      axis
      P
      (lineReflect Geo axis P)
      Q

  exact
    lineReflect_spec
      Geo
      axis
      P

  unfold IsLineReflection

  apply Or.inr

  exact
    And.intro
      hPoff
      (Exists.intro
        H
        (And.intro
          hPerp
          hMid))

/--
Helper for the geometric construction of arbitrary finite period.

In a nondegenerate isosceles triangle OBC, let M be the midpoint of BC.
Any reflection axis whose carrier contains O and M swaps B and C.

This is the local synthetic mechanism needed for a fan of reflection
axes: equal distances from the common center force the middle axis
through the base midpoint to be the reflection axis exchanging the two
neighboring radial points.
-/
theorem coxeter_general_isosceles_middle_axis_swaps_neighbors
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (middle : ReflectionAxis Geo)
    (O B C M : Geo.Point)
    (hOBC :
      Not (Collinear Geo O B C))
    (hOBOC :
      Geo.Congruent O B O C)
    (hMid :
      HilbertIsMidpoint Geo M B C)
    (hOmiddle :
      HilbertIncidence.OnLine
        O
        middle.carrier)
    (hMmiddle :
      HilbertIncidence.OnLine
        M
        middle.carrier) :
    lineReflect Geo middle B = C := by

  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hMid.1

  have hBM :
      Not (B = M) :=
    hBMCdata.1

  have hBMC :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  have hOM :
      Not (O = M) := by
    intro hEq
    subst M

    have hBOC :
        Collinear Geo B O C :=
      hBMC

    have hOBCcol :
        Collinear Geo O B C :=
      PrimCollinearSwap
        Geo
        B
        O
        C
        hBOC

    exact hOBC hOBCcol

  have hBoff :
      Not
        (HilbertIncidence.OnLine
          B
          middle.carrier) := by
    intro hBmiddle

    have hOBM :
        Collinear Geo O B M :=
      Exists.intro
        middle.carrier
        (And.intro
          hOmiddle
          (And.intro
            hBmiddle
            hMmiddle))

    have hOBCcol :
        Collinear Geo O B C :=
      hilbert_primCollinear_trans
        Geo
        O
        B
        M
        C
        hBM
        hOBM
        hBMC

    exact hOBC hOBCcol

  have hRight :
      HilbertRightAngle Geo O M B :=
    isosceles_midpoint_right_angle
      Geo
      O
      B
      C
      M
      hOBC
      hOBOC
      hMid

  have hPerp :
      PerpendicularToAxis
        Geo
        middle
        M
        B := by
    unfold PerpendicularToAxis

    refine
      And.intro
        hMmiddle
        ?_

    refine
      And.intro
        hBoff
        ?_

    exact
      Exists.intro
        O
        (And.intro
          hOmiddle
          (And.intro
            hOM
            hRight))

  exact
    coxeter_general_lineReflect_eq_of_perpendicular_midpoint
      Geo
      middle
      B
      C
      M
      hBoff
      hPerp
      hMid

/--
Helper for the geometric construction of arbitrary finite period.

In a common-center fan, suppose B lies on the preceding carrier and C
lies on the following carrier. If OB = OC and the middle axis passes
through the midpoint M of BC, then reflection in the middle axis
transports the preceding carrier exactly onto the following carrier.

This packages the isosceles-neighbor swap into ReflectionMapsLine.
-/
theorem coxeter_general_isosceles_neighbor_transport
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (previous middle next : ReflectionAxis Geo)
    (O B C M : Geo.Point)
    (hOprevious :
      HilbertIncidence.OnLine
        O
        previous.carrier)
    (hBprevious :
      HilbertIncidence.OnLine
        B
        previous.carrier)
    (hOB :
      Not (O = B))
    (hOmiddle :
      HilbertIncidence.OnLine
        O
        middle.carrier)
    (hMmiddle :
      HilbertIncidence.OnLine
        M
        middle.carrier)
    (hOnext :
      HilbertIncidence.OnLine
        O
        next.carrier)
    (hCnext :
      HilbertIncidence.OnLine
        C
        next.carrier)
    (hOBC :
      Not (Collinear Geo O B C))
    (hOBOC :
      Geo.Congruent O B O C)
    (hMid :
      HilbertIsMidpoint Geo M B C) :
    ReflectionMapsLine
      Geo
      middle
      previous.carrier
      next.carrier := by

  have hImage :
      lineReflect Geo middle B = C :=
    coxeter_general_isosceles_middle_axis_swaps_neighbors
      Geo
      middle
      O
      B
      C
      M
      hOBC
      hOBOC
      hMid
      hOmiddle
      hMmiddle

  exact
    coxeter_general_common_center_point_transport
      Geo
      previous
      middle
      next
      O
      B
      C
      hOprevious
      hBprevious
      hOB
      hOmiddle
      hOnext
      hCnext
      hImage

/--
Helper for arbitrary finite Coxeter period.

To obtain all adjacent products needed up to exponent p, carrier
transport is needed only while the middle index is still below p.

Equivalently, for a transport

    axis_n --reflection in axis_(n+1)--> axis_(n+2),

we only require n + 1 < p.

This removes one unnecessary final transport beyond the closing axis.
-/
theorem coxeter_general_products_constant_of_carrier_chain_before_closure
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (hMap :
      forall n : Nat,
        Nat.succ n < p ->
        ReflectionMapsLine
          Geo
          (axis (Nat.succ n))
          (axis n).carrier
          (axis (Nat.succ (Nat.succ n))).carrier) :
    forall n : Nat,
      n < p ->
      reflectionProduct Geo (axis 0) (axis 1) =
        reflectionProduct
          Geo
          (axis n)
          (axis (Nat.succ n)) := by

  intro n

  induction n with

  | zero =>
      intro hn
      rfl

  | succ n ih =>
      intro hn

      have hnLt :
          n < p :=
        Nat.lt_trans
          (Nat.lt_succ_self n)
          hn

      calc
        reflectionProduct Geo (axis 0) (axis 1) =
            reflectionProduct
              Geo
              (axis n)
              (axis (Nat.succ n)) :=
          ih hnLt

        _ =
            reflectionProduct
              Geo
              (axis (Nat.succ n))
              (axis (Nat.succ (Nat.succ n))) :=
          coxeter_general_adjacent_products_of_carrier_transport
            Geo
            (axis n)
            (axis (Nat.succ n))
            (axis (Nat.succ (Nat.succ n)))
            (hMap n hn)

/--
Helper for the geometric construction of arbitrary finite period.

A radial fan around a common point O produces the carrier-transport
recurrence needed for the Coxeter argument.

For every step before closure, V_n lies on axis_n, V_(n+2) lies on
axis_(n+2), the two radial segments from O are congruent, and the middle
axis passes through the midpoint M_n of V_n V_(n+2).
-/
theorem coxeter_general_carrier_chain_of_isosceles_fan
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (hOaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          O
          (axis n).carrier)
    (hVaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          (V n)
          (axis n).carrier)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n))
    (hNoncol :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ (Nat.succ n)))))
    (hRadius :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.Congruent
          O
          (V n)
          O
          (V (Nat.succ (Nat.succ n))))
    (hMid :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIsMidpoint
          Geo
          (M n)
          (V n)
          (V (Nat.succ (Nat.succ n))))
    (hMmiddle :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIncidence.OnLine
          (M n)
          (axis (Nat.succ n)).carrier) :
    forall n : Nat,
      Nat.succ n < p ->
      ReflectionMapsLine
        Geo
        (axis (Nat.succ n))
        (axis n).carrier
        (axis (Nat.succ (Nat.succ n))).carrier := by

  intro n hn

  have hnLe :
      n <= p :=
    Nat.le_trans
      (Nat.le_succ n)
      (Nat.le_of_lt hn)

  have hn1Le :
      Nat.succ n <= p :=
    Nat.le_of_lt hn

  have hn2Le :
      Nat.succ (Nat.succ n) <= p :=
    Nat.succ_le_of_lt hn

  exact
    coxeter_general_isosceles_neighbor_transport
      Geo
      (axis n)
      (axis (Nat.succ n))
      (axis (Nat.succ (Nat.succ n)))
      O
      (V n)
      (V (Nat.succ (Nat.succ n)))
      (M n)
      (hOaxis n hnLe)
      (hVaxis n hnLe)
      (hOV n hnLe)
      (hOaxis (Nat.succ n) hn1Le)
      (hMmiddle n hn)
      (hOaxis (Nat.succ (Nat.succ n)) hn2Le)
      (hVaxis (Nat.succ (Nat.succ n)) hn2Le)
      (hNoncol n hn)
      (hRadius n hn)
      (hMid n hn)

/--
Helper for the geometric construction of arbitrary finite period.

To rule out an early return of a carrier, it is enough to exhibit on
each lower axis one point that does not lie on the initial carrier.

If axis_q had the same carrier as axis_0, every point on axis_q would
also lie on axis_0.
-/
theorem coxeter_general_no_early_carrier_return_of_witness_points
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (V : Nat -> Geo.Point)
    (hVaxis :
      forall q : Nat,
        q < p ->
        HilbertIncidence.OnLine
          (V q)
          (axis q).carrier)
    (hVoffInitial :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (HilbertIncidence.OnLine
            (V q)
            (axis 0).carrier)) :
    forall q : Nat,
      0 < q ->
      q < p ->
      Not
        ((axis q).carrier =
          (axis 0).carrier) := by

  intro q hqPos hqLt hCarrier

  have hVq :
      HilbertIncidence.OnLine
        (V q)
        (axis q).carrier :=
    hVaxis q hqLt

  rw [hCarrier] at hVq

  exact
    hVoffInitial
      q
      hqPos
      hqLt
      hVq

/--
Helper for the geometric construction of arbitrary finite period.

Canonical line reflection depends only on the carrier line of a
ReflectionAxis.

Thus two ReflectionAxis structures with the same carrier define the
same point transformation, even if their stored witness points differ.
-/
theorem coxeter_general_reflections_pointwise_eq_of_carriers_eq
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hCarrier :
      axis1.carrier = axis2.carrier) :
    forall P : Geo.Point,
      lineReflect Geo axis1 P =
        lineReflect Geo axis2 P := by

  intro P

  have hSpec1 :
      IsLineReflection
        Geo
        axis1
        P
        (lineReflect Geo axis1 P) :=
    lineReflect_spec
      Geo
      axis1
      P

  have hSpec1As2 :
      IsLineReflection
        Geo
        axis2
        P
        (lineReflect Geo axis1 P) := by

    simpa
      [IsLineReflection,
       PerpendicularToAxis,
       hCarrier]
      using hSpec1

  exact
    line_reflection_unique
      Geo
      axis2
      P
      (lineReflect Geo axis1 P)
      (lineReflect Geo axis2 P)
      hSpec1As2
      (lineReflect_spec
        Geo
        axis2
        P)

/--
Helper for arbitrary finite Coxeter period.

A finite carrier chain closes at exponent p as soon as the p-th carrier
is the same geometric line as the initial carrier.

Equality of the full ReflectionAxis structures is not needed.
-/
theorem coxeter_general_relation_of_closed_carrier_line_before_closure
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (hMap :
      forall n : Nat,
        Nat.succ n < p ->
        ReflectionMapsLine
          Geo
          (axis (Nat.succ n))
          (axis n).carrier
          (axis (Nat.succ (Nat.succ n))).carrier)
    (hCloseCarrier :
      (axis p).carrier =
        (axis 0).carrier) :
    ReflectionPairRelation
      Geo
      (axis 0)
      (axis 1)
      p := by

  unfold ReflectionPairRelation

  apply Equiv.ext
  intro P

  have hPair :
      forall n : Nat,
        n < p ->
        reflectionProduct Geo (axis 0) (axis 1) =
          reflectionProduct
            Geo
            (axis n)
            (axis (Nat.succ n)) :=
    coxeter_general_products_constant_of_carrier_chain_before_closure
      Geo
      axis
      p
      hMap

  have hPow :
      reflectionProductPow
          Geo
          (axis 0)
          (axis 1)
          p
          P =
        lineReflect Geo (axis p)
          (lineReflect Geo (axis 0) P) :=
    coxeter_general_power_telescope_up_to
      Geo
      axis
      p
      hPair
      p
      P
      (Nat.le_refl p)

  have hReflectClose :
      lineReflect Geo (axis p)
          (lineReflect Geo (axis 0) P) =
        lineReflect Geo (axis 0)
          (lineReflect Geo (axis 0) P) :=
    coxeter_general_reflections_pointwise_eq_of_carriers_eq
      Geo
      (axis p)
      (axis 0)
      hCloseCarrier
      (lineReflect Geo (axis 0) P)

  have hInv :
      lineReflect Geo (axis 0)
          (lineReflect Geo (axis 0) P) =
        P :=
    lineReflect_involutive
      Geo
      (axis 0)
      P

  exact
    hPow.trans
      (hReflectClose.trans hInv)

/--
Helper for arbitrary finite Coxeter period.

A finite carrier chain whose first return of the geometric carrier line
occurs exactly at p forces exact Coxeter period p.

Equality of the full ReflectionAxis structures is not needed at closure.
Only equality of the carrier lines matters.
-/
theorem coxeter_general_exact_period_of_minimal_closed_carrier_line
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (hp : 0 < p)
    (hMap :
      forall n : Nat,
        Nat.succ n < p ->
        ReflectionMapsLine
          Geo
          (axis (Nat.succ n))
          (axis n).carrier
          (axis (Nat.succ (Nat.succ n))).carrier)
    (hCloseCarrier :
      (axis p).carrier =
        (axis 0).carrier)
    (hNoEarlyReturn :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          ((axis q).carrier =
            (axis 0).carrier)) :
    ReflectionPairExactPeriod
      Geo
      (axis 0)
      (axis 1)
      p := by

  refine
    And.intro
      hp
      ?_

  refine
    And.intro
      (coxeter_general_relation_of_closed_carrier_line_before_closure
        Geo
        axis
        p
        hMap
        hCloseCarrier)
      ?_

  intro q hqPos hqLt hRelQ

  have hPair :
      forall n : Nat,
        n < p ->
        reflectionProduct Geo (axis 0) (axis 1) =
          reflectionProduct
            Geo
            (axis n)
            (axis (Nat.succ n)) :=
    coxeter_general_products_constant_of_carrier_chain_before_closure
      Geo
      axis
      p
      hMap

  have hReturn :
      (axis q).carrier =
        (axis 0).carrier :=
    coxeter_general_carrier_returns_of_relation_up_to
      Geo
      axis
      p
      hPair
      q
      (Nat.le_of_lt hqLt)
      hRelQ

  exact
    hNoEarlyReturn
      q
      hqPos
      hqLt
      hReturn

/--
Helper for the geometric construction of arbitrary finite period.

Two reflection-axis carriers are the same geometric line as soon as they
contain the same two distinct points.

This is the pointwise closure criterion that will replace a direct
carrier-equality hypothesis.
-/
theorem coxeter_general_carriers_eq_of_two_common_points
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (O P : Geo.Point)
    (hOP :
      Not (O = P))
    (hO1 :
      HilbertIncidence.OnLine
        O
        axis1.carrier)
    (hP1 :
      HilbertIncidence.OnLine
        P
        axis1.carrier)
    (hO2 :
      HilbertIncidence.OnLine
        O
        axis2.carrier)
    (hP2 :
      HilbertIncidence.OnLine
        P
        axis2.carrier) :
    axis1.carrier = axis2.carrier := by

  exact
    HilbertPlaneIncidence.line_unique
      O
      P
      hOP
      axis1.carrier
      axis2.carrier
      hO1
      hP1
      hO2
      hP2

/--
Helper for the geometric construction of arbitrary finite period.

An isosceles radial fan has exact Coxeter period p when its closing
radial point lies again on the initial carrier, while every earlier
radial witness point stays off the initial carrier.

Thus both closure and minimality are expressed by concrete incidence
data, not by equalities or inequalities of carrier lines.
-/
theorem coxeter_general_exact_period_of_isosceles_fan_with_point_witnesses
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (hp : 0 < p)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (hOaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          O
          (axis n).carrier)
    (hVaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          (V n)
          (axis n).carrier)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n))
    (hNoncol :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ (Nat.succ n)))))
    (hRadius :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.Congruent
          O
          (V n)
          O
          (V (Nat.succ (Nat.succ n))))
    (hMid :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIsMidpoint
          Geo
          (M n)
          (V n)
          (V (Nat.succ (Nat.succ n))))
    (hMmiddle :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIncidence.OnLine
          (M n)
          (axis (Nat.succ n)).carrier)
    (hVpInitial :
      HilbertIncidence.OnLine
        (V p)
        (axis 0).carrier)
    (hVoffInitial :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (HilbertIncidence.OnLine
            (V q)
            (axis 0).carrier)) :
    ReflectionPairExactPeriod
      Geo
      (axis 0)
      (axis 1)
      p := by

  have hMap :
      forall n : Nat,
        Nat.succ n < p ->
        ReflectionMapsLine
          Geo
          (axis (Nat.succ n))
          (axis n).carrier
          (axis (Nat.succ (Nat.succ n))).carrier :=
    coxeter_general_carrier_chain_of_isosceles_fan
      Geo
      axis
      p
      O
      V
      M
      hOaxis
      hVaxis
      hOV
      hNoncol
      hRadius
      hMid
      hMmiddle

  have hCloseCarrier :
      (axis p).carrier =
        (axis 0).carrier :=
    coxeter_general_carriers_eq_of_two_common_points
      Geo
      (axis p)
      (axis 0)
      O
      (V p)
      (hOV p (Nat.le_refl p))
      (hOaxis p (Nat.le_refl p))
      (hVaxis p (Nat.le_refl p))
      (hOaxis 0 (Nat.zero_le p))
      hVpInitial

  have hNoEarlyReturn :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          ((axis q).carrier =
            (axis 0).carrier) :=
    coxeter_general_no_early_carrier_return_of_witness_points
      Geo
      axis
      p
      V
      (fun q hq =>
        hVaxis q (Nat.le_of_lt hq))
      hVoffInitial

  exact
    coxeter_general_exact_period_of_minimal_closed_carrier_line
      Geo
      axis
      p
      hp
      hMap
      hCloseCarrier
      hNoEarlyReturn

/--
Helper for the geometric construction of arbitrary finite period.

If O and V0 lie on the initial carrier, while O, Vq, V0 are not
collinear, then Vq cannot lie on the initial carrier.

This turns a geometric noncollinearity witness into the point-off-line
condition used for minimality.
-/
theorem coxeter_general_off_initial_of_noncollinear_radial_witness
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (initial : ReflectionAxis Geo)
    (O V0 Vq : Geo.Point)
    (hOinitial :
      HilbertIncidence.OnLine
        O
        initial.carrier)
    (hV0initial :
      HilbertIncidence.OnLine
        V0
        initial.carrier)
    (hNoncol :
      Not
        (Collinear
          Geo
          O
          Vq
          V0)) :
    Not
      (HilbertIncidence.OnLine
        Vq
        initial.carrier) := by

  intro hVq

  have hCol :
      Collinear Geo O Vq V0 :=
    Exists.intro
      initial.carrier
      (And.intro
        hOinitial
        (And.intro
          hVq
          hV0initial))

  exact hNoncol hCol

/--
Helper for the geometric construction of arbitrary finite period.

An isosceles radial fan has exact Coxeter period p when the radial point
cycle closes at V_p = V_0 and every earlier radial point V_q is
noncollinear with O and V_0.

Thus closure and minimality are expressed entirely by point geometry.
-/
theorem coxeter_general_exact_period_of_isosceles_fan_with_radial_point_cycle
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (hp : 0 < p)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (hOaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          O
          (axis n).carrier)
    (hVaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          (V n)
          (axis n).carrier)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n))
    (hFanNoncol :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ (Nat.succ n)))))
    (hRadius :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.Congruent
          O
          (V n)
          O
          (V (Nat.succ (Nat.succ n))))
    (hMid :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIsMidpoint
          Geo
          (M n)
          (V n)
          (V (Nat.succ (Nat.succ n))))
    (hMmiddle :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIncidence.OnLine
          (M n)
          (axis (Nat.succ n)).carrier)
    (hClosePoint :
      V p = V 0)
    (hNoEarlyCol :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (Collinear
            Geo
            O
            (V q)
            (V 0))) :
    ReflectionPairExactPeriod
      Geo
      (axis 0)
      (axis 1)
      p := by

  have hVpInitial :
      HilbertIncidence.OnLine
        (V p)
        (axis 0).carrier := by
    rw [hClosePoint]
    exact
      hVaxis
        0
        (Nat.zero_le p)

  have hVoffInitial :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (HilbertIncidence.OnLine
            (V q)
            (axis 0).carrier) := by

    intro q hqPos hqLt

    exact
      coxeter_general_off_initial_of_noncollinear_radial_witness
        Geo
        (axis 0)
        O
        (V 0)
        (V q)
        (hOaxis 0 (Nat.zero_le p))
        (hVaxis 0 (Nat.zero_le p))
        (hNoEarlyCol q hqPos hqLt)

  exact
    coxeter_general_exact_period_of_isosceles_fan_with_point_witnesses
      Geo
      axis
      p
      hp
      O
      V
      M
      hOaxis
      hVaxis
      hOV
      hFanNoncol
      hRadius
      hMid
      hMmiddle
      hVpInitial
      hVoffInitial

/--
Helper for the geometric construction of arbitrary finite period.

Two radial segments that are each congruent to the same base radial
segment are congruent to each other.

This lets the fan be specified by one common-radius condition instead
of separate congruence hypotheses for every pair two steps apart.
-/
theorem coxeter_general_radial_congruence_of_common_radius
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O V0 A B : Geo.Point)
    (hA :
      Geo.Congruent O A O V0)
    (hB :
      Geo.Congruent O B O V0) :
    Geo.Congruent O A O B := by

  have hBaseB :
      Geo.Congruent O V0 O B :=
    hilbert_congruent_symmetry
      Geo
      O
      B
      O
      V0
      hB

  exact
    hilbert_congruent_transitivity
      Geo
      O
      A
      O
      V0
      O
      B
      hA
      hBaseB

/--
Helper for the geometric construction of arbitrary finite period.

An isosceles radial fan can be specified by one common-radius condition:
every radial segment O V_n is congruent to the base radial segment
O V_0.

The local congruences O V_n = O V_(n+2) required by the fan theorem are
then derived automatically.
-/
theorem coxeter_general_exact_period_of_isosceles_fan_with_common_radius
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : Nat -> ReflectionAxis Geo)
    (p : Nat)
    (hp : 0 < p)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (hOaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          O
          (axis n).carrier)
    (hVaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          (V n)
          (axis n).carrier)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n))
    (hFanNoncol :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ (Nat.succ n)))))
    (hCommonRadius :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hMid :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIsMidpoint
          Geo
          (M n)
          (V n)
          (V (Nat.succ (Nat.succ n))))
    (hMmiddle :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIncidence.OnLine
          (M n)
          (axis (Nat.succ n)).carrier)
    (hClosePoint :
      V p = V 0)
    (hNoEarlyCol :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (Collinear
            Geo
            O
            (V q)
            (V 0))) :
    ReflectionPairExactPeriod
      Geo
      (axis 0)
      (axis 1)
      p := by

  have hRadius :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.Congruent
          O
          (V n)
          O
          (V (Nat.succ (Nat.succ n))) := by

    intro n hn

    have hnLe :
        n <= p :=
      Nat.le_trans
        (Nat.le_succ n)
        (Nat.le_of_lt hn)

    have hn2Le :
        Nat.succ (Nat.succ n) <= p :=
      Nat.succ_le_of_lt hn

    exact
      coxeter_general_radial_congruence_of_common_radius
        Geo
        O
        (V 0)
        (V n)
        (V (Nat.succ (Nat.succ n)))
        (hCommonRadius n hnLe)
        (hCommonRadius
          (Nat.succ (Nat.succ n))
          hn2Le)

  exact
    coxeter_general_exact_period_of_isosceles_fan_with_radial_point_cycle
      Geo
      axis
      p
      hp
      O
      V
      M
      hOaxis
      hVaxis
      hOV
      hFanNoncol
      hRadius
      hMid
      hMmiddle
      hClosePoint
      hNoEarlyCol

/--
Helper for the geometric construction of arbitrary finite period.

Construct a reflection axis from two distinct points.

The carrier is a line through A and B supplied by plane incidence.
-/
noncomputable def coxeter_general_axis_through
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B : Geo.Point)
    (hAB : Not (A = B)) :
    ReflectionAxis Geo := by

  have hLine :=
    HilbertPlaneIncidence.line_through
      A
      B
      hAB

  let lineAB : Geo.Line :=
    Classical.choose hLine

  have hLineData :
      And
        (HilbertIncidence.OnLine A lineAB)
        (HilbertIncidence.OnLine B lineAB) :=
    Classical.choose_spec hLine

  exact
    { carrier := lineAB
      A := A
      B := B
      hAB := hAB
      hA := hLineData.1
      hB := hLineData.2 }

/--
Helper for the geometric construction of arbitrary finite period.

The first point used to construct coxeter_general_axis_through lies
on its carrier.
-/
theorem coxeter_general_axis_through_first_on_carrier
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B : Geo.Point)
    (hAB : Not (A = B)) :
    HilbertIncidence.OnLine
      A
      (coxeter_general_axis_through
        Geo
        A
        B
        hAB).carrier := by

  simpa [coxeter_general_axis_through] using
    (coxeter_general_axis_through
      Geo
      A
      B
      hAB).hA

/--
Helper for the geometric construction of arbitrary finite period.

The second point used to construct coxeter_general_axis_through lies
on its carrier.
-/
theorem coxeter_general_axis_through_second_on_carrier
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B : Geo.Point)
    (hAB : Not (A = B)) :
    HilbertIncidence.OnLine
      B
      (coxeter_general_axis_through
        Geo
        A
        B
        hAB).carrier := by

  simpa [coxeter_general_axis_through] using
    (coxeter_general_axis_through
      Geo
      A
      B
      hAB).hB

/--
Helper for the geometric construction of arbitrary finite period.

Construct a radial axis family from a common center O and radial points
V_n, using the canonical axis through O and V_n for every n <= p.

Indices above p use the initial radial axis only as a technical total
extension of the Nat-indexed family; they are irrelevant to the finite
Coxeter argument.
-/
noncomputable def coxeter_general_radial_axis_family
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (p : Nat)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n)) :
    Nat -> ReflectionAxis Geo :=
  fun n =>
    if hn : n <= p then
      coxeter_general_axis_through
        Geo
        O
        (V n)
        (hOV n hn)
    else
      coxeter_general_axis_through
        Geo
        O
        (V 0)
        (hOV 0 (Nat.zero_le p))

/--
Helper for the geometric construction of arbitrary finite period.

For n <= p, the common center O lies on the carrier of the n-th radial
axis.
-/
theorem coxeter_general_radial_axis_center_on_carrier
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (p : Nat)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n))
    (n : Nat)
    (hn : n <= p) :
    HilbertIncidence.OnLine
      O
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        hOV
        n).carrier := by

  simp only
    [coxeter_general_radial_axis_family,
     dite_eq_left hn]

  exact
    coxeter_general_axis_through_first_on_carrier
      Geo
      O
      (V n)
      (hOV n hn)

/--
Helper for the geometric construction of arbitrary finite period.

For n <= p, the radial point V_n lies on the carrier of the n-th radial
axis.
-/
theorem coxeter_general_radial_axis_point_on_carrier
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (p : Nat)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n))
    (n : Nat)
    (hn : n <= p) :
    HilbertIncidence.OnLine
      (V n)
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        hOV
        n).carrier := by

  simp only
    [coxeter_general_radial_axis_family,
     dite_eq_left hn]

  exact
    coxeter_general_axis_through_second_on_carrier
      Geo
      O
      (V n)
      (hOV n hn)

/--
Helper for the geometric construction of arbitrary finite period.

The reflection axes of the fan are now generated canonically from the
common center O and the radial points V_n.

Thus the exact-period theorem no longer takes an independent axis family
or separate incidence hypotheses for O and V_n on those axes.
-/
theorem coxeter_general_exact_period_of_radial_point_fan
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (hp : 0 < p)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n))
    (hFanNoncol :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ (Nat.succ n)))))
    (hCommonRadius :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hMid :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIsMidpoint
          Geo
          (M n)
          (V n)
          (V (Nat.succ (Nat.succ n))))
    (hMmiddle :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIncidence.OnLine
          (M n)
          (coxeter_general_radial_axis_family
            Geo
            O
            V
            p
            hOV
            (Nat.succ n)).carrier)
    (hClosePoint :
      V p = V 0)
    (hNoEarlyCol :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (Collinear
            Geo
            O
            (V q)
            (V 0))) :
    ReflectionPairExactPeriod
      Geo
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        hOV
        0)
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        hOV
        1)
      p := by

  let axis : Nat -> ReflectionAxis Geo :=
    coxeter_general_radial_axis_family
      Geo
      O
      V
      p
      hOV

  have hOaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          O
          (axis n).carrier := by

    intro n hn

    exact
      coxeter_general_radial_axis_center_on_carrier
        Geo
        O
        V
        p
        hOV
        n
        hn

  have hVaxis :
      forall n : Nat,
        n <= p ->
        HilbertIncidence.OnLine
          (V n)
          (axis n).carrier := by

    intro n hn

    exact
      coxeter_general_radial_axis_point_on_carrier
        Geo
        O
        V
        p
        hOV
        n
        hn

  change
    ReflectionPairExactPeriod
      Geo
      (axis 0)
      (axis 1)
      p

  have hMmiddleAxis :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIncidence.OnLine
          (M n)
          (axis (Nat.succ n)).carrier := by

    intro n hn

    exact hMmiddle n hn

  exact
    coxeter_general_exact_period_of_isosceles_fan_with_common_radius
      Geo
      axis
      p
      hp
      O
      V
      M
      hOaxis
      hVaxis
      hOV
      hFanNoncol
      hCommonRadius
      hMid
      hMmiddleAxis
      hClosePoint
      hNoEarlyCol

/--
Helper for the geometric construction of arbitrary finite period.

If O, V, and M are collinear, then M lies on the canonical radial axis
constructed through the distinct points O and V.

This converts midpoint-on-axis data into pure point collinearity.
-/
theorem coxeter_general_on_radial_axis_of_collinear
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (O V M : Geo.Point)
    (hOV :
      Not (O = V))
    (hCol :
      Collinear Geo O V M) :
    HilbertIncidence.OnLine
      M
      (coxeter_general_axis_through
        Geo
        O
        V
        hOV).carrier := by

  let line : Geo.Line :=
    Classical.choose hCol

  have hData :
      And
        (HilbertIncidence.OnLine O line)
        (And
          (HilbertIncidence.OnLine V line)
          (HilbertIncidence.OnLine M line)) :=
    Classical.choose_spec hCol

  have hOaxis :
      HilbertIncidence.OnLine
        O
        (coxeter_general_axis_through
          Geo
          O
          V
          hOV).carrier :=
    coxeter_general_axis_through_first_on_carrier
      Geo
      O
      V
      hOV

  have hVaxis :
      HilbertIncidence.OnLine
        V
        (coxeter_general_axis_through
          Geo
          O
          V
          hOV).carrier :=
    coxeter_general_axis_through_second_on_carrier
      Geo
      O
      V
      hOV

  have hCarrier :
      (coxeter_general_axis_through
        Geo
        O
        V
        hOV).carrier =
      line :=
    HilbertPlaneIncidence.line_unique
      O
      V
      hOV
      (coxeter_general_axis_through
        Geo
        O
        V
        hOV).carrier
      line
      hOaxis
      hVaxis
      hData.1
      hData.2.1

  rw [hCarrier]

  exact hData.2.2

/--
Helper for the geometric construction of arbitrary finite period.

The midpoint condition for the radial fan is now expressed purely by
point collinearity:

    O, V_(n+1), M_n are collinear.

Since axis_(n+1) is canonically constructed through O and V_(n+1), this
collinearity automatically places M_n on the middle reflection axis.
-/
theorem coxeter_general_exact_period_of_radial_point_fan_with_collinear_midpoints
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (hp : 0 < p)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n))
    (hFanNoncol :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ (Nat.succ n)))))
    (hCommonRadius :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hMid :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIsMidpoint
          Geo
          (M n)
          (V n)
          (V (Nat.succ (Nat.succ n))))
    (hMcol :
      forall n : Nat,
        Nat.succ n < p ->
        Collinear
          Geo
          O
          (V (Nat.succ n))
          (M n))
    (hClosePoint :
      V p = V 0)
    (hNoEarlyCol :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (Collinear
            Geo
            O
            (V q)
            (V 0))) :
    ReflectionPairExactPeriod
      Geo
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        hOV
        0)
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        hOV
        1)
      p := by

  have hMmiddle :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIncidence.OnLine
          (M n)
          (coxeter_general_radial_axis_family
            Geo
            O
            V
            p
            hOV
            (Nat.succ n)).carrier := by

    intro n hn

    have hn1Le :
        Nat.succ n <= p :=
      Nat.le_of_lt hn

    simp only
      [coxeter_general_radial_axis_family,
       dite_eq_left hn1Le]

    exact
      coxeter_general_on_radial_axis_of_collinear
        Geo
        O
        (V (Nat.succ n))
        (M n)
        (hOV (Nat.succ n) hn1Le)
        (hMcol n hn)

  exact
    coxeter_general_exact_period_of_radial_point_fan
      Geo
      p
      hp
      O
      V
      M
      hOV
      hFanNoncol
      hCommonRadius
      hMid
      hMmiddle
      hClosePoint
      hNoEarlyCol

/--
Helper for the geometric construction of arbitrary finite period.

If every radial segment O V_n is congruent to the base radial segment O V_0,
then nondegeneracy of the base radius implies nondegeneracy of every radial
segment.

This is the first reduction of the family hOV to one point-level assumption
O != V_0.
-/
theorem coxeter_general_nonzero_radial_of_common_radius
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O V0 V : Geo.Point)
    (hOV0 :
      Not (O = V0))
    (hRadius :
      Geo.Congruent O V O V0) :
    Not (O = V) := by

  intro hOV
  subst V

  have hNull :
      Geo.Congruent O V0 O O :=
    hilbert_congruent_symmetry
      Geo
      O
      O
      O
      V0
      hRadius

  have hEq :
      O = V0 :=
    bookZero_nullSegment1
      Geo
      O
      V0
      O
      hNull

  exact hOV0 hEq

/--
Helper for the geometric construction of arbitrary finite period.

The family hOV is no longer external data.  It is derived from one
nondegenerate base radius O V_0 together with the common-radius condition.

Thus the radial fan now requires only the point-level assumption O != V_0.
-/
theorem coxeter_general_exact_period_of_radial_point_fan_with_base_radius_nonzero
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (hp : 0 < p)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (hOV0 :
      Not (O = V 0))
    (hFanNoncol :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ (Nat.succ n)))))
    (hCommonRadius :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hMid :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIsMidpoint
          Geo
          (M n)
          (V n)
          (V (Nat.succ (Nat.succ n))))
    (hMcol :
      forall n : Nat,
        Nat.succ n < p ->
        Collinear
          Geo
          O
          (V (Nat.succ n))
          (M n))
    (hClosePoint :
      V p = V 0)
    (hNoEarlyCol :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (Collinear
            Geo
            O
            (V q)
            (V 0))) :
    ReflectionPairExactPeriod
      Geo
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (fun n hn =>
          coxeter_general_nonzero_radial_of_common_radius
            Geo
            O
            (V 0)
            (V n)
            hOV0
            (hCommonRadius n hn))
        0)
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (fun n hn =>
          coxeter_general_nonzero_radial_of_common_radius
            Geo
            O
            (V 0)
            (V n)
            hOV0
            (hCommonRadius n hn))
        1)
      p := by

  let hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n) :=
    fun n hn =>
      coxeter_general_nonzero_radial_of_common_radius
        Geo
        O
        (V 0)
        (V n)
        hOV0
        (hCommonRadius n hn)

  change
    ReflectionPairExactPeriod
      Geo
      (coxeter_general_radial_axis_family
        Geo O V p hOV 0)
      (coxeter_general_radial_axis_family
        Geo O V p hOV 1)
      p

  exact
    coxeter_general_exact_period_of_radial_point_fan_with_collinear_midpoints
      Geo
      p
      hp
      O
      V
      M
      hOV
      hFanNoncol
      hCommonRadius
      hMid
      hMcol
      hClosePoint
      hNoEarlyCol

/--
Helper for the geometric construction of arbitrary finite period.

Two distinct nonzero radial points B and C at the same distance from O
cannot be collinear with O unless O lies between B and C.

Thus, for equal-radius radial points, the local fan noncollinearity can be
replaced by the more geometric condition that the two-step chord is not a
diameter through O.
-/
theorem coxeter_general_noncollinear_of_equal_radius_not_center_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O B C : Geo.Point)
    (hOB :
      Not (O = B))
    (hOC :
      Not (O = C))
    (hBC :
      Not (B = C))
    (hRadius :
      Geo.Congruent O B O C)
    (hNotBetween :
      Not (Geo.Between B O C)) :
    Not (Collinear Geo O B C) := by

  intro hCol

  have hBOCcol :
      Collinear Geo B O C :=
    PrimCollinearSwap
      Geo
      O
      B
      C
      hCol

  have hBOC :
      Geo.Between B O C :=
    hilbert_between_of_collinear_equidistant
      Geo
      B
      O
      C
      hOB
      hOC
      hBC
      hBOCcol
      hRadius

  exact hNotBetween hBOC

/--
Helper for the geometric construction of arbitrary finite period.

The local fan noncollinearity hypothesis is no longer external data.
For each two-step chord V_n V_(n+2), it is enough to assume that the
common center O does not lie between its endpoints.

The strict midpoint hypothesis already implies V_n != V_(n+2), while
the common-radius condition supplies the equal radii needed by step 54.
-/
theorem coxeter_general_exact_period_of_radial_point_fan_with_no_diameter_chords
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (hp : 0 < p)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (hOV0 :
      Not (O = V 0))
    (hNoDiameter :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Geo.Between
            (V n)
            O
            (V (Nat.succ (Nat.succ n)))))
    (hCommonRadius :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hMid :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIsMidpoint
          Geo
          (M n)
          (V n)
          (V (Nat.succ (Nat.succ n))))
    (hMcol :
      forall n : Nat,
        Nat.succ n < p ->
        Collinear
          Geo
          O
          (V (Nat.succ n))
          (M n))
    (hClosePoint :
      V p = V 0)
    (hNoEarlyCol :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (Collinear
            Geo
            O
            (V q)
            (V 0))) :
    ReflectionPairExactPeriod
      Geo
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (fun n hn =>
          coxeter_general_nonzero_radial_of_common_radius
            Geo
            O
            (V 0)
            (V n)
            hOV0
            (hCommonRadius n hn))
        0)
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (fun n hn =>
          coxeter_general_nonzero_radial_of_common_radius
            Geo
            O
            (V 0)
            (V n)
            hOV0
            (hCommonRadius n hn))
        1)
      p := by

  let hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n) :=
    fun n hn =>
      coxeter_general_nonzero_radial_of_common_radius
        Geo
        O
        (V 0)
        (V n)
        hOV0
        (hCommonRadius n hn)

  have hFanNoncol :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ (Nat.succ n)))) := by

    intro n hn

    have hnLe :
        n <= p :=
      Nat.le_trans
        (Nat.le_succ n)
        (Nat.le_of_lt hn)

    have hn2Le :
        Nat.succ (Nat.succ n) <= p :=
      Nat.succ_le_of_lt hn

    have hOB :
        Not (O = V n) :=
      hOV n hnLe

    have hOC :
        Not (O = V (Nat.succ (Nat.succ n))) :=
      hOV
        (Nat.succ (Nat.succ n))
        hn2Le

    have hBC :
        Not (V n = V (Nat.succ (Nat.succ n))) :=
      (HilbertOrder.between_incidence
        (V n)
        (M n)
        (V (Nat.succ (Nat.succ n)))
        (hMid n hn).1).2.2.1

    have hRadius :
        Geo.Congruent
          O
          (V n)
          O
          (V (Nat.succ (Nat.succ n))) :=
      coxeter_general_radial_congruence_of_common_radius
        Geo
        O
        (V 0)
        (V n)
        (V (Nat.succ (Nat.succ n)))
        (hCommonRadius n hnLe)
        (hCommonRadius
          (Nat.succ (Nat.succ n))
          hn2Le)

    exact
      coxeter_general_noncollinear_of_equal_radius_not_center_between
        Geo
        O
        (V n)
        (V (Nat.succ (Nat.succ n)))
        hOB
        hOC
        hBC
        hRadius
        (hNoDiameter n hn)

  change
    ReflectionPairExactPeriod
      Geo
      (coxeter_general_radial_axis_family
        Geo O V p hOV 0)
      (coxeter_general_radial_axis_family
        Geo O V p hOV 1)
      p

  exact
    coxeter_general_exact_period_of_radial_point_fan_with_base_radius_nonzero
      Geo
      p
      hp
      O
      V
      M
      hOV0
      hFanNoncol
      hCommonRadius
      hMid
      hMcol
      hClosePoint
      hNoEarlyCol

/--
Helper for the geometric construction of arbitrary finite period.

For an equal-radius chord BC with strict midpoint M, the condition that the
center O is not the midpoint of BC already excludes O from lying between B
and C.

Indeed, if B-O-C, then equal radii make O itself a Hilbert midpoint of BC.
Midpoint uniqueness then gives O = M.
-/
theorem coxeter_general_not_center_between_of_midpoint_off_center
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O M B C : Geo.Point)
    (hRadius :
      Geo.Congruent O B O C)
    (hMid :
      HilbertIsMidpoint Geo M B C)
    (hOM :
      Not (O = M)) :
    Not (Geo.Between B O C) := by

  intro hBOC

  have hBO_OC :
      Geo.Congruent B O O C :=
    CongruentReverseFirst
      Geo
      O B
      O C
      hRadius

  have hCenterMid :
      HilbertIsMidpoint Geo O B C := by
    exact ⟨hBOC, hBO_OC⟩

  have hEq : O = M :=
    hilbert_midpoint_unique_local
      Geo
      O
      M
      B
      C
      hCenterMid
      hMid

  exact hOM hEq

/--
Helper for the geometric construction of arbitrary finite period.

The local no-diameter condition is no longer external data.  For each
strict midpoint M_n of the two-step chord V_n V_(n+2), it is enough to
assume that the midpoint is different from the common center O.

Equal radii then show that O cannot lie between the chord endpoints:
otherwise O would be a second midpoint of the same chord, contradicting
midpoint uniqueness.
-/
theorem coxeter_general_exact_period_of_radial_point_fan_with_midpoints_off_center
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (hp : 0 < p)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (hOV0 :
      Not (O = V 0))
    (hOM :
      forall n : Nat,
        Nat.succ n < p ->
        Not (O = M n))
    (hCommonRadius :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hMid :
      forall n : Nat,
        Nat.succ n < p ->
        HilbertIsMidpoint
          Geo
          (M n)
          (V n)
          (V (Nat.succ (Nat.succ n))))
    (hMcol :
      forall n : Nat,
        Nat.succ n < p ->
        Collinear
          Geo
          O
          (V (Nat.succ n))
          (M n))
    (hClosePoint :
      V p = V 0)
    (hNoEarlyCol :
      forall q : Nat,
        0 < q ->
        q < p ->
        Not
          (Collinear
            Geo
            O
            (V q)
            (V 0))) :
    ReflectionPairExactPeriod
      Geo
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (fun n hn =>
          coxeter_general_nonzero_radial_of_common_radius
            Geo
            O
            (V 0)
            (V n)
            hOV0
            (hCommonRadius n hn))
        0)
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (fun n hn =>
          coxeter_general_nonzero_radial_of_common_radius
            Geo
            O
            (V 0)
            (V n)
            hOV0
            (hCommonRadius n hn))
        1)
      p := by

  have hNoDiameter :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Geo.Between
            (V n)
            O
            (V (Nat.succ (Nat.succ n)))) := by

    intro n hn

    have hnLe :
        n <= p :=
      Nat.le_trans
        (Nat.le_succ n)
        (Nat.le_of_lt hn)

    have hn2Le :
        Nat.succ (Nat.succ n) <= p :=
      Nat.succ_le_of_lt hn

    have hRadius :
        Geo.Congruent
          O
          (V n)
          O
          (V (Nat.succ (Nat.succ n))) :=
      coxeter_general_radial_congruence_of_common_radius
        Geo
        O
        (V 0)
        (V n)
        (V (Nat.succ (Nat.succ n)))
        (hCommonRadius n hnLe)
        (hCommonRadius
          (Nat.succ (Nat.succ n))
          hn2Le)

    exact
      coxeter_general_not_center_between_of_midpoint_off_center
        Geo
        O
        (M n)
        (V n)
        (V (Nat.succ (Nat.succ n)))
        hRadius
        (hMid n hn)
        (hOM n hn)

  exact
    coxeter_general_exact_period_of_radial_point_fan_with_no_diameter_chords
      Geo
      p
      hp
      O
      V
      M
      hOV0
      hNoDiameter
      hCommonRadius
      hMid
      hMcol
      hClosePoint
      hNoEarlyCol

/--
Helper for the geometric construction of arbitrary finite period.

A finite radial point fan packages the point-level data that survived the
incremental reductions of steps 49--57.  It contains no independent axis
family and no abstract Coxeter algebra.  The reflection axes are recovered
canonically from the center O and the radial points V_n.
-/
structure CoxeterRadialPointFan
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point) : Prop where
  period_pos :
    0 < p
  center_ne_base :
    Not (O = V 0)
  midpoint_off_center :
    forall n : Nat,
      Nat.succ n < p ->
      Not (O = M n)
  common_radius :
    forall n : Nat,
      n <= p ->
      Geo.Congruent
        O
        (V n)
        O
        (V 0)
  chord_midpoint :
    forall n : Nat,
      Nat.succ n < p ->
      HilbertIsMidpoint
        Geo
        (M n)
        (V n)
        (V (Nat.succ (Nat.succ n)))
  middle_collinear :
    forall n : Nat,
      Nat.succ n < p ->
      Collinear
        Geo
        O
        (V (Nat.succ n))
        (M n)
  closed :
    V p = V 0
  no_early_radial_return :
    forall q : Nat,
      0 < q ->
      q < p ->
      Not
        (Collinear
          Geo
          O
          (V q)
          (V 0))

/--
Every radial point of a CoxeterRadialPointFan is distinct from its center.
-/
theorem coxeter_general_radial_nonzero_of_fan
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (fan : CoxeterRadialPointFan Geo p O V M) :
    forall n : Nat,
      n <= p ->
      Not (O = V n) :=
  fun n hn =>
    coxeter_general_nonzero_radial_of_common_radius
      Geo
      O
      (V 0)
      (V n)
      fan.center_ne_base
      (fan.common_radius n hn)

/--
A finite radial point fan of period p determines a pair of canonical radial
reflection axes whose reflection product has exact period p.
-/
theorem coxeter_general_exact_period_of_radial_point_fan_data
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V M : Nat -> Geo.Point)
    (fan : CoxeterRadialPointFan Geo p O V M) :
    ReflectionPairExactPeriod
      Geo
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (coxeter_general_radial_nonzero_of_fan
          Geo p O V M fan)
        0)
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (coxeter_general_radial_nonzero_of_fan
          Geo p O V M fan)
        1)
      p := by

  exact
    coxeter_general_exact_period_of_radial_point_fan_with_midpoints_off_center
      Geo
      p
      fan.period_pos
      O
      V
      M
      fan.center_ne_base
      fan.midpoint_off_center
      fan.common_radius
      fan.chord_midpoint
      fan.middle_collinear
      fan.closed
      fan.no_early_radial_return

/--
Helper for the geometric construction of arbitrary finite period.

This structure isolates the exact existence datum that is not supplied by the
current Hilbert incidence/order/congruence/parallel/constructible-continuity
layers: a finite radial point fan of prescribed period p.

No angle measure, coordinates, trigonometric functions, or regular-polygon
construction is built into the datum.  All geometry remains expressed by the
synthetic predicate CoxeterRadialPointFan.
-/
structure CoxeterRadialPeriodData
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat) where
  center : Geo.Point
  radialPoint : Nat -> Geo.Point
  chordMidpoint : Nat -> Geo.Point
  fan :
    CoxeterRadialPointFan
      Geo
      p
      center
      radialPoint
      chordMidpoint

/--
Helper for arbitrary finite Coxeter period.

The missing geometric existence datum is now completely separated from the
reflection argument.  Any CoxeterRadialPeriodData of period p determines two
reflection axes whose product has exact period p.
-/
theorem coxeter_general_exact_period_axes_of_radial_period_data
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (data : CoxeterRadialPeriodData Geo p) :
    exists a b : ReflectionAxis Geo,
      ReflectionPairExactPeriod Geo a b p := by

  let hRadialNonzero :=
    coxeter_general_radial_nonzero_of_fan
      Geo
      p
      data.center
      data.radialPoint
      data.chordMidpoint
      data.fan

  let a : ReflectionAxis Geo :=
    coxeter_general_radial_axis_family
      Geo
      data.center
      data.radialPoint
      p
      hRadialNonzero
      0

  let b : ReflectionAxis Geo :=
    coxeter_general_radial_axis_family
      Geo
      data.center
      data.radialPoint
      p
      hRadialNonzero
      1

  refine ⟨a, b, ?_⟩

  exact
    coxeter_general_exact_period_of_radial_point_fan_data
      Geo
      p
      data.center
      data.radialPoint
      data.chordMidpoint
      data.fan

end Geometry


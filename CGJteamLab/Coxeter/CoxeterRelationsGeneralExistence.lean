import CGJteamLab.Coxeter.CoxeterRelationsGeneral

namespace Geometry

/-!
# General finite Coxeter periods from raw Hilbert polygon data

This module isolates the geometric existence boundary for arbitrary finite
Coxeter periods. The reflection algebra and carrier telescoping are imported
from `CoxeterRelationsGeneral`.

For p >= 3, the additional geometric datum is an oriented equilateral radial
polygon stated only with Hilbert incidence, order/separation, and segment
congruence. From such a polygon the canonical radial reflection axes have
exact product period p. Period 2 is constructed directly from a
nondegenerate Hilbert right angle.

No coordinates, metric formulas, angle measure, trigonometry, or analytic
model occur in this module.
-/

/--
A closed equilateral polygon on one Hilbert circle, with minimal radial
return. The orientation data are added by
`HilbertFiniteOrientedEquilateralRadialPolygon` below.
-/
structure HilbertFiniteEquilateralRadialPolygon
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point) : Prop where
  period_ge_three :
    3 <= p
  center_ne_base :
    Not (O = V 0)
  common_radius :
    forall n : Nat,
      n <= p ->
      Geo.Congruent
        O
        (V n)
        O
        (V 0)
  equal_consecutive_sides :
    forall n : Nat,
      Nat.succ n < p ->
      Geo.Congruent
        (V n)
        (V (Nat.succ n))
        (V (Nat.succ n))
        (V (Nat.succ (Nat.succ n)))
  terminal_radial_return :
    Collinear Geo O (V p) (V 0)
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
An oriented equilateral radial polygon.

For every local triple V_n, V_(n+1), V_(n+2), a radial line through O and
the middle vertex separates the two outer vertices.  This excludes the
local backtracking allowed by the unoriented underlying radial-polygon structure.
-/
structure HilbertFiniteOrientedEquilateralRadialPolygon
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point) : Prop
    extends HilbertFiniteEquilateralRadialPolygon Geo p O V where
  local_radial_separation :
    forall n : Nat,
      Nat.succ n < p ->
      exists radial : Geo.Line,
        HilbertIncidence.OnLine O radial /\
        HilbertIncidence.OnLine (V (Nat.succ n)) radial /\
        HilbertOppositeSide
          Geo
          (V n)
          (V (Nat.succ (Nat.succ n)))
          radial

/--
a perpendicular reflection axis preserves the other carrier exactly.

The existing theorem `lineReflect_preserves_perpendicular_axis_second` gives
only the forward incidence implication.  Since line reflection is involutive,
the reverse implication follows by applying the same preservation theorem to
the reflected point.

This packages the diameter branch in the exact `ReflectionMapsLine` form used
by the general Coxeter carrier telescope.
-/
theorem coxeter_general_reflection_maps_perpendicular_carrier_self
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (mirror source : ReflectionAxis Geo)
    (hPerp : ReflectionAxesPerpendicular Geo mirror source) :
    ReflectionMapsLine
      Geo
      mirror
      source.carrier
      source.carrier := by

  intro P
  constructor

  · intro hP

    exact
      lineReflect_preserves_perpendicular_axis_second
        Geo
        mirror
        source
        hPerp
        P
        hP

  · intro hImage

    have hBack :
        HilbertIncidence.OnLine
          (lineReflect Geo mirror
            (lineReflect Geo mirror P))
          source.carrier :=
      lineReflect_preserves_perpendicular_axis_second
        Geo
        mirror
        source
        hPerp
        (lineReflect Geo mirror P)
        hImage

    simpa only
      [lineReflect_involutive Geo mirror P]
      using hBack


/--
the diameter branch produces perpendicular canonical radial axes.

Assume O is the midpoint of BC, W lies with O on the candidate middle
radial line, B lies off that line, and WB ~= WC.  Then the isosceles
triangle WBC has its median WO perpendicular to BC.  Hence the canonical
axis OW is perpendicular to the canonical axis OB.

This is the local geometric replacement for the noncollinear isosceles-fan
argument when the two-step chord BC is a diameter through O.
-/
def coxeter_general_perpendicular_radial_axes_of_center_midpoint
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O B W C : Geo.Point)
    (radial : Geo.Line)
    (hOW : Not (O = W))
    (hOB : Not (O = B))
    (hOradial : HilbertIncidence.OnLine O radial)
    (hWradial : HilbertIncidence.OnLine W radial)
    (hBoff : Not (HilbertIncidence.OnLine B radial))
    (hMid : HilbertIsMidpoint Geo O B C)
    (hWBWC : Geo.Congruent W B W C) :
    ReflectionAxesPerpendicular
      Geo
      (coxeter_general_axis_through Geo O W hOW)
      (coxeter_general_axis_through Geo O B hOB) := by

  have hWOB :
      Not (Collinear Geo W O B) := by
    intro hCol

    have hOWB :
        Collinear Geo O W B :=
      PrimCollinearSwap
        Geo
        W O B
        hCol

    have hBon :
        HilbertIncidence.OnLine B radial :=
      hilbert_collinear_on_line
        Geo
        O W B
        radial
        hOW
        hOradial
        hWradial
        hOWB

    exact hBoff hBon

  have hBOC :
      Collinear Geo B O C :=
    (HilbertOrder.between_incidence
      B O C hMid.1).2.2.2.1

  have hBC :
      Not (B = C) :=
    (HilbertOrder.between_incidence
      B O C hMid.1).2.2.1

  have hWBC :
      Not (Collinear Geo W B C) := by
    intro hCol

    have hBCO :
        Collinear Geo B C O :=
      PrimCollinearRotate
        Geo
        B O C
        hBOC

    have hWBO :
        Collinear Geo W B O :=
      hilbert_primCollinear_trans
        Geo
        W B C O
        hBC
        hCol
        hBCO

    have hWOB' :
        Collinear Geo W O B :=
      PrimCollinearRotate
        Geo
        W B O
        hWBO

    exact hWOB hWOB'

  have hRight :
      HilbertRightAngle Geo W O B :=
    isosceles_midpoint_right_angle
      Geo
      W B C O
      hWBC
      hWBWC
      hMid

  refine
    { O := O
      U := W
      V := B
      hO1 := ?_
      hO2 := ?_
      hU1 := ?_
      hV2 := ?_
      hOU := hOW
      hOV := hOB
      hNonCol := hWOB
      hRight := hRight }

  · exact
      coxeter_general_axis_through_first_on_carrier
        Geo O W hOW

  · exact
      coxeter_general_axis_through_first_on_carrier
        Geo O B hOB

  · exact
      coxeter_general_axis_through_second_on_carrier
        Geo O W hOW

  · exact
      coxeter_general_axis_through_second_on_carrier
        Geo O B hOB


/--
the diameter branch gives the local carrier transport needed by the
finite Coxeter telescope.

Assume O is the midpoint of BC.  Then B,O,C are collinear, so the canonical
radial axes OB and OC have the same carrier.  The perpendicular-axis
helper shows that the middle axis OW is perpendicular to OB, and the
carrier-preservation helper shows that reflection in OW preserves OB.  Replacing that carrier by the equal carrier OC
gives the required transport from the previous radial axis to the next one.
-/
theorem coxeter_general_diameter_neighbor_transport
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O B W C : Geo.Point)
    (radial : Geo.Line)
    (hOW : Not (O = W))
    (hOB : Not (O = B))
    (hOC : Not (O = C))
    (hOradial : HilbertIncidence.OnLine O radial)
    (hWradial : HilbertIncidence.OnLine W radial)
    (hBoff : Not (HilbertIncidence.OnLine B radial))
    (hMid : HilbertIsMidpoint Geo O B C)
    (hWBWC : Geo.Congruent W B W C) :
    ReflectionMapsLine
      Geo
      (coxeter_general_axis_through Geo O W hOW)
      (coxeter_general_axis_through Geo O B hOB).carrier
      (coxeter_general_axis_through Geo O C hOC).carrier := by

  have hPerp :
      ReflectionAxesPerpendicular
        Geo
        (coxeter_general_axis_through Geo O W hOW)
        (coxeter_general_axis_through Geo O B hOB) :=
    coxeter_general_perpendicular_radial_axes_of_center_midpoint
      Geo
      O B W C
      radial
      hOW
      hOB
      hOradial
      hWradial
      hBoff
      hMid
      hWBWC

  have hSelf :
      ReflectionMapsLine
        Geo
        (coxeter_general_axis_through Geo O W hOW)
        (coxeter_general_axis_through Geo O B hOB).carrier
        (coxeter_general_axis_through Geo O B hOB).carrier :=
    coxeter_general_reflection_maps_perpendicular_carrier_self
      Geo
      (coxeter_general_axis_through Geo O W hOW)
      (coxeter_general_axis_through Geo O B hOB)
      hPerp

  have hBOC :
      Collinear Geo B O C :=
    (HilbertOrder.between_incidence
      B O C hMid.1).2.2.2.1

  have hOCB :
      Collinear Geo O C B :=
    PrimCollinearCycle
      Geo
      B O C
      hBOC

  have hBnext :
      HilbertIncidence.OnLine
        B
        (coxeter_general_axis_through Geo O C hOC).carrier :=
    coxeter_general_on_radial_axis_of_collinear
      Geo
      O C B
      hOC
      hOCB

  have hCarrier :
      (coxeter_general_axis_through Geo O B hOB).carrier =
        (coxeter_general_axis_through Geo O C hOC).carrier :=
    coxeter_general_carriers_eq_of_two_common_points
      Geo
      (coxeter_general_axis_through Geo O B hOB)
      (coxeter_general_axis_through Geo O C hOC)
      O
      B
      hOB
      (coxeter_general_axis_through_first_on_carrier
        Geo O B hOB)
      (coxeter_general_axis_through_second_on_carrier
        Geo O B hOB)
      (coxeter_general_axis_through_first_on_carrier
        Geo O C hOC)
      hBnext

  rw [<- hCarrier]

  exact hSelf


/--
one local neighbor-transport theorem covers both the ordinary
isosceles branch and the diameter branch.

The points B and C are the two-step neighbors, W is the intermediate radial
point, and M is the midpoint of BC.  The line `radial` contains O, W, and M;
B is off this line.  We assume both the equal-radii condition OB ~= OC and
the equal-chords condition WB ~= WC.

If M != O, equal radii imply that O is not between B and C, hence O,B,C are
noncollinear and the existing isosceles-neighbor transport applies.

If M = O, the chord BC is a diameter.  The diameter helper supplies the same carrier
transport through perpendicular radial axes.
-/
theorem coxeter_general_neighbor_transport_with_diameter_case
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O B W C M : Geo.Point)
    (radial : Geo.Line)
    (hOW : Not (O = W))
    (hOB : Not (O = B))
    (hOC : Not (O = C))
    (hOradial : HilbertIncidence.OnLine O radial)
    (hWradial : HilbertIncidence.OnLine W radial)
    (hMradial : HilbertIncidence.OnLine M radial)
    (hBoff : Not (HilbertIncidence.OnLine B radial))
    (hOBOC : Geo.Congruent O B O C)
    (hWBWC : Geo.Congruent W B W C)
    (hMid : HilbertIsMidpoint Geo M B C) :
    ReflectionMapsLine
      Geo
      (coxeter_general_axis_through Geo O W hOW)
      (coxeter_general_axis_through Geo O B hOB).carrier
      (coxeter_general_axis_through Geo O C hOC).carrier := by

  by_cases hOM : O = M

  · subst M

    exact
      coxeter_general_diameter_neighbor_transport
        Geo
        O B W C
        radial
        hOW
        hOB
        hOC
        hOradial
        hWradial
        hBoff
        hMid
        hWBWC

  · have hBC :
        Not (B = C) :=
      (HilbertOrder.between_incidence
        B M C hMid.1).2.2.1

    have hNotBetween :
        Not (Geo.Between B O C) :=
      coxeter_general_not_center_between_of_midpoint_off_center
        Geo
        O M B C
        hOBOC
        hMid
        hOM

    have hOBC :
        Not (Collinear Geo O B C) :=
      coxeter_general_noncollinear_of_equal_radius_not_center_between
        Geo
        O B C
        hOB
        hOC
        hBC
        hOBOC
        hNotBetween

    have hOWM :
        Collinear Geo O W M :=
      Exists.intro
        radial
        (And.intro
          hOradial
          (And.intro
            hWradial
            hMradial))

    have hMmiddle :
        HilbertIncidence.OnLine
          M
          (coxeter_general_axis_through Geo O W hOW).carrier :=
      coxeter_general_on_radial_axis_of_collinear
        Geo
        O W M
        hOW
        hOWM

    exact
      coxeter_general_isosceles_neighbor_transport
        Geo
        (coxeter_general_axis_through Geo O B hOB)
        (coxeter_general_axis_through Geo O W hOW)
        (coxeter_general_axis_through Geo O C hOC)
        O B C M
        (coxeter_general_axis_through_first_on_carrier
          Geo O B hOB)
        (coxeter_general_axis_through_second_on_carrier
          Geo O B hOB)
        hOB
        (coxeter_general_axis_through_first_on_carrier
          Geo O W hOW)
        hMmiddle
        (coxeter_general_axis_through_first_on_carrier
          Geo O C hOC)
        (coxeter_general_axis_through_second_on_carrier
          Geo O C hOC)
        hOBC
        hOBOC
        hMid

/--
the entire pre-closure carrier chain can be obtained without any
midpoint-off-center hypothesis and without supplying a midpoint family.

At each local window V_n, V_(n+1), V_(n+2), an oriented radial separator
contains O and V_(n+1) and puts the two outer vertices on opposite sides.
The separating chord therefore meets the radial line at some point M.
Equal radii and equal consecutive sides make both O and V_(n+1)
equidistant from the chord endpoints, so the existing Hilbert
perpendicular-bisector theorem proves that this intersection is the strict
midpoint.  The local neighbor-transport theorem then handles both possibilities M != O and M = O.
-/
theorem coxeter_general_carrier_chain_with_diameter_case
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n))
    (hCommonRadius :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hEqualSides :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.Congruent
          (V n)
          (V (Nat.succ n))
          (V (Nat.succ n))
          (V (Nat.succ (Nat.succ n))))
    (hSeparation :
      forall n : Nat,
        Nat.succ n < p ->
        exists radial : Geo.Line,
          HilbertIncidence.OnLine O radial /\
          HilbertIncidence.OnLine (V (Nat.succ n)) radial /\
          HilbertOppositeSide
            Geo
            (V n)
            (V (Nat.succ (Nat.succ n)))
            radial) :
    forall n : Nat,
      Nat.succ n < p ->
      ReflectionMapsLine
        Geo
        (coxeter_general_radial_axis_family
          Geo O V p hOV (Nat.succ n))
        (coxeter_general_radial_axis_family
          Geo O V p hOV n).carrier
        (coxeter_general_radial_axis_family
          Geo O V p hOV (Nat.succ (Nat.succ n))).carrier := by

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

  have hOB :
      Not (O = V n) :=
    hOV n hnLe

  have hOW :
      Not (O = V (Nat.succ n)) :=
    hOV (Nat.succ n) hn1Le

  have hOC :
      Not (O = V (Nat.succ (Nat.succ n))) :=
    hOV (Nat.succ (Nat.succ n)) hn2Le

  have hOBOC :
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

  have hWBWC :
      Geo.Congruent
        (V (Nat.succ n))
        (V n)
        (V (Nat.succ n))
        (V (Nat.succ (Nat.succ n))) :=
    CongruentReverseFirst
      Geo
      (V n)
      (V (Nat.succ n))
      (V (Nat.succ n))
      (V (Nat.succ (Nat.succ n)))
      (hEqualSides n hn)

  rcases hSeparation n hn with
    ⟨radial, hOradial, hWradial, hOpp⟩

  rcases hOpp.2.2 with
    ⟨M, hBetween, hMradial⟩

  have hBisect :
      Geo.Congruent
        (V n)
        M
        M
        (V (Nat.succ (Nat.succ n))) :=
    hilbert_equidistant_line_bisects_segment
      Geo
      O
      (V (Nat.succ n))
      (V n)
      (V (Nat.succ (Nat.succ n)))
      M
      radial
      hOW
      hOradial
      hWradial
      hMradial
      hOpp
      hOBOC
      hWBWC
      hBetween

  have hMid :
      HilbertIsMidpoint
        Geo
        M
        (V n)
        (V (Nat.succ (Nat.succ n))) :=
    And.intro hBetween hBisect

  simp only
    [coxeter_general_radial_axis_family,
     dite_eq_left hnLe,
     dite_eq_left hn1Le,
     dite_eq_left hn2Le]

  exact
    coxeter_general_neighbor_transport_with_diameter_case
      Geo
      O
      (V n)
      (V (Nat.succ n))
      (V (Nat.succ (Nat.succ n)))
      M
      radial
      hOW
      hOB
      hOC
      hOradial
      hWradial
      hMradial
      hOpp.1
      hOBOC
      hWBWC
      hMid


/--
every radial point of an oriented equilateral radial polygon is
nonzero relative to the common center.

This is just the common-radius nondegeneracy argument already used in the
Coxeter radial fan layer, now applied to the raw polygon data.
-/
theorem coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (poly : HilbertFiniteOrientedEquilateralRadialPolygon Geo p O V) :
    forall n : Nat,
      n <= p ->
      Not (O = V n) := by

  let basePoly : HilbertFiniteEquilateralRadialPolygon Geo p O V :=
    poly.toHilbertFiniteEquilateralRadialPolygon

  intro n hn

  exact
    coxeter_general_nonzero_radial_of_common_radius
      Geo
      O
      (V 0)
      (V n)
      basePoly.center_ne_base
      (basePoly.common_radius n hn)

/--
an oriented equilateral radial polygon directly generates the
entire pre-closure carrier-transport chain for its canonical radial axes.

No midpoint family and no midpoint-off-center hypothesis occur here.  All
local midpoint data are reconstructed internally by the carrier-chain theorem from the raw
Hilbert separation and congruence data of the polygon.
-/
theorem coxeter_general_carrier_chain_of_oriented_equilateral_polygon
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (poly : HilbertFiniteOrientedEquilateralRadialPolygon Geo p O V) :
    forall n : Nat,
      Nat.succ n < p ->
      ReflectionMapsLine
        Geo
        (coxeter_general_radial_axis_family
          Geo
          O
          V
          p
          (coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
            Geo p O V poly)
          (Nat.succ n))
        (coxeter_general_radial_axis_family
          Geo
          O
          V
          p
          (coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
            Geo p O V poly)
          n).carrier
        (coxeter_general_radial_axis_family
          Geo
          O
          V
          p
          (coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
            Geo p O V poly)
          (Nat.succ (Nat.succ n))).carrier := by

  let basePoly : HilbertFiniteEquilateralRadialPolygon Geo p O V :=
    poly.toHilbertFiniteEquilateralRadialPolygon

  exact
    coxeter_general_carrier_chain_with_diameter_case
      Geo
      p
      O
      V
      (coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
        Geo p O V poly)
      basePoly.common_radius
      basePoly.equal_consecutive_sides
      poly.local_radial_separation

/--
an oriented equilateral radial polygon determines canonical radial
reflection axes whose product has exact period p.

The geometric recurrence is the carrier-chain theorem.  Closure is the polygon equality
V_p = V_0, which identifies the p-th radial carrier with the initial one.
Minimality is exactly the no-early-radial-return field of the polygon.
-/
theorem coxeter_general_exact_period_of_oriented_equilateral_polygon
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (poly : HilbertFiniteOrientedEquilateralRadialPolygon Geo p O V) :
    ReflectionPairExactPeriod
      Geo
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
          Geo p O V poly)
        0)
      (coxeter_general_radial_axis_family
        Geo
        O
        V
        p
        (coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
          Geo p O V poly)
        1)
      p := by

  let hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n) :=
    coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
      Geo p O V poly

  let axis : Nat -> ReflectionAxis Geo :=
    coxeter_general_radial_axis_family
      Geo O V p hOV

  have hp : 0 < p :=
    Nat.lt_of_lt_of_le
      (by decide : 0 < 3)
      poly.period_ge_three

  have hMap :
      forall n : Nat,
        Nat.succ n < p ->
        ReflectionMapsLine
          Geo
          (axis (Nat.succ n))
          (axis n).carrier
          (axis (Nat.succ (Nat.succ n))).carrier := by

    intro n hn

    simpa only [axis, hOV] using
      coxeter_general_carrier_chain_of_oriented_equilateral_polygon
        Geo
        p
        O
        V
        poly
        n
        hn

  have hCloseCarrier :
      (axis p).carrier =
        (axis 0).carrier := by

    have hOp :
        HilbertIncidence.OnLine
          O
          (axis p).carrier := by
      exact
        coxeter_general_radial_axis_center_on_carrier
          Geo O V p hOV p (Nat.le_refl p)

    have hVp :
        HilbertIncidence.OnLine
          (V p)
          (axis p).carrier := by
      exact
        coxeter_general_radial_axis_point_on_carrier
          Geo O V p hOV p (Nat.le_refl p)

    have hO0 :
        HilbertIncidence.OnLine
          O
          (axis 0).carrier := by
      exact
        coxeter_general_radial_axis_center_on_carrier
          Geo O V p hOV 0 (Nat.zero_le p)

    have hVp0 :
        HilbertIncidence.OnLine
          (V p)
          (axis 0).carrier := by

      have hV00 :
          HilbertIncidence.OnLine
            (V 0)
            (axis 0).carrier := by
        exact
          coxeter_general_radial_axis_point_on_carrier
            Geo O V p hOV 0 (Nat.zero_le p)

      rcases poly.terminal_radial_return with
        ⟨terminal, hOterminal, hVpterminal, hV0terminal⟩

      have hTerminalEq :
          terminal = (axis 0).carrier :=
        HilbertPlaneIncidence.line_unique
          O
          (V 0)
          poly.center_ne_base
          terminal
          (axis 0).carrier
          hOterminal
          hV0terminal
          hO0
          hV00

      rw [<- hTerminalEq]
      exact hVpterminal

    exact
      coxeter_general_carriers_eq_of_two_common_points
        Geo
        (axis p)
        (axis 0)
        O
        (V p)
        (hOV p (Nat.le_refl p))
        hOp
        hVp
        hO0
        hVp0

  have hNoEarlyReturn :
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
      coxeter_general_radial_axis_point_on_carrier
        Geo
        O
        V
        p
        hOV
        q
        (Nat.le_of_lt hqLt)

    have hVq0 :
        HilbertIncidence.OnLine
          (V q)
          (axis 0).carrier := by
      rw [<- hCarrier]
      exact hVq

    have hO0 :
        HilbertIncidence.OnLine
          O
          (axis 0).carrier :=
      coxeter_general_radial_axis_center_on_carrier
        Geo
        O
        V
        p
        hOV
        0
        (Nat.zero_le p)

    have hV00 :
        HilbertIncidence.OnLine
          (V 0)
          (axis 0).carrier :=
      coxeter_general_radial_axis_point_on_carrier
        Geo
        O
        V
        p
        hOV
        0
        (Nat.zero_le p)

    have hCol :
        Collinear Geo O (V q) (V 0) :=
      Exists.intro
        (axis 0).carrier
        (And.intro
          hO0
          (And.intro
            hVq0
            hV00))

    exact
      poly.no_early_radial_return
        q
        hqPos
        hqLt
        hCol

  change
    ReflectionPairExactPeriod
      Geo
      (axis 0)
      (axis 1)
      p

  exact
    coxeter_general_exact_period_of_minimal_closed_carrier_line
      Geo
      axis
      p
      hp
      hMap
      hCloseCarrier
      hNoEarlyReturn


/-!
isolate the exact remaining geometric existence principle.

All reflection algebra and all local carrier transport have now been derived
from the raw oriented equilateral radial polygon.  The only additional datum
needed for arbitrary finite p is therefore existence of such a polygon for
every p >= 3.
-/

/--
Pure Hilbert-style existence principle for finite oriented equilateral radial
polygons.

For every p >= 3, there exist a center O and vertices V_n forming the raw
polygonal configuration used by the polygon-to-period chain.  No reflection axis, midpoint
family, angle measure, coordinates, or trigonometric datum occurs in the
statement.
-/
class HilbertFiniteOrientedEquilateralRadialPolygonExistence
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] : Prop where
  exists_oriented_equilateral_radial_polygon :
    forall p : Nat,
      3 <= p ->
      exists O : Geo.Point,
        exists V : Nat -> Geo.Point,
          HilbertFiniteOrientedEquilateralRadialPolygon
            Geo p O V

/--
The raw polygon-existence principle implies existence of two reflection axes
whose product has exact period p for every p >= 3.

This theorem is only a wrapper: all substantive Coxeter and synthetic-geometry
work lies below the polygon-existence boundary.
-/
theorem coxeter_general_exact_period_exists_of_oriented_polygon_existence
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertFiniteOrientedEquilateralRadialPolygonExistence Geo]
    (p : Nat)
    (hp : 3 <= p) :
    exists a b : ReflectionAxis Geo,
      ReflectionPairExactPeriod Geo a b p := by

  have hData :=
    HilbertFiniteOrientedEquilateralRadialPolygonExistence.exists_oriented_equilateral_radial_polygon
      (Geo := Geo)
      p
      hp

  exact
    Exists.elim hData (fun O hV =>
      Exists.elim hV (fun V poly =>
        Exists.intro
          (coxeter_general_radial_axis_family
            Geo
            O
            V
            p
            (coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
              Geo p O V poly)
            0)
          (Exists.intro
            (coxeter_general_radial_axis_family
              Geo
              O
              V
              p
              (coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
                Geo p O V poly)
              1)
            (coxeter_general_exact_period_of_oriented_equilateral_polygon
              Geo p O V poly))))

/-!
close the finite range p >= 2.

The polygon-existence principle is needed only from p = 3 upward.  Period 2
is already available in raw Hilbert congruence geometry: construct a
nondegenerate right angle, take its two carrier lines as reflection axes,
and use the established exact-period-two theorem for perpendicular axes.
-/

/--
Raw Hilbert incidence/order/congruence already supplies a pair of reflection
axes whose product has exact period 2.
-/
theorem coxeter_general_exact_period_two_exists
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    exists a b : ReflectionAxis Geo,
      ReflectionPairExactPeriod Geo a b 2 := by

  rcases
      HilbertPlaneIncidence.two_points_on_line
        (Geo := Geo) with
    ⟨base, A, C, hAC, hAbase, hCbase⟩

  rcases
      HilbertOrder.between_extension
        A C hAC with
    ⟨B, hACB⟩

  rcases
      hilbert_right_angle_exists_nondegenerate
        Geo A C B hACB with
    ⟨X, hACX, hRight⟩

  have hCA : Not (C = A) :=
    Ne.symm hAC

  have hCX : Not (C = X) := by
    intro hEq
    subst X

    exact
      hACX
        (PrimCollinear.mk
          (Geo := Geo)
          hAbase
          hCbase
          hCbase)

  let axis1 : ReflectionAxis Geo :=
    coxeter_general_axis_through
      Geo C A hCA

  let axis2 : ReflectionAxis Geo :=
    coxeter_general_axis_through
      Geo C X hCX

  have hPerp :
      ReflectionAxesPerpendicular
        Geo axis1 axis2 := by

    refine
      { O := C
        U := A
        V := X
        hO1 := ?_
        hO2 := ?_
        hU1 := ?_
        hV2 := ?_
        hOU := hCA
        hOV := hCX
        hNonCol := hACX
        hRight := hRight }

    · simpa [axis1] using
        coxeter_general_axis_through_first_on_carrier
          Geo C A hCA

    · simpa [axis2] using
        coxeter_general_axis_through_first_on_carrier
          Geo C X hCX

    · simpa [axis1] using
        coxeter_general_axis_through_second_on_carrier
          Geo C A hCA

    · simpa [axis2] using
        coxeter_general_axis_through_second_on_carrier
          Geo C X hCX

  exact
    Exists.intro axis1
      (Exists.intro axis2
        (perpendicular_axes_reflections_exact_period_two
          Geo axis1 axis2 hPerp))

/--
Assuming existence of oriented equilateral radial polygons for every
p >= 3, every finite period p >= 2 occurs as the exact period of a product
of two line reflections.

The p = 2 branch uses only the ordinary Hilbert congruence layer; the extra
polygon-existence principle is used only when p >= 3.
-/
theorem coxeter_general_exact_period_exists_of_oriented_polygon_existence_ge_two
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertFiniteOrientedEquilateralRadialPolygonExistence Geo]
    (p : Nat)
    (hp : 2 <= p) :
    exists a b : ReflectionAxis Geo,
      ReflectionPairExactPeriod Geo a b p := by

  rcases Nat.eq_or_lt_of_le hp with hEq | hLt

  · subst p
    exact
      coxeter_general_exact_period_two_exists
        Geo

  · exact
      coxeter_general_exact_period_exists_of_oriented_polygon_existence
        Geo
        p
        hLt


/-!
equal subdivision of a half-turn.

The Coxeter exact-period theorem above consumes only an oriented equilateral
radial polygon.  For the geometric existence boundary, however, we use the
stronger and more literal synthetic datum that p equal oriented chord steps
run from one radius to its opposite radius.

The half-turn endpoint is encoded without angle measure by

  Between (V 0) O (V p).

Thus no coordinates, trigonometry, numerical angle measure, or reflection
datum occurs in the existence principle itself.
-/

/--
A finite oriented equilateral subdivision of a Hilbert semicircle.

The terminal condition `Between (V 0) O (V p)` is the synthetic replacement
for saying that p equal angular steps fill one half-turn.
-/
structure HilbertFiniteOrientedEquilateralSemicircleDivision
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point) : Prop where
  period_ge_three :
    3 <= p
  common_radius :
    forall n : Nat,
      n <= p ->
      Geo.Congruent
        O
        (V n)
        O
        (V 0)
  equal_consecutive_sides :
    forall n : Nat,
      Nat.succ n < p ->
      Geo.Congruent
        (V n)
        (V (Nat.succ n))
        (V (Nat.succ n))
        (V (Nat.succ (Nat.succ n)))
  local_radial_separation :
    forall n : Nat,
      Nat.succ n < p ->
      exists radial : Geo.Line,
        HilbertIncidence.OnLine O radial /\
        HilbertIncidence.OnLine (V (Nat.succ n)) radial /\
        HilbertOppositeSide
          Geo
          (V n)
          (V (Nat.succ (Nat.succ n)))
          radial
  terminal_opposite :
    Geo.Between (V 0) O (V p)
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
A semicircle division gives the weaker first-radial-return polygon used by
the Coxeter carrier argument.

The only additional conversion is at the endpoint:
`Between (V 0) O (V p)` gives both `O != V 0` and
`Collinear O (V p) (V 0)`.
-/
theorem coxeter_general_oriented_polygon_of_semicircle_division
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (division :
      HilbertFiniteOrientedEquilateralSemicircleDivision
        Geo p O V) :
    HilbertFiniteOrientedEquilateralRadialPolygon
      Geo p O V := by

  have hV0O :
      Not (V 0 = O) :=
    (HilbertOrder.between_incidence
      (V 0) O (V p) division.terminal_opposite).1

  have hCenterNeBase :
      Not (O = V 0) :=
    Ne.symm hV0O

  have hV0OVp :
      Collinear Geo (V 0) O (V p) :=
    (HilbertOrder.between_incidence
      (V 0) O (V p) division.terminal_opposite).2.2.2.1

  have hTerminal :
      Collinear Geo O (V p) (V 0) :=
    PrimCollinearCycle
      Geo
      (V 0)
      O
      (V p)
      hV0OVp

  exact
    { period_ge_three := division.period_ge_three
      center_ne_base := hCenterNeBase
      common_radius := division.common_radius
      equal_consecutive_sides := division.equal_consecutive_sides
      terminal_radial_return := hTerminal
      no_early_radial_return := division.no_early_radial_return
      local_radial_separation := division.local_radial_separation }

/--
Existence of p-fold oriented equilateral subdivisions of a half-turn for
every p >= 3.
-/
class HilbertFiniteOrientedEquilateralSemicircleDivisionExistence
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] : Prop where
  exists_oriented_equilateral_semicircle_division :
    forall p : Nat,
      3 <= p ->
      exists O : Geo.Point,
        exists V : Nat -> Geo.Point,
          HilbertFiniteOrientedEquilateralSemicircleDivision
            Geo p O V

/--
The half-turn subdivision existence principle implies the weaker oriented
radial-polygon existence principle consumed by the Coxeter theorem.
-/
theorem coxeter_general_oriented_polygon_existence_of_semicircle_division
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertFiniteOrientedEquilateralSemicircleDivisionExistence Geo] :
    HilbertFiniteOrientedEquilateralRadialPolygonExistence Geo := by

  refine
    { exists_oriented_equilateral_radial_polygon := ?_ }

  intro p hp

  have hData :=
    HilbertFiniteOrientedEquilateralSemicircleDivisionExistence.exists_oriented_equilateral_semicircle_division
      (Geo := Geo)
      p
      hp

  exact
    Exists.elim hData (fun O hV =>
      Exists.elim hV (fun V division =>
        Exists.intro O
          (Exists.intro V
            (coxeter_general_oriented_polygon_of_semicircle_division
              Geo p O V division))))

/--
For every p >= 3, existence of an oriented equilateral subdivision of a
half-turn yields two reflection axes whose product has exact period p.
-/
theorem coxeter_general_exact_period_exists_of_semicircle_division_existence
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertFiniteOrientedEquilateralSemicircleDivisionExistence Geo]
    (p : Nat)
    (hp : 3 <= p) :
    exists a b : ReflectionAxis Geo,
      ReflectionPairExactPeriod Geo a b p := by

  rcases
      HilbertFiniteOrientedEquilateralSemicircleDivisionExistence.exists_oriented_equilateral_semicircle_division
        (Geo := Geo)
        p
        hp with
    ⟨O, V, division⟩

  have poly :
      HilbertFiniteOrientedEquilateralRadialPolygon
        Geo p O V :=
    coxeter_general_oriented_polygon_of_semicircle_division
      Geo p O V division

  let hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n) :=
    coxeter_general_radial_nonzero_of_oriented_equilateral_polygon
      Geo p O V poly

  let axis : Nat -> ReflectionAxis Geo :=
    coxeter_general_radial_axis_family
      Geo O V p hOV

  exact
    ⟨axis 0,
      axis 1,
      coxeter_general_exact_period_of_oriented_equilateral_polygon
        Geo p O V poly⟩

/--
Assuming existence of an oriented equilateral subdivision of a half-turn
for every p >= 3, every finite Coxeter period p >= 2 is realized by the
product of two Hilbert line reflections.

The case p = 2 is already available from perpendicular reflection axes.
For p >= 3, the only additional geometric assumption is existence of the
equal half-turn subdivision.
-/
theorem coxeter_general_exact_period_exists_of_semicircle_division_existence_ge_two
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertFiniteOrientedEquilateralSemicircleDivisionExistence Geo]
    (p : Nat)
    (hp : 2 <= p) :
    exists a b : ReflectionAxis Geo,
      ReflectionPairExactPeriod Geo a b p := by

  rcases Nat.eq_or_lt_of_le hp with hEq | hLt

  · subst p
    exact
      coxeter_general_exact_period_two_exists
        Geo

  · exact
      coxeter_general_exact_period_exists_of_semicircle_division_existence
        Geo
        p
        hLt

/--
Local central-angle/chord bridge.

For three points A,B,C on one circle about O, congruent consecutive
central angles imply congruent consecutive chords.  This is pure SAS.
-/
theorem coxeter_general_equal_chord_of_common_radius_equal_angle
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A B C : Geo.Point)
    (hOA_OB : Geo.Congruent O A O B)
    (hOB_OC : Geo.Congruent O B O C)
    (hAngle :
      Geo.AngleCongruent A O B B O C)
    (hAOB :
      Not (Collinear Geo O A B))
    (hBOC :
      Not (Collinear Geo O B C)) :
    Geo.Congruent A B B C := by

  have hSAS :
      TriangleCongruenceResult
        Geo
        O A B
        O B C :=
    TriangleCongruentFromSAS
      Geo
      O A B
      O B C
      hAOB
      hBOC
      hOA_OB
      hAngle
      hOB_OC

  exact hSAS.sideBC


/--
Global finite-chain form of the local central-angle/chord bridge.

If V_0,...,V_p have one common radius, consecutive central angles are
congruent, and the two local triangles are nondegenerate, then all
consecutive chord pairs required by the semicircle-division structure
are congruent.
-/
theorem coxeter_general_equal_consecutive_chords_of_common_radius_equal_angles
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (hCommonRadius :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hEqualAngles :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.AngleCongruent
          (V n)
          O
          (V (Nat.succ n))
          (V (Nat.succ n))
          O
          (V (Nat.succ (Nat.succ n))))
    (hLocalNoncollinear :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ n))) /\
        Not
          (Collinear
            Geo
            O
            (V (Nat.succ n))
            (V (Nat.succ (Nat.succ n))))) :
    forall n : Nat,
      Nat.succ n < p ->
      Geo.Congruent
        (V n)
        (V (Nat.succ n))
        (V (Nat.succ n))
        (V (Nat.succ (Nat.succ n))) := by

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

  have hOnOn1 :
      Geo.Congruent
        O
        (V n)
        O
        (V (Nat.succ n)) :=
    coxeter_general_radial_congruence_of_common_radius
      Geo
      O
      (V 0)
      (V n)
      (V (Nat.succ n))
      (hCommonRadius n hnLe)
      (hCommonRadius
        (Nat.succ n)
        hn1Le)

  have hOn1On2 :
      Geo.Congruent
        O
        (V (Nat.succ n))
        O
        (V (Nat.succ (Nat.succ n))) :=
    coxeter_general_radial_congruence_of_common_radius
      Geo
      O
      (V 0)
      (V (Nat.succ n))
      (V (Nat.succ (Nat.succ n)))
      (hCommonRadius
        (Nat.succ n)
        hn1Le)
      (hCommonRadius
        (Nat.succ (Nat.succ n))
        hn2Le)

  exact
    coxeter_general_equal_chord_of_common_radius_equal_angle
      Geo
      O
      (V n)
      (V (Nat.succ n))
      (V (Nat.succ (Nat.succ n)))
      hOnOn1
      hOn1On2
      (hEqualAngles n hn)
      (hLocalNoncollinear n hn).1
      (hLocalNoncollinear n hn).2

/--
A finite oriented equiangular subdivision of a Hilbert semicircle.

This is one step weaker than
`HilbertFiniteOrientedEquilateralSemicircleDivision`: equal consecutive
chords are replaced by equal consecutive central angles.  The common-radius,
orientation, terminal half-turn, and minimal-return data are unchanged.
-/
structure HilbertFiniteOrientedEquiangularSemicircleDivision
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point) : Prop where
  period_ge_three :
    3 <= p
  common_radius :
    forall n : Nat,
      n <= p ->
      Geo.Congruent
        O
        (V n)
        O
        (V 0)
  equal_consecutive_angles :
    forall n : Nat,
      Nat.succ n < p ->
      Geo.AngleCongruent
        (V n)
        O
        (V (Nat.succ n))
        (V (Nat.succ n))
        O
        (V (Nat.succ (Nat.succ n)))
  local_radial_separation :
    forall n : Nat,
      Nat.succ n < p ->
      exists radial : Geo.Line,
        HilbertIncidence.OnLine O radial /\
        HilbertIncidence.OnLine (V (Nat.succ n)) radial /\
        HilbertOppositeSide
          Geo
          (V n)
          (V (Nat.succ (Nat.succ n)))
          radial
  terminal_opposite :
    Geo.Between (V 0) O (V p)
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
An oriented equiangular semicircle subdivision is automatically an
oriented equilateral semicircle subdivision.

The only geometric conversion is SAS on consecutive central triangles.
Local nondegeneracy follows from the radial-separation data after first
showing that every represented radius is nonzero.
-/
theorem coxeter_general_equilateral_semicircle_division_of_equiangular
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (p : Nat)
    (O : Geo.Point)
    (V : Nat -> Geo.Point)
    (division :
      HilbertFiniteOrientedEquiangularSemicircleDivision
        Geo p O V) :
    HilbertFiniteOrientedEquilateralSemicircleDivision
      Geo p O V := by

  have hV0O :
      Not (V 0 = O) :=
    (HilbertOrder.between_incidence
      (V 0) O (V p) division.terminal_opposite).1

  have hOV0 :
      Not (O = V 0) :=
    Ne.symm hV0O

  have hOV :
      forall n : Nat,
        n <= p ->
        Not (O = V n) := by

    intro n hn hEq

    have hRadius :
        Geo.Congruent
          O
          (V n)
          O
          (V 0) :=
      division.common_radius n hn

    rw [← hEq] at hRadius

    have hNull :
        Geo.Congruent
          O
          (V 0)
          O
          O :=
      CongruentSymmetry
        Geo
        O O
        O (V 0)
        hRadius

    have hEq0 :
        O = V 0 :=
      bookZero_nullSegment1
        Geo
        O
        (V 0)
        O
        hNull

    exact hOV0 hEq0

  have hLocalNoncollinear :
      forall n : Nat,
        Nat.succ n < p ->
        Not
          (Collinear
            Geo
            O
            (V n)
            (V (Nat.succ n))) /\
        Not
          (Collinear
            Geo
            O
            (V (Nat.succ n))
            (V (Nat.succ (Nat.succ n)))) := by

    intro n hn

    rcases division.local_radial_separation n hn with
      ⟨radial, hOradial, hMiddleRadial, hOpp⟩

    have hOMiddle :
        Not (O = V (Nat.succ n)) :=
      hOV
        (Nat.succ n)
        (Nat.le_of_lt hn)

    constructor

    · intro hCol

      have hCol' :
          Collinear
            Geo
            O
            (V (Nat.succ n))
            (V n) :=
        PrimCollinearRotate
          Geo
          O
          (V n)
          (V (Nat.succ n))
          hCol

      have hOuterOn :
          HilbertIncidence.OnLine
            (V n)
            radial :=
        hilbert_collinear_on_line
          Geo
          O
          (V (Nat.succ n))
          (V n)
          radial
          hOMiddle
          hOradial
          hMiddleRadial
          hCol'

      exact hOpp.1 hOuterOn

    · intro hCol

      have hOuterOn :
          HilbertIncidence.OnLine
            (V (Nat.succ (Nat.succ n)))
            radial :=
        hilbert_collinear_on_line
          Geo
          O
          (V (Nat.succ n))
          (V (Nat.succ (Nat.succ n)))
          radial
          hOMiddle
          hOradial
          hMiddleRadial
          hCol

      exact hOpp.2.1 hOuterOn

  have hEqualSides :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.Congruent
          (V n)
          (V (Nat.succ n))
          (V (Nat.succ n))
          (V (Nat.succ (Nat.succ n))) :=
    coxeter_general_equal_consecutive_chords_of_common_radius_equal_angles
      Geo
      p
      O
      V
      division.common_radius
      division.equal_consecutive_angles
      hLocalNoncollinear

  exact
    { period_ge_three := division.period_ge_three
      common_radius := division.common_radius
      equal_consecutive_sides := hEqualSides
      local_radial_separation := division.local_radial_separation
      terminal_opposite := division.terminal_opposite
      no_early_radial_return := division.no_early_radial_return }

/--
Lay off the radius OA on the prescribed nonzero ray OR.

This is the point-level normalization primitive used to put an abstract
finite ray chain onto one Hilbert circle about O.
-/
theorem coxeter_general_point_on_ray_with_prescribed_radius
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O R A : Geo.Point)
    (hOR : Not (O = R)) :
    exists X : Geo.Point,
      HilbertSameRay Geo O R X /\
      Geo.Congruent O X O A := by

  exact
    HilbertCongruence.segment_construction
      (Geo := Geo)
      O A
      O R
      hOR


/--
Angle congruence is unchanged when each side is represented by another
point on the same ray from the common vertex.
-/
theorem coxeter_general_angle_congruent_of_same_rays
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A B A' B' C D C' D' : Geo.Point)
    (hAA' : HilbertSameRay Geo O A A')
    (hBB' : HilbertSameRay Geo O B B')
    (hCC' : HilbertSameRay Geo O C C')
    (hDD' : HilbertSameRay Geo O D D')
    (hAngle :
      Geo.AngleCongruent
        A O B
        C O D) :
    Geo.AngleCongruent
      A' O B'
      C' O D' := by

  have hLeftFirst :
      Geo.Angle A O B =
      Geo.Angle A' O B :=
    hilbert_angle_eq_of_sameRay_first
      Geo O A A' B hAA'

  have hLeftSecond :
      Geo.Angle A' O B =
      Geo.Angle A' O B' :=
    hilbert_angle_eq_of_sameRay_second
      Geo O A' B B' hBB'

  have hLeft :
      Geo.Angle A O B =
      Geo.Angle A' O B' := by
    calc
      Geo.Angle A O B =
          Geo.Angle A' O B := hLeftFirst
      _ =
          Geo.Angle A' O B' := hLeftSecond

  have hRightFirst :
      Geo.Angle C O D =
      Geo.Angle C' O D :=
    hilbert_angle_eq_of_sameRay_first
      Geo O C C' D hCC'

  have hRightSecond :
      Geo.Angle C' O D =
      Geo.Angle C' O D' :=
    hilbert_angle_eq_of_sameRay_second
      Geo O C' D D' hDD'

  have hRight :
      Geo.Angle C O D =
      Geo.Angle C' O D' := by
    calc
      Geo.Angle C O D =
          Geo.Angle C' O D := hRightFirst
      _ =
          Geo.Angle C' O D' := hRightSecond

  unfold Geometry.Geo.AngleCongruent at hAngle ⊢

  rw [← hLeft, ← hRight]

  exact hAngle

/--
An oriented half-pencil at `O`.

`OA` and `OAstar` are opposite boundary rays.  The point `S`, lying off their
common carrier, selects one of the two half-planes and therefore one of the
two half-pencils bounded by those opposite rays.
-/
structure HilbertOrientedHalfPencil
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    (O A Astar S : Geo.Point) where
  base :
    Geo.Line
  boundary_opposite :
    Geo.OppositeRays O A Astar
  origin_on_base :
    HilbertIncidence.OnLine O base
  start_on_base :
    HilbertIncidence.OnLine A base
  terminal_on_base :
    HilbertIncidence.OnLine Astar base
  side_selector_off_base :
    Not (HilbertIncidence.OnLine S base)

/--
An extensional ray belongs to the open part of the chosen half-pencil when
it has a representative point on the same side of the boundary carrier as
the selector point `S`.
-/
def HilbertRayInOpenHalfPencil
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (r : Geo.Ray) : Prop :=
  exists X : Geo.Point,
    r = Geo.ray O X /\
    HilbertSameSide Geo X S hp.base

/--
The closed half-pencil consists of its two boundary rays together with its
open rays.
-/
def HilbertRayInClosedHalfPencil
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (r : Geo.Ray) : Prop :=
  r = Geo.ray O A \/
  r = Geo.ray O Astar \/
  HilbertRayInOpenHalfPencil Geo O A Astar S hp r

/--
Strict order on the chosen half-pencil, from `OA` toward `OAstar`.
-/
def HilbertHalfPencilRayLess
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (r s : Geo.Ray) : Prop :=
  (r = Geo.ray O A /\
    HilbertRayInClosedHalfPencil Geo O A Astar S hp s /\
    Not (s = Geo.ray O A))
  \/
  (HilbertRayInOpenHalfPencil Geo O A Astar S hp r /\
    s = Geo.ray O Astar)
  \/
  exists X Y : Geo.Point,
    r = Geo.ray O X /\
    s = Geo.ray O Y /\
    HilbertSameSide Geo X S hp.base /\
    HilbertSameSide Geo Y S hp.base /\
    HilbertRayMeetsSegment Geo O X A Y

/--
A finite chain of p consecutive congruent angular steps inside one oriented
half-pencil.
-/
structure HilbertHalfPencilEqualAngleChain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p) where
  V :
    Fin (p + 1) -> Geo.Point
  start_ray :
    Geo.ray O (V 0) = Geo.ray O A
  ray_mem :
    forall i : Fin (p + 1),
      HilbertRayInClosedHalfPencil
        Geo O A Astar S hp
        (Geo.ray O (V i))
  strict_step :
    forall i : Fin p,
      HilbertHalfPencilRayLess
        Geo O A Astar S hp
        (Geo.ray O (V i.castSucc))
        (Geo.ray O (V i.succ))
  equal_step :
    forall i : Fin p,
      Geo.AngleCongruent
        (V i.castSucc)
        O
        (V i.succ)
        (V 0)
        O
        (V ⟨1, Nat.succ_lt_succ hpos⟩)

/--
Normalize a finite equal-angle ray chain onto one circle about O.

Assuming only that every point representative of the chain is nonzero,
choose on each represented ray a point at the fixed radius OA.  The new
points remain on the same rays, have one common radius, and preserve all
equal-angle step relations.
-/
theorem coxeter_general_normalize_equal_angle_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (hNonzero :
      forall i : Fin (p + 1),
        Not (O = chain.V i)) :
    exists W : Fin (p + 1) -> Geo.Point,
      (forall i : Fin (p + 1),
        HilbertSameRay Geo O (chain.V i) (W i)) /\
      (forall i : Fin (p + 1),
        Geo.Congruent O (W i) O A) /\
      (forall i : Fin p,
        Geo.AngleCongruent
          (W i.castSucc)
          O
          (W i.succ)
          (W 0)
          O
          (W ⟨1, Nat.succ_lt_succ hpos⟩)) := by

  classical

  have hExists :
      forall i : Fin (p + 1),
        exists X : Geo.Point,
          HilbertSameRay Geo O (chain.V i) X /\
          Geo.Congruent O X O A := by

    intro i

    exact
      coxeter_general_point_on_ray_with_prescribed_radius
        Geo
        O
        (chain.V i)
        A
        (hNonzero i)

  let W : Fin (p + 1) -> Geo.Point :=
    fun i => Classical.choose (hExists i)

  have hRay :
      forall i : Fin (p + 1),
        HilbertSameRay Geo O (chain.V i) (W i) := by

    intro i
    exact (Classical.choose_spec (hExists i)).1

  have hRadius :
      forall i : Fin (p + 1),
        Geo.Congruent O (W i) O A := by

    intro i
    exact (Classical.choose_spec (hExists i)).2

  have hEqual :
      forall i : Fin p,
        Geo.AngleCongruent
          (W i.castSucc)
          O
          (W i.succ)
          (W 0)
          O
          (W ⟨1, Nat.succ_lt_succ hpos⟩) := by

    intro i

    exact
      coxeter_general_angle_congruent_of_same_rays
        Geo
        O
        (chain.V i.castSucc)
        (chain.V i.succ)
        (W i.castSucc)
        (W i.succ)
        (chain.V 0)
        (chain.V ⟨1, Nat.succ_lt_succ hpos⟩)
        (W 0)
        (W ⟨1, Nat.succ_lt_succ hpos⟩)
        (hRay i.castSucc)
        (hRay i.succ)
        (hRay 0)
        (hRay ⟨1, Nat.succ_lt_succ hpos⟩)
        (chain.equal_step i)

  exact
    ⟨W, hRay, hRadius, hEqual⟩

/--
If the extensional ray OX is equal to a ray OB determined by a non-origin
point B, then X itself is non-origin.
-/
theorem coxeter_general_nonzero_of_ray_eq_nonzero
    (Geo : Geometry.Geo)
    (O X B : Geo.Point)
    (hBO : Not (B = O))
    (hRay : Geo.ray O X = Geo.ray O B) :
    Not (O = X) := by

  intro hOX

  have hBmemB :
      (Geo.ray O B) B := by
    change
      B = O \/
      Relation.ReflTransGen
        (Geo.SameDirectionStep O) B B
    exact Or.inr Relation.ReflTransGen.refl

  subst X

  have hBmemO :
      (Geo.ray O O) B := by
    rw [hRay]
    exact hBmemB

  change
    B = O \/
    Relation.ReflTransGen
      (Geo.SameDirectionStep O) O B
    at hBmemO

  rcases hBmemO with hEq | hPath

  · exact hBO hEq

  · have origin_path_eq :
        forall {Q : Geo.Point},
          Relation.ReflTransGen
            (Geo.SameDirectionStep O) O Q ->
          Q = O := by
      intro Q h
      induction h with
      | refl =>
          rfl
      | @tail P Q hPath hStep ih =>
          exact False.elim (hStep.1 ih)

    exact hBO (origin_path_eq hPath)

/--
Every point representative of a ray in a closed oriented half-pencil is
nonzero relative to the common origin.
-/
theorem coxeter_general_closed_half_pencil_representative_nonzero
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    (O A Astar S X : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (hClosed :
      HilbertRayInClosedHalfPencil
        Geo O A Astar S hp
        (Geo.ray O X)) :
    Not (O = X) := by

  rcases hClosed with hStart | hRest

  · exact
      coxeter_general_nonzero_of_ray_eq_nonzero
        Geo O X A
        hp.boundary_opposite.1
        hStart

  · rcases hRest with hTerminal | hOpen

    · exact
        coxeter_general_nonzero_of_ray_eq_nonzero
          Geo O X Astar
          hp.boundary_opposite.2.1
          hTerminal

    · rcases hOpen with ⟨Y, hRayXY, hYS⟩

      have hYO : Not (Y = O) := by
        intro h
        subst Y
        exact hYS.1 hp.origin_on_base

      exact
        coxeter_general_nonzero_of_ray_eq_nonzero
          Geo O X Y
          hYO
          hRayXY

/--
Normalize a finite equal-angle chain in a closed oriented half-pencil onto one
circle about O.  Nonzeroness of the original representatives follows from
closed-half-pencil membership and need not be supplied separately.
-/
theorem coxeter_general_normalize_equal_angle_chain_closed
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos) :
    exists W : Fin (p + 1) -> Geo.Point,
      (forall i : Fin (p + 1),
        HilbertSameRay Geo O (chain.V i) (W i)) /\
      (forall i : Fin (p + 1),
        Geo.Congruent O (W i) O A) /\
      (forall i : Fin p,
        Geo.AngleCongruent
          (W i.castSucc)
          O
          (W i.succ)
          (W 0)
          O
          (W ⟨1, Nat.succ_lt_succ hpos⟩)) := by

  have hNonzero :
      forall i : Fin (p + 1),
        Not (O = chain.V i) := by
    intro i
    exact
      coxeter_general_closed_half_pencil_representative_nonzero
        Geo
        O A Astar S
        (chain.V i)
        hp
        (chain.ray_mem i)

  exact
    coxeter_general_normalize_equal_angle_chain
      Geo
      O A Astar S
      hp
      p hpos
      chain
      hNonzero

/--
Extend a normalized finite chain indexed by `Fin (p+1)` to a total
`Nat -> Point` function while preserving all data on indices `0,...,p`.

Outside the finite range the total function is arbitrary; no later theorem
uses those values.
-/
theorem coxeter_general_normalized_chain_to_nat
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (W : Fin (p + 1) -> Geo.Point)
    (hRay :
      forall i : Fin (p + 1),
        HilbertSameRay Geo O (chain.V i) (W i))
    (hRadius :
      forall i : Fin (p + 1),
        Geo.Congruent O (W i) O A)
    (hEqual :
      forall i : Fin p,
        Geo.AngleCongruent
          (W i.castSucc)
          O
          (W i.succ)
          (W 0)
          O
          (W ⟨1, Nat.succ_lt_succ hpos⟩)) :
    exists V : Nat -> Geo.Point,
      (forall n : Nat,
        forall hn : n <= p,
          V n =
            W ⟨n, Nat.lt_succ_iff.mpr hn⟩) /\
      (forall n : Nat,
        forall hn : n <= p,
          HilbertSameRay
            Geo
            O
            (chain.V ⟨n, Nat.lt_succ_iff.mpr hn⟩)
            (V n)) /\
      (forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0)) /\
      (forall n : Nat,
        Nat.succ n < p ->
        Geo.AngleCongruent
          (V n)
          O
          (V (Nat.succ n))
          (V (Nat.succ n))
          O
          (V (Nat.succ (Nat.succ n)))) := by

  classical

  let V : Nat -> Geo.Point :=
    fun n =>
      if hn : n <= p then
        W ⟨n, Nat.lt_succ_iff.mpr hn⟩
      else
        W 0

  have hAgree :
      forall n : Nat,
        forall hn : n <= p,
          V n =
            W ⟨n, Nat.lt_succ_iff.mpr hn⟩ := by

    intro n hn
    simp [V, hn]

  have hRayNat :
      forall n : Nat,
        forall hn : n <= p,
          HilbertSameRay
            Geo
            O
            (chain.V ⟨n, Nat.lt_succ_iff.mpr hn⟩)
            (V n) := by

    intro n hn

    rw [hAgree n hn]

    exact
      hRay ⟨n, Nat.lt_succ_iff.mpr hn⟩

  have hCommon :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0) := by

    intro n hn

    have h0 :
        0 <= p :=
      Nat.zero_le p

    rw [hAgree n hn, hAgree 0 h0]

    exact
      coxeter_general_radial_congruence_of_common_radius
        Geo
        O
        A
        (W ⟨n, Nat.lt_succ_iff.mpr hn⟩)
        (W ⟨0, Nat.lt_succ_iff.mpr h0⟩)
        (hRadius ⟨n, Nat.lt_succ_iff.mpr hn⟩)
        (hRadius ⟨0, Nat.lt_succ_iff.mpr h0⟩)

  have hEqualNat :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.AngleCongruent
          (V n)
          O
          (V (Nat.succ n))
          (V (Nat.succ n))
          O
          (V (Nat.succ (Nat.succ n))) := by

    intro n hn

    have hn0 :
        n <= p :=
      Nat.le_trans
        (Nat.le_succ n)
        (Nat.le_of_lt hn)

    have hn1 :
        Nat.succ n <= p :=
      Nat.le_of_lt hn

    have hn2 :
        Nat.succ (Nat.succ n) <= p :=
      Nat.succ_le_of_lt hn

    rw [
      hAgree n hn0,
      hAgree (Nat.succ n) hn1,
      hAgree (Nat.succ (Nat.succ n)) hn2
    ]

    let i : Fin p :=
      ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩

    let j : Fin p :=
      ⟨Nat.succ n, hn⟩

    have hFirst :
        Geo.AngleCongruent
          (W ⟨n, Nat.lt_succ_iff.mpr hn0⟩)
          O
          (W ⟨Nat.succ n, Nat.lt_succ_iff.mpr hn1⟩)
          (W 0)
          O
          (W ⟨1, Nat.succ_lt_succ hpos⟩) := by

      simpa [i] using hEqual i

    have hSecond :
        Geo.AngleCongruent
          (W ⟨Nat.succ n, Nat.lt_succ_iff.mpr hn1⟩)
          O
          (W ⟨Nat.succ (Nat.succ n), Nat.lt_succ_iff.mpr hn2⟩)
          (W 0)
          O
          (W ⟨1, Nat.succ_lt_succ hpos⟩) := by

      simpa [j] using hEqual j

    have hSecondSymm :
        Geo.AngleCongruent
          (W 0)
          O
          (W ⟨1, Nat.succ_lt_succ hpos⟩)
          (W ⟨Nat.succ n, Nat.lt_succ_iff.mpr hn1⟩)
          O
          (W ⟨Nat.succ (Nat.succ n), Nat.lt_succ_iff.mpr hn2⟩) :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        (W ⟨Nat.succ n, Nat.lt_succ_iff.mpr hn1⟩)
        O
        (W ⟨Nat.succ (Nat.succ n), Nat.lt_succ_iff.mpr hn2⟩)
        (W 0)
        O
        (W ⟨1, Nat.succ_lt_succ hpos⟩)
        hSecond

    exact
      Geometry.Geo.angle_congruent_transitivity
        Geo
        (W ⟨n, Nat.lt_succ_iff.mpr hn0⟩)
        O
        (W ⟨Nat.succ n, Nat.lt_succ_iff.mpr hn1⟩)
        (W 0)
        O
        (W ⟨1, Nat.succ_lt_succ hpos⟩)
        (W ⟨Nat.succ n, Nat.lt_succ_iff.mpr hn1⟩)
        O
        (W ⟨Nat.succ (Nat.succ n), Nat.lt_succ_iff.mpr hn2⟩)
        hFirst
        hSecondSymm

  exact
    ⟨V,
      hAgree,
      hRayNat,
      hCommon,
      hEqualNat⟩

/--
One `SameDirectionStep` is already a Hilbert same-ray relation.
-/
theorem coxeter_general_sameRay_of_sameDirectionStep
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O P Q : Geo.Point)
    (hStep : Geo.SameDirectionStep O P Q) :
    HilbertSameRay Geo O P Q := by

  rcases hStep with
    ⟨hPO, hQO, hPQ | hOPQ | hOQP⟩

  · subst Q
    exact
      hilbert_sameRay_refl
        Geo O P hPO

  · exact
      hilbert_sameRay_of_between
        Geo O P Q hOPQ

  · exact
      hilbert_sameRay_symm
        Geo O Q P
        (hilbert_sameRay_of_between
          Geo O Q P hOQP)


/--
A finite chain of `SameDirectionStep`s determines one Hilbert ray.
-/
theorem coxeter_general_sameRay_of_sameDirectionPath
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O P Q : Geo.Point)
    (hPO : Not (P = O))
    (hPath :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O) P Q) :
    HilbertSameRay Geo O P Q := by

  induction hPath with

  | refl =>
      exact
        hilbert_sameRay_refl
          Geo O P hPO

  | @tail B C hPath hStep ih =>

      have hBC :
          HilbertSameRay Geo O B C :=
        coxeter_general_sameRay_of_sameDirectionStep
          Geo O B C hStep

      have hBP :
          HilbertSameRay Geo O B P :=
        hilbert_sameRay_symm
          Geo O P B ih

      exact
        hilbert_sameRay_of_common
          Geo O B P C
          hBP hBC



/--
Conversely to `hilbert_sameRay_ray_eq`, equality of two extensional rays
through non-origin points implies the Hilbert same-ray relation.
-/
theorem coxeter_general_sameRay_of_ray_eq
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O P Q : Geo.Point)
    (hPO : Not (P = O))
    (hQO : Not (Q = O))
    (hEq :
      Geo.ray O P = Geo.ray O Q) :
    HilbertSameRay Geo O P Q := by

  have hQmemQ :
      (Geo.ray O Q) Q := by
    change
      Q = O \/
      Relation.ReflTransGen
        (Geo.SameDirectionStep O) Q Q
    exact
      Or.inr Relation.ReflTransGen.refl

  have hQmemP :
      (Geo.ray O P) Q := by
    rw [hEq]
    exact hQmemQ

  change
    Q = O \/
    Relation.ReflTransGen
      (Geo.SameDirectionStep O) P Q
    at hQmemP

  rcases hQmemP with
    hQOrigin | hPath

  · exact
      False.elim
        (hQO hQOrigin)

  · exact
      coxeter_general_sameRay_of_sameDirectionPath
        Geo O P Q hPO hPath



/--
Transport the opposite terminal boundary of an oriented half-pencil to the
normalized Nat-indexed representatives of the first and last chain rays.
-/
theorem coxeter_general_terminal_opposite_of_normalized_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (V : Nat -> Geo.Point)
    (hRayNat :
      forall n : Nat,
        forall hn : n <= p,
          HilbertSameRay
            Geo
            O
            (chain.V
              ⟨n, Nat.lt_succ_iff.mpr hn⟩)
            (V n))
    (hTerminal :
      Geo.ray O (chain.V (Fin.last p)) =
        Geo.ray O Astar) :
    Geo.Between (V 0) O (V p) := by

  have h0Le :
      0 <= p :=
    Nat.zero_le p

  have hpLe :
      p <= p :=
    Nat.le_refl p

  have hChain0NeO :
      Not (chain.V 0 = O) := by
    exact
      Ne.symm
        (coxeter_general_closed_half_pencil_representative_nonzero
          Geo
          O A Astar S
          (chain.V 0)
          hp
          (chain.ray_mem 0))

  have hChainPNeO :
      Not (chain.V (Fin.last p) = O) := by
    exact
      Ne.symm
        (coxeter_general_closed_half_pencil_representative_nonzero
          Geo
          O A Astar S
          (chain.V (Fin.last p))
          hp
          (chain.ray_mem (Fin.last p)))

  have hChain0A :
      HilbertSameRay
        Geo O
        (chain.V 0)
        A :=
    coxeter_general_sameRay_of_ray_eq
      Geo
      O
      (chain.V 0)
      A
      hChain0NeO
      hp.boundary_opposite.1
      chain.start_ray

  have hChainPAstar :
      HilbertSameRay
        Geo O
        (chain.V (Fin.last p))
        Astar :=
    coxeter_general_sameRay_of_ray_eq
      Geo
      O
      (chain.V (Fin.last p))
      Astar
      hChainPNeO
      hp.boundary_opposite.2.1
      hTerminal

  have hRay0 :
      HilbertSameRay
        Geo O
        (chain.V
          ⟨0, Nat.lt_succ_iff.mpr h0Le⟩)
        (V 0) :=
    hRayNat 0 h0Le

  have hRayP :
      HilbertSameRay
        Geo O
        (chain.V
          ⟨p, Nat.lt_succ_iff.mpr hpLe⟩)
        (V p) :=
    hRayNat p hpLe

  have hA_V0 :
      HilbertSameRay Geo O A (V 0) := by

    have hCommonV0 :
        HilbertSameRay
          Geo O
          (chain.V 0)
          (V 0) := by
      simpa using hRay0

    exact
      bookZero_36_ray3
        Geo O
        (chain.V 0)
        A
        (V 0)
        hChain0A
        hCommonV0

  have hAstar_Vp :
      HilbertSameRay Geo O Astar (V p) := by

    have hCommonVp :
        HilbertSameRay
          Geo O
          (chain.V (Fin.last p))
          (V p) := by
      simpa [Fin.last] using hRayP

    exact
      bookZero_36_ray3
        Geo O
        (chain.V (Fin.last p))
        Astar
        (V p)
        hChainPAstar
        hCommonVp

  exact
    hilbert_between_transport_sameRays
      Geo
      A O Astar
      (V 0) (V p)
      hp.boundary_opposite.2.2
      hA_V0
      hAstar_Vp

/--
An off-base point cannot determine the same ray as a non-origin point on
the boundary carrier.
-/
theorem coxeter_general_off_base_ray_ne_boundary_ray
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O A Astar S X B : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (hXS : HilbertSameSide Geo X S hp.base)
    (hBO : Not (B = O))
    (hBbase : HilbertIncidence.OnLine B hp.base) :
    Not (Geo.ray O X = Geo.ray O B) := by

  intro hRay

  have hXO :
      Not (X = O) := by
    intro h
    subst X
    exact hXS.1 hp.origin_on_base

  have hSameXB :
      HilbertSameRay Geo O X B :=
    coxeter_general_sameRay_of_ray_eq
      Geo O X B
      hXO hBO
      hRay

  have hOB :
      Not (O = B) := by
    intro h
    exact hBO h.symm

  have hXbase :
      HilbertIncidence.OnLine X hp.base :=
    hilbert_collinear_on_line
      Geo
      O B X
      hp.base
      hOB
      hp.origin_on_base
      hBbase
      (PrimCollinearRotate
        Geo O X B hSameXB.2.2.1)

  exact hXS.1 hXbase


/--
A boundary ray is not an open ray of its own oriented half-pencil.
-/
theorem coxeter_general_boundary_ray_not_open_half_pencil
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O A Astar S B : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (hBO : Not (B = O))
    (hBbase : HilbertIncidence.OnLine B hp.base) :
    Not
      (HilbertRayInOpenHalfPencil
        Geo O A Astar S hp
        (Geo.ray O B)) := by

  intro hOpen

  rcases hOpen with
    ⟨X, hRayBX, hXS⟩

  have hNe :
      Not (Geo.ray O X = Geo.ray O B) :=
    coxeter_general_off_base_ray_ne_boundary_ray
      Geo
      O A Astar S
      X B
      hp
      hXS
      hBO
      hBbase

  exact hNe hRayBX.symm


/--
The two opposite boundary rays of an oriented half-pencil are distinct.
-/
theorem coxeter_general_half_pencil_boundary_rays_ne
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S) :
    Not (Geo.ray O Astar = Geo.ray O A) := by

  intro hRay

  have hSame :
      HilbertSameRay Geo O Astar A :=
    coxeter_general_sameRay_of_ray_eq
      Geo O Astar A
      hp.boundary_opposite.2.1
      hp.boundary_opposite.1
      hRay

  have hAstarOA :
      Geo.Between Astar O A :=
    (HilbertOrder.between_incidence
      A O Astar
      hp.boundary_opposite.2.2).2.2.2.2

  exact hSame.2.2.2 hAstarOA


/--
The terminal boundary ray cannot be strictly less than another ray.
-/
theorem coxeter_general_terminal_ray_not_less
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (s : Geo.Ray) :
    Not
      (HilbertHalfPencilRayLess
        Geo O A Astar S hp
        (Geo.ray O Astar)
        s) := by

  intro hLess

  have hTerminalNotOpen :
      Not
        (HilbertRayInOpenHalfPencil
          Geo O A Astar S hp
          (Geo.ray O Astar)) :=
    coxeter_general_boundary_ray_not_open_half_pencil
      Geo
      O A Astar S
      Astar
      hp
      hp.boundary_opposite.2.1
      hp.terminal_on_base

  rcases hLess with
    hStart | hRest

  · exact
      (coxeter_general_half_pencil_boundary_rays_ne
        Geo O A Astar S hp)
        hStart.1

  · rcases hRest with
      hTerminal | hOpen

    · exact
        hTerminalNotOpen hTerminal.1

    · rcases hOpen with
        ⟨X, Y,
          hRayAstarX,
          _hRaySY,
          hXS,
          _hYS,
          _hMeet⟩

      exact
        hTerminalNotOpen
          ⟨X, hRayAstarX, hXS⟩


/--
No ray is strictly before the start boundary ray.
-/
theorem coxeter_general_start_ray_not_greater
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (r : Geo.Ray) :
    Not
      (HilbertHalfPencilRayLess
        Geo O A Astar S hp
        r
        (Geo.ray O A)) := by

  intro hLess

  rcases hLess with
    hStart | hRest

  · exact
      hStart.2.2 rfl

  · rcases hRest with
      hTerminal | hOpen

    · exact
        (coxeter_general_half_pencil_boundary_rays_ne
          Geo O A Astar S hp)
          hTerminal.2.symm

    · rcases hOpen with
        ⟨X, Y,
          _hRayRX,
          hRayAY,
          _hXS,
          hYS,
          _hMeet⟩

      exact
        (coxeter_general_off_base_ray_ne_boundary_ray
          Geo
          O A Astar S
          Y A
          hp
          hYS
          hp.boundary_opposite.1
          hp.start_on_base)
          hRayAY.symm


/--
A normalized equal-angle chain has no early radial return to the initial
carrier.

For `0 < q < p`, collinearity of `O,V_q,V_0` would force the closed
half-pencil ray of `V_q` to be either the start boundary, the terminal
boundary, or an open ray represented by a point on the base.  The first
two cases contradict the adjacent strict steps; the open case contradicts
side-of-line separation.
-/
theorem coxeter_general_no_early_radial_return_of_normalized_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (V : Nat -> Geo.Point)
    (hRayNat :
      forall n : Nat,
        forall hn : n <= p,
          HilbertSameRay
            Geo
            O
            (chain.V
              ⟨n, Nat.lt_succ_iff.mpr hn⟩)
            (V n)) :
    forall q : Nat,
      0 < q ->
      q < p ->
      Not (Collinear Geo O (V q) (V 0)) := by

  intro q hqPos hqLt hCol

  have hqLe :
      q <= p :=
    Nat.le_of_lt hqLt

  have h0Le :
      0 <= p :=
    Nat.zero_le p

  have hRayQ :
      HilbertSameRay
        Geo O
        (chain.V
          ⟨q, Nat.lt_succ_iff.mpr hqLe⟩)
        (V q) :=
    hRayNat q hqLe

  have hRay0 :
      HilbertSameRay
        Geo O
        (chain.V
          ⟨0, Nat.lt_succ_iff.mpr h0Le⟩)
        (V 0) :=
    hRayNat 0 h0Le

  have hRayEqQ :
      Geo.ray O
          (chain.V
            ⟨q, Nat.lt_succ_iff.mpr hqLe⟩) =
        Geo.ray O (V q) :=
    hilbert_sameRay_ray_eq
      Geo
      O
      (chain.V
        ⟨q, Nat.lt_succ_iff.mpr hqLe⟩)
      (V q)
      hRayQ

  have hClosedQ :
      HilbertRayInClosedHalfPencil
        Geo O A Astar S hp
        (Geo.ray O (V q)) := by
    rw [<- hRayEqQ]
    exact
      chain.ray_mem
        ⟨q, Nat.lt_succ_iff.mpr hqLe⟩

  have hChain0A :
      HilbertSameRay Geo O (chain.V 0) A :=
    coxeter_general_sameRay_of_ray_eq
      Geo
      O
      (chain.V 0)
      A
      (Ne.symm
        (coxeter_general_closed_half_pencil_representative_nonzero
          Geo
          O A Astar S
          (chain.V 0)
          hp
          (chain.ray_mem 0)))
      hp.boundary_opposite.1
      chain.start_ray

  have hA_V0 :
      HilbertSameRay Geo O A (V 0) := by

    have hCommonV0 :
        HilbertSameRay Geo O (chain.V 0) (V 0) := by
      simpa using hRay0

    exact
      bookZero_36_ray3
        Geo O
        (chain.V 0)
        A
        (V 0)
        hChain0A
        hCommonV0

  have hV0base :
      HilbertIncidence.OnLine (V 0) hp.base :=
    hilbert_collinear_on_line
      Geo
      O A (V 0)
      hp.base
      hp.boundary_opposite.1.symm
      hp.origin_on_base
      hp.start_on_base
      hA_V0.2.2.1

  have hVqbase :
      HilbertIncidence.OnLine (V q) hp.base := by

    rcases hCol with
      ⟨line, hOline, hVqline, hV0line⟩

    have hLineEq :
        line = hp.base :=
      HilbertPlaneIncidence.line_unique
        O (V 0)
        hRay0.2.1.symm
        line hp.base
        hOline hV0line
        hp.origin_on_base hV0base

    exact hLineEq ▸ hVqline

  rcases hClosedQ with
    hStart | hRest

  · cases q with

    | zero =>
        exact False.elim (Nat.lt_asymm hqPos hqPos)

    | succ n =>

        have hnLt :
            n < p :=
          Nat.lt_trans
            (Nat.lt_succ_self n)
            hqLt

        let i : Fin p :=
          ⟨n, hnLt⟩

        have hChainQStart :
            Geo.ray O
                (chain.V
                  ⟨Nat.succ n,
                    Nat.lt_succ_iff.mpr
                      (Nat.le_of_lt hqLt)⟩) =
              Geo.ray O A := by
          exact hRayEqQ.trans hStart

        have hPrevLess :
            HilbertHalfPencilRayLess
              Geo O A Astar S hp
              (Geo.ray O (chain.V i.castSucc))
              (Geo.ray O A) := by

          rw [<- hChainQStart]

          simpa [i] using
            chain.strict_step i

        exact
          (coxeter_general_start_ray_not_greater
            Geo
            O A Astar S
            hp
            (Geo.ray O (chain.V i.castSucc)))
            hPrevLess

  · rcases hRest with
      hTerminal | hOpen

    · let j : Fin p :=
        ⟨q, hqLt⟩

      have hChainQTerminal :
          Geo.ray O
              (chain.V
                ⟨q, Nat.lt_succ_iff.mpr hqLe⟩) =
            Geo.ray O Astar :=
        hRayEqQ.trans hTerminal

      have hNextLess :
          HilbertHalfPencilRayLess
            Geo O A Astar S hp
            (Geo.ray O Astar)
            (Geo.ray O (chain.V j.succ)) := by

        rw [<- hChainQTerminal]

        simpa [j] using
          chain.strict_step j

      exact
        (coxeter_general_terminal_ray_not_less
          Geo
          O A Astar S
          hp
          (Geo.ray O (chain.V j.succ)))
          hNextLess

    · rcases hOpen with
        ⟨X, hRayVqX, hXS⟩

      have hVqNeO :
          Not (V q = O) :=
        hRayQ.2.1

      exact
        (coxeter_general_off_base_ray_ne_boundary_ray
          Geo
          O A Astar S
          X (V q)
          hp
          hXS
          hVqNeO
          hVqbase)
          hRayVqX.symm

/--
If the ray OY meets the open segment XZ, and X and Z are off the carrier
of OY, then X and Z lie on opposite sides of that carrier.

This is the point-line core needed for the local radial-separation field.
-/
theorem coxeter_general_opposite_side_of_middle_ray_meets_segment
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O X Y Z : Geo.Point)
    (hMeet :
      HilbertRayMeetsSegment Geo O Y X Z) :
    exists radial : Geo.Line,
      HilbertIncidence.OnLine O radial /\
      HilbertIncidence.OnLine Y radial /\
      ((Not (HilbertIncidence.OnLine X radial) /\
        Not (HilbertIncidence.OnLine Z radial)) ->
        HilbertOppositeSide Geo X Z radial) := by

  rcases hMeet with
    ⟨T, hXTZ, hRayYT⟩

  have hOY :
      Not (O = Y) :=
    Ne.symm hRayYT.1

  rcases
      HilbertPlaneIncidence.line_through
        O Y hOY with
    ⟨radial, hOradial, hYradial⟩

  have hTradial :
      HilbertIncidence.OnLine T radial :=
    hilbert_collinear_on_line
      Geo
      O Y T
      radial
      hOY
      hOradial
      hYradial
      hRayYT.2.2.1

  exact
    ⟨radial,
      hOradial,
      hYradial,
      by
        rintro ⟨hXoff, hZoff⟩
        exact
          ⟨hXoff,
            hZoff,
            ⟨T, hXTZ, hTradial⟩⟩⟩


/--
A more convenient form: once the two outer points are known not to lie on
the middle radial carrier, the local radial-separation package follows.
-/
theorem coxeter_general_local_radial_separation_of_middle_ray_meets
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O X Y Z : Geo.Point)
    (radial : Geo.Line)
    (hOradial :
      HilbertIncidence.OnLine O radial)
    (hYradial :
      HilbertIncidence.OnLine Y radial)
    (hXoff :
      Not (HilbertIncidence.OnLine X radial))
    (hZoff :
      Not (HilbertIncidence.OnLine Z radial))
    (hMeet :
      HilbertRayMeetsSegment Geo O Y X Z) :
    HilbertOppositeSide Geo X Z radial := by

  rcases hMeet with
    ⟨T, hXTZ, hRayYT⟩

  have hOY :
      Not (O = Y) :=
    Ne.symm hRayYT.1

  have hTradial :
      HilbertIncidence.OnLine T radial :=
    hilbert_collinear_on_line
      Geo
      O Y T
      radial
      hOY
      hOradial
      hYradial
      hRayYT.2.2.1

  exact
    ⟨hXoff,
      hZoff,
      ⟨T, hXTZ, hTradial⟩⟩

/--
Three successive open rays in one oriented half-pencil give exactly the
local radial-separation package needed by the semicircle division.

The hypotheses are point-level strict-order witnesses:
  OX < OY < OZ.
The carrier of OY separates X and Z.
-/
theorem coxeter_general_open_triple_local_radial_separation
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S X Y Z : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (hXS : HilbertSameSide Geo X S hp.base)
    (hYS : HilbertSameSide Geo Y S hp.base)
    (_hZS : HilbertSameSide Geo Z S hp.base)
    (hXY : HilbertRayMeetsSegment Geo O X A Y)
    (hYZ : HilbertRayMeetsSegment Geo O Y A Z) :
    exists radial : Geo.Line,
      HilbertIncidence.OnLine O radial /\
      HilbertIncidence.OnLine Y radial /\
      HilbertOppositeSide Geo X Z radial := by

  have hAO :
      A ≠ O :=
    hp.boundary_opposite.1

  have hOA :
      O ≠ A :=
    hAO.symm

  have hOY :
      O ≠ Y := by
    intro h
    subst Y
    exact hYS.1 hp.origin_on_base

  have hOX :
      O ≠ X := by
    intro h
    subst X
    exact hXS.1 hp.origin_on_base

  have hXO :
      X ≠ O :=
    hOX.symm

  have hAOY :
      Not (PrimCollinear Geo A O Y) :=
    hilbert_not_collinear_of_off_line
      Geo
      A O Y
      hp.base
      hAO
      hp.start_on_base
      hp.origin_on_base
      hYS.1

  have hAYO :
      Not (PrimCollinear Geo A Y O) := by
    intro h
    exact
      hAOY
        (PrimCollinearRotate
          Geo A Y O h)

  rcases hXY with
    ⟨H, hAHY, hRayOXH⟩

  rcases hYZ with
    ⟨K, hAKZ, hRayOYK⟩

  rcases
      HilbertPlaneIncidence.line_through
        O Y hOY with
    ⟨lineOY, hOlineOY, hYlineOY⟩

  rcases
      HilbertPlaneIncidence.line_through
        O X hOX with
    ⟨lineOX, hOlineOX, hXlineOX⟩

  have hHlineOX :
      HilbertIncidence.OnLine H lineOX :=
    hilbert_collinear_on_line
      Geo
      O X H
      lineOX
      hOX
      hOlineOX
      hXlineOX
      hRayOXH.2.2.1

  have hKlineOY :
      HilbertIncidence.OnLine K lineOY :=
    hilbert_collinear_on_line
      Geo
      O Y K
      lineOY
      hOY
      hOlineOY
      hYlineOY
      hRayOYK.2.2.1

  have hAHSame :
      HilbertSameSide Geo A H lineOY := by

    rcases
        hilbert_between_points_sameSide_transversal
          Geo
          A H O Y
          hAHY
          hAYO with
      ⟨lineOY', hOlineOY', hYlineOY', hAHSame'⟩

    have hLineOY :
        lineOY' = lineOY :=
      HilbertPlaneIncidence.line_unique
        O Y hOY
        lineOY' lineOY
        hOlineOY' hYlineOY'
        hOlineOY hYlineOY

    rw [← hLineOY]
    exact hAHSame'

  have hYoffOX :
      Not (HilbertIncidence.OnLine Y lineOX) := by

    intro hYlineOX

    have hHY :
        H ≠ Y :=
      (HilbertOrder.between_incidence
        A H Y hAHY).2.1

    have hAHYcol :
        PrimCollinear Geo A H Y :=
      (HilbertOrder.between_incidence
        A H Y hAHY).2.2.2.1

    have hHYA :
        PrimCollinear Geo H Y A :=
      PrimCollinearCycle
        Geo A H Y hAHYcol

    have hAlineOX :
        HilbertIncidence.OnLine A lineOX :=
      hilbert_collinear_on_line
        Geo
        H Y A
        lineOX
        hHY
        hHlineOX
        hYlineOX
        hHYA

    have hEq :
        lineOX = hp.base :=
      HilbertPlaneIncidence.line_unique
        O A hOA
        lineOX hp.base
        hOlineOX hAlineOX
        hp.origin_on_base hp.start_on_base

    have hXbase :
        HilbertIncidence.OnLine X hp.base := by
      rw [← hEq]
      exact hXlineOX

    exact hXS.1 hXbase

  have hHXSame :
      HilbertSameSide Geo H X lineOY :=
    hilbert_sameRay_points_sameSide
      Geo
      O X H X Y
      lineOX lineOY
      hOlineOX
      hXlineOX
      hOlineOY
      hYlineOY
      hYoffOX
      hRayOXH
      (hilbert_sameRay_refl
        Geo O X hXO)

  have hAXSame :
      HilbertSameSide Geo A X lineOY :=
    hilbert_sameSide_trans
      Geo
      A H X
      lineOY
      hAHSame
      hHXSame

  have hAoffOY :
      Not (HilbertIncidence.OnLine A lineOY) := by

    intro hAlineOY

    exact
      hAOY
        ⟨lineOY,
          hAlineOY,
          hOlineOY,
          hYlineOY⟩

  have hZoffOY :
      Not (HilbertIncidence.OnLine Z lineOY) := by

    intro hZlineOY

    have hKZ :
        K ≠ Z :=
      (HilbertOrder.between_incidence
        A K Z hAKZ).2.1

    have hAKZcol :
        PrimCollinear Geo A K Z :=
      (HilbertOrder.between_incidence
        A K Z hAKZ).2.2.2.1

    have hKZA :
        PrimCollinear Geo K Z A :=
      PrimCollinearCycle
        Geo A K Z hAKZcol

    have hAlineOY :
        HilbertIncidence.OnLine A lineOY :=
      hilbert_collinear_on_line
        Geo
        K Z A
        lineOY
        hKZ
        hKlineOY
        hZlineOY
        hKZA

    exact hAoffOY hAlineOY

  have hOppAZ :
      HilbertOppositeSide Geo A Z lineOY :=
    ⟨hAoffOY,
      hZoffOY,
      ⟨K, hAKZ, hKlineOY⟩⟩

  have hOppZA :
      HilbertOppositeSide Geo Z A lineOY :=
    hilbert_oppositeSide_symm
      Geo A Z lineOY hOppAZ

  have hOppZX :
      HilbertOppositeSide Geo Z X lineOY :=
    hilbert_oppositeSide_transport_right
      Geo
      Z A X
      lineOY
      hOppZA
      hAXSame

  have hOppXZ :
      HilbertOppositeSide Geo X Z lineOY :=
    hilbert_oppositeSide_symm
      Geo Z X lineOY hOppZX

  exact
    ⟨lineOY,
      hOlineOY,
      hYlineOY,
      hOppXZ⟩

/--
A closed half-pencil ray with a strict predecessor and a strict successor
must lie in the open half-pencil.
-/
theorem coxeter_general_middle_ray_open_of_two_strict_steps
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (rPrev rMid rNext : Geo.Ray)
    (hMidClosed :
      HilbertRayInClosedHalfPencil
        Geo O A Astar S hp rMid)
    (hPrevMid :
      HilbertHalfPencilRayLess
        Geo O A Astar S hp
        rPrev rMid)
    (hMidNext :
      HilbertHalfPencilRayLess
        Geo O A Astar S hp
        rMid rNext) :
    HilbertRayInOpenHalfPencil
      Geo O A Astar S hp rMid := by

  rcases hMidClosed with
    hStart | hRest

  · rw [hStart] at hPrevMid

    exact
      False.elim
        ((coxeter_general_start_ray_not_greater
          Geo
          O A Astar S
          hp
          rPrev)
          hPrevMid)

  · rcases hRest with
      hTerminal | hOpen

    · rw [hTerminal] at hMidNext

      exact
        False.elim
          ((coxeter_general_terminal_ray_not_less
            Geo
            O A Astar S
            hp
            rNext)
            hMidNext)

    · exact hOpen


/--
Every nonboundary member of a finite equal-angle chain is an open
half-pencil ray.

For `0 < m < p`, the chain provides the strict predecessor step
`m-1 < m` and the strict successor step `m < m+1`.
-/
theorem coxeter_general_chain_internal_ray_open
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (m : Nat)
    (hmPos : 0 < m)
    (hmLt : m < p) :
    HilbertRayInOpenHalfPencil
      Geo O A Astar S hp
      (Geo.ray O
        (chain.V
          ⟨m, Nat.lt_succ_of_lt hmLt⟩)) := by

  cases m with

  | zero =>
      exact False.elim (Nat.lt_asymm hmPos hmPos)

  | succ n =>

      let iPrev : Fin p :=
        ⟨n,
          Nat.lt_trans
            (Nat.lt_succ_self n)
            hmLt⟩

      let iMid : Fin p :=
        ⟨Nat.succ n, hmLt⟩

      have hMidClosed :
          HilbertRayInClosedHalfPencil
            Geo O A Astar S hp
            (Geo.ray O
              (chain.V
                ⟨Nat.succ n,
                  Nat.lt_succ_of_lt hmLt⟩)) :=
        chain.ray_mem
          ⟨Nat.succ n,
            Nat.lt_succ_of_lt hmLt⟩

      have hPrevMid :
          HilbertHalfPencilRayLess
            Geo O A Astar S hp
            (Geo.ray O
              (chain.V iPrev.castSucc))
            (Geo.ray O
              (chain.V iPrev.succ)) :=
        chain.strict_step iPrev

      have hMidNext :
          HilbertHalfPencilRayLess
            Geo O A Astar S hp
            (Geo.ray O
              (chain.V iMid.castSucc))
            (Geo.ray O
              (chain.V iMid.succ)) :=
        chain.strict_step iMid

      exact
        coxeter_general_middle_ray_open_of_two_strict_steps
          Geo
          O A Astar S
          hp
          (Geo.ray O
            (chain.V iPrev.castSucc))
          (Geo.ray O
            (chain.V
              ⟨Nat.succ n,
                Nat.lt_succ_of_lt hmLt⟩))
          (Geo.ray O
            (chain.V iMid.succ))
          hMidClosed
          (by
            simpa [iPrev] using hPrevMid)
          (by
            simpa [iMid] using hMidNext)

/--
For specified open representatives X and Y, extensional strict ray order has
its intended point-level meaning.  This is the archived Step116 bridge,
reintroduced under a fresh test name for the current construction chain.
-/
theorem coxeter_general_open_rayLess_to_meets_segment
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (O A Astar S X Y : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (hXS :
      HilbertSameSide Geo X S hp.base)
    (hYS :
      HilbertSameSide Geo Y S hp.base)
    (hLess :
      HilbertHalfPencilRayLess
        Geo O A Astar S hp
        (Geo.ray O X)
        (Geo.ray O Y)) :
    HilbertRayMeetsSegment Geo O X A Y := by

  have hXO : Not (X = O) := by
    intro h
    subst X
    exact hXS.1 hp.origin_on_base

  have hYO : Not (Y = O) := by
    intro h
    subst Y
    exact hYS.1 hp.origin_on_base

  have hAO : Not (A = O) :=
    hp.boundary_opposite.1

  have hOA : Not (O = A) := by
    intro h
    exact hAO h.symm

  have hAstarO : Not (Astar = O) :=
    hp.boundary_opposite.2.1

  have hOAstar : Not (O = Astar) := by
    intro h
    exact hAstarO h.symm

  cases hLess with
  | inl hStart =>
      have hRayXA := hStart.1

      have hSameXA :
          HilbertSameRay Geo O X A :=
        coxeter_general_sameRay_of_ray_eq
          Geo O X A
          hXO hAO
          hRayXA

      have hXbase :
          HilbertIncidence.OnLine X hp.base :=
        hilbert_collinear_on_line
          Geo O A X
          hp.base
          hOA
          hp.origin_on_base
          hp.start_on_base
          (PrimCollinearRotate
            Geo O X A hSameXA.2.2.1)

      exact
        False.elim
          (hXS.1 hXbase)

  | inr hRest =>
      cases hRest with
      | inl hTerminal =>
          have hRayYAstar := hTerminal.2

          have hSameYAstar :
              HilbertSameRay Geo O Y Astar :=
            coxeter_general_sameRay_of_ray_eq
              Geo O Y Astar
              hYO hAstarO
              hRayYAstar

          have hYbase :
              HilbertIncidence.OnLine Y hp.base :=
            hilbert_collinear_on_line
              Geo O Astar Y
              hp.base
              hOAstar
              hp.origin_on_base
              hp.terminal_on_base
              (PrimCollinearRotate
                Geo O Y Astar hSameYAstar.2.2.1)

          exact
            False.elim
              (hYS.1 hYbase)

      | inr hOpen =>
          cases hOpen with
          | intro X' hOpenX =>
              cases hOpenX with
              | intro Y' hOpenData =>
                  have hRayXX' := hOpenData.1
                  have hRayYY' := hOpenData.2.1
                  have hX'S := hOpenData.2.2.1
                  have hY'S := hOpenData.2.2.2.1
                  have hMeet := hOpenData.2.2.2.2

                  have hX'O : Not (X' = O) := by
                    intro h
                    subst X'
                    exact hX'S.1 hp.origin_on_base

                  have hY'O : Not (Y' = O) := by
                    intro h
                    subst Y'
                    exact hY'S.1 hp.origin_on_base

                  have hSameXX' :
                      HilbertSameRay Geo O X X' :=
                    coxeter_general_sameRay_of_ray_eq
                      Geo O X X'
                      hXO hX'O
                      hRayXX'

                  have hSameYY' :
                      HilbertSameRay Geo O Y Y' :=
                    coxeter_general_sameRay_of_ray_eq
                      Geo O Y Y'
                      hYO hY'O
                      hRayYY'

                  cases hMeet with
                  | intro H hMeetData =>
                      have hAHY' := hMeetData.1
                      have hSameX'H := hMeetData.2

                      have hSameX'X :
                          HilbertSameRay Geo O X' X :=
                        hilbert_sameRay_symm
                          Geo O X X' hSameXX'

                      have hSameXH :
                          HilbertSameRay Geo O X H :=
                        hilbert_sameRay_of_common
                          Geo O X' X H
                          hSameX'X
                          hSameX'H

                      have hMeetXY' :
                          HilbertRayMeetsSegment Geo O X A Y' :=
                        Exists.intro H
                          (And.intro hAHY' hSameXH)

                      have hSameY'Y :
                          HilbertSameRay Geo O Y' Y :=
                        hilbert_sameRay_symm
                          Geo O Y Y' hSameYY'

                      have hSameAA :
                          HilbertSameRay Geo O A A :=
                        hilbert_sameRay_refl
                          Geo O A hAO

                      have hAOY' :
                          Not (PrimCollinear Geo A O Y') :=
                        hilbert_not_collinear_of_off_line
                          Geo
                          A O Y'
                          hp.base
                          hAO
                          hp.start_on_base
                          hp.origin_on_base
                          hY'S.1

                      have hAOY :
                          Not (PrimCollinear Geo A O Y) :=
                        hilbert_not_collinear_of_off_line
                          Geo
                          A O Y
                          hp.base
                          hAO
                          hp.start_on_base
                          hp.origin_on_base
                          hYS.1

                      exact
                        hilbert_ray_meets_segment_sameRays
                          Geo
                          O X
                          A Y'
                          A Y
                          hMeetXY'
                          hSameAA
                          hSameY'Y
                          hAOY'
                          hAOY

/--
Every fully internal triple of consecutive chain rays admits open point
representatives X,Y,Z in the selected half-pencil, and the radial carrier
through O and Y separates X from Z.

The hypotheses are exactly 0 < n and n+2 < p, written with successors so the
Fin indices used by strict_step are definitionally transparent.
-/
theorem coxeter_general_chain_fully_internal_open_triple
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (n : Nat)
    (hnPos : 0 < n)
    (hn2Lt : Nat.succ (Nat.succ n) < p) :
    let hn1Lt : Nat.succ n < p :=
      Nat.lt_trans
        (Nat.lt_succ_self (Nat.succ n))
        hn2Lt
    let hnLt : n < p :=
      Nat.lt_trans
        (Nat.lt_succ_self n)
        hn1Lt
    let j0 : Fin (p + 1) :=
      { val := n
        isLt := Nat.lt_succ_of_lt hnLt }
    let j1 : Fin (p + 1) :=
      { val := Nat.succ n
        isLt := Nat.lt_succ_of_lt hn1Lt }
    let j2 : Fin (p + 1) :=
      { val := Nat.succ (Nat.succ n)
        isLt := Nat.lt_succ_of_lt hn2Lt }
    exists X Y Z : Geo.Point,
      Geo.ray O (chain.V j0) = Geo.ray O X /\
      Geo.ray O (chain.V j1) = Geo.ray O Y /\
      Geo.ray O (chain.V j2) = Geo.ray O Z /\
      HilbertSameSide Geo X S hp.base /\
      HilbertSameSide Geo Y S hp.base /\
      HilbertSameSide Geo Z S hp.base /\
      exists radial : Geo.Line,
        HilbertIncidence.OnLine O radial /\
        HilbertIncidence.OnLine Y radial /\
        HilbertOppositeSide Geo X Z radial := by

  let hn1Lt : Nat.succ n < p :=
    Nat.lt_trans
      (Nat.lt_succ_self (Nat.succ n))
      hn2Lt

  let hnLt : n < p :=
    Nat.lt_trans
      (Nat.lt_succ_self n)
      hn1Lt

  let j0 : Fin (p + 1) :=
    { val := n
      isLt := Nat.lt_succ_of_lt hnLt }

  let j1 : Fin (p + 1) :=
    { val := Nat.succ n
      isLt := Nat.lt_succ_of_lt hn1Lt }

  let j2 : Fin (p + 1) :=
    { val := Nat.succ (Nat.succ n)
      isLt := Nat.lt_succ_of_lt hn2Lt }

  change
    exists X Y Z : Geo.Point,
      Geo.ray O (chain.V j0) = Geo.ray O X /\
      Geo.ray O (chain.V j1) = Geo.ray O Y /\
      Geo.ray O (chain.V j2) = Geo.ray O Z /\
      HilbertSameSide Geo X S hp.base /\
      HilbertSameSide Geo Y S hp.base /\
      HilbertSameSide Geo Z S hp.base /\
      exists radial : Geo.Line,
        HilbertIncidence.OnLine O radial /\
        HilbertIncidence.OnLine Y radial /\
        HilbertOppositeSide Geo X Z radial

  have hOpen0 :
      HilbertRayInOpenHalfPencil
        Geo O A Astar S hp
        (Geo.ray O (chain.V j0)) := by
    simpa [j0] using
      (coxeter_general_chain_internal_ray_open
        Geo
        O A Astar S
        hp
        p hpos
        chain
        n
        hnPos
        hnLt)

  have hOpen1 :
      HilbertRayInOpenHalfPencil
        Geo O A Astar S hp
        (Geo.ray O (chain.V j1)) := by
    simpa [j1] using
      (coxeter_general_chain_internal_ray_open
        Geo
        O A Astar S
        hp
        p hpos
        chain
        (Nat.succ n)
        (Nat.succ_pos n)
        hn1Lt)

  have hOpen2 :
      HilbertRayInOpenHalfPencil
        Geo O A Astar S hp
        (Geo.ray O (chain.V j2)) := by
    simpa [j2] using
      (coxeter_general_chain_internal_ray_open
        Geo
        O A Astar S
        hp
        p hpos
        chain
        (Nat.succ (Nat.succ n))
        (Nat.succ_pos (Nat.succ n))
        hn2Lt)

  cases hOpen0 with
  | intro X hOpen0Data =>
      have hRay0X := hOpen0Data.1
      have hXS := hOpen0Data.2

      cases hOpen1 with
      | intro Y hOpen1Data =>
          have hRay1Y := hOpen1Data.1
          have hYS := hOpen1Data.2

          cases hOpen2 with
          | intro Z hOpen2Data =>
              have hRay2Z := hOpen2Data.1
              have hZS := hOpen2Data.2

              let i0 : Fin p :=
                { val := n
                  isLt := hnLt }

              let i1 : Fin p :=
                { val := Nat.succ n
                  isLt := hn1Lt }

              have hLess01 :
                  HilbertHalfPencilRayLess
                    Geo O A Astar S hp
                    (Geo.ray O (chain.V j0))
                    (Geo.ray O (chain.V j1)) := by
                simpa [i0, j0, j1] using
                  (chain.strict_step i0)

              have hLess12 :
                  HilbertHalfPencilRayLess
                    Geo O A Astar S hp
                    (Geo.ray O (chain.V j1))
                    (Geo.ray O (chain.V j2)) := by
                simpa [i1, j1, j2] using
                  (chain.strict_step i1)

              have hLessXY :
                  HilbertHalfPencilRayLess
                    Geo O A Astar S hp
                    (Geo.ray O X)
                    (Geo.ray O Y) := by
                have h := hLess01
                rw [hRay0X, hRay1Y] at h
                exact h

              have hLessYZ :
                  HilbertHalfPencilRayLess
                    Geo O A Astar S hp
                    (Geo.ray O Y)
                    (Geo.ray O Z) := by
                have h := hLess12
                rw [hRay1Y, hRay2Z] at h
                exact h

              have hXY :
                  HilbertRayMeetsSegment Geo O X A Y :=
                coxeter_general_open_rayLess_to_meets_segment
                  Geo
                  O A Astar S
                  X Y
                  hp
                  hXS hYS
                  hLessXY

              have hYZ :
                  HilbertRayMeetsSegment Geo O Y A Z :=
                coxeter_general_open_rayLess_to_meets_segment
                  Geo
                  O A Astar S
                  Y Z
                  hp
                  hYS hZS
                  hLessYZ

              have hSep :
                  exists radial : Geo.Line,
                    HilbertIncidence.OnLine O radial /\
                    HilbertIncidence.OnLine Y radial /\
                    HilbertOppositeSide Geo X Z radial :=
                coxeter_general_open_triple_local_radial_separation
                  Geo
                  O A Astar S
                  X Y Z
                  hp
                  hXS hYS hZS
                  hXY hYZ

              refine Exists.intro X ?_
              refine Exists.intro Y ?_
              refine Exists.intro Z ?_
              exact
                And.intro hRay0X
                  (And.intro hRay1Y
                    (And.intro hRay2Z
                      (And.intro hXS
                        (And.intro hYS
                          (And.intro hZS hSep)))))

/--
If P and Q lie on the same ray from O, and a line cross passes through O
but not through P, then P and Q lie on the same side of cross.

The auxiliary point C on cross is used only to identify cross with any
hypothetical carrier OP containing C.
-/
theorem coxeter_general_same_side_of_same_ray_from_line_origin
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O C P Q : Geo.Point)
    (cross : Geo.Line)
    (hOcross : HilbertIncidence.OnLine O cross)
    (hCcross : HilbertIncidence.OnLine C cross)
    (hCO : Not (C = O))
    (hPoff : Not (HilbertIncidence.OnLine P cross))
    (hPQ : HilbertSameRay Geo O P Q) :
    HilbertSameSide Geo P Q cross := by

  have hOP : Not (O = P) := by
    intro h
    exact hPQ.1 h.symm

  have hOC : Not (O = C) := by
    intro h
    exact hCO h.symm

  rcases
      HilbertPlaneIncidence.line_through O P hOP with
    ⟨base, hObase, hPbase⟩

  have hCoffBase :
      Not (HilbertIncidence.OnLine C base) := by
    intro hCbase

    have hEq : cross = base :=
      HilbertPlaneIncidence.line_unique
        O C hOC
        cross base
        hOcross hCcross
        hObase hCbase

    have hPcross :
        HilbertIncidence.OnLine P cross := by
      rw [hEq]
      exact hPbase

    exact hPoff hPcross

  exact
    hilbert_sameRay_points_sameSide
      Geo
      O P
      P Q
      C
      base cross
      hObase hPbase
      hOcross hCcross
      hCoffBase
      (hilbert_sameRay_refl Geo O P hPQ.1)
      hPQ

/--
For a fully internal triple n,n+1,n+2, transport the local radial
separation obtained from open half-pencil representatives to the normalized
Nat-indexed points V n, V (n+1), V (n+2).

Boundary triples are intentionally not treated here.
-/
theorem coxeter_general_fully_internal_local_radial_separation_of_normalized_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (V : Nat -> Geo.Point)
    (hRayNat :
      forall m : Nat,
        forall hm : m <= p,
          HilbertSameRay
            Geo O
            (chain.V
              ⟨m, Nat.lt_succ_iff.mpr hm⟩)
            (V m))
    (n : Nat)
    (hnPos : 0 < n)
    (hn2Lt : Nat.succ (Nat.succ n) < p) :
    exists radial : Geo.Line,
      HilbertIncidence.OnLine O radial /\
      HilbertIncidence.OnLine (V (Nat.succ n)) radial /\
      HilbertOppositeSide
        Geo
        (V n)
        (V (Nat.succ (Nat.succ n)))
        radial := by

  let hn1Lt : Nat.succ n < p :=
    Nat.lt_trans
      (Nat.lt_succ_self (Nat.succ n))
      hn2Lt

  let hnLt : n < p :=
    Nat.lt_trans
      (Nat.lt_succ_self n)
      hn1Lt

  let j0 : Fin (p + 1) :=
    { val := n
      isLt := Nat.lt_succ_of_lt hnLt }

  let j1 : Fin (p + 1) :=
    { val := Nat.succ n
      isLt := Nat.lt_succ_of_lt hn1Lt }

  let j2 : Fin (p + 1) :=
    { val := Nat.succ (Nat.succ n)
      isLt := Nat.lt_succ_of_lt hn2Lt }

  have hTriple :
      exists X Y Z : Geo.Point,
        Geo.ray O (chain.V j0) = Geo.ray O X /\
        Geo.ray O (chain.V j1) = Geo.ray O Y /\
        Geo.ray O (chain.V j2) = Geo.ray O Z /\
        HilbertSameSide Geo X S hp.base /\
        HilbertSameSide Geo Y S hp.base /\
        HilbertSameSide Geo Z S hp.base /\
        exists radial : Geo.Line,
          HilbertIncidence.OnLine O radial /\
          HilbertIncidence.OnLine Y radial /\
          HilbertOppositeSide Geo X Z radial := by
    simpa [hn1Lt, hnLt, j0, j1, j2] using
      (coxeter_general_chain_fully_internal_open_triple
        Geo
        O A Astar S
        hp
        p hpos
        chain
        n hnPos hn2Lt)

  rcases hTriple with
    ⟨X, Y, Z,
      hRay0X, hRay1Y, hRay2Z,
      hXS, hYS, hZS,
      radial, hOradial, hYradial, hOppXZ⟩

  have hnLe : n <= p :=
    Nat.le_of_lt hnLt

  have hn1Le : Nat.succ n <= p :=
    Nat.le_of_lt hn1Lt

  have hn2Le : Nat.succ (Nat.succ n) <= p :=
    Nat.le_of_lt hn2Lt

  have hChain0V0 :
      HilbertSameRay Geo O (chain.V j0) (V n) := by
    simpa [j0] using hRayNat n hnLe

  have hChain1V1 :
      HilbertSameRay
        Geo O (chain.V j1) (V (Nat.succ n)) := by
    simpa [j1] using hRayNat (Nat.succ n) hn1Le

  have hChain2V2 :
      HilbertSameRay
        Geo O
        (chain.V j2)
        (V (Nat.succ (Nat.succ n))) := by
    simpa [j2] using
      hRayNat (Nat.succ (Nat.succ n)) hn2Le

  have hRayChain0V0 :
      Geo.ray O (chain.V j0) = Geo.ray O (V n) :=
    hilbert_sameRay_ray_eq
      Geo O (chain.V j0) (V n) hChain0V0

  have hRayChain1V1 :
      Geo.ray O (chain.V j1) =
        Geo.ray O (V (Nat.succ n)) :=
    hilbert_sameRay_ray_eq
      Geo O (chain.V j1) (V (Nat.succ n)) hChain1V1

  have hRayChain2V2 :
      Geo.ray O (chain.V j2) =
        Geo.ray O (V (Nat.succ (Nat.succ n))) :=
    hilbert_sameRay_ray_eq
      Geo O
      (chain.V j2)
      (V (Nat.succ (Nat.succ n)))
      hChain2V2

  have hXO : Not (X = O) := by
    intro h
    subst X
    exact hXS.1 hp.origin_on_base

  have hYO : Not (Y = O) := by
    intro h
    subst Y
    exact hYS.1 hp.origin_on_base

  have hZO : Not (Z = O) := by
    intro h
    subst Z
    exact hZS.1 hp.origin_on_base

  have hSameXV0 :
      HilbertSameRay Geo O X (V n) :=
    coxeter_general_sameRay_of_ray_eq
      Geo O X (V n)
      hXO hChain0V0.2.1
      (hRay0X.symm.trans hRayChain0V0)

  have hSameYV1 :
      HilbertSameRay Geo O Y (V (Nat.succ n)) :=
    coxeter_general_sameRay_of_ray_eq
      Geo O Y (V (Nat.succ n))
      hYO hChain1V1.2.1
      (hRay1Y.symm.trans hRayChain1V1)

  have hSameZV2 :
      HilbertSameRay
        Geo O Z (V (Nat.succ (Nat.succ n))) :=
    coxeter_general_sameRay_of_ray_eq
      Geo O Z (V (Nat.succ (Nat.succ n)))
      hZO hChain2V2.2.1
      (hRay2Z.symm.trans hRayChain2V2)

  have hSameXNat :
      HilbertSameSide Geo X (V n) radial :=
    coxeter_general_same_side_of_same_ray_from_line_origin
      Geo
      O Y X (V n)
      radial
      hOradial hYradial
      hYO
      hOppXZ.1
      hSameXV0

  have hSameZNat :
      HilbertSameSide
        Geo Z (V (Nat.succ (Nat.succ n))) radial :=
    coxeter_general_same_side_of_same_ray_from_line_origin
      Geo
      O Y Z (V (Nat.succ (Nat.succ n)))
      radial
      hOradial hYradial
      hYO
      hOppXZ.2.1
      hSameZV2

  have hV1radial :
      HilbertIncidence.OnLine (V (Nat.succ n)) radial := by
    have hOY : Not (O = Y) := by
      intro h
      exact hYO h.symm

    exact
      hilbert_collinear_on_line
        Geo
        O Y (V (Nat.succ n))
        radial
        hOY
        hOradial hYradial
        hSameYV1.2.2.1

  have hOppXNat2 :
      HilbertOppositeSide
        Geo X (V (Nat.succ (Nat.succ n))) radial :=
    hilbert_oppositeSide_transport_right
      Geo
      X Z (V (Nat.succ (Nat.succ n)))
      radial
      hOppXZ
      hSameZNat

  have hOppNat2X :
      HilbertOppositeSide
        Geo (V (Nat.succ (Nat.succ n))) X radial :=
    hilbert_oppositeSide_symm
      Geo
      X (V (Nat.succ (Nat.succ n)))
      radial
      hOppXNat2

  have hOppNat2Nat0 :
      HilbertOppositeSide
        Geo (V (Nat.succ (Nat.succ n))) (V n) radial :=
    hilbert_oppositeSide_transport_right
      Geo
      (V (Nat.succ (Nat.succ n))) X (V n)
      radial
      hOppNat2X
      hSameXNat

  have hOppNat0Nat2 :
      HilbertOppositeSide
        Geo (V n) (V (Nat.succ (Nat.succ n))) radial :=
    hilbert_oppositeSide_symm
      Geo
      (V (Nat.succ (Nat.succ n))) (V n)
      radial
      hOppNat2Nat0

  exact
    ⟨radial,
      hOradial,
      hV1radial,
      hOppNat0Nat2⟩

/--
The initial boundary triple 0,1,2 has the required local radial separation
once 2 < p.

The first point lies on the start boundary ray OA, while rays 1 and 2 are
open.  The strict step 1 < 2 therefore says directly that a representative
of ray 1 meets the open segment from A to a representative of ray 2.
Step132 turns that crossing into separation by the radial carrier through
ray 1.  Finally the separation is transported to the normalized Nat-indexed
points V 0, V 1, V 2.
-/
theorem coxeter_general_start_local_radial_separation_of_normalized_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (V : Nat -> Geo.Point)
    (hRayNat :
      forall m : Nat,
        forall hm : m <= p,
          HilbertSameRay
            Geo O
            (chain.V
              { val := m
                isLt := Nat.lt_succ_iff.mpr hm })
            (V m))
    (hTwoLt : Nat.succ (Nat.succ 0) < p) :
    exists radial : Geo.Line,
      HilbertIncidence.OnLine O radial /\
      HilbertIncidence.OnLine (V (Nat.succ 0)) radial /\
      HilbertOppositeSide
        Geo
        (V 0)
        (V (Nat.succ (Nat.succ 0)))
        radial := by

  have hOneLt : Nat.succ 0 < p :=
    Nat.lt_trans
      (Nat.lt_succ_self (Nat.succ 0))
      hTwoLt

  let j1 : Fin (p + 1) :=
    { val := Nat.succ 0
      isLt := Nat.lt_succ_of_lt hOneLt }

  let j2 : Fin (p + 1) :=
    { val := Nat.succ (Nat.succ 0)
      isLt := Nat.lt_succ_of_lt hTwoLt }

  have hOpen1 :
      HilbertRayInOpenHalfPencil
        Geo O A Astar S hp
        (Geo.ray O (chain.V j1)) := by
    simpa [j1] using
      (coxeter_general_chain_internal_ray_open
        Geo
        O A Astar S
        hp
        p hpos
        chain
        (Nat.succ 0)
        (Nat.succ_pos 0)
        hOneLt)

  have hOpen2 :
      HilbertRayInOpenHalfPencil
        Geo O A Astar S hp
        (Geo.ray O (chain.V j2)) := by
    simpa [j2] using
      (coxeter_general_chain_internal_ray_open
        Geo
        O A Astar S
        hp
        p hpos
        chain
        (Nat.succ (Nat.succ 0))
        (Nat.succ_pos (Nat.succ 0))
        hTwoLt)

  cases hOpen1 with
  | intro Y hOpen1Data =>
      have hRay1Y := hOpen1Data.1
      have hYS := hOpen1Data.2

      cases hOpen2 with
      | intro Z hOpen2Data =>
          have hRay2Z := hOpen2Data.1
          have hZS := hOpen2Data.2

          let i1 : Fin p :=
            { val := Nat.succ 0
              isLt := hOneLt }

          have hLess12 :
              HilbertHalfPencilRayLess
                Geo O A Astar S hp
                (Geo.ray O (chain.V j1))
                (Geo.ray O (chain.V j2)) := by
            simpa [i1, j1, j2] using
              (chain.strict_step i1)

          have hLessYZ :
              HilbertHalfPencilRayLess
                Geo O A Astar S hp
                (Geo.ray O Y)
                (Geo.ray O Z) := by
            have h := hLess12
            rw [hRay1Y, hRay2Z] at h
            exact h

          have hMeet :
              HilbertRayMeetsSegment Geo O Y A Z :=
            coxeter_general_open_rayLess_to_meets_segment
              Geo
              O A Astar S
              Y Z
              hp
              hYS hZS
              hLessYZ

          have hCore :=
            coxeter_general_opposite_side_of_middle_ray_meets_segment
              Geo
              O A Y Z
              hMeet

          cases hCore with
          | intro radial hCoreData =>
              have hOradial := hCoreData.1
              have hYradial := hCoreData.2.1
              have hSepIfOff := hCoreData.2.2

              have hYO : Not (Y = O) := by
                intro h
                subst Y
                exact hYS.1 hp.origin_on_base

              have hOY : Not (O = Y) := by
                intro h
                exact hYO h.symm

              have hOA : Not (O = A) := by
                intro h
                exact hp.boundary_opposite.1 h.symm

              have hAoff :
                  Not (HilbertIncidence.OnLine A radial) := by
                intro hAradial

                have hEq : radial = hp.base :=
                  HilbertPlaneIncidence.line_unique
                    O A hOA
                    radial hp.base
                    hOradial hAradial
                    hp.origin_on_base hp.start_on_base

                have hYbase :
                    HilbertIncidence.OnLine Y hp.base := by
                  rw [hEq] at hYradial
                  exact hYradial

                exact hYS.1 hYbase

              have hZoff :
                  Not (HilbertIncidence.OnLine Z radial) := by
                intro hZradial

                rcases hMeet with
                  ⟨T, hATZ, hRayYT⟩

                have hTradial :
                    HilbertIncidence.OnLine T radial :=
                  hilbert_collinear_on_line
                    Geo
                    O Y T
                    radial
                    hOY
                    hOradial
                    hYradial
                    hRayYT.2.2.1

                have hTZ : Not (T = Z) :=
                  (HilbertOrder.between_incidence
                    A T Z hATZ).2.1

                have hATZcol :
                    PrimCollinear Geo A T Z :=
                  (HilbertOrder.between_incidence
                    A T Z hATZ).2.2.2.1

                have hTZA :
                    PrimCollinear Geo T Z A :=
                  PrimCollinearCycle
                    Geo A T Z hATZcol

                have hAradial :
                    HilbertIncidence.OnLine A radial :=
                  hilbert_collinear_on_line
                    Geo
                    T Z A
                    radial
                    hTZ
                    hTradial
                    hZradial
                    hTZA

                exact hAoff hAradial

              have hOppAZ :
                  HilbertOppositeSide Geo A Z radial :=
                hSepIfOff (And.intro hAoff hZoff)

              have h0Le : 0 <= p :=
                Nat.zero_le p

              have h1Le : Nat.succ 0 <= p :=
                Nat.le_of_lt hOneLt

              have h2Le : Nat.succ (Nat.succ 0) <= p :=
                Nat.le_of_lt hTwoLt

              have hChain0V0 :
                  HilbertSameRay Geo O (chain.V 0) (V 0) := by
                simpa using hRayNat 0 h0Le

              have hChain0A :
                  HilbertSameRay Geo O (chain.V 0) A :=
                coxeter_general_sameRay_of_ray_eq
                  Geo
                  O (chain.V 0) A
                  hChain0V0.1
                  hp.boundary_opposite.1
                  chain.start_ray

              have hSameAV0 :
                  HilbertSameRay Geo O A (V 0) :=
                bookZero_36_ray3
                  Geo O
                  (chain.V 0)
                  A
                  (V 0)
                  hChain0A
                  hChain0V0

              have hChain1V1 :
                  HilbertSameRay
                    Geo O (chain.V j1) (V (Nat.succ 0)) := by
                simpa [j1] using
                  hRayNat (Nat.succ 0) h1Le

              have hChain2V2 :
                  HilbertSameRay
                    Geo O
                    (chain.V j2)
                    (V (Nat.succ (Nat.succ 0))) := by
                simpa [j2] using
                  hRayNat (Nat.succ (Nat.succ 0)) h2Le

              have hRayChain1V1 :
                  Geo.ray O (chain.V j1) =
                    Geo.ray O (V (Nat.succ 0)) :=
                hilbert_sameRay_ray_eq
                  Geo O
                  (chain.V j1)
                  (V (Nat.succ 0))
                  hChain1V1

              have hRayChain2V2 :
                  Geo.ray O (chain.V j2) =
                    Geo.ray O (V (Nat.succ (Nat.succ 0))) :=
                hilbert_sameRay_ray_eq
                  Geo O
                  (chain.V j2)
                  (V (Nat.succ (Nat.succ 0)))
                  hChain2V2

              have hZO : Not (Z = O) := by
                intro h
                subst Z
                exact hZS.1 hp.origin_on_base

              have hSameYV1 :
                  HilbertSameRay Geo O Y (V (Nat.succ 0)) :=
                coxeter_general_sameRay_of_ray_eq
                  Geo O
                  Y (V (Nat.succ 0))
                  hYO hChain1V1.2.1
                  (hRay1Y.symm.trans hRayChain1V1)

              have hSameZV2 :
                  HilbertSameRay
                    Geo O Z (V (Nat.succ (Nat.succ 0))) :=
                coxeter_general_sameRay_of_ray_eq
                  Geo O
                  Z (V (Nat.succ (Nat.succ 0)))
                  hZO hChain2V2.2.1
                  (hRay2Z.symm.trans hRayChain2V2)

              have hSameANat :
                  HilbertSameSide Geo A (V 0) radial :=
                coxeter_general_same_side_of_same_ray_from_line_origin
                  Geo
                  O Y A (V 0)
                  radial
                  hOradial hYradial
                  hYO
                  hAoff
                  hSameAV0

              have hSameZNat :
                  HilbertSameSide
                    Geo Z (V (Nat.succ (Nat.succ 0))) radial :=
                coxeter_general_same_side_of_same_ray_from_line_origin
                  Geo
                  O Y Z (V (Nat.succ (Nat.succ 0)))
                  radial
                  hOradial hYradial
                  hYO
                  hZoff
                  hSameZV2

              have hV1radial :
                  HilbertIncidence.OnLine (V (Nat.succ 0)) radial :=
                hilbert_collinear_on_line
                  Geo
                  O Y (V (Nat.succ 0))
                  radial
                  hOY
                  hOradial hYradial
                  hSameYV1.2.2.1

              have hOppA_V2 :
                  HilbertOppositeSide
                    Geo A (V (Nat.succ (Nat.succ 0))) radial :=
                hilbert_oppositeSide_transport_right
                  Geo
                  A Z (V (Nat.succ (Nat.succ 0)))
                  radial
                  hOppAZ
                  hSameZNat

              have hOppV2_A :
                  HilbertOppositeSide
                    Geo (V (Nat.succ (Nat.succ 0))) A radial :=
                hilbert_oppositeSide_symm
                  Geo
                  A (V (Nat.succ (Nat.succ 0)))
                  radial
                  hOppA_V2

              have hOppV2_V0 :
                  HilbertOppositeSide
                    Geo (V (Nat.succ (Nat.succ 0))) (V 0) radial :=
                hilbert_oppositeSide_transport_right
                  Geo
                  (V (Nat.succ (Nat.succ 0))) A (V 0)
                  radial
                  hOppV2_A
                  hSameANat

              have hOppV0_V2 :
                  HilbertOppositeSide
                    Geo (V 0) (V (Nat.succ (Nat.succ 0))) radial :=
                hilbert_oppositeSide_symm
                  Geo
                  (V (Nat.succ (Nat.succ 0))) (V 0)
                  radial
                  hOppV2_V0

              exact
                Exists.intro radial
                  (And.intro hOradial
                    (And.intro hV1radial hOppV0_V2))

/--
The terminal boundary triple n,n+1,p has the required local radial
separation when n+2=p and n>0.

The two lower rays are open.  Their strict order gives a point T on the
ray OX with A-T-Y.  Relative to the radial carrier OY, A and X are on the
same side.  The opposite boundary point Astar is on the other side because
A-O-Astar.  The resulting separation is then transported to the normalized
Nat-indexed representatives V n, V (n+1), V p.
-/
theorem coxeter_general_terminal_local_radial_separation_of_normalized_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (V : Nat -> Geo.Point)
    (hRayNat :
      forall m : Nat,
        forall hm : m <= p,
          HilbertSameRay
            Geo O
            (chain.V
              { val := m
                isLt := Nat.lt_succ_iff.mpr hm })
            (V m))
    (hTerminal :
      Geo.ray O (chain.V (Fin.last p)) =
        Geo.ray O Astar)
    (n : Nat)
    (hnPos : 0 < n)
    (hEnd : Nat.succ (Nat.succ n) = p) :
    exists radial : Geo.Line,
      HilbertIncidence.OnLine O radial /\
      HilbertIncidence.OnLine (V (Nat.succ n)) radial /\
      HilbertOppositeSide
        Geo
        (V n)
        (V (Nat.succ (Nat.succ n)))
        radial := by

  have hnLt : n < p := by
    rw [hEnd.symm]
    exact Nat.lt_succ_of_lt (Nat.lt_succ_self n)

  have hn1Lt : Nat.succ n < p := by
    rw [hEnd.symm]
    exact Nat.lt_succ_self (Nat.succ n)

  have hnLe : n <= p :=
    Nat.le_of_lt hnLt

  have hn1Le : Nat.succ n <= p :=
    Nat.le_of_lt hn1Lt

  have hpLe : p <= p :=
    Nat.le_refl p

  let j0 : Fin (p + 1) :=
    { val := n
      isLt := Nat.lt_succ_of_lt hnLt }

  let j1 : Fin (p + 1) :=
    { val := Nat.succ n
      isLt := Nat.lt_succ_of_lt hn1Lt }

  have hOpen0 :
      HilbertRayInOpenHalfPencil
        Geo O A Astar S hp
        (Geo.ray O (chain.V j0)) := by
    simpa [j0] using
      (coxeter_general_chain_internal_ray_open
        Geo
        O A Astar S
        hp
        p hpos
        chain
        n hnPos hnLt)

  have hOpen1 :
      HilbertRayInOpenHalfPencil
        Geo O A Astar S hp
        (Geo.ray O (chain.V j1)) := by
    simpa [j1] using
      (coxeter_general_chain_internal_ray_open
        Geo
        O A Astar S
        hp
        p hpos
        chain
        (Nat.succ n)
        (Nat.succ_pos n)
        hn1Lt)

  cases hOpen0 with
  | intro X hOpen0Data =>
      have hRay0X := hOpen0Data.1
      have hXS := hOpen0Data.2

      cases hOpen1 with
      | intro Y hOpen1Data =>
          have hRay1Y := hOpen1Data.1
          have hYS := hOpen1Data.2

          let i0 : Fin p :=
            { val := n
              isLt := hnLt }

          have hLess01 :
              HilbertHalfPencilRayLess
                Geo O A Astar S hp
                (Geo.ray O (chain.V j0))
                (Geo.ray O (chain.V j1)) := by
            simpa [i0, j0, j1] using
              (chain.strict_step i0)

          have hLessXY :
              HilbertHalfPencilRayLess
                Geo O A Astar S hp
                (Geo.ray O X)
                (Geo.ray O Y) := by
            have h := hLess01
            rw [hRay0X, hRay1Y] at h
            exact h

          have hMeet :
              HilbertRayMeetsSegment Geo O X A Y :=
            coxeter_general_open_rayLess_to_meets_segment
              Geo
              O A Astar S
              X Y
              hp
              hXS hYS
              hLessXY

          have hXO : Not (X = O) := by
            intro h
            subst X
            exact hXS.1 hp.origin_on_base

          have hYO : Not (Y = O) := by
            intro h
            subst Y
            exact hYS.1 hp.origin_on_base

          have hOY : Not (O = Y) := by
            intro h
            exact hYO h.symm

          let hRadialExists :=
            HilbertPlaneIncidence.line_through O Y hOY

          let radial : Geo.Line :=
            Classical.choose hRadialExists

          have hRadialSpec :=
            Classical.choose_spec hRadialExists

          have hOradial :
              HilbertIncidence.OnLine O radial :=
            hRadialSpec.1

          have hYradial :
              HilbertIncidence.OnLine Y radial :=
            hRadialSpec.2

          have hAoff :
              Not (HilbertIncidence.OnLine A radial) := by
            intro hAradial

            have hEq : radial = hp.base :=
              HilbertPlaneIncidence.line_unique
                O A
                (by
                  intro h
                  exact hp.boundary_opposite.1 h.symm)
                radial hp.base
                hOradial hAradial
                hp.origin_on_base hp.start_on_base

            have hYbase :
                HilbertIncidence.OnLine Y hp.base := by
              rw [hEq] at hYradial
              exact hYradial

            exact hYS.1 hYbase

          have hAstarOff :
              Not (HilbertIncidence.OnLine Astar radial) := by
            intro hAstarRadial

            have hEq : radial = hp.base :=
              HilbertPlaneIncidence.line_unique
                O Astar
                (by
                  intro h
                  exact hp.boundary_opposite.2.1 h.symm)
                radial hp.base
                hOradial hAstarRadial
                hp.origin_on_base hp.terminal_on_base

            have hYbase :
                HilbertIncidence.OnLine Y hp.base := by
              rw [hEq] at hYradial
              exact hYradial

            exact hYS.1 hYbase

          have hOppA_Astar :
              HilbertOppositeSide Geo A Astar radial :=
            And.intro hAoff
              (And.intro hAstarOff
                (Exists.intro O
                  (And.intro
                    hp.boundary_opposite.2.2
                    hOradial)))

          let T : Geo.Point :=
            Classical.choose hMeet

          have hTSpec :=
            Classical.choose_spec hMeet

          have hATY : Geo.Between A T Y :=
            hTSpec.1

          have hRayXT : HilbertSameRay Geo O X T :=
            hTSpec.2

          have hTY : Not (T = Y) :=
            (HilbertOrder.between_incidence A T Y hATY).2.1

          have hAY : Not (A = Y) :=
            (HilbertOrder.between_incidence A T Y hATY).2.2.1

          let hLineAYExists :=
            HilbertPlaneIncidence.line_through A Y hAY

          let lineAY : Geo.Line :=
            Classical.choose hLineAYExists

          have hLineAYSpec :=
            Classical.choose_spec hLineAYExists

          have hAlineAY :
              HilbertIncidence.OnLine A lineAY :=
            hLineAYSpec.1

          have hYlineAY :
              HilbertIncidence.OnLine Y lineAY :=
            hLineAYSpec.2

          have hTlineAY :
              HilbertIncidence.OnLine T lineAY :=
            hilbert_between_on_line
              Geo A T Y lineAY
              hAlineAY hYlineAY hATY

          have hLinesAY : Not (lineAY = radial) := by
            intro hEq
            rw [hEq] at hAlineAY
            exact hAoff hAlineAY

          have hNotAYT : Not (Geo.Between A Y T) := by
            intro hAYT
            exact
              (HilbertOrder.between_unique
                (Geo := Geo)
                A T Y
                (HilbertOrder.between_incidence
                  A T Y hATY).2.2.2.1
                hATY).2 hAYT

          have hATavoids :
              Not (HilbertSegmentMeetsLine Geo A T radial) :=
            hilbert_segment_not_meets_crossing_line
              Geo
              A T Y
              lineAY radial
              hLinesAY
              hAlineAY hTlineAY hYlineAY hYradial
              hNotAYT

          have hToff :
              Not (HilbertIncidence.OnLine T radial) := by
            intro hTradial

            have hEq : lineAY = radial :=
              HilbertPlaneIncidence.line_unique
                T Y hTY
                lineAY radial
                hTlineAY hYlineAY
                hTradial hYradial

            exact hLinesAY hEq

          have hSameAT :
              HilbertSameSide Geo A T radial :=
            And.intro hAoff
              (And.intro hToff
                (Relation.ReflTransGen.single
                  (And.intro hAoff
                    (And.intro hToff hATavoids))))

          let hLineOXExists :=
            hRayXT.2.2.1

          let lineOX : Geo.Line :=
            Classical.choose hLineOXExists

          have hLineOXSpec :=
            Classical.choose_spec hLineOXExists

          have hOlineOX :
              HilbertIncidence.OnLine O lineOX :=
            hLineOXSpec.1

          have hXlineOX :
              HilbertIncidence.OnLine X lineOX :=
            hLineOXSpec.2.1

          have hTlineOX :
              HilbertIncidence.OnLine T lineOX :=
            hLineOXSpec.2.2

          have hYoffLineOX :
              Not (HilbertIncidence.OnLine Y lineOX) := by
            intro hYlineOX

            have hAlineOX :
                HilbertIncidence.OnLine A lineOX :=
              hilbert_collinear_on_line
                Geo
                T Y A
                lineOX
                hTY
                hTlineOX hYlineOX
                (PrimCollinearCycle
                  Geo A T Y
                  (HilbertOrder.between_incidence
                    A T Y hATY).2.2.2.1)

            have hEq : lineOX = hp.base :=
              HilbertPlaneIncidence.line_unique
                O A
                (by
                  intro h
                  exact hp.boundary_opposite.1 h.symm)
                lineOX hp.base
                hOlineOX hAlineOX
                hp.origin_on_base hp.start_on_base

            have hXbase :
                HilbertIncidence.OnLine X hp.base := by
              rw [hEq.symm]
              exact hXlineOX

            exact hXS.1 hXbase

          have hRayXX :
              HilbertSameRay Geo O X X :=
            hilbert_sameRay_refl
              Geo O X hXO

          have hSameTX :
              HilbertSameSide Geo T X radial :=
            hilbert_sameRay_points_sameSide
              Geo
              O X
              T X
              Y
              lineOX radial
              hOlineOX hXlineOX
              hOradial hYradial
              hYoffLineOX
              hRayXT hRayXX

          have hSameAX :
              HilbertSameSide Geo A X radial :=
            hilbert_sameSide_trans
              Geo A T X radial
              hSameAT hSameTX

          have hOppAstarA :
              HilbertOppositeSide Geo Astar A radial :=
            hilbert_oppositeSide_symm
              Geo A Astar radial hOppA_Astar

          have hOppAstarX :
              HilbertOppositeSide Geo Astar X radial :=
            hilbert_oppositeSide_transport_right
              Geo
              Astar A X
              radial
              hOppAstarA hSameAX

          have hOppX_Astar :
              HilbertOppositeSide Geo X Astar radial :=
            hilbert_oppositeSide_symm
              Geo Astar X radial hOppAstarX

          have hChain0Vn :
              HilbertSameRay Geo O (chain.V j0) (V n) := by
            simpa [j0] using
              hRayNat n hnLe

          have hChain1Vn1 :
              HilbertSameRay
                Geo O
                (chain.V j1)
                (V (Nat.succ n)) := by
            simpa [j1] using
              hRayNat (Nat.succ n) hn1Le

          have hRayChain0Vn :
              Geo.ray O (chain.V j0) = Geo.ray O (V n) :=
            hilbert_sameRay_ray_eq
              Geo O
              (chain.V j0) (V n)
              hChain0Vn

          have hRayChain1Vn1 :
              Geo.ray O (chain.V j1) =
                Geo.ray O (V (Nat.succ n)) :=
            hilbert_sameRay_ray_eq
              Geo O
              (chain.V j1) (V (Nat.succ n))
              hChain1Vn1

          have hSameXVn :
              HilbertSameRay Geo O X (V n) :=
            coxeter_general_sameRay_of_ray_eq
              Geo O
              X (V n)
              hXO hChain0Vn.2.1
              (hRay0X.symm.trans hRayChain0Vn)

          have hSameYVn1 :
              HilbertSameRay Geo O Y (V (Nat.succ n)) :=
            coxeter_general_sameRay_of_ray_eq
              Geo O
              Y (V (Nat.succ n))
              hYO hChain1Vn1.2.1
              (hRay1Y.symm.trans hRayChain1Vn1)

          have hRayP :
              HilbertSameRay
                Geo O
                (chain.V
                  { val := p
                    isLt := Nat.lt_succ_iff.mpr hpLe })
                (V p) :=
            hRayNat p hpLe

          have hChainPAstar :
              HilbertSameRay
                Geo O
                (chain.V (Fin.last p))
                Astar :=
            coxeter_general_sameRay_of_ray_eq
              Geo O
              (chain.V (Fin.last p)) Astar
              (by
                exact Ne.symm
                  (coxeter_general_closed_half_pencil_representative_nonzero
                    Geo
                    O A Astar S
                    (chain.V (Fin.last p))
                    hp
                    (chain.ray_mem (Fin.last p))))
              hp.boundary_opposite.2.1
              hTerminal

          have hIndexP :
              ({ val := p
                 isLt := Nat.lt_succ_iff.mpr hpLe } : Fin (p + 1)) =
                Fin.last p := by
            apply Fin.ext
            rfl

          have hCommonPVp :
              HilbertSameRay
                Geo O
                (chain.V (Fin.last p))
                (V p) := by
            rw [hIndexP] at hRayP
            exact hRayP

          have hSameAstarVp :
              HilbertSameRay Geo O Astar (V p) :=
            bookZero_36_ray3
              Geo O
              (chain.V (Fin.last p))
              Astar (V p)
              hChainPAstar hCommonPVp

          have hSameXNat :
              HilbertSameSide Geo X (V n) radial :=
            coxeter_general_same_side_of_same_ray_from_line_origin
              Geo
              O Y X (V n)
              radial
              hOradial hYradial
              hYO
              hOppX_Astar.1
              hSameXVn

          have hSameAstarNat :
              HilbertSameSide Geo Astar (V p) radial :=
            coxeter_general_same_side_of_same_ray_from_line_origin
              Geo
              O Y Astar (V p)
              radial
              hOradial hYradial
              hYO
              hAstarOff
              hSameAstarVp

          have hVn1radial :
              HilbertIncidence.OnLine (V (Nat.succ n)) radial :=
            hilbert_collinear_on_line
              Geo
              O Y (V (Nat.succ n))
              radial
              hOY
              hOradial hYradial
              hSameYVn1.2.2.1

          have hOppX_Vp :
              HilbertOppositeSide Geo X (V p) radial :=
            hilbert_oppositeSide_transport_right
              Geo
              X Astar (V p)
              radial
              hOppX_Astar hSameAstarNat

          have hOppVp_X :
              HilbertOppositeSide Geo (V p) X radial :=
            hilbert_oppositeSide_symm
              Geo X (V p) radial hOppX_Vp

          have hOppVp_Vn :
              HilbertOppositeSide Geo (V p) (V n) radial :=
            hilbert_oppositeSide_transport_right
              Geo
              (V p) X (V n)
              radial
              hOppVp_X hSameXNat

          have hOppVn_Vp :
              HilbertOppositeSide Geo (V n) (V p) radial :=
            hilbert_oppositeSide_symm
              Geo (V p) (V n) radial hOppVp_Vn

          rw [hEnd]

          exact
            Exists.intro radial
              (And.intro hOradial
                (And.intro hVn1radial hOppVn_Vp))

/--
All local radial-separation cases for a normalized equal-angle half-pencil
chain can be assembled into one uniform statement once p >= 3.

For n = 0 we use the initial boundary theorem.  For n > 0, the hypothesis
n+1 < p implies n+2 <= p.  If n+2 < p the triple is fully internal; if
n+2 = p it is the terminal boundary triple.
-/
theorem coxeter_general_local_radial_separation_of_normalized_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hThree : 3 <= p)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (V : Nat -> Geo.Point)
    (hRayNat :
      forall m : Nat,
        forall hm : m <= p,
          HilbertSameRay
            Geo O
            (chain.V
              { val := m
                isLt := Nat.lt_succ_iff.mpr hm })
            (V m))
    (hTerminal :
      Geo.ray O (chain.V (Fin.last p)) =
        Geo.ray O Astar)
    (n : Nat)
    (hn : Nat.succ n < p) :
    exists radial : Geo.Line,
      HilbertIncidence.OnLine O radial /\
      HilbertIncidence.OnLine (V (Nat.succ n)) radial /\
      HilbertOppositeSide
        Geo
        (V n)
        (V (Nat.succ (Nat.succ n)))
        radial := by

  by_cases hnZero : n = 0

  · subst n

    have hTwoLt :
        Nat.succ (Nat.succ 0) < p :=
      Nat.lt_of_succ_le hThree

    exact
      coxeter_general_start_local_radial_separation_of_normalized_chain
        Geo
        O A Astar S
        hp
        p hpos
        chain
        V hRayNat
        hTwoLt

  · have hnPos : 0 < n :=
      Nat.pos_of_ne_zero hnZero

    have hn2Le :
        Nat.succ (Nat.succ n) <= p :=
      Nat.succ_le_of_lt hn

    rcases Nat.lt_or_eq_of_le hn2Le with hn2Lt | hn2Eq

    · exact
        coxeter_general_fully_internal_local_radial_separation_of_normalized_chain
          Geo
          O A Astar S
          hp
          p hpos
          chain
          V hRayNat
          n hnPos hn2Lt

    · exact
        coxeter_general_terminal_local_radial_separation_of_normalized_chain
          Geo
          O A Astar S
          hp
          p hpos
          chain
          V hRayNat
          hTerminal
          n hnPos hn2Eq

/--
Package all data of a normalized equal-angle half-pencil chain into a finite
oriented equiangular subdivision of the semicircle.

At this point every field of
`HilbertFiniteOrientedEquiangularSemicircleDivision` has already been proved
separately: common radius and equal angles come from the normalization layer,
local radial separation from Step139, terminal opposition from Step130, and
minimal radial return from Step131.
-/
theorem coxeter_general_equiangular_semicircle_division_of_normalized_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hThree : 3 <= p)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (V : Nat -> Geo.Point)
    (hRayNat :
      forall n : Nat,
        forall hn : n <= p,
          HilbertSameRay
            Geo O
            (chain.V
              { val := n
                isLt := Nat.lt_succ_iff.mpr hn })
            (V n))
    (hCommon :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hEqualNat :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.AngleCongruent
          (V n)
          O
          (V (Nat.succ n))
          (V (Nat.succ n))
          O
          (V (Nat.succ (Nat.succ n))))
    (hTerminal :
      Geo.ray O (chain.V (Fin.last p)) =
        Geo.ray O Astar) :
    HilbertFiniteOrientedEquiangularSemicircleDivision
      Geo p O V := by

  refine
    { period_ge_three := hThree
      common_radius := hCommon
      equal_consecutive_angles := hEqualNat
      local_radial_separation := ?_
      terminal_opposite := ?_
      no_early_radial_return := ?_ }

  · intro n hn

    exact
      coxeter_general_local_radial_separation_of_normalized_chain
        Geo
        O A Astar S
        hp
        p hThree hpos
        chain
        V hRayNat
        hTerminal
        n hn

  · exact
      coxeter_general_terminal_opposite_of_normalized_chain
        Geo
        O A Astar S
        hp
        p hpos
        chain
        V hRayNat
        hTerminal

  · exact
      coxeter_general_no_early_radial_return_of_normalized_chain
        Geo
        O A Astar S
        hp
        p hpos
        chain
        V hRayNat


/--
A normalized equal-angle half-pencil chain landing on the terminal boundary
therefore yields the full oriented equilateral semicircle subdivision used by
the Coxeter reflection layer.
-/
theorem coxeter_general_equilateral_semicircle_division_of_normalized_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hThree : 3 <= p)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (V : Nat -> Geo.Point)
    (hRayNat :
      forall n : Nat,
        forall hn : n <= p,
          HilbertSameRay
            Geo O
            (chain.V
              { val := n
                isLt := Nat.lt_succ_iff.mpr hn })
            (V n))
    (hCommon :
      forall n : Nat,
        n <= p ->
        Geo.Congruent
          O
          (V n)
          O
          (V 0))
    (hEqualNat :
      forall n : Nat,
        Nat.succ n < p ->
        Geo.AngleCongruent
          (V n)
          O
          (V (Nat.succ n))
          (V (Nat.succ n))
          O
          (V (Nat.succ (Nat.succ n))))
    (hTerminal :
      Geo.ray O (chain.V (Fin.last p)) =
        Geo.ray O Astar) :
    HilbertFiniteOrientedEquilateralSemicircleDivision
      Geo p O V := by

  have division :
      HilbertFiniteOrientedEquiangularSemicircleDivision
        Geo p O V :=
    coxeter_general_equiangular_semicircle_division_of_normalized_chain
      Geo
      O A Astar S
      hp
      p hThree hpos
      chain
      V hRayNat
      hCommon hEqualNat
      hTerminal

  exact
    coxeter_general_equilateral_semicircle_division_of_equiangular
      Geo p O V division

/--
A finite equal-angle chain in an oriented half-pencil which starts at the
initial boundary and lands on the terminal boundary yields, after radial
normalization, an oriented equilateral semicircle subdivision.

This is the direct bridge from the synthetic equal-angle-chain language to the
semicircle-division interface consumed by the Coxeter reflection layer.
-/
theorem coxeter_general_equilateral_semicircle_division_exists_of_terminal_equal_angle_chain
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A Astar S : Geo.Point)
    (hp : HilbertOrientedHalfPencil Geo O A Astar S)
    (p : Nat)
    (hThree : 3 <= p)
    (hpos : 0 < p)
    (chain :
      HilbertHalfPencilEqualAngleChain
        Geo O A Astar S hp p hpos)
    (hTerminal :
      Geo.ray O (chain.V (Fin.last p)) =
        Geo.ray O Astar) :
    exists V : Nat -> Geo.Point,
      HilbertFiniteOrientedEquilateralSemicircleDivision
        Geo p O V := by

  rcases
      coxeter_general_normalize_equal_angle_chain_closed
        Geo
        O A Astar S
        hp
        p hpos
        chain with
    ⟨W, hRay, hRadius, hEqual⟩

  rcases
      coxeter_general_normalized_chain_to_nat
        Geo
        O A Astar S
        hp
        p hpos
        chain
        W
        hRay
        hRadius
        hEqual with
    ⟨V, _hAgree, hRayNat, hCommon, hEqualNat⟩

  refine ⟨V, ?_⟩

  exact
    coxeter_general_equilateral_semicircle_division_of_normalized_chain
      Geo
      O A Astar S
      hp
      p hThree hpos
      chain
      V hRayNat
      hCommon hEqualNat
      hTerminal

/--
Synthetic existence of an equal finite subdivision of a half-turn.

For every p >= 3, there is an oriented half-pencil together with a finite
chain of p congruent angular steps which starts at the initial boundary ray
and lands exactly on the opposite terminal boundary ray.

No numerical angle measure is mentioned.  This is the precise hypothesis
needed by the normalization and semicircle-division bridge.
-/
class HilbertFiniteEqualAngleHalfTurnDivisionExistence
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] : Prop where
  exists_terminal_equal_angle_chain :
    forall p : Nat,
      3 <= p ->
      exists O A Astar S : Geo.Point,
        exists hp : HilbertOrientedHalfPencil Geo O A Astar S,
          exists hpos : 0 < p,
            exists chain :
                HilbertHalfPencilEqualAngleChain
                  Geo O A Astar S hp p hpos,
              Geo.ray O (chain.V (Fin.last p)) =
                Geo.ray O Astar

/--
The equal-half-turn-division hypothesis implies the semicircle-division
existence interface already consumed by the Coxeter exact-period theorem.
-/
theorem coxeter_general_semicircle_division_existence_of_equal_halfturn_division
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertFiniteEqualAngleHalfTurnDivisionExistence Geo] :
    HilbertFiniteOrientedEquilateralSemicircleDivisionExistence Geo := by

  refine
    { exists_oriented_equilateral_semicircle_division := ?_ }

  intro p hThree

  have hData :=
    HilbertFiniteEqualAngleHalfTurnDivisionExistence.exists_terminal_equal_angle_chain
      (Geo := Geo)
      p hThree

  exact
    Exists.elim hData (fun O hA =>
      Exists.elim hA (fun A hAstar =>
        Exists.elim hAstar (fun Astar hS =>
          Exists.elim hS (fun S hHp =>
            Exists.elim hHp (fun hp hHpos =>
              Exists.elim hHpos (fun hpos hChain =>
                Exists.elim hChain (fun chain hTerminal =>
                  Exists.elim
                    (coxeter_general_equilateral_semicircle_division_exists_of_terminal_equal_angle_chain
                      Geo
                      O A Astar S
                      hp
                      p hThree hpos
                      chain
                      hTerminal)
                    (fun V division =>
                      Exists.intro O
                        (Exists.intro V division)))))))))

/--
Assuming synthetic existence of equal finite subdivisions of a half-turn,
every finite Coxeter period p >= 2 is realized by a pair of Hilbert line
reflections.
-/
theorem coxeter_general_exact_period_exists_of_equal_halfturn_division_ge_two
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    [HilbertFiniteEqualAngleHalfTurnDivisionExistence Geo] :
    forall p : Nat,
      2 <= p ->
      exists a b : ReflectionAxis Geo,
        ReflectionPairExactPeriod Geo a b p := by

  have hDivision :
      HilbertFiniteOrientedEquilateralSemicircleDivisionExistence Geo :=
    coxeter_general_semicircle_division_existence_of_equal_halfturn_division
      Geo

  intro p hp

  exact
    @coxeter_general_exact_period_exists_of_semicircle_division_existence_ge_two
      Geo
      (inferInstance : HilbertIncidence Geo)
      (inferInstance : HilbertCongruence Geo)
      hDivision
      p
      hp

end Geometry

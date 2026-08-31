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
end Geometry

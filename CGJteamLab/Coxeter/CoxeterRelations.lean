import CGJteamLab.Coxeter.ReflectionWords
import CGJteamLab.Coxeter.ReflectionIsometry

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


/--
Witness data for two perpendicular reflection axes.

The axes meet at O.  The points U and V determine nondegenerate
directions on axis1 and axis2, and angle UOV is right.
-/
structure ReflectionAxesPerpendicular
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo) where

  O : Geo.Point
  U : Geo.Point
  V : Geo.Point

  hO1 :
    HilbertIncidence.OnLine O axis1.carrier

  hO2 :
    HilbertIncidence.OnLine O axis2.carrier

  hU1 :
    HilbertIncidence.OnLine U axis1.carrier

  hV2 :
    HilbertIncidence.OnLine V axis2.carrier

  hOU :
    Not (O = U)

  hOV :
    Not (O = V)

  hNonCol :
    Not (PrimCollinear Geo U O V)

  hRight :
    HilbertRightAngle Geo U O V

/--
Perpendicularity of reflection axes is symmetric.
-/
def reflectionAxesPerpendicular_symm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2) :
    ReflectionAxesPerpendicular Geo axis2 axis1 := by

  have hNonColSymm :
      Not (PrimCollinear Geo hAxes.V hAxes.O hAxes.U) := by
    intro h
    exact
      hAxes.hNonCol
        (PrimCollinearSymm
          Geo
          hAxes.V hAxes.O hAxes.U
          h)

  have hRightSymm :
      HilbertRightAngle Geo hAxes.V hAxes.O hAxes.U :=
    coxeter_right_angle_swap
      Geo
      hAxes.U hAxes.O hAxes.V
      hAxes.hNonCol
      hAxes.hRight

  exact
    {
      O := hAxes.O
      U := hAxes.V
      V := hAxes.U

      hO1 := hAxes.hO2
      hO2 := hAxes.hO1

      hU1 := hAxes.hV2
      hV2 := hAxes.hU1

      hOU := hAxes.hOV
      hOV := hAxes.hOU

      hNonCol := hNonColSymm
      hRight := hRightSymm
    }


/--
A point of the second perpendicular axis, different from the
intersection point O, cannot lie on the first axis.
-/
theorem perpendicular_axes_second_off_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2)
    (P : Geo.Point)
    (hP2 :
      HilbertIncidence.OnLine P axis2.carrier)
    (hOP :
      Not (hAxes.O = P)) :
    Not (HilbertIncidence.OnLine P axis1.carrier) := by

  intro hP1

  ----------------------------------------------------------------------
  -- If P were also on axis1, then the two axes would share the
  -- two distinct points O and P, hence would be the same line.
  ----------------------------------------------------------------------

  have hAxesEq :
      axis1.carrier = axis2.carrier :=
    HilbertPlaneIncidence.line_unique
      hAxes.O P
      hOP
      axis1.carrier
      axis2.carrier
      hAxes.hO1
      hP1
      hAxes.hO2
      hP2

  ----------------------------------------------------------------------
  -- Therefore V would also lie on axis1.
  ----------------------------------------------------------------------

  have hV1 :
      HilbertIncidence.OnLine hAxes.V axis1.carrier := by
    rw [hAxesEq]
    exact hAxes.hV2

  ----------------------------------------------------------------------
  -- But then U,O,V would all lie on axis1, contradicting the
  -- nondegenerate right-angle configuration.
  ----------------------------------------------------------------------

  have hUOV :
      PrimCollinear Geo hAxes.U hAxes.O hAxes.V :=
    ⟨axis1.carrier,
      hAxes.hU1,
      hAxes.hO1,
      hV1⟩

  exact hAxes.hNonCol hUOV


/--
Every nonintersection point of axis2 is perpendicular to axis1
with foot O.
-/
theorem perpendicular_axes_second_point_perpendicular_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2)
    (P : Geo.Point)
    (hP2 :
      HilbertIncidence.OnLine P axis2.carrier)
    (hOP :
      Not (hAxes.O = P)) :
    PerpendicularToAxis Geo axis1 hAxes.O P := by

  have hPoff1 :
      Not (HilbertIncidence.OnLine P axis1.carrier) :=
    perpendicular_axes_second_off_first
      Geo
      axis1 axis2
      hAxes
      P
      hP2
      hOP

  ----------------------------------------------------------------------
  -- O,V,P lie on axis2.
  ----------------------------------------------------------------------

  have hOVP :
      PrimCollinear Geo hAxes.O hAxes.V P :=
    ⟨axis2.carrier,
      hAxes.hO2,
      hAxes.hV2,
      hP2⟩

  ----------------------------------------------------------------------
  -- Transport the right angle UOV along the second carrier from V to P.
  ----------------------------------------------------------------------

  have hRightUOP :
      HilbertRightAngle Geo hAxes.U hAxes.O P :=
    coxeter_right_angle_collinear_second
      Geo
      hAxes.U
      hAxes.O
      hAxes.V
      P
      hAxes.hOV
      hOP
      hOVP
      hAxes.hNonCol
      hAxes.hRight

  have hUO :
      Not (hAxes.U = hAxes.O) :=
    Ne.symm hAxes.hOU

  exact
    ⟨hAxes.hO1,
      hPoff1,
      ⟨hAxes.U,
        hAxes.hU1,
        hUO,
        hRightUOP⟩⟩


/--
Reflection in axis1 preserves the perpendicular axis2 setwise.
-/
theorem lineReflect_preserves_perpendicular_axis_second
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2)
    (P : Geo.Point)
    (hP2 :
      HilbertIncidence.OnLine P axis2.carrier) :
    HilbertIncidence.OnLine
      (lineReflect Geo axis1 P)
      axis2.carrier := by

  by_cases hOP : hAxes.O = P

  ----------------------------------------------------------------------
  -- P = O.  The intersection lies on axis1, hence is fixed.
  ----------------------------------------------------------------------

  · subst P

    have hFixO :
        lineReflect Geo axis1 hAxes.O = hAxes.O :=
      lineReflect_fixed_of_on_axis
        Geo
        axis1
        hAxes.O
        hAxes.hO1

    rw [hFixO]

    exact hAxes.hO2

  ----------------------------------------------------------------------
  -- P != O.  Then O is the perpendicular foot of P on axis1.
  ----------------------------------------------------------------------

  · have hPerpO :
        PerpendicularToAxis Geo axis1 hAxes.O P :=
      perpendicular_axes_second_point_perpendicular_first
        Geo
        axis1 axis2
        hAxes
        P
        hP2
        hOP

    have hPoff1 :
        Not (HilbertIncidence.OnLine P axis1.carrier) :=
      hPerpO.2.1

    --------------------------------------------------------------------
    -- The canonical reflection has some perpendicular foot H.
    --------------------------------------------------------------------

    rcases
        lineReflect_off_axis_data
          Geo
          axis1
          P
          hPoff1
      with
      ⟨H, hPerpH, hMidH⟩

    --------------------------------------------------------------------
    -- Uniqueness of the perpendicular foot forces H = O.
    --------------------------------------------------------------------

    have hOH :
        hAxes.O = H :=
      perpendicular_foot_unique
        Geo
        axis1
        P
        hAxes.O
        H
        hPerpO
        hPerpH

    subst H

    --------------------------------------------------------------------
    -- Thus P-O-r1(P), so P, O, r1(P) are collinear.
    --------------------------------------------------------------------

    have hPOR :
        PrimCollinear
          Geo
          P
          hAxes.O
          (lineReflect Geo axis1 P) :=
      (HilbertOrder.between_incidence
        P
        hAxes.O
        (lineReflect Geo axis1 P)
        hMidH.1).2.2.2.1

    have hPO :
        Not (P = hAxes.O) :=
      Ne.symm hOP

    --------------------------------------------------------------------
    -- P and O are distinct points of axis2, so the whole carrier is
    -- axis2; hence r1(P) also lies on axis2.
    --------------------------------------------------------------------

    exact
      hilbert_collinear_on_line
        Geo
        P
        hAxes.O
        (lineReflect Geo axis1 P)
        axis2.carrier
        hPO
        hP2
        hAxes.hO2
        hPOR


/--
Reflection in axis2 preserves the perpendicular axis1 setwise.
-/
theorem lineReflect_preserves_perpendicular_axis_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2)
    (P : Geo.Point)
    (hP1 :
      HilbertIncidence.OnLine P axis1.carrier) :
    HilbertIncidence.OnLine
      (lineReflect Geo axis2 P)
      axis1.carrier := by

  have hAxesSymm :
      ReflectionAxesPerpendicular Geo axis2 axis1 :=
    reflectionAxesPerpendicular_symm
      Geo
      axis1 axis2
      hAxes

  exact
    lineReflect_preserves_perpendicular_axis_second
      Geo
      axis2 axis1
      hAxesSymm
      P
      hP1

/--
Line reflection preserves strict betweenness.
-/
theorem lineReflect_preserves_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    Geo.Between
      (lineReflect Geo axis A)
      (lineReflect Geo axis B)
      (lineReflect Geo axis C) := by

  have hABCData :=
    HilbertOrder.between_incidence
      A B C hABC

  have hAB :
      A ≠ B :=
    hABCData.1

  have hBC :
      B ≠ C :=
    hABCData.2.1

  have hAC :
      A ≠ C :=
    hABCData.2.2.1

  have hInjective :
      Function.Injective
        (lineReflect Geo axis) := by
    intro X Y hXY

    have hBack :=
      congrArg
        (lineReflect Geo axis)
        hXY

    rw [lineReflect_involutive Geo axis X,
        lineReflect_involutive Geo axis Y] at hBack

    exact hBack

  have hAB' :
      lineReflect Geo axis A ≠
        lineReflect Geo axis B := by
    intro hEq
    exact hAB (hInjective hEq)

  have hBC' :
      lineReflect Geo axis B ≠
        lineReflect Geo axis C := by
    intro hEq
    exact hBC (hInjective hEq)

  have hAC' :
      lineReflect Geo axis A ≠
        lineReflect Geo axis C := by
    intro hEq
    exact hAC (hInjective hEq)

  have hABCong :
      Geo.Congruent
        A B
        (lineReflect Geo axis A)
        (lineReflect Geo axis B) :=
    lineReflect_preserves_congruence
      Geo axis A B

  have hACCong :
      Geo.Congruent
        A C
        (lineReflect Geo axis A)
        (lineReflect Geo axis C) :=
    lineReflect_preserves_congruence
      Geo axis A C

  have hBCCong :
      Geo.Congruent
        B C
        (lineReflect Geo axis B)
        (lineReflect Geo axis C) :=
    lineReflect_preserves_congruence
      Geo axis B C

  exact
    hilbert_theorem27_three_points
      Geo
      A B C
      (lineReflect Geo axis A)
      (lineReflect Geo axis B)
      (lineReflect Geo axis C)
      hABC
      hAB'
      hBC'
      hAC'
      hABCong
      hACCong
      hBCCong

/--
Line reflection preserves collinearity.
-/
theorem lineReflect_preserves_collinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (A B C : Geo.Point)
    (hABC :
      PrimCollinear Geo A B C) :
    PrimCollinear
      Geo
      (lineReflect Geo axis A)
      (lineReflect Geo axis B)
      (lineReflect Geo axis C) := by

  have hAB :
      Geo.Congruent
        A B
        (lineReflect Geo axis A)
        (lineReflect Geo axis B) :=
    lineReflect_preserves_congruence
      Geo axis A B

  have hAC :
      Geo.Congruent
        A C
        (lineReflect Geo axis A)
        (lineReflect Geo axis C) :=
    lineReflect_preserves_congruence
      Geo axis A C

  have hBC :
      Geo.Congruent
        B C
        (lineReflect Geo axis B)
        (lineReflect Geo axis C) :=
    lineReflect_preserves_congruence
      Geo axis B C

  exact
    hilbert_collinearity_preserved_by_three_congruences
      Geo
      A B C
      (lineReflect Geo axis A)
      (lineReflect Geo axis B)
      (lineReflect Geo axis C)
      hABC
      hAB
      hAC
      hBC

/--
Line reflection preserves noncollinearity.
-/
theorem lineReflect_preserves_noncollinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (A B C : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C)) :
    Not
      (PrimCollinear
        Geo
        (lineReflect Geo axis A)
        (lineReflect Geo axis B)
        (lineReflect Geo axis C)) := by

  intro hImage

  have hBack :
      PrimCollinear
        Geo
        (lineReflect Geo axis
          (lineReflect Geo axis A))
        (lineReflect Geo axis
          (lineReflect Geo axis B))
        (lineReflect Geo axis
          (lineReflect Geo axis C)) :=
    lineReflect_preserves_collinear
      Geo
      axis
      (lineReflect Geo axis A)
      (lineReflect Geo axis B)
      (lineReflect Geo axis C)
      hImage

  rw [lineReflect_involutive Geo axis A,
      lineReflect_involutive Geo axis B,
      lineReflect_involutive Geo axis C] at hBack

  exact hABC hBack

/--
Line reflection preserves angles of nondegenerate triples.
-/
theorem lineReflect_preserves_angle
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (A B C : Geo.Point)
    (hABC :
      Not (PrimCollinear Geo A B C)) :
    Geo.AngleCongruent
      A B C
      (lineReflect Geo axis A)
      (lineReflect Geo axis B)
      (lineReflect Geo axis C) := by

  have hAB :
      Geo.Congruent
        A B
        (lineReflect Geo axis A)
        (lineReflect Geo axis B) :=
    lineReflect_preserves_congruence
      Geo axis A B

  have hBC :
      Geo.Congruent
        B C
        (lineReflect Geo axis B)
        (lineReflect Geo axis C) :=
    lineReflect_preserves_congruence
      Geo axis B C

  have hAC :
      Geo.Congruent
        A C
        (lineReflect Geo axis A)
        (lineReflect Geo axis C) :=
    lineReflect_preserves_congruence
      Geo axis A C

  have hSSS :=
    HilbertSSS
      Geo
      A B C
      (lineReflect Geo axis A)
      (lineReflect Geo axis B)
      (lineReflect Geo axis C)
      hABC
      hAB
      hBC
      hAC

  exact hSSS.2.angleB

/--
Line reflection preserves right angles.
-/
theorem lineReflect_preserves_right_angle
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (A O B : Geo.Point)
    (hAOB :
      Not (PrimCollinear Geo A O B))
    (hRight :
      HilbertRightAngle Geo A O B) :
    HilbertRightAngle
      Geo
      (lineReflect Geo axis A)
      (lineReflect Geo axis O)
      (lineReflect Geo axis B) := by

  have hImageNonCol :
      Not
        (PrimCollinear
          Geo
          (lineReflect Geo axis A)
          (lineReflect Geo axis O)
          (lineReflect Geo axis B)) :=
    lineReflect_preserves_noncollinear
      Geo
      axis
      A O B
      hAOB

  have hAngle :
      Geo.AngleCongruent
        A O B
        (lineReflect Geo axis A)
        (lineReflect Geo axis O)
        (lineReflect Geo axis B) :=
    lineReflect_preserves_angle
      Geo
      axis
      A O B
      hAOB

  exact
    hilbert_right_angle_transport
      Geo
      A O B
      (lineReflect Geo axis A)
      (lineReflect Geo axis O)
      (lineReflect Geo axis B)
      hAOB
      hImageNonCol
      hRight
      hAngle

/--
Line reflection transports midpoint configurations.

This is the order-and-congruence form of the statement that an
isometry sends a midpoint to a midpoint.
-/
theorem lineReflect_preserves_midpoint
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (M A B : Geo.Point)
    (hMid :
      HilbertIsMidpoint Geo M A B) :
    HilbertIsMidpoint
      Geo
      (lineReflect Geo axis M)
      (lineReflect Geo axis A)
      (lineReflect Geo axis B) := by

  have hBetween :
      Geo.Between
        (lineReflect Geo axis A)
        (lineReflect Geo axis M)
        (lineReflect Geo axis B) :=
    lineReflect_preserves_between
      Geo
      axis
      A M B
      hMid.1

  have hAM_image :
      Geo.Congruent
        A M
        (lineReflect Geo axis A)
        (lineReflect Geo axis M) :=
    lineReflect_preserves_congruence
      Geo
      axis
      A M

  have hMB_image :
      Geo.Congruent
        M B
        (lineReflect Geo axis M)
        (lineReflect Geo axis B) :=
    lineReflect_preserves_congruence
      Geo
      axis
      M B

  have hImageAM_AM :
      Geo.Congruent
        (lineReflect Geo axis A)
        (lineReflect Geo axis M)
        A M :=
    hilbert_congruent_symmetry
      Geo
      A M
      (lineReflect Geo axis A)
      (lineReflect Geo axis M)
      hAM_image

  have hImageAM_MB :
      Geo.Congruent
        (lineReflect Geo axis A)
        (lineReflect Geo axis M)
        M B :=
    hilbert_congruent_transitivity
      Geo
      (lineReflect Geo axis A)
      (lineReflect Geo axis M)
      A M
      M B
      hImageAM_AM
      hMid.2

  have hCong :
      Geo.Congruent
        (lineReflect Geo axis A)
        (lineReflect Geo axis M)
        (lineReflect Geo axis M)
        (lineReflect Geo axis B) :=
    hilbert_congruent_transitivity
      Geo
      (lineReflect Geo axis A)
      (lineReflect Geo axis M)
      M B
      (lineReflect Geo axis M)
      (lineReflect Geo axis B)
      hImageAM_MB
      hMB_image

  exact
    ⟨hBetween, hCong⟩


/--
Reflection in axis1 transports a perpendicular to the invariant
perpendicular axis2 to another perpendicular to axis2.
-/
theorem perpendicular_axes_transport_second_perpendicular
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2)
    (H P : Geo.Point)
    (hPerp :
      PerpendicularToAxis Geo axis2 H P) :
    PerpendicularToAxis
      Geo
      axis2
      (lineReflect Geo axis1 H)
      (lineReflect Geo axis1 P) := by

  rcases hPerp with
    ⟨hH2,
      hPoff2,
      R,
      hR2,
      hRH,
      hRightRHP⟩

  have hHimage2 :
      HilbertIncidence.OnLine
        (lineReflect Geo axis1 H)
        axis2.carrier :=
    lineReflect_preserves_perpendicular_axis_second
      Geo
      axis1 axis2
      hAxes
      H
      hH2

  have hRimage2 :
      HilbertIncidence.OnLine
        (lineReflect Geo axis1 R)
        axis2.carrier :=
    lineReflect_preserves_perpendicular_axis_second
      Geo
      axis1 axis2
      hAxes
      R
      hR2

  ----------------------------------------------------------------------
  -- An off-axis point cannot be carried onto axis2, because applying
  -- r1 once more would put the original point on axis2.
  ----------------------------------------------------------------------

  have hPimageOff2 :
      Not
        (HilbertIncidence.OnLine
          (lineReflect Geo axis1 P)
          axis2.carrier) := by

    intro hPimage2

    have hBack :
        HilbertIncidence.OnLine
          (lineReflect Geo axis1
            (lineReflect Geo axis1 P))
          axis2.carrier :=
      lineReflect_preserves_perpendicular_axis_second
        Geo
        axis1 axis2
        hAxes
        (lineReflect Geo axis1 P)
        hPimage2

    rw [lineReflect_involutive Geo axis1 P] at hBack

    exact hPoff2 hBack

  have hRHP :
      Not (PrimCollinear Geo R H P) :=
    hilbert_not_collinear_of_off_line
      Geo
      R H P
      axis2.carrier
      hRH
      hR2
      hH2
      hPoff2

  have hRimageHimage :
      Not
        (lineReflect Geo axis1 R =
          lineReflect Geo axis1 H) := by

    intro hEq

    have hBack :=
      congrArg
        (lineReflect Geo axis1)
        hEq

    rw [lineReflect_involutive Geo axis1 R,
        lineReflect_involutive Geo axis1 H] at hBack

    exact hRH hBack

  have hRightImage :
      HilbertRightAngle
        Geo
        (lineReflect Geo axis1 R)
        (lineReflect Geo axis1 H)
        (lineReflect Geo axis1 P) :=
    lineReflect_preserves_right_angle
      Geo
      axis1
      R H P
      hRHP
      hRightRHP

  exact
    ⟨hHimage2,
      hPimageOff2,
      ⟨lineReflect Geo axis1 R,
        hRimage2,
        hRimageHimage,
        hRightImage⟩⟩


/--
For perpendicular axes, conjugating reflection in axis2 by reflection
in axis1 gives reflection in axis2, pointwise:

    r1 (r2 (r1 P)) = r2 P.
-/
theorem perpendicular_axes_conjugation_pointwise
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2)
    (P : Geo.Point) :
    lineReflect Geo axis1
        (lineReflect Geo axis2
          (lineReflect Geo axis1 P)) =
      lineReflect Geo axis2 P := by

  by_cases hP2 :
      HilbertIncidence.OnLine P axis2.carrier

  ----------------------------------------------------------------------
  -- P lies on axis2.
  --
  -- r1(P) is again on axis2, hence r2 fixes both P and r1(P).
  ----------------------------------------------------------------------

  · have hP1on2 :
        HilbertIncidence.OnLine
          (lineReflect Geo axis1 P)
          axis2.carrier :=
      lineReflect_preserves_perpendicular_axis_second
        Geo
        axis1 axis2
        hAxes
        P
        hP2

    have hFixP1 :
        lineReflect Geo axis2
          (lineReflect Geo axis1 P) =
        lineReflect Geo axis1 P :=
      lineReflect_fixed_of_on_axis
        Geo
        axis2
        (lineReflect Geo axis1 P)
        hP1on2

    have hFixP :
        lineReflect Geo axis2 P = P :=
      lineReflect_fixed_of_on_axis
        Geo
        axis2
        P
        hP2

    calc
      lineReflect Geo axis1
          (lineReflect Geo axis2
            (lineReflect Geo axis1 P))
          =
        lineReflect Geo axis1
          (lineReflect Geo axis1 P) := by
            rw [hFixP1]

      _ = P :=
        lineReflect_involutive
          Geo axis1 P

      _ = lineReflect Geo axis2 P :=
        hFixP.symm

  ----------------------------------------------------------------------
  -- P lies off axis2.
  ----------------------------------------------------------------------

  · have hP1off2 :
        Not
          (HilbertIncidence.OnLine
            (lineReflect Geo axis1 P)
            axis2.carrier) := by

      intro hP1on2

      have hBack :
          HilbertIncidence.OnLine
            (lineReflect Geo axis1
              (lineReflect Geo axis1 P))
            axis2.carrier :=
        lineReflect_preserves_perpendicular_axis_second
          Geo
          axis1 axis2
          hAxes
          (lineReflect Geo axis1 P)
          hP1on2

      rw [lineReflect_involutive Geo axis1 P] at hBack

      exact hP2 hBack

    --------------------------------------------------------------------
    -- Reflect r1(P) in axis2.  Let H be its perpendicular foot.
    --------------------------------------------------------------------

    rcases
        lineReflect_off_axis_data
          Geo
          axis2
          (lineReflect Geo axis1 P)
          hP1off2
      with
      ⟨H, hPerpH, hMidH⟩

    --------------------------------------------------------------------
    -- Apply r1 to the entire perpendicular configuration.
    --------------------------------------------------------------------

    have hPerpBackRaw :
        PerpendicularToAxis
          Geo
          axis2
          (lineReflect Geo axis1 H)
          (lineReflect Geo axis1
            (lineReflect Geo axis1 P)) :=
      perpendicular_axes_transport_second_perpendicular
        Geo
        axis1 axis2
        hAxes
        H
        (lineReflect Geo axis1 P)
        hPerpH

    have hPerpBack :
        PerpendicularToAxis
          Geo
          axis2
          (lineReflect Geo axis1 H)
          P := by
      simpa only
        [lineReflect_involutive Geo axis1 P]
        using hPerpBackRaw

    --------------------------------------------------------------------
    -- Midpoint data is transported by the isometry r1.
    --------------------------------------------------------------------

    have hMidBackRaw :
        HilbertIsMidpoint
          Geo
          (lineReflect Geo axis1 H)
          (lineReflect Geo axis1
            (lineReflect Geo axis1 P))
          (lineReflect Geo axis1
            (lineReflect Geo axis2
              (lineReflect Geo axis1 P))) :=
      lineReflect_preserves_midpoint
        Geo
        axis1
        H
        (lineReflect Geo axis1 P)
        (lineReflect Geo axis2
          (lineReflect Geo axis1 P))
        hMidH

    have hMidBack :
        HilbertIsMidpoint
          Geo
          (lineReflect Geo axis1 H)
          P
          (lineReflect Geo axis1
            (lineReflect Geo axis2
              (lineReflect Geo axis1 P))) := by
      simpa only
        [lineReflect_involutive Geo axis1 P]
        using hMidBackRaw

    --------------------------------------------------------------------
    -- Hence r1 r2 r1(P) satisfies the defining reflection relation
    -- for axis2 and the original point P.
    --------------------------------------------------------------------

    have hCandidate :
        IsLineReflection
          Geo
          axis2
          P
          (lineReflect Geo axis1
            (lineReflect Geo axis2
              (lineReflect Geo axis1 P))) :=
      Or.inr
        ⟨hP2,
          ⟨lineReflect Geo axis1 H,
            hPerpBack,
            hMidBack⟩⟩

    --------------------------------------------------------------------
    -- Reflection in a fixed axis is unique.
    --------------------------------------------------------------------

    exact
      line_reflection_unique
        Geo
        axis2
        P
        (lineReflect Geo axis1
          (lineReflect Geo axis2
            (lineReflect Geo axis1 P)))
        (lineReflect Geo axis2 P)
        hCandidate
        (lineReflect_spec Geo axis2 P)


/--
Reflections in perpendicular axes commute pointwise.
-/
theorem perpendicular_axes_reflections_commute_pointwise
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2)
    (P : Geo.Point) :
    lineReflect Geo axis1
        (lineReflect Geo axis2 P) =
      lineReflect Geo axis2
        (lineReflect Geo axis1 P) := by

  have hConj :=
    perpendicular_axes_conjugation_pointwise
      Geo
      axis1 axis2
      hAxes
      (lineReflect Geo axis1 P)

  simpa only
    [lineReflect_involutive Geo axis1 P]
    using hConj


/--
The product of reflections in perpendicular axes has order dividing two,
pointwise.
-/
theorem perpendicular_axes_reflectionProduct_square_apply
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2)
    (P : Geo.Point) :
    reflectionProduct Geo axis1 axis2
        (reflectionProduct Geo axis1 axis2 P) =
      P := by

  simp only [reflectionProduct_apply]

  rw [
    perpendicular_axes_conjugation_pointwise
      Geo axis1 axis2 hAxes P
  ]

  exact
    lineReflect_involutive
      Geo axis2 P

/--
For perpendicular axes, the square of the product of the two
reflections is the identity permutation.
-/
theorem perpendicular_axes_reflectionProductPow_two
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2) :
    reflectionProductPow Geo axis1 axis2 2 =
      Equiv.refl Geo.Point := by

  apply Equiv.ext
  intro P

  have hSquare :
      reflectionProduct Geo axis1 axis2
        (reflectionProduct Geo axis1 axis2 P) =
      P :=
    perpendicular_axes_reflectionProduct_square_apply
      Geo
      axis1 axis2
      hAxes
      P

  rw [show (2 : Nat) = Nat.succ 1 by rfl]
  rw [reflectionProductPow_succ]
  rw [reflectionProductPow_one]

  exact hSquare


end Geometry

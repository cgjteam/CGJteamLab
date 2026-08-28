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

/-!
----------------------------------------------------------------------------
General reflection transport and the Coxeter relation p = 3
----------------------------------------------------------------------------

The following layer extends the perpendicular-axis p = 2 development by
introducing exact transport of carrier lines under reflection.

For an equilateral triangle, the three median reflection axes are then used
synthetically to prove:

    r_b(a) = c,
    r_a(b) = c,
    r_a r_b r_a = r_b r_a r_b,
    (r_a r_b)^3 = 1.

No metric, coordinates, trigonometric formulas, or angle-measure machinery
is used in this chain.
----------------------------------------------------------------------------
-/
/--
`ReflectionMapsLine Geo mirror source target` means that reflection in
`mirror` sends the whole carrier `source` exactly onto `target`.

The definition is deliberately stated on `Geo.Line`, not on
`ReflectionAxis`, because the auxiliary witness points stored in
`ReflectionAxis` are irrelevant to the image of the carrier.
-/
def ReflectionMapsLine
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (mirror : ReflectionAxis Geo)
    (source target : Geo.Line) : Prop :=
  forall P : Geo.Point,
    HilbertIncidence.OnLine P source <->
      HilbertIncidence.OnLine
        (lineReflect Geo mirror P)
        target

/--
General transport of perpendicular-to-axis data through a reflection.

If `mirror` maps the carrier of `source` exactly onto the carrier of
`target`, then a perpendicular from `P` to `source` with foot `H`
is transported to a perpendicular from the reflected point to `target`.
-/
theorem lineReflect_transports_perpendicularToAxis
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (mirror source target : ReflectionAxis Geo)
    (hMap :
      ReflectionMapsLine
        Geo
        mirror
        source.carrier
        target.carrier)
    (H P : Geo.Point)
    (hPerp : PerpendicularToAxis Geo source H P) :
    PerpendicularToAxis
      Geo
      target
      (lineReflect Geo mirror H)
      (lineReflect Geo mirror P) := by
  have hHsource := hPerp.1
  have hPoffSource := hPerp.2.1

  apply And.intro

  exact (hMap H).mp hHsource

  apply And.intro

  exact
    (by
      intro hPtarget
      exact hPoffSource ((hMap P).mpr hPtarget))

  apply Exists.elim hPerp.2.2
  intro R hRdata

  have hRsource := hRdata.1
  have hRH := hRdata.2.1
  have hRight := hRdata.2.2

  apply Exists.intro (lineReflect Geo mirror R)
  apply And.intro

  exact (hMap R).mp hRsource

  apply And.intro

  exact
    (by
      intro hEq

      have hBack :=
        congrArg
          (lineReflect Geo mirror)
          hEq

      rw [
        lineReflect_involutive Geo mirror R,
        lineReflect_involutive Geo mirror H
      ] at hBack

      exact hRH hBack)

  have hNonCol :
      Not (PrimCollinear Geo R H P) := by
    intro hRHP

    apply hPoffSource

    exact
      hilbert_collinear_on_line
        Geo
        R
        H
        P
        source.carrier
        hRH
        hRsource
        hHsource
        hRHP

  exact
    lineReflect_preserves_right_angle
      Geo
      mirror
      R
      H
      P
      hNonCol
      hRight


/--
Transport the complete line-reflection relation through another reflection.

If `mirror` maps the carrier of `source` exactly onto the carrier of
`target`, then reflecting both endpoints of an `IsLineReflection`
configuration for `source` produces an `IsLineReflection` configuration
for `target`.
-/
theorem lineReflect_transports_isLineReflection
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (mirror source target : ReflectionAxis Geo)
    (hMap :
      ReflectionMapsLine
        Geo
        mirror
        source.carrier
        target.carrier)
    (P Q : Geo.Point)
    (hRef : IsLineReflection Geo source P Q) :
    IsLineReflection
      Geo
      target
      (lineReflect Geo mirror P)
      (lineReflect Geo mirror Q) := by
  unfold IsLineReflection at hRef
  unfold IsLineReflection

  apply Or.elim hRef

  intro hFixed

  apply Or.inl
  apply And.intro

  exact (hMap P).mp hFixed.1

  exact
    congrArg
      (lineReflect Geo mirror)
      hFixed.2

  intro hOff

  apply Or.inr
  apply And.intro

  exact
    (by
      intro hPtarget
      exact hOff.1 ((hMap P).mpr hPtarget))

  apply Exists.elim hOff.2
  intro H hHdata

  apply Exists.intro (lineReflect Geo mirror H)
  apply And.intro

  exact
    lineReflect_transports_perpendicularToAxis
      Geo
      mirror
      source
      target
      hMap
      H
      P
      hHdata.1

  exact
    lineReflect_preserves_midpoint
      Geo
      mirror
      H
      P
      Q
      hHdata.2


/--
General pointwise conjugation theorem for line reflections.

If reflection in `mirror` maps the carrier of `source` exactly onto the
carrier of `target`, then conjugating reflection in `source` by reflection
in `mirror` is reflection in `target`.
-/
theorem lineReflect_conjugation_pointwise
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (mirror source target : ReflectionAxis Geo)
    (hMap :
      ReflectionMapsLine
        Geo
        mirror
        source.carrier
        target.carrier)
    (P : Geo.Point) :
    lineReflect Geo mirror
      (lineReflect Geo source
        (lineReflect Geo mirror P)) =
    lineReflect Geo target P := by
  have hSource :
      IsLineReflection
        Geo
        source
        (lineReflect Geo mirror P)
        (lineReflect Geo source
          (lineReflect Geo mirror P)) :=
    lineReflect_spec
      Geo
      source
      (lineReflect Geo mirror P)

  have hTransport :
      IsLineReflection
        Geo
        target
        (lineReflect Geo mirror
          (lineReflect Geo mirror P))
        (lineReflect Geo mirror
          (lineReflect Geo source
            (lineReflect Geo mirror P))) :=
    lineReflect_transports_isLineReflection
      Geo
      mirror
      source
      target
      hMap
      (lineReflect Geo mirror P)
      (lineReflect Geo source
        (lineReflect Geo mirror P))
      hSource

  rw [lineReflect_involutive Geo mirror P] at hTransport

  have hTarget :
      IsLineReflection
        Geo
        target
        P
        (lineReflect Geo target P) :=
    lineReflect_spec Geo target P

  exact
    line_reflection_unique
      Geo
      target
      P
      (lineReflect Geo mirror
        (lineReflect Geo source
          (lineReflect Geo mirror P)))
      (lineReflect Geo target P)
      hTransport
      hTarget



/--
In an isosceles triangle, the segment from the apex to the midpoint of
the base is perpendicular to the base.

This is the geometric core needed to turn the old provisional
`isosceles_axis_exists` statement into a theorem.
-/
theorem isosceles_midpoint_right_angle
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C M : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C)
    (hMid : HilbertIsMidpoint Geo M B C) :
    HilbertRightAngle Geo A M B := by
  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hMid.1

  have hBM : Not (B = M) :=
    hBMCdata.1

  have hBMC :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  have hABM :
      Not (Collinear Geo A B M) := by
    intro hABMcol

    have hABCcol :
        Collinear Geo A B C :=
      hilbert_primCollinear_trans
        Geo
        A
        B
        M
        C
        hBM
        hABMcol
        hBMC

    exact hABC hABCcol

  have hBM_CM :
      Geo.Congruent B M C M :=
    (Geo.congruent_reverse_second
      B M M C).mp hMid.2

  have hAM_AM :
      Geo.Congruent A M A M :=
    hilbert_congruent_reflexive
      Geo A M

  have hSSS :=
    HilbertSSS
      Geo
      A B M
      A C M
      hABM
      hABAC
      hBM_CM
      hAM_AM

  have hBMA_AMC :
      Geo.AngleCongruent B M A A M C :=
    (Geo.angle_congruent_reverse_first
      A M B
      A M C).mp hSSS.2.angleC

  have hRightBMA :
      HilbertRightAngle Geo B M A :=
    Exists.intro
      C
      (And.intro
        hMid.1
        hBMA_AMC)

  have hBMA :
      Not (PrimCollinear Geo B M A) := by
    intro hBMAcol

    have hMAB :
        PrimCollinear Geo M A B :=
      PrimCollinearCycle
        Geo B M A hBMAcol

    have hABMcol :
        PrimCollinear Geo A B M :=
      PrimCollinearCycle
        Geo M A B hMAB

    exact hABM hABMcol

  exact
    coxeter_right_angle_swap
      Geo
      B M A
      hBMA
      hRightBMA


/--
The median axis of an isosceles triangle is a genuine reflection axis
which fixes the apex and midpoint and swaps the two base vertices.

This replaces the old provisional `isosceles_axis_exists` axiom by a
theorem built from the current Hilbert reflection machinery.
-/
theorem isosceles_midpoint_axis_swaps_base
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C M : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C)
    (hMid : HilbertIsMidpoint Geo M B C) :
    Exists fun axis : ReflectionAxis Geo =>
      And
        (HilbertIncidence.OnLine A axis.carrier)
        (And
          (HilbertIncidence.OnLine M axis.carrier)
          (And
            (lineReflect Geo axis A = A)
            (And
              (lineReflect Geo axis M = M)
              (And
                (lineReflect Geo axis B = C)
                (lineReflect Geo axis C = B))))) := by
  have hBMCdata :=
    HilbertOrder.between_incidence
      B M C hMid.1

  have hBM : Not (B = M) :=
    hBMCdata.1

  have hBMC :
      Collinear Geo B M C :=
    hBMCdata.2.2.2.1

  have hAM : Not (A = M) := by
    intro hEq
    subst M

    have hBAC :
        Collinear Geo B A C :=
      hBMC

    have hABCcol :
        Collinear Geo A B C :=
      PrimCollinearSwap
        Geo B A C hBAC

    exact hABC hABCcol

  have hLine :=
    HilbertPlaneIncidence.line_through
      A M hAM

  let lineAM : Geo.Line :=
    Classical.choose hLine

  have hLineData :
      And
        (HilbertIncidence.OnLine A lineAM)
        (HilbertIncidence.OnLine M lineAM) :=
    Classical.choose_spec hLine

  have hAline :
      HilbertIncidence.OnLine A lineAM :=
    hLineData.1

  have hMline :
      HilbertIncidence.OnLine M lineAM :=
    hLineData.2

  let axis : ReflectionAxis Geo :=
    { carrier := lineAM
      A := A
      B := M
      hAB := hAM
      hA := hAline
      hB := hMline }

  have hBoff :
      Not
        (HilbertIncidence.OnLine
          B axis.carrier) := by
    intro hBline

    have hBlineAM :
        HilbertIncidence.OnLine B lineAM := by
      simpa [axis] using hBline

    have hABM :
        Collinear Geo A B M :=
      Exists.intro
        lineAM
        (And.intro
          hAline
          (And.intro
            hBlineAM
            hMline))

    have hABCcol :
        Collinear Geo A B C :=
      hilbert_primCollinear_trans
        Geo
        A
        B
        M
        C
        hBM
        hABM
        hBMC

    exact hABC hABCcol

  have hRight :
      HilbertRightAngle Geo A M B :=
    isosceles_midpoint_right_angle
      Geo
      A B C M
      hABC
      hABAC
      hMid

  have hPerp :
      PerpendicularToAxis
        Geo axis M B := by
    unfold PerpendicularToAxis

    apply And.intro

    simpa [axis] using hMline

    apply And.intro
    exact hBoff

    apply Exists.intro A
    apply And.intro

    simpa [axis] using hAline

    apply And.intro
    exact hAM
    exact hRight

  have hRefBC :
      IsLineReflection Geo axis B C := by
    unfold IsLineReflection

    apply Or.inr
    apply And.intro
    exact hBoff

    apply Exists.intro M
    apply And.intro
    exact hPerp
    exact hMid

  have hSwapBC :
      lineReflect Geo axis B = C :=
    line_reflection_unique
      Geo
      axis
      B
      (lineReflect Geo axis B)
      C
      (lineReflect_spec Geo axis B)
      hRefBC

  have hSwapCB :
      lineReflect Geo axis C = B := by
    have hInv :
        lineReflect Geo axis
          (lineReflect Geo axis B) = B :=
      lineReflect_involutive
        Geo axis B

    rw [hSwapBC] at hInv
    exact hInv

  have hFixA :
      lineReflect Geo axis A = A := by
    rcases
        lineReflect_spec Geo axis A with
      hFixed | hOff

    exact hFixed.2

    exact
      False.elim
        (hOff.1
          (by
            simpa [axis] using hAline))

  have hFixM :
      lineReflect Geo axis M = M := by
    rcases
        lineReflect_spec Geo axis M with
      hFixed | hOff

    exact hFixed.2

    exact
      False.elim
        (hOff.1
          (by
            simpa [axis] using hMline))

  apply Exists.intro axis
  apply And.intro

  simpa [axis] using hAline

  apply And.intro

  simpa [axis] using hMline

  apply And.intro
  exact hFixA

  apply And.intro
  exact hFixM

  apply And.intro
  exact hSwapBC
  exact hSwapCB

/--
Two-point criterion for the image of a line under a reflection.

Two distinct source points determine the source carrier. If their reflected
images lie on the target carrier, preservation of collinearity and
involutivity upgrade this to an exact `ReflectionMapsLine` statement.
-/
theorem reflectionMapsLine_of_two_points
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (mirror : ReflectionAxis Geo)
    (source target : Geo.Line)
    (X Y : Geo.Point)
    (hXsource : HilbertIncidence.OnLine X source)
    (hYsource : HilbertIncidence.OnLine Y source)
    (hXY : Not (X = Y))
    (hXtarget :
      HilbertIncidence.OnLine
        (lineReflect Geo mirror X)
        target)
    (hYtarget :
      HilbertIncidence.OnLine
        (lineReflect Geo mirror Y)
        target) :
    ReflectionMapsLine Geo mirror source target := by
  have hImageXY :
      Not
        (lineReflect Geo mirror X =
          lineReflect Geo mirror Y) := by
    intro hEq

    have hBack :=
      congrArg
        (lineReflect Geo mirror)
        hEq

    rw [
      lineReflect_involutive Geo mirror X,
      lineReflect_involutive Geo mirror Y
    ] at hBack

    exact hXY hBack

  intro P

  apply Iff.intro

  intro hPsource

  have hXYP :
      Collinear Geo X Y P :=
    Exists.intro
      source
      (And.intro
        hXsource
        (And.intro
          hYsource
          hPsource))

  have hImageCol :
      Collinear
        Geo
        (lineReflect Geo mirror X)
        (lineReflect Geo mirror Y)
        (lineReflect Geo mirror P) :=
    lineReflect_preserves_collinear
      Geo
      mirror
      X Y P
      hXYP

  exact
    hilbert_collinear_on_line
      Geo
      (lineReflect Geo mirror X)
      (lineReflect Geo mirror Y)
      (lineReflect Geo mirror P)
      target
      hImageXY
      hXtarget
      hYtarget
      hImageCol

  intro hPtarget

  have hImageCol :
      Collinear
        Geo
        (lineReflect Geo mirror X)
        (lineReflect Geo mirror Y)
        (lineReflect Geo mirror P) :=
    Exists.intro
      target
      (And.intro
        hXtarget
        (And.intro
          hYtarget
          hPtarget))

  have hBackCol :
      Collinear
        Geo
        (lineReflect Geo mirror
          (lineReflect Geo mirror X))
        (lineReflect Geo mirror
          (lineReflect Geo mirror Y))
        (lineReflect Geo mirror
          (lineReflect Geo mirror P)) :=
    lineReflect_preserves_collinear
      Geo
      mirror
      (lineReflect Geo mirror X)
      (lineReflect Geo mirror Y)
      (lineReflect Geo mirror P)
      hImageCol

  rw [
    lineReflect_involutive Geo mirror X,
    lineReflect_involutive Geo mirror Y,
    lineReflect_involutive Geo mirror P
  ] at hBackCol

  exact
    hilbert_collinear_on_line
      Geo
      X Y P
      source
      hXY
      hXsource
      hYsource
      hBackCol


/--
A strict Hilbert midpoint of a nondegenerate segment is unique.

This local theorem is the missing bridge needed for the p = 3 median-axis
construction: after a reflection transports one midpoint to another midpoint
of the same segment, uniqueness identifies the transported point.
-/
theorem hilbert_midpoint_unique_local
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (M N A B : Geo.Point)
    (hM : HilbertIsMidpoint Geo M A B)
    (hN : HilbertIsMidpoint Geo N A B) :
    M = N := by
  by_cases hMN : M = N

  exact hMN

  have hMdata :=
    HilbertOrder.between_incidence
      A M B hM.1

  have hNdata :=
    HilbertOrder.between_incidence
      A N B hN.1

  have hAM : Not (A = M) :=
    hMdata.1

  have hAN : Not (A = N) :=
    hNdata.1

  have hAB : Not (A = B) :=
    hMdata.2.2.1

  have hLine :=
    HilbertPlaneIncidence.line_through
      A B hAB

  let lineAB : Geo.Line :=
    Classical.choose hLine

  have hLineData :
      And
        (HilbertIncidence.OnLine A lineAB)
        (HilbertIncidence.OnLine B lineAB) :=
    Classical.choose_spec hLine

  have hAline :
      HilbertIncidence.OnLine A lineAB :=
    hLineData.1

  have hBline :
      HilbertIncidence.OnLine B lineAB :=
    hLineData.2

  have hMline :
      HilbertIncidence.OnLine M lineAB :=
    hilbert_between_on_line
      Geo
      A M B
      lineAB
      hAline
      hBline
      hM.1

  have hNline :
      HilbertIncidence.OnLine N lineAB :=
    hilbert_between_on_line
      Geo
      A N B
      lineAB
      hAline
      hBline
      hN.1

  have hAMNcol :
      Collinear Geo A M N :=
    Exists.intro
      lineAB
      (And.intro
        hAline
        (And.intro
          hMline
          hNline))

  have hTri :=
    hilbert_between_trichotomy
      Geo
      A M N
      hAM
      hMN
      hAN
      hAMNcol

  exact
    match hTri with
    | Or.inl hAMN =>
        False.elim (by
          have hMNB :
              Geo.Between M N B :=
            (hilbert_between_inner_trans
              Geo
              A M N B
              hAMN
              hN.1).1

          have hAMltAN :
              HilbertSegmentLess Geo A M A N :=
            hilbert_segmentLess_of_between
              Geo A M N hAMN

          have hMB_AM :
              Geo.Congruent M B A M :=
            hilbert_congruent_symmetry
              Geo
              A M
              M B
              hM.2

          have hMBltAN :
              HilbertSegmentLess Geo M B A N :=
            hilbert_segmentLess_congruent_left
              Geo
              A M
              M B
              A N
              hAMltAN
              hMB_AM

          have hMBltNB :
              HilbertSegmentLess Geo M B N B :=
            hilbert_segmentLess_congruent_right
              Geo
              M B
              A N
              N B
              hMBltAN
              hN.2

          have hBNM :
              Geo.Between B N M :=
            (HilbertOrder.between_incidence
              M N B hMNB).2.2.2.2

          have hBNltBM :
              HilbertSegmentLess Geo B N B M :=
            hilbert_segmentLess_of_between
              Geo B N M hBNM

          have hNB_BN :
              Geo.Congruent N B B N :=
            (Geo.congruent_reverse_first
              B N
              B N).mp
                (hilbert_congruent_reflexive
                  Geo B N)

          have hNBltBM :
              HilbertSegmentLess Geo N B B M :=
            hilbert_segmentLess_congruent_left
              Geo
              B N
              N B
              B M
              hBNltBM
              hNB_BN

          have hBM_MB :
              Geo.Congruent B M M B :=
            (Geo.congruent_reverse_second
              B M
              B M).mp
                (hilbert_congruent_reflexive
                  Geo B M)

          have hNBltMB :
              HilbertSegmentLess Geo N B M B :=
            hilbert_segmentLess_congruent_right
              Geo
              N B
              B M
              M B
              hNBltBM
              hBM_MB

          exact
            (hilbert_segmentLess_asymm
              Geo
              M B
              N B
              hMBltNB)
              hNBltMB)

    | Or.inr (Or.inl hMAN) =>
        False.elim (by
          have hBMA :
              Geo.Between B M A :=
            (HilbertOrder.between_incidence
              A M B hM.1).2.2.2.2

          have hBAN :
              Geo.Between B A N :=
            (hilbert_between_outer_trans
              Geo
              B M A N
              hBMA
              hMAN).1

          have hBNA :
              Geo.Between B N A :=
            (HilbertOrder.between_incidence
              A N B hN.1).2.2.2.2

          have hBANdata :=
            HilbertOrder.between_incidence
              B A N hBAN

          exact
            ((HilbertOrder.between_unique
              (Geo := Geo)
              B A N
              hBANdata.2.2.2.1
              hBAN).2
              hBNA))

    | Or.inr (Or.inr hANM) =>
        False.elim (by
          have hNMB :
              Geo.Between N M B :=
            (hilbert_between_inner_trans
              Geo
              A N M B
              hANM
              hM.1).1

          have hANltAM :
              HilbertSegmentLess Geo A N A M :=
            hilbert_segmentLess_of_between
              Geo A N M hANM

          have hNB_AN :
              Geo.Congruent N B A N :=
            hilbert_congruent_symmetry
              Geo
              A N
              N B
              hN.2

          have hNBltAM :
              HilbertSegmentLess Geo N B A M :=
            hilbert_segmentLess_congruent_left
              Geo
              A N
              N B
              A M
              hANltAM
              hNB_AN

          have hNBltMB :
              HilbertSegmentLess Geo N B M B :=
            hilbert_segmentLess_congruent_right
              Geo
              N B
              A M
              M B
              hNBltAM
              hM.2

          have hBMN :
              Geo.Between B M N :=
            (HilbertOrder.between_incidence
              N M B hNMB).2.2.2.2

          have hBMltBN :
              HilbertSegmentLess Geo B M B N :=
            hilbert_segmentLess_of_between
              Geo B M N hBMN

          have hMB_BM :
              Geo.Congruent M B B M :=
            (Geo.congruent_reverse_first
              B M
              B M).mp
                (hilbert_congruent_reflexive
                  Geo B M)

          have hMBltBN :
              HilbertSegmentLess Geo M B B N :=
            hilbert_segmentLess_congruent_left
              Geo
              B M
              M B
              B N
              hBMltBN
              hMB_BM

          have hBN_NB :
              Geo.Congruent B N N B :=
            (Geo.congruent_reverse_second
              B N
              B N).mp
                (hilbert_congruent_reflexive
                  Geo B N)

          have hMBltNB :
              HilbertSegmentLess Geo M B N B :=
            hilbert_segmentLess_congruent_right
              Geo
              M B
              B N
              N B
              hMBltBN
              hBN_NB

          exact
            (hilbert_segmentLess_asymm
              Geo
              N B
              M B
              hNBltMB)
              hMBltNB)


/--
First genuine p = 3 carrier-transport step for an equilateral triangle.

Let `MA`, `MB`, `MC` be the midpoints of `BC`, `AC`, `BA`, respectively,
and let `a`, `b`, `c` be the corresponding median reflection axes through
`A`, `B`, `C`.  Reflection in `b` swaps `A` and `C` and fixes `B`.
Therefore it sends the midpoint `MA` of `BC` to the midpoint `MC` of `BA`.
The two-point criterion then sends the whole carrier of `a` onto the carrier
of `c`.

The three congruence hypotheses are deliberately oriented for direct use of
`isosceles_midpoint_axis_swaps_base`; they are the three apex forms of the
equilateral-side condition.
-/
theorem equilateral_median_axis_b_maps_a_to_c
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C MA MB MC : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C)
    (hBABC : Geo.Congruent B A B C)
    (hCBCA : Geo.Congruent C B C A)
    (hMidA : HilbertIsMidpoint Geo MA B C)
    (hMidB : HilbertIsMidpoint Geo MB A C)
    (hMidC : HilbertIsMidpoint Geo MC B A) :
    Exists fun a : ReflectionAxis Geo =>
      Exists fun b : ReflectionAxis Geo =>
        Exists fun c : ReflectionAxis Geo =>
          And
            (HilbertIncidence.OnLine A a.carrier)
            (And
              (HilbertIncidence.OnLine MA a.carrier)
              (And
                (HilbertIncidence.OnLine B b.carrier)
                (And
                  (HilbertIncidence.OnLine MB b.carrier)
                  (And
                    (HilbertIncidence.OnLine C c.carrier)
                    (And
                      (HilbertIncidence.OnLine MC c.carrier)
                      (ReflectionMapsLine
                        Geo b a.carrier c.carrier)))))) := by
  have hBAC :
      Not (Collinear Geo B A C) := by
    intro hBACcol
    exact
      hABC
        (PrimCollinearSwap
          Geo B A C hBACcol)

  have hCBA :
      Not (Collinear Geo C B A) := by
    intro hCBAcol

    have hBACcol :
        Collinear Geo B A C :=
      PrimCollinearCycle
        Geo C B A hCBAcol

    exact
      hABC
        (PrimCollinearSwap
          Geo B A C hBACcol)

  rcases
      isosceles_midpoint_axis_swaps_base
        Geo
        A B C MA
        hABC
        hABAC
        hMidA with
    ⟨a, hAa, hMAa, hFixA, hFixMA, hSwapBCa, hSwapCBa⟩

  rcases
      isosceles_midpoint_axis_swaps_base
        Geo
        B A C MB
        hBAC
        hBABC
        hMidB with
    ⟨b, hBb, hMBb, hFixB, hFixMB, hSwapAC, hSwapCA⟩

  rcases
      isosceles_midpoint_axis_swaps_base
        Geo
        C B A MC
        hCBA
        hCBCA
        hMidC with
    ⟨c, hCc, hMCc, hFixC, hFixMC, hSwapBAc, hSwapABc⟩

  have hAMA : Not (A = MA) := by
    intro hEq
    subst MA

    have hBACcol :
        Collinear Geo B A C :=
      (HilbertOrder.between_incidence
        B A C hMidA.1).2.2.2.1

    exact
      hABC
        (PrimCollinearSwap
          Geo B A C hBACcol)

  have hImageMid :
      HilbertIsMidpoint
        Geo
        (lineReflect Geo b MA)
        (lineReflect Geo b B)
        (lineReflect Geo b C) :=
    lineReflect_preserves_midpoint
      Geo
      b
      MA B C
      hMidA

  have hImageMidBA :
      HilbertIsMidpoint
        Geo
        (lineReflect Geo b MA)
        B A := by
    rw [hFixB, hSwapCA] at hImageMid
    exact hImageMid

  have hImageMA :
      lineReflect Geo b MA = MC :=
    hilbert_midpoint_unique_local
      Geo
      (lineReflect Geo b MA)
      MC
      B A
      hImageMidBA
      hMidC

  have hImageAonC :
      HilbertIncidence.OnLine
        (lineReflect Geo b A)
        c.carrier := by
    rw [hSwapAC]
    exact hCc

  have hImageMAonC :
      HilbertIncidence.OnLine
        (lineReflect Geo b MA)
        c.carrier := by
    rw [hImageMA]
    exact hMCc

  have hMap :
      ReflectionMapsLine
        Geo
        b
        a.carrier
        c.carrier :=
    reflectionMapsLine_of_two_points
      Geo
      b
      a.carrier
      c.carrier
      A MA
      hAa
      hMAa
      hAMA
      hImageAonC
      hImageMAonC

  exact
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      hMap⟩


/--
Step 13 for p = 3: conjugation of the median-axis reflection.

Step 12 established that reflection in the median axis `b` sends the carrier
of the median axis `a` exactly onto the carrier of the median axis `c`.
The general carrier-image conjugation theorem therefore gives, pointwise,

    r_b r_a r_b = r_c.

No braid relation is used here; this is only the direct conjugation
consequence of the carrier transport proved in Step 12.
-/
theorem equilateral_median_reflection_conjugation_bab_eq_c
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C MA MB MC : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C)
    (hBABC : Geo.Congruent B A B C)
    (hCBCA : Geo.Congruent C B C A)
    (hMidA : HilbertIsMidpoint Geo MA B C)
    (hMidB : HilbertIsMidpoint Geo MB A C)
    (hMidC : HilbertIsMidpoint Geo MC B A) :
    Exists fun a : ReflectionAxis Geo =>
      Exists fun b : ReflectionAxis Geo =>
        Exists fun c : ReflectionAxis Geo =>
          And
            (HilbertIncidence.OnLine A a.carrier)
            (And
              (HilbertIncidence.OnLine MA a.carrier)
              (And
                (HilbertIncidence.OnLine B b.carrier)
                (And
                  (HilbertIncidence.OnLine MB b.carrier)
                  (And
                    (HilbertIncidence.OnLine C c.carrier)
                    (And
                      (HilbertIncidence.OnLine MC c.carrier)
                      (forall P : Geo.Point,
                        lineReflect Geo b
                          (lineReflect Geo a
                            (lineReflect Geo b P)) =
                        lineReflect Geo c P)))))) := by
  rcases
      equilateral_median_axis_b_maps_a_to_c
        Geo
        A B C MA MB MC
        hABC
        hABAC
        hBABC
        hCBCA
        hMidA
        hMidB
        hMidC with
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      hMap⟩

  refine
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      ?_⟩

  intro P

  exact
    lineReflect_conjugation_pointwise
      Geo
      b
      a
      c
      hMap
      P


/--
Step 14 for p = 3: the same three median axes support both carrier transports.

For an equilateral triangle with median axes `a`, `b`, `c`,

    r_b(a) = c
    r_a(b) = c.

The first transport is the Step 12 argument.  The second is its geometric
counterpart, proved on the same chosen axes.  This synchronization is the
point of the present theorem: Step 15 can compare the two conjugations
without having to identify separately chosen existential reflection axes.
-/
theorem equilateral_median_axes_two_transports
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C MA MB MC : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C)
    (hBABC : Geo.Congruent B A B C)
    (hCBCA : Geo.Congruent C B C A)
    (hMidA : HilbertIsMidpoint Geo MA B C)
    (hMidB : HilbertIsMidpoint Geo MB A C)
    (hMidC : HilbertIsMidpoint Geo MC B A) :
    Exists fun a : ReflectionAxis Geo =>
      Exists fun b : ReflectionAxis Geo =>
        Exists fun c : ReflectionAxis Geo =>
          And
            (HilbertIncidence.OnLine A a.carrier)
            (And
              (HilbertIncidence.OnLine MA a.carrier)
              (And
                (HilbertIncidence.OnLine B b.carrier)
                (And
                  (HilbertIncidence.OnLine MB b.carrier)
                  (And
                    (HilbertIncidence.OnLine C c.carrier)
                    (And
                      (HilbertIncidence.OnLine MC c.carrier)
                      (And
                        (ReflectionMapsLine
                          Geo b a.carrier c.carrier)
                        (ReflectionMapsLine
                          Geo a b.carrier c.carrier))))))) := by
  have hBAC :
      Not (Collinear Geo B A C) := by
    intro hBACcol
    exact
      hABC
        (PrimCollinearSwap
          Geo B A C hBACcol)

  have hCBA :
      Not (Collinear Geo C B A) := by
    intro hCBAcol

    have hBACcol :
        Collinear Geo B A C :=
      PrimCollinearCycle
        Geo C B A hCBAcol

    exact
      hABC
        (PrimCollinearSwap
          Geo B A C hBACcol)

  rcases
      isosceles_midpoint_axis_swaps_base
        Geo
        A B C MA
        hABC
        hABAC
        hMidA with
    ⟨a, hAa, hMAa, hFixA, hFixMA, hSwapBCa, hSwapCBa⟩

  rcases
      isosceles_midpoint_axis_swaps_base
        Geo
        B A C MB
        hBAC
        hBABC
        hMidB with
    ⟨b, hBb, hMBb, hFixB, hFixMB, hSwapACb, hSwapCAb⟩

  rcases
      isosceles_midpoint_axis_swaps_base
        Geo
        C B A MC
        hCBA
        hCBCA
        hMidC with
    ⟨c, hCc, hMCc, hFixC, hFixMC, hSwapBAc, hSwapABc⟩

  have hAMA : Not (A = MA) := by
    intro hEq
    subst MA

    have hBACcol :
        Collinear Geo B A C :=
      (HilbertOrder.between_incidence
        B A C hMidA.1).2.2.2.1

    exact
      hABC
        (PrimCollinearSwap
          Geo B A C hBACcol)

  have hImageMidA :
      HilbertIsMidpoint
        Geo
        (lineReflect Geo b MA)
        (lineReflect Geo b B)
        (lineReflect Geo b C) :=
    lineReflect_preserves_midpoint
      Geo
      b
      MA B C
      hMidA

  have hImageMidA_BA :
      HilbertIsMidpoint
        Geo
        (lineReflect Geo b MA)
        B A := by
    rw [hFixB, hSwapCAb] at hImageMidA
    exact hImageMidA

  have hImageMA :
      lineReflect Geo b MA = MC :=
    hilbert_midpoint_unique_local
      Geo
      (lineReflect Geo b MA)
      MC
      B A
      hImageMidA_BA
      hMidC

  have hImageAonC :
      HilbertIncidence.OnLine
        (lineReflect Geo b A)
        c.carrier := by
    rw [hSwapACb]
    exact hCc

  have hImageMAonC :
      HilbertIncidence.OnLine
        (lineReflect Geo b MA)
        c.carrier := by
    rw [hImageMA]
    exact hMCc

  have hMapBA :
      ReflectionMapsLine
        Geo
        b
        a.carrier
        c.carrier :=
    reflectionMapsLine_of_two_points
      Geo
      b
      a.carrier
      c.carrier
      A MA
      hAa
      hMAa
      hAMA
      hImageAonC
      hImageMAonC

  have hBMB : Not (B = MB) := by
    intro hEq
    subst MB

    have hABCcol :
        Collinear Geo A B C :=
      (HilbertOrder.between_incidence
        A B C hMidB.1).2.2.2.1

    exact hABC hABCcol

  have hImageMidB :
      HilbertIsMidpoint
        Geo
        (lineReflect Geo a MB)
        (lineReflect Geo a A)
        (lineReflect Geo a C) :=
    lineReflect_preserves_midpoint
      Geo
      a
      MB A C
      hMidB

  have hImageMidB_AB :
      HilbertIsMidpoint
        Geo
        (lineReflect Geo a MB)
        A B := by
    rw [hFixA, hSwapCBa] at hImageMidB
    exact hImageMidB

  have hMidC_AB :
      HilbertIsMidpoint Geo MC A B :=
    MidpointSymmetry
      Geo
      MC B A
      hMidC

  have hImageMB :
      lineReflect Geo a MB = MC :=
    hilbert_midpoint_unique_local
      Geo
      (lineReflect Geo a MB)
      MC
      A B
      hImageMidB_AB
      hMidC_AB

  have hImageBonC :
      HilbertIncidence.OnLine
        (lineReflect Geo a B)
        c.carrier := by
    rw [hSwapBCa]
    exact hCc

  have hImageMBonC :
      HilbertIncidence.OnLine
        (lineReflect Geo a MB)
        c.carrier := by
    rw [hImageMB]
    exact hMCc

  have hMapAB :
      ReflectionMapsLine
        Geo
        a
        b.carrier
        c.carrier :=
    reflectionMapsLine_of_two_points
      Geo
      a
      b.carrier
      c.carrier
      B MB
      hBb
      hMBb
      hBMB
      hImageBonC
      hImageMBonC

  exact
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      hMapBA,
      hMapAB⟩


/--
Step 15 for p = 3: the braid relation for the two median reflections.

Step 14 gives the two carrier transports on the same three axes:

    r_b(a) = c,
    r_a(b) = c.

The general conjugation theorem therefore gives

    r_b r_a r_b = r_c,
    r_a r_b r_a = r_c.

Comparing the two pointwise identities yields the Coxeter braid relation

    r_a r_b r_a = r_b r_a r_b.

This is the first genuine p = 3 relation theorem in the present synthetic
development.  The order-three relation `(r_a r_b)^3 = 1` is not proved here.
-/
theorem equilateral_median_reflections_braid
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C MA MB MC : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C)
    (hBABC : Geo.Congruent B A B C)
    (hCBCA : Geo.Congruent C B C A)
    (hMidA : HilbertIsMidpoint Geo MA B C)
    (hMidB : HilbertIsMidpoint Geo MB A C)
    (hMidC : HilbertIsMidpoint Geo MC B A) :
    Exists fun a : ReflectionAxis Geo =>
      Exists fun b : ReflectionAxis Geo =>
        Exists fun c : ReflectionAxis Geo =>
          And
            (HilbertIncidence.OnLine A a.carrier)
            (And
              (HilbertIncidence.OnLine MA a.carrier)
              (And
                (HilbertIncidence.OnLine B b.carrier)
                (And
                  (HilbertIncidence.OnLine MB b.carrier)
                  (And
                    (HilbertIncidence.OnLine C c.carrier)
                    (And
                      (HilbertIncidence.OnLine MC c.carrier)
                      (forall P : Geo.Point,
                        lineReflect Geo a
                          (lineReflect Geo b
                            (lineReflect Geo a P)) =
                        lineReflect Geo b
                          (lineReflect Geo a
                            (lineReflect Geo b P)))))))) := by
  rcases
      equilateral_median_axes_two_transports
        Geo
        A B C MA MB MC
        hABC
        hABAC
        hBABC
        hCBCA
        hMidA
        hMidB
        hMidC with
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      hMapBA,
      hMapAB⟩

  refine
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      ?_⟩

  intro P

  have hABA :
      lineReflect Geo a
        (lineReflect Geo b
          (lineReflect Geo a P)) =
      lineReflect Geo c P :=
    lineReflect_conjugation_pointwise
      Geo
      a
      b
      c
      hMapAB
      P

  have hBAB :
      lineReflect Geo b
        (lineReflect Geo a
          (lineReflect Geo b P)) =
      lineReflect Geo c P :=
    lineReflect_conjugation_pointwise
      Geo
      b
      a
      c
      hMapBA
      P

  exact hABA.trans hBAB.symm


/--
Step 16 for p = 3: order three of the product of the two median reflections.

Step 15 established the braid relation

    r_a r_b r_a = r_b r_a r_b.

Together with involutivity of each line reflection,

    r_a^2 = 1,
    r_b^2 = 1,

this gives pointwise

    (r_a r_b)^3 = 1.

The proof below is purely algebraic at the reflection-map level; all geometry
needed for p = 3 has already been isolated in Steps 12--15.
-/
theorem equilateral_median_reflections_product_order_three
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C MA MB MC : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C)
    (hBABC : Geo.Congruent B A B C)
    (hCBCA : Geo.Congruent C B C A)
    (hMidA : HilbertIsMidpoint Geo MA B C)
    (hMidB : HilbertIsMidpoint Geo MB A C)
    (hMidC : HilbertIsMidpoint Geo MC B A) :
    Exists fun a : ReflectionAxis Geo =>
      Exists fun b : ReflectionAxis Geo =>
        Exists fun c : ReflectionAxis Geo =>
          And
            (HilbertIncidence.OnLine A a.carrier)
            (And
              (HilbertIncidence.OnLine MA a.carrier)
              (And
                (HilbertIncidence.OnLine B b.carrier)
                (And
                  (HilbertIncidence.OnLine MB b.carrier)
                  (And
                    (HilbertIncidence.OnLine C c.carrier)
                    (And
                      (HilbertIncidence.OnLine MC c.carrier)
                      (forall P : Geo.Point,
                        lineReflect Geo a
                          (lineReflect Geo b
                            (lineReflect Geo a
                              (lineReflect Geo b
                                (lineReflect Geo a
                                  (lineReflect Geo b P))))) =
                        P)))))) := by
  rcases
      equilateral_median_reflections_braid
        Geo
        A B C MA MB MC
        hABC
        hABAC
        hBABC
        hCBCA
        hMidA
        hMidB
        hMidC with
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      hBraid⟩

  refine
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      ?_⟩

  intro P

  calc
    lineReflect Geo a
        (lineReflect Geo b
          (lineReflect Geo a
            (lineReflect Geo b
              (lineReflect Geo a
                (lineReflect Geo b P))))) =
      lineReflect Geo b
        (lineReflect Geo a
          (lineReflect Geo b
            (lineReflect Geo b
              (lineReflect Geo a
                (lineReflect Geo b P))))) := by
          exact
            hBraid
              (lineReflect Geo b
                (lineReflect Geo a
                  (lineReflect Geo b P)))
    _ =
      lineReflect Geo b
        (lineReflect Geo a
          (lineReflect Geo a
            (lineReflect Geo b P))) := by
          rw [
            lineReflect_involutive
              Geo
              b
              (lineReflect Geo a
                (lineReflect Geo b P))
          ]
    _ =
      lineReflect Geo b
        (lineReflect Geo b P) := by
          rw [
            lineReflect_involutive
              Geo
              a
              (lineReflect Geo b P)
          ]
    _ = P := by
      exact lineReflect_involutive Geo b P


/--
Step 20a: package the equilateral-median pointwise order-three theorem as
the pair relation with the public axis order `(a,b)`.

The existing Step 16 pointwise word is naturally the cube of
`reflectionProduct Geo b a`.  Symmetry of `ReflectionPairRelation`
then removes this implementation-order artifact.
-/
theorem equilateral_median_reflections_coxeter_relation_three
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C MA MB MC : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C)
    (hBABC : Geo.Congruent B A B C)
    (hCBCA : Geo.Congruent C B C A)
    (hMidA : HilbertIsMidpoint Geo MA B C)
    (hMidB : HilbertIsMidpoint Geo MB A C)
    (hMidC : HilbertIsMidpoint Geo MC B A) :
    Exists fun a : ReflectionAxis Geo =>
      Exists fun b : ReflectionAxis Geo =>
        Exists fun c : ReflectionAxis Geo =>
          And
            (HilbertIncidence.OnLine A a.carrier)
            (And
              (HilbertIncidence.OnLine MA a.carrier)
              (And
                (HilbertIncidence.OnLine B b.carrier)
                (And
                  (HilbertIncidence.OnLine MB b.carrier)
                  (And
                    (HilbertIncidence.OnLine C c.carrier)
                    (And
                      (HilbertIncidence.OnLine MC c.carrier)
                      (ReflectionPairRelation
                        Geo a b 3)))))) := by

  rcases
      equilateral_median_reflections_product_order_three
        Geo
        A B C MA MB MC
        hABC
        hABAC
        hBABC
        hCBCA
        hMidA
        hMidB
        hMidC with
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      hOrder3⟩

  refine
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      ?_⟩

  have hRelBA :
      ReflectionPairRelation Geo b a 3 := by
    unfold ReflectionPairRelation
    apply Equiv.ext
    intro P
    change
      lineReflect Geo a
        (lineReflect Geo b
          (lineReflect Geo a
            (lineReflect Geo b
              (lineReflect Geo a
                (lineReflect Geo b P))))) =
      P
    exact hOrder3 P

  exact
    reflectionPairRelation_symm
      Geo
      b a
      3
      hRelBA


/--
Step 20b: the two equilateral median reflections have exact period three,
with the public axis order `(a,b)`.

The period-three relation is obtained from Step 16.  Exactness is detected
geometrically at the vertex `B`: reflection in `b` fixes `B`, while
reflection in `a` moves it.  Hence the product is nontrivial.

The intermediate proof naturally yields exact period for `(b,a)`;
`reflectionPairExactPeriod_symm` then gives the public `(a,b)` form.
-/
theorem equilateral_median_reflections_exact_period_three
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C MA MB MC : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hABAC : Geo.Congruent A B A C)
    (hBABC : Geo.Congruent B A B C)
    (hCBCA : Geo.Congruent C B C A)
    (hMidA : HilbertIsMidpoint Geo MA B C)
    (hMidB : HilbertIsMidpoint Geo MB A C)
    (hMidC : HilbertIsMidpoint Geo MC B A) :
    Exists fun a : ReflectionAxis Geo =>
      Exists fun b : ReflectionAxis Geo =>
        Exists fun c : ReflectionAxis Geo =>
          And
            (HilbertIncidence.OnLine A a.carrier)
            (And
              (HilbertIncidence.OnLine MA a.carrier)
              (And
                (HilbertIncidence.OnLine B b.carrier)
                (And
                  (HilbertIncidence.OnLine MB b.carrier)
                  (And
                    (HilbertIncidence.OnLine C c.carrier)
                    (And
                      (HilbertIncidence.OnLine MC c.carrier)
                      (ReflectionPairExactPeriod
                        Geo a b 3)))))) := by

  rcases
      equilateral_median_reflections_product_order_three
        Geo
        A B C MA MB MC
        hABC
        hABAC
        hBABC
        hCBCA
        hMidA
        hMidB
        hMidC with
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      hOrder3⟩

  refine
    ⟨a, b, c,
      hAa,
      hMAa,
      hBb,
      hMBb,
      hCc,
      hMCc,
      ?_⟩

  ----------------------------------------------------------------------
  -- B is off axis a.
  ----------------------------------------------------------------------

  have hBM :
      Not (B = MA) :=
    (HilbertOrder.between_incidence
      B MA C hMidA.1).1

  have hBMAC :
      Collinear Geo B MA C :=
    (HilbertOrder.between_incidence
      B MA C hMidA.1).2.2.2.1

  have hBoffA :
      Not (HilbertIncidence.OnLine B a.carrier) := by
    intro hBa

    have hCa :
        HilbertIncidence.OnLine C a.carrier :=
      hilbert_collinear_on_line
        Geo
        B MA C
        a.carrier
        hBM
        hBa
        hMAa
        hBMAC

    exact
      hABC
        ⟨a.carrier,
          hAa,
          hBa,
          hCa⟩

  ----------------------------------------------------------------------
  -- b fixes B; a moves B.
  ----------------------------------------------------------------------

  have hFixB :
      lineReflect Geo b B = B := by
    have hFixedRel :
        IsLineReflection Geo b B B :=
      (line_reflection_fixed_iff_on_axis
        Geo b B).2 hBb

    exact
      line_reflection_unique
        Geo
        b
        B
        (lineReflect Geo b B)
        B
        (lineReflect_spec Geo b B)
        hFixedRel

  have hMoveA :
      Not (lineReflect Geo a B = B) :=
    line_reflection_moves_off_axis
      Geo
      a
      B
      (lineReflect Geo a B)
      hBoffA
      (lineReflect_spec Geo a B)

  have hProductMovesB :
      Not (reflectionProduct Geo b a B = B) := by
    simp only [reflectionProduct_apply, hFixB]
    exact hMoveA

  ----------------------------------------------------------------------
  -- Period three for the implementation-order pair (b,a).
  ----------------------------------------------------------------------

  have hPow3 :
      reflectionProductPow Geo b a 3 =
        Equiv.refl Geo.Point := by
    apply Equiv.ext
    intro P
    change
      lineReflect Geo a
        (lineReflect Geo b
          (lineReflect Geo a
            (lineReflect Geo b
              (lineReflect Geo a
                (lineReflect Geo b P))))) =
      P
    exact hOrder3 P

  have hRel3 :
      ReflectionPairRelation Geo b a 3 := by
    unfold ReflectionPairRelation
    exact hPow3

  ----------------------------------------------------------------------
  -- Exactness for (b,a).
  ----------------------------------------------------------------------

  have hExactBA :
      ReflectionPairExactPeriod Geo b a 3 := by

    refine
      ⟨by decide,
        hRel3,
        ?_⟩

    intro q hqPos hqLt

    have hqCases :
        q = 1 \/ q = 2 := by
      omega

    rcases hqCases with hq1 | hq2

    · subst q
      intro hRel1

      have hRel1Eq := hRel1
      unfold ReflectionPairRelation at hRel1Eq
      rw [reflectionProductPow_one] at hRel1Eq

      have hAtB :=
        congrArg
          (fun f : Equiv Geo.Point Geo.Point => f B)
          hRel1Eq

      apply hProductMovesB
      simpa using hAtB

    · subst q
      intro hRel2

      have hRel2Eq := hRel2
      unfold ReflectionPairRelation at hRel2Eq

      have hPow3EqProduct :
          reflectionProductPow Geo b a 3 =
            reflectionProduct Geo b a := by
        rw [show (3 : Nat) = Nat.succ 2 by rfl]
        rw [reflectionProductPow_succ]
        rw [hRel2Eq]

        apply Equiv.ext
        intro P
        rfl

      have hProductEqId :
          reflectionProduct Geo b a =
            Equiv.refl Geo.Point :=
        hPow3EqProduct.symm.trans hPow3

      have hAtB :=
        congrArg
          (fun f : Equiv Geo.Point Geo.Point => f B)
          hProductEqId

      apply hProductMovesB
      simpa using hAtB

  ----------------------------------------------------------------------
  -- Remove the implementation-order artifact.
  ----------------------------------------------------------------------

  exact
    reflectionPairExactPeriod_symm
      Geo
      b a
      3
      hExactBA


/--
Step 21a: restore the public p = 2 Coxeter-relation wrapper.

The permutation-level square theorem already proves the whole content.
This theorem only packages it as `ReflectionPairRelation`.
-/
theorem perpendicular_axes_coxeter_relation_two
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2) :
    ReflectionPairRelation
      Geo
      axis1 axis2
      2 := by

  unfold ReflectionPairRelation

  exact
    perpendicular_axes_reflectionProductPow_two
      Geo
      axis1 axis2
      hAxes


/--
Step 21b: perpendicular reflection axes give exact period two.

The relation `(r2 r1)^2 = 1` is already known.  Exactness only requires
excluding exponent one.

Use the distinguished point `U` on `axis1`.  Reflection in `axis1`
fixes `U`, while perpendicularity implies that `U` is off `axis2`,
so reflection in `axis2` moves it.  Therefore the product
`r_axis2 r_axis1` is not the identity.
-/
theorem perpendicular_axes_reflections_exact_period_two
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis1 axis2 : ReflectionAxis Geo)
    (hAxes :
      ReflectionAxesPerpendicular Geo axis1 axis2) :
    ReflectionPairExactPeriod
      Geo
      axis1 axis2
      2 := by

  have hRel2 :
      ReflectionPairRelation Geo axis1 axis2 2 :=
    perpendicular_axes_coxeter_relation_two
      Geo
      axis1 axis2
      hAxes

  ----------------------------------------------------------------------
  -- U lies on axis1 but not on axis2.
  ----------------------------------------------------------------------

  have hUoff2 :
      Not
        (HilbertIncidence.OnLine
          hAxes.U
          axis2.carrier) := by

    apply
      perpendicular_axes_second_off_first
        Geo
        axis2 axis1
        (reflectionAxesPerpendicular_symm
          Geo
          axis1 axis2
          hAxes)
        hAxes.U
        hAxes.hU1

    change Not (hAxes.O = hAxes.U)
    exact hAxes.hOU

  ----------------------------------------------------------------------
  -- axis1 fixes U; axis2 moves U.
  ----------------------------------------------------------------------

  have hFixU :
      lineReflect Geo axis1 hAxes.U =
        hAxes.U := by

    have hFixedRel :
        IsLineReflection
          Geo
          axis1
          hAxes.U
          hAxes.U :=
      (line_reflection_fixed_iff_on_axis
        Geo axis1 hAxes.U).2 hAxes.hU1

    exact
      line_reflection_unique
        Geo
        axis1
        hAxes.U
        (lineReflect Geo axis1 hAxes.U)
        hAxes.U
        (lineReflect_spec
          Geo axis1 hAxes.U)
        hFixedRel

  have hMove2 :
      Not
        (lineReflect Geo axis2 hAxes.U =
          hAxes.U) :=
    line_reflection_moves_off_axis
      Geo
      axis2
      hAxes.U
      (lineReflect Geo axis2 hAxes.U)
      hUoff2
      (lineReflect_spec
        Geo axis2 hAxes.U)

  have hProductMovesU :
      Not
        (reflectionProduct
          Geo axis1 axis2 hAxes.U =
          hAxes.U) := by

    simp only [
      reflectionProduct_apply,
      hFixU
    ]

    exact hMove2

  ----------------------------------------------------------------------
  -- Exactness: the only positive q < 2 is q = 1.
  ----------------------------------------------------------------------

  refine
    ⟨by decide,
      hRel2,
      ?_⟩

  intro q hqPos hqLt

  have hq :
      q = 1 := by
    omega

  subst q
  intro hRel1

  have hRel1Eq := hRel1
  unfold ReflectionPairRelation at hRel1Eq
  rw [reflectionProductPow_one] at hRel1Eq

  have hAtU :=
    congrArg
      (fun f : Equiv Geo.Point Geo.Point =>
        f hAxes.U)
      hRel1Eq

  apply hProductMovesU
  simpa using hAtU

end Geometry

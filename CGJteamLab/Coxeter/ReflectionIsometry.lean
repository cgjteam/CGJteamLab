import CGJteamLab.Coxeter.Reflection

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
A point on the perpendicular through the midpoint of AB is
equidistant from A and B.

This is the elementary SAS core of the perpendicular-bisector theorem.
-/
theorem coxeter_perpendicular_bisector_point_equidistant
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A M B X : Geo.Point)
    (hAMB : Geo.Between A M B)
    (hAM_MB : Geo.Congruent A M M B)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X) :
    Geo.Congruent A X B X := by

  ----------------------------------------------------------------------
  -- Triangle MAX is nondegenerate.
  ----------------------------------------------------------------------

  have hMAX :
      Not (PrimCollinear Geo M A X) := by
    intro h
    exact
      hAMX
        (PrimCollinearSwap
          Geo M A X h)

  ----------------------------------------------------------------------
  -- Triangle MBX is nondegenerate.
  ----------------------------------------------------------------------

  have hMB :
      M ≠ B :=
    (HilbertOrder.between_incidence
      A M B hAMB).2.1

  have hAMBcol :
      PrimCollinear Geo A M B :=
    (HilbertOrder.between_incidence
      A M B hAMB).2.2.2.1

  have hMBX :
      Not (PrimCollinear Geo M B X) := by
    intro h

    have hAMXcol :
        PrimCollinear Geo A M X :=
      hilbert_primCollinear_trans
        Geo
        A M B X
        hMB
        hAMBcol
        h

    exact hAMX hAMXcol

  ----------------------------------------------------------------------
  -- MA ~= MB.
  ----------------------------------------------------------------------

  have hMA_MB :
      Geo.Congruent M A M B :=
    (Geometry.Geo.congruent_reverse_first
      Geo
      A M
      M B).mp hAM_MB

  ----------------------------------------------------------------------
  -- Since A-M-B, the right angle AMX is congruent to BMX.
  ----------------------------------------------------------------------

  have hAMX_XMB :
      Geo.AngleCongruent A M X X M B :=
    hilbert_right_angle_opposite_extension
      Geo
      A M X B
      hAMX
      hRight
      hAMB

  have hAMX_BMX :
      Geo.AngleCongruent A M X B M X :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A M X
      X M B).mp hAMX_XMB

  ----------------------------------------------------------------------
  -- MX is common.
  ----------------------------------------------------------------------

  have hMX_MX :
      Geo.Congruent M X M X :=
    hilbert_congruent_reflexive
      Geo M X

  ----------------------------------------------------------------------
  -- SAS for triangles MAX and MBX.
  ----------------------------------------------------------------------

  have hTriangles :
      TriangleCongruenceResult
        Geo
        M A X
        M B X :=
    SAS
      Geo
      M A X
      M B X
      hMAX
      hMBX
      hMA_MB
      hAMX_BMX
      hMX_MX

  exact hTriangles.sideBC

/--
Swapping the two arms of a right angle preserves rightness.
-/
theorem coxeter_right_angle_swap
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo B O A := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hRefl :
      Geo.AngleCongruent A O B A O B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A O B
      hAOB

  have hAngle :
      Geo.AngleCongruent A O B B O A :=
    (Geo.angle_congruent_reverse_second
      A O B
      A O B).mp hRefl

  exact
    hilbert_right_angle_transport
      Geo
      A O B
      B O A
      hAOB
      hBOA
      hRight
      hAngle


/--
A right angle remains right when its second arm is replaced by any
nonvertex point on the same carrier.
-/
theorem coxeter_right_angle_collinear_second
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B B' : Geo.Point)
    (hOB : Not (O = B))
    (hOB' : Not (O = B'))
    (hCol : PrimCollinear Geo O B B')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo A O B' := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hRightBOA :
      HilbertRightAngle Geo B O A :=
    coxeter_right_angle_swap
      Geo
      A O B
      hAOB
      hRight

  have hRightB'OA :
      HilbertRightAngle Geo B' O A :=
    coxeter_right_angle_collinear_first
      Geo
      B B' O A
      hOB
      hOB'
      hCol
      hBOA
      hRightBOA

  have hB'OA :
      Not (PrimCollinear Geo B' O A) := by
    intro h

    have hOB'A :
        PrimCollinear Geo O B' A :=
      PrimCollinearSwap
        Geo B' O A h

    have hBOB' :
        PrimCollinear Geo B O B' :=
      PrimCollinearSwap
        Geo O B B' hCol

    have hBOAcol :
        PrimCollinear Geo B O A :=
      hilbert_primCollinear_trans
        Geo
        B O B' A
        hOB'
        hBOB'
        hOB'A

    exact hBOA hBOAcol

  exact
    coxeter_right_angle_swap
      Geo
      B' O A
      hB'OA
      hRightB'OA


/--
Every nonvertex point on the perpendicular through the midpoint of AB
is equidistant from A and B.
-/
theorem coxeter_perpendicular_bisector_collinear_equidistant
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A M B X P : Geo.Point)
    (hAMB : Geo.Between A M B)
    (hAM_MB : Geo.Congruent A M M B)
    (hMX : Not (M = X))
    (hMP : Not (M = P))
    (hMXP : PrimCollinear Geo M X P)
    (hAMX : Not (PrimCollinear Geo A M X))
    (hRight : HilbertRightAngle Geo A M X) :
    Geo.Congruent A P B P := by

  have hRightP :
      HilbertRightAngle Geo A M P :=
    coxeter_right_angle_collinear_second
      Geo
      A M X P
      hMX
      hMP
      hMXP
      hAMX
      hRight

  have hAMP :
      Not (PrimCollinear Geo A M P) := by
    intro hAMPcol

    have hMPX :
        PrimCollinear Geo M P X :=
      PrimCollinearRotate
        Geo M X P hMXP

    have hAMXcol :
        PrimCollinear Geo A M X :=
      hilbert_primCollinear_trans
        Geo
        A M P X
        hMP
        hAMPcol
        hMPX

    exact hAMX hAMXcol

  exact
    coxeter_perpendicular_bisector_point_equidistant
      Geo
      A M B P
      hAMB
      hAM_MB
      hAMP
      hRightP

/--
Every point of the reflection axis is equidistant from a point and
its reflected image.
-/
theorem line_reflection_axis_point_equidistant
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P P' Q : Geo.Point)
    (hQaxis : HilbertIncidence.OnLine Q axis.carrier)
    (hRef : IsLineReflection Geo axis P P') :
    Geo.Congruent Q P Q P' := by

  rcases hRef with hFixed | hOff

  ----------------------------------------------------------------------
  -- P lies on the axis, hence P' = P.
  ----------------------------------------------------------------------

  · rcases hFixed with ⟨_hPaxis, hEq⟩
    subst P'

    exact
      hilbert_congruent_reflexive
        Geo Q P

  ----------------------------------------------------------------------
  -- P is off the axis.
  ----------------------------------------------------------------------

  · rcases hOff with
      ⟨hPoff, H, hPerp, hMid⟩

    rcases hPerp with
      ⟨hHaxis, _hPoffPerp,
        R, hRaxis, hRH, hRightRHP⟩

    --------------------------------------------------------------------
    -- If Q is the midpoint H, the result is already in hMid.
    --------------------------------------------------------------------

    by_cases hQH : Q = H

    · subst Q

      exact
        (Geometry.Geo.congruent_reverse_first
          Geo
          P H
          H P').mp hMid.2

    --------------------------------------------------------------------
    -- Otherwise H, R, Q are three points of the axis.
    --------------------------------------------------------------------

    · have hHQ :
          H ≠ Q :=
        Ne.symm hQH

      have hHR :
          H ≠ R :=
        Ne.symm hRH

      have hHRQ :
          PrimCollinear Geo H R Q :=
        ⟨axis.carrier,
          hHaxis,
          hRaxis,
          hQaxis⟩

      ------------------------------------------------------------------
      -- RHP is noncollinear because P is off the axis.
      ------------------------------------------------------------------

      have hRHP :
          Not (PrimCollinear Geo R H P) :=
        hilbert_not_collinear_of_off_line
          Geo
          R H P
          axis.carrier
          hRH
          hRaxis
          hHaxis
          hPoff

      ------------------------------------------------------------------
      -- Swap the arms: PHR is also a right angle.
      ------------------------------------------------------------------

      have hRightPHR :
          HilbertRightAngle Geo P H R :=
        coxeter_right_angle_swap
          Geo
          R H P
          hRHP
          hRightRHP

      have hPHR :
          Not (PrimCollinear Geo P H R) := by
        intro h

        exact
          hRHP
            (PrimCollinearSymm
              Geo P H R h)

      ------------------------------------------------------------------
      -- Q lies on the perpendicular bisector of PP'.
      ------------------------------------------------------------------

      have hPQ_P'Q :
          Geo.Congruent P Q P' Q :=
        coxeter_perpendicular_bisector_collinear_equidistant
          Geo
          P H P'
          R Q
          hMid.1
          hMid.2
          hHR
          hHQ
          hHRQ
          hPHR
          hRightPHR

      have hQP_P'Q :
          Geo.Congruent Q P P' Q :=
        (Geometry.Geo.congruent_reverse_first
          Geo
          P Q
          P' Q).mp hPQ_P'Q

      exact
        (Geometry.Geo.congruent_reverse_second
          Geo
          Q P
          P' Q).mp hQP_P'Q

/--
Every point of the reflection axis is equidistant from a point and
its canonical reflected image.
-/
theorem lineReflect_axis_point_equidistant
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q : Geo.Point)
    (hQaxis : HilbertIncidence.OnLine Q axis.carrier) :
    Geo.Congruent
      Q P
      Q (lineReflect Geo axis P) := by

  exact
    line_reflection_axis_point_equidistant
      Geo
      axis
      P
      (lineReflect Geo axis P)
      Q
      hQaxis
      (lineReflect_spec Geo axis P)


/--
A point off the reflection axis and its reflected image lie on
opposite sides of the axis.
-/
theorem line_reflection_oppositeSide
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P P' : Geo.Point)
    (hPoff : Not (HilbertIncidence.OnLine P axis.carrier))
    (hRef : IsLineReflection Geo axis P P') :
    HilbertOppositeSide Geo P P' axis.carrier := by

  rcases hRef with hFixed | hOff

  ----------------------------------------------------------------------
  -- The fixed branch contradicts P being off the axis.
  ----------------------------------------------------------------------

  · exact
      False.elim
        (hPoff hFixed.1)

  ----------------------------------------------------------------------
  -- Off-axis reflection: P-H-P', with H on the axis.
  ----------------------------------------------------------------------

  · rcases hOff with
      ⟨_hPoffRef, H, hPerp, hMid⟩

    rcases hPerp with
      ⟨hHaxis, _hPoffPerp,
        R, _hRaxis, _hRH, _hRight⟩

    have hPHP' :=
      HilbertOrder.between_incidence
        P H P' hMid.1

    have hHP' :
        H ≠ P' :=
      hPHP'.2.1

    have hPHP'col :
        PrimCollinear Geo P H P' :=
      hPHP'.2.2.2.1

    --------------------------------------------------------------------
    -- P' cannot lie on the axis.
    --------------------------------------------------------------------

    have hP'off :
        Not (HilbertIncidence.OnLine P' axis.carrier) := by

      intro hP'axis

      have hHP'P :
          PrimCollinear Geo H P' P :=
        PrimCollinearCycle
          Geo P H P' hPHP'col

      have hPaxis :
          HilbertIncidence.OnLine P axis.carrier :=
        hilbert_collinear_on_line
          Geo
          H P' P
          axis.carrier
          hHP'
          hHaxis
          hP'axis
          hHP'P

      exact hPoff hPaxis

    --------------------------------------------------------------------
    -- The segment PP' meets the axis at H.
    --------------------------------------------------------------------

    exact
      ⟨hPoff,
        hP'off,
        ⟨H,
          hMid.1,
          hHaxis⟩⟩


/--
The canonical reflected image of an off-axis point lies on the
opposite side of the reflection axis.
-/
theorem lineReflect_oppositeSide
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier)) :
    HilbertOppositeSide
      Geo
      P
      (lineReflect Geo axis P)
      axis.carrier := by

  exact
    line_reflection_oppositeSide
      Geo
      axis
      P
      (lineReflect Geo axis P)
      hPoff
      (lineReflect_spec Geo axis P)


/--
For a point off the reflection axis, the two rays from `axis.A`
to the point and to its reflected image make congruent angles
with the axis ray `axis.A axis.B`.
-/
theorem lineReflect_axis_angle_symmetry
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier)) :
    Geo.AngleCongruent
      axis.B axis.A P
      axis.B axis.A (lineReflect Geo axis P) := by

  have hABP :
      Not (Collinear Geo axis.A axis.B P) :=
    hilbert_not_collinear_of_off_line
      Geo
      axis.A axis.B P
      axis.carrier
      axis.hAB
      axis.hA
      axis.hB
      hPoff

  have hAB_AB :
      Geo.Congruent
        axis.A axis.B
        axis.A axis.B :=
    hilbert_congruent_reflexive
      Geo axis.A axis.B

  have hBP_BP' :
      Geo.Congruent
        axis.B P
        axis.B (lineReflect Geo axis P) :=
    lineReflect_axis_point_equidistant
      Geo
      axis
      P
      axis.B
      axis.hB

  have hAP_AP' :
      Geo.Congruent
        axis.A P
        axis.A (lineReflect Geo axis P) :=
    lineReflect_axis_point_equidistant
      Geo
      axis
      P
      axis.A
      axis.hA

  have hSSS :=
    HilbertSSS
      Geo
      axis.A axis.B P
      axis.A axis.B (lineReflect Geo axis P)
      hABP
      hAB_AB
      hBP_BP'
      hAP_AP'

  exact hSSS.2.angleA

/--
For a point off the reflection axis, the canonical reflected point
comes with a perpendicular foot on the axis which is the midpoint
of the point and its image.
-/
theorem lineReflect_off_axis_data
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier)) :
    ∃ H : Geo.Point,
      PerpendicularToAxis Geo axis H P ∧
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P) := by

  rcases lineReflect_spec Geo axis P with hFixed | hOff

  · exact
      False.elim
        (hPoff hFixed.1)

  · rcases hOff with
      ⟨_hPoff, H, hPerp, hMid⟩

    exact
      ⟨H, hPerp, hMid⟩

/--
Reflection preserves the angle made with the axis at any chosen
axis point.
-/
theorem lineReflect_axis_angle_symmetry_at
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (O R P : Geo.Point)
    (hOR : O ≠ R)
    (hOaxis : HilbertIncidence.OnLine O axis.carrier)
    (hRaxis : HilbertIncidence.OnLine R axis.carrier)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier)) :
    Geo.AngleCongruent
      R O P
      R O (lineReflect Geo axis P) := by

  have hORP :
      Not (Collinear Geo O R P) :=
    hilbert_not_collinear_of_off_line
      Geo
      O R P
      axis.carrier
      hOR
      hOaxis
      hRaxis
      hPoff

  have hOR_OR :
      Geo.Congruent O R O R :=
    hilbert_congruent_reflexive
      Geo O R

  have hRP_RP' :
      Geo.Congruent
        R P
        R (lineReflect Geo axis P) :=
    lineReflect_axis_point_equidistant
      Geo
      axis
      P
      R
      hRaxis

  have hOP_OP' :
      Geo.Congruent
        O P
        O (lineReflect Geo axis P) :=
    lineReflect_axis_point_equidistant
      Geo
      axis
      P
      O
      hOaxis

  have hSSS :=
    HilbertSSS
      Geo
      O R P
      O R (lineReflect Geo axis P)
      hORP
      hOR_OR
      hRP_RP'
      hOP_OP'

  exact hSSS.2.angleA

/--
The reflected image of an off-axis point is again off the axis.
-/
theorem lineReflect_off_axis
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier)) :
    Not
      (HilbertIncidence.OnLine
        (lineReflect Geo axis P)
        axis.carrier) := by

  have hOpp :
      HilbertOppositeSide
        Geo
        P
        (lineReflect Geo axis P)
        axis.carrier :=
    lineReflect_oppositeSide
      Geo
      axis
      P
      hPoff

  exact hOpp.2.1

/--
At the midpoint foot of an off-axis reflection, both the original
point and its reflected image determine right angles with the axis.
-/
theorem lineReflect_foot_right_angles
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (Q K R : Geo.Point)
    (hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier))
    (hPerp :
      PerpendicularToAxis Geo axis K Q)
    (hMid :
      HilbertIsMidpoint
        Geo K Q (lineReflect Geo axis Q))
    (hRaxis :
      HilbertIncidence.OnLine R axis.carrier)
    (hKR : K ≠ R) :
    HilbertRightAngle Geo R K Q ∧
    HilbertRightAngle
      Geo R K (lineReflect Geo axis Q) := by

  rcases hPerp with
    ⟨hKaxis, _hQoffPerp,
      S, hSaxis, hSK, hRightSKQ⟩

  have hKS :
      K ≠ S :=
    Ne.symm hSK

  have hKSR :
      PrimCollinear Geo K S R :=
    ⟨axis.carrier,
      hKaxis,
      hSaxis,
      hRaxis⟩

  have hSKQ :
      Not (PrimCollinear Geo S K Q) :=
    hilbert_not_collinear_of_off_line
      Geo
      S K Q
      axis.carrier
      hSK
      hSaxis
      hKaxis
      hQoff

  have hRightRKQ :
      HilbertRightAngle Geo R K Q :=
    coxeter_right_angle_collinear_first
      Geo
      S R K Q
      hKS
      hKR
      hKSR
      hSKQ
      hRightSKQ

  have hQKQ' :=
    HilbertOrder.between_incidence
      Q K (lineReflect Geo axis Q)
      hMid.1

  have hKQ :
      K ≠ Q :=
    Ne.symm hQKQ'.1

  have hKQ' :
      K ≠ lineReflect Geo axis Q :=
    hQKQ'.2.1

  have hKQQ' :
      PrimCollinear
        Geo
        K Q
        (lineReflect Geo axis Q) :=
    PrimCollinearSwap
      Geo
      Q K (lineReflect Geo axis Q)
      hQKQ'.2.2.2.1

  have hRKQ :
      Not (PrimCollinear Geo R K Q) :=
    hilbert_not_collinear_of_off_line
      Geo
      R K Q
      axis.carrier
      (Ne.symm hKR)
      hRaxis
      hKaxis
      hQoff

  have hRightRKQ' :
      HilbertRightAngle
        Geo R K (lineReflect Geo axis Q) :=
    coxeter_right_angle_collinear_second
      Geo
      R K
      Q
      (lineReflect Geo axis Q)
      hKQ
      hKQ'
      hKQQ'
      hRKQ
      hRightRKQ

  exact
    ⟨hRightRKQ, hRightRKQ'⟩

/--
For two distinct reflection feet H and K, the axis ray KH gives
the common reference arm for the reflected point P, while Q and
its image determine right angles with the same axis ray.
-/
theorem lineReflect_distinct_feet_angle_data
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H K : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier))
    (hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier))
    (hHK : Not (H = K))
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hPerpQ :
      PerpendicularToAxis Geo axis K Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo K Q (lineReflect Geo axis Q)) :
    Geo.AngleCongruent
        H K P
        H K (lineReflect Geo axis P) /\
    HilbertRightAngle Geo H K Q /\
    HilbertRightAngle
      Geo H K (lineReflect Geo axis Q) := by

  have hHaxis :
      HilbertIncidence.OnLine H axis.carrier :=
    hPerpP.1

  have hKaxis :
      HilbertIncidence.OnLine K axis.carrier :=
    hPerpQ.1

  have hKH :
      Not (K = H) :=
    Ne.symm hHK

  have hAngleP :
      Geo.AngleCongruent
        H K P
        H K (lineReflect Geo axis P) :=
    lineReflect_axis_angle_symmetry_at
      Geo
      axis
      K H P
      hKH
      hKaxis
      hHaxis
      hPoff

  have hRightQ :=
    lineReflect_foot_right_angles
      Geo
      axis
      Q K H
      hQoff
      hPerpQ
      hMidQ
      hHaxis
      hKH

  exact
    ⟨hAngleP,
      hRightQ.1,
      hRightQ.2⟩

theorem coxeter_opposite_opposite_sameSide_nondegenerate
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C : Geo.Point)
    (l : Geo.Line)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hAB :
      HilbertOppositeSide Geo A B l)
    (hBC :
      HilbertOppositeSide Geo B C l) :
    HilbertSameSide Geo A C l := by

  rcases hAB.2.2 with
    ⟨X, hAXB, hXl⟩

  rcases hBC.2.2 with
    ⟨Y, hBYC, hYl⟩

  have hBXA :
      Geo.Between B X A :=
    (HilbertOrder.between_incidence
      A X B hAXB).2.2.2.2

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap
          Geo B A C h)

  exact
    hilbert_third_side_endpoints_sameSide
      Geo
      B A C
      X Y
      l
      hBAC
      hBXA
      hBYC
      hXl
      hYl

/--
Distinct perpendicular feet force the original point, its reflected
image, and the second point to be noncollinear.
-/
theorem lineReflect_distinct_feet_noncollinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H K : Geo.Point)
    (hHK : Not (H = K))
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis K Q) :
    Not
      (PrimCollinear
        Geo
        P
        (lineReflect Geo axis P)
        Q) := by

  intro hCol

  rcases hPerpP with
    ⟨hHaxis, hPoff,
      R, hRaxis, hRH, hRightRHP⟩

  have hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier) :=
    hPerpQ.2.1

  have hMidData :=
    HilbertOrder.between_incidence
      P H (lineReflect Geo axis P)
      hMidP.1

  have hHP :
      Not (H = P) :=
    Ne.symm hMidData.1

  have hPP' :
      Not (P = lineReflect Geo axis P) :=
    hMidData.2.2.1

  have hPHP' :
      PrimCollinear
        Geo
        P H (lineReflect Geo axis P) :=
    hMidData.2.2.2.1

  have hHPP' :
      PrimCollinear
        Geo
        H P (lineReflect Geo axis P) :=
    PrimCollinearSwap
      Geo
      P H (lineReflect Geo axis P)
      hPHP'

  have hHPQ :
      PrimCollinear Geo H P Q :=
    hilbert_primCollinear_trans
      Geo
      H P (lineReflect Geo axis P) Q
      hPP'
      hHPP'
      hCol

  have hHQ :
      Not (H = Q) := by
    intro h
    subst Q
    exact hQoff hHaxis

  have hRHP :
      Not (PrimCollinear Geo R H P) :=
    hilbert_not_collinear_of_off_line
      Geo
      R H P
      axis.carrier
      hRH
      hRaxis
      hHaxis
      hPoff

  have hRightRHQ :
      HilbertRightAngle Geo R H Q :=
    coxeter_right_angle_collinear_second
      Geo
      R H
      P Q
      hHP
      hHQ
      hHPQ
      hRHP
      hRightRHP

  have hPerpHQ :
      PerpendicularToAxis Geo axis H Q :=
    ⟨hHaxis,
      hQoff,
      ⟨R,
        hRaxis,
        hRH,
        hRightRHQ⟩⟩

  have hEq :
      H = K :=
    perpendicular_foot_unique
      Geo
      axis
      Q H K
      hPerpHQ
      hPerpQ

  exact hHK hEq

/--
The perpendicular foot of an off-axis point is also the perpendicular
foot of its reflected image.
-/
theorem lineReflect_reflected_perpendicular
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P H : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier))
    (hPerp :
      PerpendicularToAxis Geo axis H P)
    (hMid :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P)) :
    PerpendicularToAxis
      Geo axis H (lineReflect Geo axis P) := by

  rcases hPerp with
    ⟨hHaxis, _hPoffPerp,
      R, hRaxis, hRH, hRightRHP⟩

  have hP'off :
      Not
        (HilbertIncidence.OnLine
          (lineReflect Geo axis P)
          axis.carrier) :=
    lineReflect_off_axis
      Geo axis P hPoff

  have hMidData :=
    HilbertOrder.between_incidence
      P H (lineReflect Geo axis P)
      hMid.1

  have hHP :
      Not (H = P) :=
    Ne.symm hMidData.1

  have hHP' :
      Not (H = lineReflect Geo axis P) :=
    hMidData.2.1

  have hHP'col :
      PrimCollinear
        Geo
        H P (lineReflect Geo axis P) :=
    PrimCollinearSwap
      Geo
      P H (lineReflect Geo axis P)
      hMidData.2.2.2.1

  have hRHP :
      Not (PrimCollinear Geo R H P) :=
    hilbert_not_collinear_of_off_line
      Geo
      R H P
      axis.carrier
      hRH
      hRaxis
      hHaxis
      hPoff

  have hRightRHP' :
      HilbertRightAngle
        Geo R H (lineReflect Geo axis P) :=
    coxeter_right_angle_collinear_second
      Geo
      R H
      P
      (lineReflect Geo axis P)
      hHP
      hHP'
      hHP'col
      hRHP
      hRightRHP

  exact
    ⟨hHaxis,
      hP'off,
      ⟨R,
        hRaxis,
        hRH,
        hRightRHP'⟩⟩

/--
For two off-axis points with distinct perpendicular feet, reflection
preserves the same-side relation with respect to the reflection axis.
-/
theorem lineReflect_sameSide_of_distinct_feet
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H K : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier))
    (hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier))
    (hHK :
      Not (H = K))
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis K Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo K Q (lineReflect Geo axis Q))
    (hSamePQ :
      HilbertSameSide Geo P Q axis.carrier) :
    HilbertSameSide
      Geo
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q)
      axis.carrier := by

  ----------------------------------------------------------------------
  -- P' and P are on opposite sides of the axis.
  ----------------------------------------------------------------------

  have hOppPP' :
      HilbertOppositeSide
        Geo
        P
        (lineReflect Geo axis P)
        axis.carrier :=
    lineReflect_oppositeSide
      Geo axis P hPoff

  have hOppP'P :
      HilbertOppositeSide
        Geo
        (lineReflect Geo axis P)
        P
        axis.carrier :=
    hilbert_oppositeSide_symm
      Geo
      P
      (lineReflect Geo axis P)
      axis.carrier
      hOppPP'

  ----------------------------------------------------------------------
  -- Since P and Q are on the same side, transporting across that
  -- same-side step gives P' opposite Q.
  ----------------------------------------------------------------------

  have hOppP'Q :
      HilbertOppositeSide
        Geo
        (lineReflect Geo axis P)
        Q
        axis.carrier :=
    hilbert_oppositeSide_transport_right
      Geo
      (lineReflect Geo axis P)
      P Q
      axis.carrier
      hOppP'P
      hSamePQ

  ----------------------------------------------------------------------
  -- Q and Q' are on opposite sides.
  ----------------------------------------------------------------------

  have hOppQQ' :
      HilbertOppositeSide
        Geo
        Q
        (lineReflect Geo axis Q)
        axis.carrier :=
    lineReflect_oppositeSide
      Geo axis Q hQoff

  ----------------------------------------------------------------------
  -- H is also the perpendicular foot of P'.
  ----------------------------------------------------------------------

  have hPerpP' :
      PerpendicularToAxis
        Geo axis H (lineReflect Geo axis P) :=
    lineReflect_reflected_perpendicular
      Geo
      axis
      P H
      hPoff
      hPerpP
      hMidP

  ----------------------------------------------------------------------
  -- Since K != H, apply the distinct-foot noncollinearity theorem
  -- with Q as the first point and P' as the second point:
  --
  --     Q, Q', P'
  --
  -- are noncollinear.
  ----------------------------------------------------------------------

  have hQQ'P' :
      Not
        (PrimCollinear
          Geo
          Q
          (lineReflect Geo axis Q)
          (lineReflect Geo axis P)) :=
    lineReflect_distinct_feet_noncollinear
      Geo
      axis
      Q
      (lineReflect Geo axis P)
      K H
      (Ne.symm hHK)
      hPerpQ
      hMidQ
      hPerpP'

  ----------------------------------------------------------------------
  -- Rotate this to the order P', Q, Q'.
  ----------------------------------------------------------------------

  have hP'QQ' :
      Not
        (PrimCollinear
          Geo
          (lineReflect Geo axis P)
          Q
          (lineReflect Geo axis Q)) := by

    intro hCol

    exact
      hQQ'P'
        (PrimCollinearCycle
          Geo
          (lineReflect Geo axis P)
          Q
          (lineReflect Geo axis Q)
          hCol)

  ----------------------------------------------------------------------
  -- P' opposite Q and Q opposite Q' imply P' same-side Q'.
  ----------------------------------------------------------------------

  exact
    coxeter_opposite_opposite_sameSide_nondegenerate
      Geo
      (lineReflect Geo axis P)
      Q
      (lineReflect Geo axis Q)
      axis.carrier
      hP'QQ'
      hOppP'Q
      hOppQQ'

/--
For two off-axis points with distinct perpendicular feet, reflection
preserves and reflects the same-side relation with respect to its axis.
-/
theorem lineReflect_sameSide_iff_of_distinct_feet
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H K : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier))
    (hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier))
    (hHK :
      Not (H = K))
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis K Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo K Q (lineReflect Geo axis Q)) :
    HilbertSameSide Geo P Q axis.carrier ↔
    HilbertSameSide
      Geo
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q)
      axis.carrier := by

  constructor

  ----------------------------------------------------------------------
  -- Forward direction: already proved.
  ----------------------------------------------------------------------

  · intro hSamePQ

    exact
      lineReflect_sameSide_of_distinct_feet
        Geo
        axis
        P Q H K
        hPoff
        hQoff
        hHK
        hPerpP
        hMidP
        hPerpQ
        hMidQ
        hSamePQ

  ----------------------------------------------------------------------
  -- Reverse direction.
  --
  -- Reflect P' and Q' once more. Since reflection is involutive,
  -- the resulting points are P and Q.
  ----------------------------------------------------------------------

  · intro hSameP'Q'

    have hP'off :
        Not
          (HilbertIncidence.OnLine
            (lineReflect Geo axis P)
            axis.carrier) :=
      lineReflect_off_axis
        Geo axis P hPoff

    have hQ'off :
        Not
          (HilbertIncidence.OnLine
            (lineReflect Geo axis Q)
            axis.carrier) :=
      lineReflect_off_axis
        Geo axis Q hQoff

    --------------------------------------------------------------------
    -- H and K are also perpendicular feet of P' and Q'.
    --------------------------------------------------------------------

    have hPerpP' :
        PerpendicularToAxis
          Geo axis H (lineReflect Geo axis P) :=
      lineReflect_reflected_perpendicular
        Geo
        axis
        P H
        hPoff
        hPerpP
        hMidP

    have hPerpQ' :
        PerpendicularToAxis
          Geo axis K (lineReflect Geo axis Q) :=
      lineReflect_reflected_perpendicular
        Geo
        axis
        Q K
        hQoff
        hPerpQ
        hMidQ

    --------------------------------------------------------------------
    -- Obtain the canonical reflection data for P' and Q'.
    --------------------------------------------------------------------

    rcases
        lineReflect_off_axis_data
          Geo
          axis
          (lineReflect Geo axis P)
          hP'off
      with
      ⟨H', hPerpP'H', hMidP'⟩

    rcases
        lineReflect_off_axis_data
          Geo
          axis
          (lineReflect Geo axis Q)
          hQ'off
      with
      ⟨K', hPerpQ'K', hMidQ'⟩

    --------------------------------------------------------------------
    -- Perpendicular-foot uniqueness identifies H' = H and K' = K.
    --------------------------------------------------------------------

    have hH'H :
        H' = H :=
      perpendicular_foot_unique
        Geo
        axis
        (lineReflect Geo axis P)
        H' H
        hPerpP'H'
        hPerpP'

    have hK'K :
        K' = K :=
      perpendicular_foot_unique
        Geo
        axis
        (lineReflect Geo axis Q)
        K' K
        hPerpQ'K'
        hPerpQ'

    subst H'
    subst K'

    --------------------------------------------------------------------
    -- Apply the forward theorem to P' and Q'.
    --------------------------------------------------------------------

    have hSameBack :
        HilbertSameSide
          Geo
          (lineReflect Geo axis
            (lineReflect Geo axis P))
          (lineReflect Geo axis
            (lineReflect Geo axis Q))
          axis.carrier :=
      lineReflect_sameSide_of_distinct_feet
        Geo
        axis
        (lineReflect Geo axis P)
        (lineReflect Geo axis Q)
        H K
        hP'off
        hQ'off
        hHK
        hPerpP'
        hMidP'
        hPerpQ'
        hMidQ'
        hSameP'Q'

    --------------------------------------------------------------------
    -- r^2 = 1.
    --------------------------------------------------------------------

    rw
      [lineReflect_involutive Geo axis P,
       lineReflect_involutive Geo axis Q]
      at hSameBack

    exact hSameBack

/--
Two off-axis points with distinct perpendicular feet cannot be
collinear with the second foot.
-/
theorem coxeter_distinct_feet_noncollinear_at_second
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H K : Geo.Point)
    (hHK : Not (H = K))
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hPerpQ :
      PerpendicularToAxis Geo axis K Q) :
    Not (PrimCollinear Geo P K Q) := by

  intro hPKQ

  rcases hPerpQ with
    ⟨hKaxis, hQoff,
      R, hRaxis, hRK, hRightRKQ⟩

  have hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier) :=
    hPerpP.2.1

  have hKQ :
      Not (K = Q) := by
    intro h
    subst Q
    exact hQoff hKaxis

  have hKP :
      Not (K = P) := by
    intro h
    subst P
    exact hPoff hKaxis

  have hKQP :
      PrimCollinear Geo K Q P :=
    PrimCollinearCycle
      Geo P K Q hPKQ

  have hRKQ :
      Not (PrimCollinear Geo R K Q) :=
    hilbert_not_collinear_of_off_line
      Geo
      R K Q
      axis.carrier
      hRK
      hRaxis
      hKaxis
      hQoff

  have hRightRKP :
      HilbertRightAngle Geo R K P :=
    coxeter_right_angle_collinear_second
      Geo
      R K
      Q P
      hKQ
      hKP
      hKQP
      hRKQ
      hRightRKQ

  have hPerpKP :
      PerpendicularToAxis Geo axis K P :=
    ⟨hKaxis,
      hPoff,
      ⟨R,
        hRaxis,
        hRK,
        hRightRKP⟩⟩

  have hEq :
      H = K :=
    perpendicular_foot_unique
      Geo
      axis
      P H K
      hPerpP
      hPerpKP

  exact hHK hEq

/--
For two off-axis points with distinct perpendicular feet, reflection
preserves the angle at the second foot.
-/
theorem lineReflect_distinct_feet_angle_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H K : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier))
    (hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier))
    (hHK :
      Not (H = K))
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis K Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo K Q (lineReflect Geo axis Q)) :
    Geo.AngleCongruent
      P K Q
      (lineReflect Geo axis P)
      K
      (lineReflect Geo axis Q) := by

  have hHaxis :
      HilbertIncidence.OnLine H axis.carrier :=
    hPerpP.1

  have hKaxis :
      HilbertIncidence.OnLine K axis.carrier :=
    hPerpQ.1

  have hKH :
      Not (K = H) :=
    Ne.symm hHK

  ----------------------------------------------------------------------
  -- First component:
  --
  --     angle PKH ~= angle P'KH.
  ----------------------------------------------------------------------

  have hData :=
    lineReflect_distinct_feet_angle_data
      Geo
      axis
      P Q H K
      hPoff
      hQoff
      hHK
      hPerpP
      hPerpQ
      hMidQ

  have hHKP_HKP' :
      Geo.AngleCongruent
        H K P
        H K (lineReflect Geo axis P) :=
    hData.1

  have hPKH_HKP' :
      Geo.AngleCongruent
        P K H
        H K (lineReflect Geo axis P) :=
    (Geo.angle_congruent_reverse_first
      H K P
      H K (lineReflect Geo axis P)).mp
      hHKP_HKP'

  have hPKH_P'KH :
      Geo.AngleCongruent
        P K H
        (lineReflect Geo axis P) K H :=
    (Geo.angle_congruent_reverse_second
      P K H
      H K (lineReflect Geo axis P)).mp
      hPKH_HKP'

  ----------------------------------------------------------------------
  -- Second component:
  --
  --     angle HKQ ~= angle HKQ',
  --
  -- because both are right angles.
  ----------------------------------------------------------------------

  have hRightHKQ :
      HilbertRightAngle Geo H K Q :=
    hData.2.1

  have hRightHKQ' :
      HilbertRightAngle
        Geo H K (lineReflect Geo axis Q) :=
    hData.2.2

  have hHKQ :
      Not (PrimCollinear Geo H K Q) :=
    hilbert_not_collinear_of_off_line
      Geo
      H K Q
      axis.carrier
      hHK
      hHaxis
      hKaxis
      hQoff

  have hQ'off :
      Not
        (HilbertIncidence.OnLine
          (lineReflect Geo axis Q)
          axis.carrier) :=
    lineReflect_off_axis
      Geo axis Q hQoff

  have hHKQ' :
      Not
        (PrimCollinear
          Geo H K (lineReflect Geo axis Q)) :=
    hilbert_not_collinear_of_off_line
      Geo
      H K
      (lineReflect Geo axis Q)
      axis.carrier
      hHK
      hHaxis
      hKaxis
      hQ'off

  have hHKQ_HKQ' :
      Geo.AngleCongruent
        H K Q
        H K (lineReflect Geo axis Q) :=
    hilbert_all_right_angles_congruent
      Geo
      H K Q
      H K (lineReflect Geo axis Q)
      hHKQ
      hHKQ'
      hRightHKQ
      hRightHKQ'

  ----------------------------------------------------------------------
  -- The outer angles PKQ and P'KQ' are nondegenerate.
  ----------------------------------------------------------------------

  have hPKQ :
      Not (PrimCollinear Geo P K Q) :=
    coxeter_distinct_feet_noncollinear_at_second
      Geo
      axis
      P Q H K
      hHK
      hPerpP
      hPerpQ

  have hP'off :
      Not
        (HilbertIncidence.OnLine
          (lineReflect Geo axis P)
          axis.carrier) :=
    lineReflect_off_axis
      Geo axis P hPoff

  have hPerpP' :
      PerpendicularToAxis
        Geo axis H (lineReflect Geo axis P) :=
    lineReflect_reflected_perpendicular
      Geo
      axis
      P H
      hPoff
      hPerpP
      hMidP

  have hPerpQ' :
      PerpendicularToAxis
        Geo axis K (lineReflect Geo axis Q) :=
    lineReflect_reflected_perpendicular
      Geo
      axis
      Q K
      hQoff
      hPerpQ
      hMidQ

  have hP'KQ' :
      Not
        (PrimCollinear
          Geo
          (lineReflect Geo axis P)
          K
          (lineReflect Geo axis Q)) :=
    coxeter_distinct_feet_noncollinear_at_second
      Geo
      axis
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q)
      H K
      hHK
      hPerpP'
      hPerpQ'

  ----------------------------------------------------------------------
  -- Reflection preserves the side configuration of the two outer rays.
  ----------------------------------------------------------------------

  have hSideConfiguration :
      HilbertSameSide Geo P Q axis.carrier ↔
      HilbertSameSide
        Geo
        (lineReflect Geo axis P)
        (lineReflect Geo axis Q)
        axis.carrier :=
    lineReflect_sameSide_iff_of_distinct_feet
      Geo
      axis
      P Q H K
      hPoff
      hQoff
      hHK
      hPerpP
      hMidP
      hPerpQ
      hMidQ

  ----------------------------------------------------------------------
  -- Hilbert Theorem 15: add the two component angles.
  ----------------------------------------------------------------------

  exact
    hilbert_angle_addition
      Geo
      P K H Q
      (lineReflect Geo axis P)
      K
      H
      (lineReflect Geo axis Q)
      axis.carrier
      axis.carrier
      hKH
      hKH
      hKaxis
      hHaxis
      hKaxis
      hHaxis
      hPoff
      hQoff
      hP'off
      hQ'off
      hSideConfiguration
      hPKQ
      hP'KQ'
      hPKH_P'KH
      hHKQ_HKQ'

/--
For two off-axis points with distinct perpendicular feet, line
reflection preserves the segment joining them.
-/
theorem lineReflect_preserves_congruence_distinct_feet
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H K : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier))
    (hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier))
    (hHK :
      Not (H = K))
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis K Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo K Q (lineReflect Geo axis Q)) :
    Geo.Congruent
      P Q
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q) := by

  have hKaxis :
      HilbertIncidence.OnLine K axis.carrier :=
    hPerpQ.1

  ----------------------------------------------------------------------
  -- The two sides from K are preserved.
  ----------------------------------------------------------------------

  have hKP_KP' :
      Geo.Congruent
        K P
        K (lineReflect Geo axis P) :=
    lineReflect_axis_point_equidistant
      Geo
      axis
      P K
      hKaxis

  have hKQ_KQ' :
      Geo.Congruent
        K Q
        K (lineReflect Geo axis Q) :=
    lineReflect_axis_point_equidistant
      Geo
      axis
      Q K
      hKaxis

  ----------------------------------------------------------------------
  -- The included angle at K is preserved.
  ----------------------------------------------------------------------

  have hAngle :
      Geo.AngleCongruent
        P K Q
        (lineReflect Geo axis P)
        K
        (lineReflect Geo axis Q) :=
    lineReflect_distinct_feet_angle_congruent
      Geo
      axis
      P Q H K
      hPoff
      hQoff
      hHK
      hPerpP
      hMidP
      hPerpQ
      hMidQ

  ----------------------------------------------------------------------
  -- The original triangle KPQ is nondegenerate.
  ----------------------------------------------------------------------

  have hKPQ :
      Not (PrimCollinear Geo K P Q) := by
    intro h

    exact
      (coxeter_distinct_feet_noncollinear_at_second
        Geo
        axis
        P Q H K
        hHK
        hPerpP
        hPerpQ)
        (PrimCollinearSwap Geo K P Q h)

  ----------------------------------------------------------------------
  -- The reflected triangle KP'Q' is also nondegenerate.
  ----------------------------------------------------------------------

  have hPerpP' :
      PerpendicularToAxis
        Geo axis H (lineReflect Geo axis P) :=
    lineReflect_reflected_perpendicular
      Geo
      axis
      P H
      hPoff
      hPerpP
      hMidP

  have hPerpQ' :
      PerpendicularToAxis
        Geo axis K (lineReflect Geo axis Q) :=
    lineReflect_reflected_perpendicular
      Geo
      axis
      Q K
      hQoff
      hPerpQ
      hMidQ

  have hP'KQ' :
      Not
        (PrimCollinear
          Geo
          (lineReflect Geo axis P)
          K
          (lineReflect Geo axis Q)) :=
    coxeter_distinct_feet_noncollinear_at_second
      Geo
      axis
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q)
      H K
      hHK
      hPerpP'
      hPerpQ'

  have hKP'Q' :
      Not
        (PrimCollinear
          Geo
          K
          (lineReflect Geo axis P)
          (lineReflect Geo axis Q)) := by
    intro h

    exact
      hP'KQ'
        (PrimCollinearSwap
          Geo
          K
          (lineReflect Geo axis P)
          (lineReflect Geo axis Q)
          h)

  ----------------------------------------------------------------------
  -- SAS for triangles KPQ and KP'Q'.
  ----------------------------------------------------------------------

  have hSAS :
      TriangleCongruenceResult
        Geo
        K P Q
        K
        (lineReflect Geo axis P)
        (lineReflect Geo axis Q) :=
    SAS
      Geo
      K P Q
      K
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q)
      hKPQ
      hKP'Q'
      hKP_KP'
      hAngle
      hKQ_KQ'

  exact hSAS.sideBC

/--
If two points have the same perpendicular foot on the axis, their
right-angle data can be normalized to one common axis direction.
-/
theorem coxeter_same_foot_common_axis_right_angles
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hPerpQ :
      PerpendicularToAxis Geo axis H Q) :
    Exists fun R : Geo.Point =>
      HilbertIncidence.OnLine R axis.carrier /\
      Not (R = H) /\
      HilbertRightAngle Geo R H P /\
      HilbertRightAngle Geo R H Q := by

  rcases hPerpP with
    ⟨hHaxis, _hPoff,
      R, hRaxis, hRH, hRightRHP⟩

  rcases hPerpQ with
    ⟨_hHaxisQ, hQoff,
      S, hSaxis, hSH, hRightSHQ⟩

  have hHS :
      Not (H = S) :=
    Ne.symm hSH

  have hHR :
      Not (H = R) :=
    Ne.symm hRH

  have hHSR :
      PrimCollinear Geo H S R :=
    ⟨axis.carrier,
      hHaxis,
      hSaxis,
      hRaxis⟩

  have hSHQ :
      Not (PrimCollinear Geo S H Q) :=
    hilbert_not_collinear_of_off_line
      Geo
      S H Q
      axis.carrier
      hSH
      hSaxis
      hHaxis
      hQoff

  have hRightRHQ :
      HilbertRightAngle Geo R H Q :=
    coxeter_right_angle_collinear_first
      Geo
      S R H Q
      hHS
      hHR
      hHSR
      hSHQ
      hRightSHQ

  exact
    ⟨R,
      hRaxis,
      hRH,
      hRightRHP,
      hRightRHQ⟩

/--
Two points having the same perpendicular foot on the reflection axis
lie on one line with that foot.
-/
theorem coxeter_same_perpendicular_foot_collinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hPerpQ :
      PerpendicularToAxis Geo axis H Q) :
    PrimCollinear Geo P H Q := by

  have hHaxis :
      HilbertIncidence.OnLine H axis.carrier :=
    hPerpP.1

  have hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier) :=
    hPerpP.2.1

  have hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier) :=
    hPerpQ.2.1

  rcases
      coxeter_same_foot_common_axis_right_angles
        Geo
        axis
        P Q H
        hPerpP
        hPerpQ
    with
    ⟨R, hRaxis, hRH, hRightRHP, hRightRHQ⟩

  have hRHP :
      Not (PrimCollinear Geo R H P) :=
    hilbert_not_collinear_of_off_line
      Geo
      R H P
      axis.carrier
      hRH
      hRaxis
      hHaxis
      hPoff

  have hRHQ :
      Not (PrimCollinear Geo R H Q) :=
    hilbert_not_collinear_of_off_line
      Geo
      R H Q
      axis.carrier
      hRH
      hRaxis
      hHaxis
      hQoff

  by_contra hPHQ

  by_cases hSamePQ :
      HilbertSameSide Geo P Q axis.carrier

  ----------------------------------------------------------------------
  -- Case 1: P and Q are on the same side of the axis.
  --
  -- RHP and RHQ are both right. Hence the angles are congruent.
  -- Angle uniqueness forces HP and HQ to be the same ray.
  ----------------------------------------------------------------------

  · have hAnglePQ :
        Geo.AngleCongruent R H P R H Q :=
      hilbert_all_right_angles_congruent
        Geo
        R H P
        R H Q
        hRHP
        hRHQ
        hRightRHP
        hRightRHQ

    rcases
        hilbert_angle_unique_common_ray
          Geo
          R H P Q
          axis.carrier
          hRH
          hRaxis
          hHaxis
          hPoff
          hSamePQ
          hAnglePQ
      with
      ⟨X, hRayXP, hRayXQ⟩

    have hRayPQ :
        HilbertSameRay Geo H P Q :=
      hilbert_sameRay_of_common
        Geo
        H X P Q
        hRayXP
        hRayXQ

    have hHPQ :
        PrimCollinear Geo H P Q :=
      hRayPQ.2.2.1

    exact
      hPHQ
        (PrimCollinearSwap
          Geo H P Q hHPQ)

  ----------------------------------------------------------------------
  -- Case 2: P and Q are on opposite sides of the axis.
  --
  -- Extend QH through H to T. Then Q-H-T.
  -- P and T are on the same side of the axis.
  -- The right angles RHP and RHT then determine the same ray.
  ----------------------------------------------------------------------

  · have hOppPQ :
        HilbertOppositeSide Geo P Q axis.carrier :=
      hilbert_order_oppositeSide_of_not_sameSide
        Geo
        P Q
        axis.carrier
        hPoff
        hQoff
        hSamePQ

    have hRightQHR :
        HilbertRightAngle Geo Q H R :=
      coxeter_right_angle_swap
        Geo
        R H Q
        hRHQ
        hRightRHQ

    rcases hRightQHR with
      ⟨T, hQHT, _hAngleQHR_RHT⟩

    have hQHTdata :=
      HilbertOrder.between_incidence
        Q H T hQHT

    have hHQ :
        Not (H = Q) :=
      Ne.symm hQHTdata.1

    have hHT :
        Not (H = T) :=
      hQHTdata.2.1

    have hQT :
        Not (Q = T) :=
      hQHTdata.2.2.1

    have hQHTcol :
        PrimCollinear Geo Q H T :=
      hQHTdata.2.2.2.1

    --------------------------------------------------------------------
    -- T is also off the reflection axis.
    --------------------------------------------------------------------

    have hToff :
        Not (HilbertIncidence.OnLine T axis.carrier) := by

      intro hTaxis

      have hHTQ :
          PrimCollinear Geo H T Q :=
        PrimCollinearCycle
          Geo Q H T hQHTcol

      have hQaxis :
          HilbertIncidence.OnLine Q axis.carrier :=
        hilbert_collinear_on_line
          Geo
          H T Q
          axis.carrier
          hHT
          hHaxis
          hTaxis
          hHTQ

      exact hQoff hQaxis

    have hOppQT :
        HilbertOppositeSide Geo Q T axis.carrier :=
      ⟨hQoff,
        hToff,
        ⟨H,
          hQHT,
          hHaxis⟩⟩

    --------------------------------------------------------------------
    -- P,Q,T cannot be collinear, otherwise P,H,Q would already be
    -- collinear because Q,H,T are collinear.
    --------------------------------------------------------------------

    have hPQT :
        Not (PrimCollinear Geo P Q T) := by

      intro hPQTcol

      have hQTH :
          PrimCollinear Geo Q T H :=
        PrimCollinearRotate
          Geo Q H T hQHTcol

      have hPQH :
          PrimCollinear Geo P Q H :=
        hilbert_primCollinear_trans
          Geo
          P Q T H
          hQT
          hPQTcol
          hQTH

      exact
        hPHQ
          (PrimCollinearRotate
            Geo P Q H hPQH)

    --------------------------------------------------------------------
    -- P opposite Q and Q opposite T imply P same-side T.
    --------------------------------------------------------------------

    have hSamePT :
        HilbertSameSide Geo P T axis.carrier :=
      coxeter_opposite_opposite_sameSide_nondegenerate
        Geo
        P Q T
        axis.carrier
        hPQT
        hOppPQ
        hOppQT

    --------------------------------------------------------------------
    -- Since Q,H,T are collinear, RHT is right as well.
    --------------------------------------------------------------------

    have hHQT :
        PrimCollinear Geo H Q T :=
      PrimCollinearSwap
        Geo Q H T hQHTcol

    have hRightRHT :
        HilbertRightAngle Geo R H T :=
      coxeter_right_angle_collinear_second
        Geo
        R H
        Q T
        hHQ
        hHT
        hHQT
        hRHQ
        hRightRHQ

    have hRHT :
        Not (PrimCollinear Geo R H T) :=
      hilbert_not_collinear_of_off_line
        Geo
        R H T
        axis.carrier
        hRH
        hRaxis
        hHaxis
        hToff

    have hAnglePT :
        Geo.AngleCongruent R H P R H T :=
      hilbert_all_right_angles_congruent
        Geo
        R H P
        R H T
        hRHP
        hRHT
        hRightRHP
        hRightRHT

    --------------------------------------------------------------------
    -- P and T are on the same side and make equal angles with HR.
    -- Hence HP and HT are the same ray.
    --------------------------------------------------------------------

    rcases
        hilbert_angle_unique_common_ray
          Geo
          R H P T
          axis.carrier
          hRH
          hRaxis
          hHaxis
          hPoff
          hSamePT
          hAnglePT
      with
      ⟨X, hRayXP, hRayXT⟩

    have hRayPT :
        HilbertSameRay Geo H P T :=
      hilbert_sameRay_of_common
        Geo
        H X P T
        hRayXP
        hRayXT

    have hHPT :
        PrimCollinear Geo H P T :=
      hRayPT.2.2.1

    have hPHT :
        PrimCollinear Geo P H T :=
      PrimCollinearSwap
        Geo H P T hHPT

    have hHTQ :
        PrimCollinear Geo H T Q :=
      PrimCollinearCycle
        Geo Q H T hQHTcol

    have hPHQ' :
        PrimCollinear Geo P H Q :=
      hilbert_primCollinear_trans
        Geo
        P H T Q
        hHT
        hPHT
        hHTQ

    exact hPHQ hPHQ'

/--
Two perpendicular rays from the same foot, lying on the same side
of the reflection axis, are the same ray.
-/
theorem coxeter_same_foot_perpendicular_same_ray
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hPerpQ :
      PerpendicularToAxis Geo axis H Q)
    (hSame :
      HilbertSameSide Geo P Q axis.carrier) :
    HilbertSameRay Geo H P Q := by

  have hHaxis :
      HilbertIncidence.OnLine H axis.carrier :=
    hPerpP.1

  have hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier) :=
    hPerpP.2.1

  have hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier) :=
    hPerpQ.2.1

  rcases
      coxeter_same_foot_common_axis_right_angles
        Geo
        axis
        P Q H
        hPerpP
        hPerpQ
    with
    ⟨R, hRaxis, hRH, hRightRHP, hRightRHQ⟩

  have hRHP :
      Not (PrimCollinear Geo R H P) :=
    hilbert_not_collinear_of_off_line
      Geo
      R H P
      axis.carrier
      hRH
      hRaxis
      hHaxis
      hPoff

  have hRHQ :
      Not (PrimCollinear Geo R H Q) :=
    hilbert_not_collinear_of_off_line
      Geo
      R H Q
      axis.carrier
      hRH
      hRaxis
      hHaxis
      hQoff

  have hAngle :
      Geo.AngleCongruent
        R H P
        R H Q :=
    hilbert_all_right_angles_congruent
      Geo
      R H P
      R H Q
      hRHP
      hRHQ
      hRightRHP
      hRightRHQ

  rcases
      hilbert_angle_unique_common_ray
        Geo
        R H P Q
        axis.carrier
        hRH
        hRaxis
        hHaxis
        hPoff
        hSame
        hAngle
    with
    ⟨X, hRayXP, hRayXQ⟩

  exact
    hilbert_sameRay_of_common
      Geo
      H X P Q
      hRayXP
      hRayXQ

/--
If two off-axis points have the same perpendicular foot and lie on
opposite sides of the reflection axis, then their common foot lies
strictly between them.
-/
theorem coxeter_same_foot_oppositeSide_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hPerpQ :
      PerpendicularToAxis Geo axis H Q)
    (hOpp :
      HilbertOppositeSide Geo P Q axis.carrier) :
    Geo.Between P H Q := by

  have hHaxis :
      HilbertIncidence.OnLine H axis.carrier :=
    hPerpP.1

  have hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier) :=
    hPerpP.2.1

  have hPHQcol :
      PrimCollinear Geo P H Q :=
    coxeter_same_perpendicular_foot_collinear
      Geo
      axis
      P Q H
      hPerpP
      hPerpQ

  rcases hPHQcol with
    ⟨m, hPm, hHm, hQm⟩

  rcases hOpp.2.2 with
    ⟨X, hPXQ, hXaxis⟩

  have hPXQdata :=
    HilbertOrder.between_incidence
      P X Q hPXQ

  have hPQ :
      Not (P = Q) :=
    hPXQdata.2.2.1

  have hPXQcol :
      PrimCollinear Geo P X Q :=
    hPXQdata.2.2.2.1

  have hPQX :
      PrimCollinear Geo P Q X :=
    PrimCollinearRotate
      Geo P X Q hPXQcol

  ----------------------------------------------------------------------
  -- X also lies on the common perpendicular m through P,H,Q.
  ----------------------------------------------------------------------

  have hXm :
      HilbertIncidence.OnLine X m :=
    hilbert_collinear_on_line
      Geo
      P Q X
      m
      hPQ
      hPm
      hQm
      hPQX

  ----------------------------------------------------------------------
  -- The intersection point X must be H.
  --
  -- Otherwise m and the reflection axis would contain the two distinct
  -- points X and H and therefore would be the same line.
  ----------------------------------------------------------------------

  have hXH :
      X = H := by

    by_contra hXH

    have hEq :
        m = axis.carrier :=
      HilbertPlaneIncidence.line_unique
        X H
        hXH
        m
        axis.carrier
        hXm
        hHm
        hXaxis
        hHaxis

    have hPaxis :
        HilbertIncidence.OnLine P axis.carrier := by
      rw [← hEq]
      exact hPm

    exact hPoff hPaxis

  subst X

  exact hPXQ

/--
In the common-foot opposite-side configuration, the reflected points
also have the common foot strictly between them.
-/
theorem lineReflect_same_foot_oppositeSide_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis H Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo H Q (lineReflect Geo axis Q))
    (hOpp :
      HilbertOppositeSide Geo P Q axis.carrier) :
    Geo.Between
      (lineReflect Geo axis P)
      H
      (lineReflect Geo axis Q) := by

  have hPHQ :
      Geo.Between P H Q :=
    coxeter_same_foot_oppositeSide_between
      Geo
      axis
      P Q H
      hPerpP
      hPerpQ
      hOpp

  have hQHP :
      Geo.Between Q H P :=
    (HilbertOrder.between_incidence
      P H Q hPHQ).2.2.2.2

  have hPHQData :=
    HilbertOrder.between_incidence
      P H Q hPHQ

  have hPH :
      Not (P = H) :=
    hPHQData.1

  have hQH :
      Not (Q = H) :=
    Ne.symm hPHQData.2.1

  ----------------------------------------------------------------------
  -- Q and P' lie on the same ray from H.
  ----------------------------------------------------------------------

  have hRayPHQ :
      HilbertSameRay Geo P H Q :=
    hilbert_sameRay_of_between
      Geo P H Q hPHQ

  have hRayPHP' :
      HilbertSameRay
        Geo P H (lineReflect Geo axis P) :=
    hilbert_sameRay_of_between
      Geo
      P H
      (lineReflect Geo axis P)
      hMidP.1

  have hRayPQP' :
      HilbertSameRay
        Geo P Q (lineReflect Geo axis P) :=
    hilbert_sameRay_of_common
      Geo
      P H
      Q
      (lineReflect Geo axis P)
      hRayPHQ
      hRayPHP'

  have hRayHQP' :
      HilbertSameRay
        Geo H Q (lineReflect Geo axis P) := by

    rcases
        hilbert_sameRay_cases
          Geo
          P
          Q
          (lineReflect Geo axis P)
          hRayPQP'
      with hEq | hPQP' | hPP'Q

    · rw [← hEq]
      exact
        hilbert_sameRay_refl
          Geo H Q hQH

    · have hHQP' :
          Geo.Between
            H Q (lineReflect Geo axis P) :=
        (hilbert_between_inner_trans
          Geo
          P H Q
          (lineReflect Geo axis P)
          hPHQ
          hPQP').1

      exact
        hilbert_sameRay_of_between
          Geo
          H Q
          (lineReflect Geo axis P)
          hHQP'

    · have hHP'Q :
          Geo.Between
            H
            (lineReflect Geo axis P)
            Q :=
        (hilbert_between_inner_trans
          Geo
          P H
          (lineReflect Geo axis P)
          Q
          hMidP.1
          hPP'Q).1

      have hRayHP'Q :
          HilbertSameRay
            Geo
            H
            (lineReflect Geo axis P)
            Q :=
        hilbert_sameRay_of_between
          Geo
          H
          (lineReflect Geo axis P)
          Q
          hHP'Q

      exact
        hilbert_sameRay_symm
          Geo
          H
          (lineReflect Geo axis P)
          Q
          hRayHP'Q

  ----------------------------------------------------------------------
  -- P and Q' lie on the same ray from H.
  ----------------------------------------------------------------------

  have hRayQHP :
      HilbertSameRay Geo Q H P :=
    hilbert_sameRay_of_between
      Geo Q H P hQHP

  have hRayQHQ' :
      HilbertSameRay
        Geo Q H (lineReflect Geo axis Q) :=
    hilbert_sameRay_of_between
      Geo
      Q H
      (lineReflect Geo axis Q)
      hMidQ.1

  have hRayQPQ' :
      HilbertSameRay
        Geo Q P (lineReflect Geo axis Q) :=
    hilbert_sameRay_of_common
      Geo
      Q H
      P
      (lineReflect Geo axis Q)
      hRayQHP
      hRayQHQ'

  have hRayHPQ' :
      HilbertSameRay
        Geo H P (lineReflect Geo axis Q) := by

    rcases
        hilbert_sameRay_cases
          Geo
          Q
          P
          (lineReflect Geo axis Q)
          hRayQPQ'
      with hEq | hQPQ' | hQQ'P

    · rw [← hEq]
      exact
        hilbert_sameRay_refl
          Geo H P hPH

    · have hHPQ' :
          Geo.Between
            H P (lineReflect Geo axis Q) :=
        (hilbert_between_inner_trans
          Geo
          Q H P
          (lineReflect Geo axis Q)
          hQHP
          hQPQ').1

      exact
        hilbert_sameRay_of_between
          Geo
          H P
          (lineReflect Geo axis Q)
          hHPQ'

    · have hHQ'P :
          Geo.Between
            H
            (lineReflect Geo axis Q)
            P :=
        (hilbert_between_inner_trans
          Geo
          Q H
          (lineReflect Geo axis Q)
          P
          hMidQ.1
          hQQ'P).1

      have hRayHQ'P :
          HilbertSameRay
            Geo
            H
            (lineReflect Geo axis Q)
            P :=
        hilbert_sameRay_of_between
          Geo
          H
          (lineReflect Geo axis Q)
          P
          hHQ'P

      exact
        hilbert_sameRay_symm
          Geo
          H
          (lineReflect Geo axis Q)
          P
          hRayHQ'P

  ----------------------------------------------------------------------
  -- Transport Q-H-P to P'-H-Q'.
  ----------------------------------------------------------------------

  exact
    hilbert_between_transport_sameRays
      Geo
      Q H P
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q)
      hQHP
      hRayHQP'
      hRayHPQ'

/--
If two off-axis points have the same perpendicular foot and lie on
opposite sides of the reflection axis, line reflection preserves the
segment joining them.
-/
theorem lineReflect_preserves_congruence_same_foot_oppositeSide
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis H Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo H Q (lineReflect Geo axis Q))
    (hOpp :
      HilbertOppositeSide Geo P Q axis.carrier) :
    Geo.Congruent
      P Q
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q) := by

  have hPHQ :
      Geo.Between P H Q :=
    coxeter_same_foot_oppositeSide_between
      Geo
      axis
      P Q H
      hPerpP
      hPerpQ
      hOpp

  have hP'HQ' :
      Geo.Between
        (lineReflect Geo axis P)
        H
        (lineReflect Geo axis Q) :=
    lineReflect_same_foot_oppositeSide_between
      Geo
      axis
      P Q H
      hPerpP
      hMidP
      hPerpQ
      hMidQ
      hOpp

  ----------------------------------------------------------------------
  -- Midpoint data:
  --
  --   PH ~= HP'
  --   QH ~= HQ'
  --
  -- Normalize endpoint orientation for segment additivity.
  ----------------------------------------------------------------------

  have hPH_P'H :
      Geo.Congruent
        P H
        (lineReflect Geo axis P) H :=
    CongruentSwapSecond
      Geo
      P H
      H (lineReflect Geo axis P)
      hMidP.2

  have hHQ_HQ' :
      Geo.Congruent
        H Q
        H (lineReflect Geo axis Q) :=
    CongruentReverseFirst
      Geo
      Q H
      H (lineReflect Geo axis Q)
      hMidQ.2

  ----------------------------------------------------------------------
  -- Hilbert III.3:
  --
  --   P-H-Q, P'-H-Q',
  --   PH ~= P'H, HQ ~= HQ'
  --   --------------------------------
  --              PQ ~= P'Q'
  ----------------------------------------------------------------------

  exact
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      P H Q
      (lineReflect Geo axis P)
      H
      (lineReflect Geo axis Q)
      hPHQ
      hP'HQ'
      hPH_P'H
      hHQ_HQ'

/--
For two off-axis points with the same perpendicular foot, if the
original points lie on the same side of the reflection axis, then
their reflected images lie on the same ray from the common foot.
-/
theorem lineReflect_same_foot_sameSide_sameRay
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis H Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo H Q (lineReflect Geo axis Q))
    (hSame :
      HilbertSameSide Geo P Q axis.carrier) :
    HilbertSameRay
      Geo
      H
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q) := by

  have hHaxis :
      HilbertIncidence.OnLine H axis.carrier :=
    hPerpP.1

  have hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier) :=
    hPerpP.2.1

  have hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier) :=
    hPerpQ.2.1

  have hP'off :
      Not
        (HilbertIncidence.OnLine
          (lineReflect Geo axis P)
          axis.carrier) :=
    lineReflect_off_axis
      Geo axis P hPoff

  have hQ'off :
      Not
        (HilbertIncidence.OnLine
          (lineReflect Geo axis Q)
          axis.carrier) :=
    lineReflect_off_axis
      Geo axis Q hQoff

  ----------------------------------------------------------------------
  -- H is also the perpendicular foot of P' and Q'.
  ----------------------------------------------------------------------

  have hPerpP' :
      PerpendicularToAxis
        Geo axis H (lineReflect Geo axis P) :=
    lineReflect_reflected_perpendicular
      Geo
      axis
      P H
      hPoff
      hPerpP
      hMidP

  have hPerpQ' :
      PerpendicularToAxis
        Geo axis H (lineReflect Geo axis Q) :=
    lineReflect_reflected_perpendicular
      Geo
      axis
      Q H
      hQoff
      hPerpQ
      hMidQ

  ----------------------------------------------------------------------
  -- Since r^2 = 1, H is the midpoint of P'P and Q'Q.
  ----------------------------------------------------------------------

  have hMidP'raw :
      HilbertIsMidpoint
        Geo
        H
        (lineReflect Geo axis P)
        P :=
    MidpointSymmetry
      Geo
      H
      P
      (lineReflect Geo axis P)
      hMidP

  have hMidQ'raw :
      HilbertIsMidpoint
        Geo
        H
        (lineReflect Geo axis Q)
        Q :=
    MidpointSymmetry
      Geo
      H
      Q
      (lineReflect Geo axis Q)
      hMidQ

  have hMidP' :
      HilbertIsMidpoint
        Geo
        H
        (lineReflect Geo axis P)
        (lineReflect Geo axis
          (lineReflect Geo axis P)) := by
    simpa only
      [lineReflect_involutive Geo axis P]
      using hMidP'raw

  have hMidQ' :
      HilbertIsMidpoint
        Geo
        H
        (lineReflect Geo axis Q)
        (lineReflect Geo axis
          (lineReflect Geo axis Q)) := by
    simpa only
      [lineReflect_involutive Geo axis Q]
      using hMidQ'raw

  ----------------------------------------------------------------------
  -- P', H, Q' are collinear because they have the same perpendicular
  -- foot.
  ----------------------------------------------------------------------

  have hP'HQ' :
      PrimCollinear
        Geo
        (lineReflect Geo axis P)
        H
        (lineReflect Geo axis Q) :=
    coxeter_same_perpendicular_foot_collinear
      Geo
      axis
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q)
      H
      hPerpP'
      hPerpQ'

  have hCol :
      PrimCollinear
        Geo
        H
        (lineReflect Geo axis P)
        (lineReflect Geo axis Q) :=
    PrimCollinearSwap
      Geo
      (lineReflect Geo axis P)
      H
      (lineReflect Geo axis Q)
      hP'HQ'

  have hMidPData :=
    HilbertOrder.between_incidence
      P H (lineReflect Geo axis P)
      hMidP.1

  have hMidQData :=
    HilbertOrder.between_incidence
      Q H (lineReflect Geo axis Q)
      hMidQ.1

  have hP'H :
      Not (lineReflect Geo axis P = H) :=
    Ne.symm hMidPData.2.1

  have hQ'H :
      Not (lineReflect Geo axis Q = H) :=
    Ne.symm hMidQData.2.1

  refine
    ⟨hP'H,
      hQ'H,
      hCol,
      ?_⟩

  ----------------------------------------------------------------------
  -- If H lay between P' and Q', then P' and Q' would be opposite
  -- across the reflection axis.
  ----------------------------------------------------------------------

  intro hP'HQ'Between

  have hOppP'Q' :
      HilbertOppositeSide
        Geo
        (lineReflect Geo axis P)
        (lineReflect Geo axis Q)
        axis.carrier :=
    ⟨hP'off,
      hQ'off,
      ⟨H,
        hP'HQ'Between,
        hHaxis⟩⟩

  ----------------------------------------------------------------------
  -- Reflect that opposite-side configuration once more.
  -- The already proved common-foot opposite-side theorem gives
  --
  --     r(P') - H - r(Q').
  --
  -- Involution turns this into P-H-Q.
  ----------------------------------------------------------------------

  have hBack :
      Geo.Between
        (lineReflect Geo axis
          (lineReflect Geo axis P))
        H
        (lineReflect Geo axis
          (lineReflect Geo axis Q)) :=
    lineReflect_same_foot_oppositeSide_between
      Geo
      axis
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q)
      H
      hPerpP'
      hMidP'
      hPerpQ'
      hMidQ'
      hOppP'Q'

  have hPHQ :
      Geo.Between P H Q := by
    simpa only
      [lineReflect_involutive Geo axis P,
       lineReflect_involutive Geo axis Q]
      using hBack

  have hOppPQ :
      HilbertOppositeSide
        Geo P Q axis.carrier :=
    ⟨hPoff,
      hQoff,
      ⟨H,
        hPHQ,
        hHaxis⟩⟩

  exact
    (hilbert_oppositeSide_not_sameSide
      Geo
      P Q
      axis.carrier
      hOppPQ)
      hSame

/--
If two off-axis points have the same perpendicular foot and lie on
the same side of the reflection axis, line reflection preserves the
segment joining them.
-/
theorem lineReflect_preserves_congruence_same_foot_sameSide
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis H Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo H Q (lineReflect Geo axis Q))
    (hSame :
      HilbertSameSide Geo P Q axis.carrier) :
    Geo.Congruent
      P Q
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q) := by

  have hRayPQ :
      HilbertSameRay Geo H P Q :=
    coxeter_same_foot_perpendicular_same_ray
      Geo
      axis
      P Q H
      hPerpP
      hPerpQ
      hSame

  have hRayP'Q' :
      HilbertSameRay
        Geo
        H
        (lineReflect Geo axis P)
        (lineReflect Geo axis Q) :=
    lineReflect_same_foot_sameSide_sameRay
      Geo
      axis
      P Q H
      hPerpP
      hMidP
      hPerpQ
      hMidQ
      hSame

  ----------------------------------------------------------------------
  -- Normalize the midpoint congruences:
  --
  --   PH ~= HP'  gives  HP ~= HP'
  --   QH ~= HQ'  gives  HQ ~= HQ'.
  ----------------------------------------------------------------------

  have hHP_HP' :
      Geo.Congruent
        H P
        H (lineReflect Geo axis P) :=
    CongruentReverseFirst
      Geo
      P H
      H (lineReflect Geo axis P)
      hMidP.2

  have hHQ_HQ' :
      Geo.Congruent
        H Q
        H (lineReflect Geo axis Q) :=
    CongruentReverseFirst
      Geo
      Q H
      H (lineReflect Geo axis Q)
      hMidQ.2

  have hHP'_HP :
      Geo.Congruent
        H (lineReflect Geo axis P)
        H P :=
    hilbert_congruent_symmetry
      Geo
      H P
      H (lineReflect Geo axis P)
      hHP_HP'

  have hHQ'_HQ :
      Geo.Congruent
        H (lineReflect Geo axis Q)
        H Q :=
    hilbert_congruent_symmetry
      Geo
      H Q
      H (lineReflect Geo axis Q)
      hHQ_HQ'

  ----------------------------------------------------------------------
  -- Order P and Q on their common ray from H.
  ----------------------------------------------------------------------

  rcases
      hilbert_sameRay_cases
        Geo H P Q hRayPQ
    with hPQ | hHPQ | hHQP

  ----------------------------------------------------------------------
  -- Degenerate case: P = Q.
  ----------------------------------------------------------------------

  · subst Q

    exact
      bookZero_nullSegment2
        Geo
        P
        (lineReflect Geo axis P)

  ----------------------------------------------------------------------
  -- Case H-P-Q.
  --
  -- Lay off the congruent radii HP' and HQ' on their common reflected
  -- ray. Since HP is the shorter original segment, P' lies between
  -- H and Q'.
  ----------------------------------------------------------------------

  · have hMidPData :=
      HilbertOrder.between_incidence
        P H (lineReflect Geo axis P)
        hMidP.1

    have hP'H :
        Not (lineReflect Geo axis P = H) :=
      Ne.symm hMidPData.2.1

    have hRayP'P' :
        HilbertSameRay
          Geo
          H
          (lineReflect Geo axis P)
          (lineReflect Geo axis P) :=
      hilbert_sameRay_refl
        Geo
        H
        (lineReflect Geo axis P)
        hP'H

    have hHP'Q' :
        Geo.Between
          H
          (lineReflect Geo axis P)
          (lineReflect Geo axis Q) :=
      hilbert_layoff_shorter_between
        Geo
        H P Q
        H
        (lineReflect Geo axis P)
        (lineReflect Geo axis P)
        (lineReflect Geo axis Q)
        hHPQ
        hRayP'P'
        hRayP'Q'
        hHP'_HP
        hHQ'_HQ

    exact
      hilbert_segment_subtraction
        Geo
        H P Q
        H
        (lineReflect Geo axis P)
        (lineReflect Geo axis Q)
        hHPQ
        hHP'Q'
        hHP_HP'
        hHQ_HQ'

  ----------------------------------------------------------------------
  -- Case H-Q-P.
  --
  -- This is symmetric. The reflected ray order is H-Q'-P'.
  ----------------------------------------------------------------------

  · have hMidQData :=
      HilbertOrder.between_incidence
        Q H (lineReflect Geo axis Q)
        hMidQ.1

    have hQ'H :
        Not (lineReflect Geo axis Q = H) :=
      Ne.symm hMidQData.2.1

    have hRayQ'Q' :
        HilbertSameRay
          Geo
          H
          (lineReflect Geo axis Q)
          (lineReflect Geo axis Q) :=
      hilbert_sameRay_refl
        Geo
        H
        (lineReflect Geo axis Q)
        hQ'H

    have hRayQ'P' :
        HilbertSameRay
          Geo
          H
          (lineReflect Geo axis Q)
          (lineReflect Geo axis P) :=
      hilbert_sameRay_symm
        Geo
        H
        (lineReflect Geo axis P)
        (lineReflect Geo axis Q)
        hRayP'Q'

    have hHQ'P' :
        Geo.Between
          H
          (lineReflect Geo axis Q)
          (lineReflect Geo axis P) :=
      hilbert_layoff_shorter_between
        Geo
        H Q P
        H
        (lineReflect Geo axis Q)
        (lineReflect Geo axis Q)
        (lineReflect Geo axis P)
        hHQP
        hRayQ'Q'
        hRayQ'P'
        hHQ'_HQ
        hHP'_HP

    have hQP_Q'P' :
        Geo.Congruent
          Q P
          (lineReflect Geo axis Q)
          (lineReflect Geo axis P) :=
      hilbert_segment_subtraction
        Geo
        H Q P
        H
        (lineReflect Geo axis Q)
        (lineReflect Geo axis P)
        hHQP
        hHQ'P'
        hHQ_HQ'
        hHP_HP'

    exact
      CongruentReverseBoth
        Geo
        Q P
        (lineReflect Geo axis Q)
        (lineReflect Geo axis P)
        hQP_Q'P'

/--
A point on the reflection axis is fixed by the canonical reflection.
-/
theorem lineReflect_fixed_of_on_axis
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point)
    (hPaxis :
      HilbertIncidence.OnLine P axis.carrier) :
    lineReflect Geo axis P = P := by

  rcases lineReflect_spec Geo axis P with hFixed | hOff

  · exact hFixed.2

  · exact False.elim (hOff.1 hPaxis)


/--
Reflection preserves the segment joining two off-axis points having
the same perpendicular foot.
-/
theorem lineReflect_preserves_congruence_same_foot
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q H : Geo.Point)
    (hPerpP :
      PerpendicularToAxis Geo axis H P)
    (hMidP :
      HilbertIsMidpoint
        Geo H P (lineReflect Geo axis P))
    (hPerpQ :
      PerpendicularToAxis Geo axis H Q)
    (hMidQ :
      HilbertIsMidpoint
        Geo H Q (lineReflect Geo axis Q)) :
    Geo.Congruent
      P Q
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q) := by

  have hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier) :=
    hPerpP.2.1

  have hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier) :=
    hPerpQ.2.1

  by_cases hSame :
      HilbertSameSide Geo P Q axis.carrier

  ----------------------------------------------------------------------
  -- Same side: use segment subtraction on the common perpendicular.
  ----------------------------------------------------------------------

  · exact
      lineReflect_preserves_congruence_same_foot_sameSide
        Geo
        axis
        P Q H
        hPerpP
        hMidP
        hPerpQ
        hMidQ
        hSame

  ----------------------------------------------------------------------
  -- Otherwise the two off-axis points are on opposite sides.
  ----------------------------------------------------------------------

  · have hOpp :
        HilbertOppositeSide Geo P Q axis.carrier :=
      hilbert_order_oppositeSide_of_not_sameSide
        Geo
        P Q
        axis.carrier
        hPoff
        hQoff
        hSame

    exact
      lineReflect_preserves_congruence_same_foot_oppositeSide
        Geo
        axis
        P Q H
        hPerpP
        hMidP
        hPerpQ
        hMidQ
        hOpp


/--
Reflection preserves the segment joining two points which are both
off the reflection axis.
-/
theorem lineReflect_preserves_congruence_off_axis
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q : Geo.Point)
    (hPoff :
      Not (HilbertIncidence.OnLine P axis.carrier))
    (hQoff :
      Not (HilbertIncidence.OnLine Q axis.carrier)) :
    Geo.Congruent
      P Q
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q) := by

  rcases
      lineReflect_off_axis_data
        Geo axis P hPoff
    with
    ⟨H, hPerpP, hMidP⟩

  rcases
      lineReflect_off_axis_data
        Geo axis Q hQoff
    with
    ⟨K, hPerpQ, hMidQ⟩

  by_cases hHK : H = K

  ----------------------------------------------------------------------
  -- Common perpendicular foot.
  ----------------------------------------------------------------------

  · subst K

    exact
      lineReflect_preserves_congruence_same_foot
        Geo
        axis
        P Q H
        hPerpP
        hMidP
        hPerpQ
        hMidQ

  ----------------------------------------------------------------------
  -- Distinct perpendicular feet: this was the SAS case proved earlier.
  ----------------------------------------------------------------------

  · exact
      lineReflect_preserves_congruence_distinct_feet
        Geo
        axis
        P Q H K
        hPoff
        hQoff
        hHK
        hPerpP
        hMidP
        hPerpQ
        hMidQ


/--
Canonical line reflection is an isometry in the synthetic Hilbert
sense: it preserves segment congruence.

No numerical distance function is introduced.
-/
theorem lineReflect_preserves_congruence
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P Q : Geo.Point) :
    Geo.Congruent
      P Q
      (lineReflect Geo axis P)
      (lineReflect Geo axis Q) := by

  by_cases hPaxis :
      HilbertIncidence.OnLine P axis.carrier

  ----------------------------------------------------------------------
  -- P lies on the axis.
  ----------------------------------------------------------------------

  · have hFixP :
        lineReflect Geo axis P = P :=
      lineReflect_fixed_of_on_axis
        Geo axis P hPaxis

    by_cases hQaxis :
        HilbertIncidence.OnLine Q axis.carrier

    --------------------------------------------------------------------
    -- Both points lie on the axis: both are fixed.
    --------------------------------------------------------------------

    · have hFixQ :
          lineReflect Geo axis Q = Q :=
        lineReflect_fixed_of_on_axis
          Geo axis Q hQaxis

      rw [hFixP, hFixQ]

      exact
        hilbert_congruent_reflexive
          Geo P Q

    --------------------------------------------------------------------
    -- P is fixed, Q is reflected off the axis.
    -- Every axis point is equidistant from Q and r(Q).
    --------------------------------------------------------------------

    · rw [hFixP]

      exact
        lineReflect_axis_point_equidistant
          Geo
          axis
          Q P
          hPaxis

  ----------------------------------------------------------------------
  -- P lies off the axis.
  ----------------------------------------------------------------------

  · by_cases hQaxis :
        HilbertIncidence.OnLine Q axis.carrier

    --------------------------------------------------------------------
    -- Q is fixed and P is off-axis.
    --------------------------------------------------------------------

    · have hFixQ :
          lineReflect Geo axis Q = Q :=
        lineReflect_fixed_of_on_axis
          Geo axis Q hQaxis

      rw [hFixQ]

      have hQP_QP' :
          Geo.Congruent
            Q P
            Q (lineReflect Geo axis P) :=
        lineReflect_axis_point_equidistant
          Geo
          axis
          P Q
          hQaxis

      exact
        CongruentReverseBoth
          Geo
          Q P
          Q (lineReflect Geo axis P)
          hQP_QP'

    --------------------------------------------------------------------
    -- Both points lie off the axis.
    --------------------------------------------------------------------

    · exact
        lineReflect_preserves_congruence_off_axis
          Geo
          axis
          P Q
          hPaxis
          hQaxis

end Geometry

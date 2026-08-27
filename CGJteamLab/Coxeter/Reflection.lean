import CGJteamLab.Proposition12
import CGJteamLab.HilbertRightAngle

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

structure ReflectionAxis
    [HilbertIncidence Geo] where
  carrier : Geo.Line
  A : Geo.Point
  B : Geo.Point
  hAB : A ≠ B
  hA : HilbertIncidence.OnLine A carrier
  hB : HilbertIncidence.OnLine B carrier

def PerpendicularToAxis
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (H P : Geo.Point) : Prop :=
  HilbertIncidence.OnLine H axis.carrier ∧
  ¬ HilbertIncidence.OnLine P axis.carrier ∧
  ∃ R : Geo.Point,
    HilbertIncidence.OnLine R axis.carrier ∧
    R ≠ H ∧
    HilbertRightAngle Geo R H P

def IsLineReflection
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P P' : Geo.Point) : Prop :=
  (HilbertIncidence.OnLine P axis.carrier ∧ P' = P) ∨
  (¬ HilbertIncidence.OnLine P axis.carrier ∧
    ∃ H : Geo.Point,
      PerpendicularToAxis Geo axis H P ∧
      HilbertIsMidpoint Geo H P P')

/--
Every point has a reflection across a given Hilbert reflection axis.

A point on the axis is fixed.  For a point off the axis, Euclid I.12
provides a perpendicular foot `H`; then `hilbert_extend_segment_beyond`
constructs the opposite endpoint at the same distance from `H`.
-/
theorem line_reflection_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point) :
    ∃ P' : Geo.Point,
      IsLineReflection Geo axis P P' := by

  by_cases hPaxis :
      HilbertIncidence.OnLine P axis.carrier

  ----------------------------------------------------------------------
  -- Point on the mirror: fixed.
  ----------------------------------------------------------------------

  · exact
      ⟨P,
        Or.inl
          ⟨hPaxis, rfl⟩⟩

  ----------------------------------------------------------------------
  -- Point off the mirror.
  ----------------------------------------------------------------------

  · rcases
      hilbert_perpendicular_from_point_exists
        Geo
        axis.A
        axis.B
        P
        axis.carrier
        axis.hAB
        axis.hA
        axis.hB
        hPaxis with
      ⟨H, R, hHaxis, hRaxis, hRight⟩

    --------------------------------------------------------------------
    -- R and H are distinct because R-H-C for the extension point C
    -- contained in the definition of HilbertRightAngle.
    --------------------------------------------------------------------

    have hRH : R ≠ H := by
      rcases hRight with
        ⟨C, hRHC, hAngle⟩

      exact
        (HilbertOrder.between_incidence
          R H C hRHC).1

    --------------------------------------------------------------------
    -- P differs from its perpendicular foot H because P is off the
    -- axis whereas H lies on it.
    --------------------------------------------------------------------

    have hPH : P ≠ H := by
      intro hPH
      apply hPaxis
      rw [hPH]
      exact hHaxis

    --------------------------------------------------------------------
    -- Extend PH beyond H by a congruent segment.
    --------------------------------------------------------------------

    rcases
      hilbert_extend_segment_beyond
        Geo P H hPH with
      ⟨P', hPHP', hPH_HP'⟩

    --------------------------------------------------------------------
    -- Package the perpendicular data.
    --------------------------------------------------------------------

    have hPerp :
        PerpendicularToAxis Geo axis H P :=
      ⟨hHaxis,
        hPaxis,
        ⟨R,
          hRaxis,
          hRH,
          hRight⟩⟩

    --------------------------------------------------------------------
    -- H is the midpoint of P and P'.
    --------------------------------------------------------------------

    have hMid :
        HilbertIsMidpoint Geo H P P' :=
      ⟨hPHP',
        hPH_HP'⟩

    exact
      ⟨P',
        Or.inr
          ⟨hPaxis,
            ⟨H,
              hPerp,
              hMid⟩⟩⟩

/--
Line reflection is symmetric as a geometric relation.

This is the relational form of the Coxeter involution relation:
reflecting P to P' across the same axis also reflects P' back to P.
-/
theorem line_reflection_symmetric
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P P' : Geo.Point)
    (hRef : IsLineReflection Geo axis P P') :
    IsLineReflection Geo axis P' P := by

  rcases hRef with hFixed | hOff

  ----------------------------------------------------------------------
  -- A point on the axis is fixed.
  ----------------------------------------------------------------------

  · rcases hFixed with ⟨hPaxis, hEq⟩
    subst P'
    exact
      Or.inl
        ⟨hPaxis, rfl⟩

  ----------------------------------------------------------------------
  -- Off-axis reflection.
  ----------------------------------------------------------------------

  · rcases hOff with
      ⟨hPoff, H, hPerp, hMid⟩

    rcases hPerp with
      ⟨hHaxis, _hPoffAgain, R, hRaxis, hRH, hRightRHP⟩

    have hPHP' :
        Geo.Between P H P' :=
      hMid.1

    have hBetweenData :=
      HilbertOrder.between_incidence
        P H P' hPHP'

    have hHP' : H ≠ P' :=
      hBetweenData.2.1

    have hPHP'col :
        PrimCollinear Geo P H P' :=
      hBetweenData.2.2.2.1

    --------------------------------------------------------------------
    -- P' is also off the axis.
    --------------------------------------------------------------------

    have hP'off :
        Not (HilbertIncidence.OnLine P' axis.carrier) := by
      intro hP'axis

      have hHP'P :
          PrimCollinear Geo H P' P :=
        PrimCollinearRotate
          Geo H P P'
          (PrimCollinearSwap
            Geo P H P' hPHP'col)

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
    -- R-H-P is noncollinear because R,H are on the axis and P is not.
    --------------------------------------------------------------------

    have hRHPnc :
        Not (PrimCollinear Geo R H P) :=
      hilbert_not_collinear_of_off_line
        Geo
        R H P
        axis.carrier
        hRH
        hRaxis
        hHaxis
        hPoff

    have hPHRnc :
        Not (PrimCollinear Geo P H R) := by
      intro h
      exact
        hRHPnc
          (PrimCollinearSymm
            Geo P H R h)

    --------------------------------------------------------------------
    -- Swap the arms: P-H-R is right as well.
    --------------------------------------------------------------------

    have hSwap :
        Geo.AngleCongruent R H P P H R :=
      bookZero_56_ABCequalsCBA
        Geo
        R H P
        hRHPnc

    have hRightPHR :
        HilbertRightAngle Geo P H R :=
      hilbert_right_angle_transport
        Geo
        R H P
        P H R
        hRHPnc
        hPHRnc
        hRightRHP
        hSwap

    --------------------------------------------------------------------
    -- Since P-H-P', the opposite ray HP' is also perpendicular
    -- to the axis.
    --------------------------------------------------------------------

    have hPHR_RHP' :
        Geo.AngleCongruent P H R R H P' :=
      hilbert_right_angle_opposite_extension
        Geo
        P H R P'
        hPHRnc
        hRightPHR
        hPHP'

    have hRHP'nc :
        Not (PrimCollinear Geo R H P') :=
      hilbert_not_collinear_of_off_line
        Geo
        R H P'
        axis.carrier
        hRH
        hRaxis
        hHaxis
        hP'off

    have hRightRHP' :
        HilbertRightAngle Geo R H P' :=
      hilbert_right_angle_transport
        Geo
        P H R
        R H P'
        hPHRnc
        hRHP'nc
        hRightPHR
        hPHR_RHP'

    have hPerp' :
        PerpendicularToAxis Geo axis H P' :=
      ⟨hHaxis,
        hP'off,
        ⟨R,
          hRaxis,
          hRH,
          hRightRHP'⟩⟩

    --------------------------------------------------------------------
    -- Midpoint symmetry gives H as midpoint of P'P.
    --------------------------------------------------------------------

    have hMid' :
        HilbertIsMidpoint Geo H P' P :=
      MidpointSymmetry
        Geo
        H P P'
        hMid

    exact
      Or.inr
        ⟨hP'off,
          ⟨H,
            hPerp',
            hMid'⟩⟩

/--
The fixed points of a line reflection are exactly the points on its axis.
-/
theorem line_reflection_fixed_iff_on_axis
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point) :
    Iff
      (IsLineReflection Geo axis P P)
      (HilbertIncidence.OnLine P axis.carrier) := by

  constructor

  · intro hRef
    rcases hRef with hFixed | hOff

    · exact hFixed.1

    · rcases hOff with
        ⟨_hPoff, H, _hPerp, hMid⟩

      have hPP : P ≠ P :=
        (HilbertOrder.between_incidence
          P H P hMid.1).2.2.1

      exact False.elim (hPP rfl)

  · intro hPaxis

    exact
      Or.inl
        ⟨hPaxis, rfl⟩


/--
A point off the reflection axis cannot be fixed by the reflection.
-/
theorem line_reflection_moves_off_axis
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P P' : Geo.Point)
    (hPoff : Not (HilbertIncidence.OnLine P axis.carrier))
    (hRef : IsLineReflection Geo axis P P') :
    P' ≠ P := by

  intro hEq
  subst P'

  have hPaxis :
      HilbertIncidence.OnLine P axis.carrier :=
    (line_reflection_fixed_iff_on_axis
      Geo axis P).1 hRef

  exact hPoff hPaxis

/--
Moving the first arm of a right angle along the same ray preserves
rightness.
-/
theorem coxeter_right_angle_sameRay_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A A' O B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B)
    (hRay : HilbertSameRay Geo O A A') :
    HilbertRightAngle Geo A' O B := by

  have hOA' : Not (O = A') := by
    intro h
    apply hRay.2.1
    exact h.symm

  have hA'OB :
      Not (PrimCollinear Geo A' O B) := by
    intro hA'OBcol

    have hAOA' :
        PrimCollinear Geo A O A' :=
      PrimCollinearSwap
        Geo O A A' hRay.2.2.1

    have hOA'B :
        PrimCollinear Geo O A' B :=
      PrimCollinearSwap
        Geo A' O B hA'OBcol

    have hAOBcol :
        PrimCollinear Geo A O B :=
      hilbert_primCollinear_trans
        Geo
        A O A' B
        hOA'
        hAOA'
        hOA'B

    exact hAOB hAOBcol

  have hAngleEq :
      Geo.Angle A O B = Geo.Angle A' O B :=
    hilbert_angle_eq_of_sameRay_first
      Geo O A A' B hRay

  have hRefl :
      Geo.AngleCongruent A O B A O B :=
    Geometry.Geo.angle_congruent_reflexive
      Geo A O B

  have hAngle :
      Geo.AngleCongruent A O B A' O B := by
    unfold Geometry.Geo.AngleCongruent at hRefl
    unfold Geometry.Geo.AngleCongruent
    rw [Eq.symm hAngleEq]
    exact hRefl

  exact
    hilbert_right_angle_transport
      Geo
      A O B
      A' O B
      hAOB
      hA'OB
      hRight
      hAngle


/--
Reversing the first arm of a right angle preserves rightness.
-/
theorem coxeter_right_angle_opposite_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A A' O B : Geo.Point)
    (hAOA' : Geo.Between A O A')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo A' O B := by

  have hRightEq :
      Geo.AngleCongruent A O B B O A' :=
    hilbert_right_angle_opposite_extension
      Geo
      A O B A'
      hAOB
      hRight
      hAOA'

  have hAOB_A'OB :
      Geo.AngleCongruent A O B A' O B :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A O B
      B O A').mp hRightEq

  have hA'OB_AOB :
      Geo.AngleCongruent A' O B A O B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O B
      A' O B
      hAOB_A'OB

  have hA'OB_BOA :
      Geo.AngleCongruent A' O B B O A :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A' O B
      A O B).mp hA'OB_AOB

  have hA'OA :
      Geo.Between A' O A :=
    (HilbertOrder.between_incidence
      A O A' hAOA').2.2.2.2

  exact
    Exists.intro A
      (And.intro hA'OA hA'OB_BOA)


/--
A right angle does not depend on which non-vertex point is chosen
on the carrier of its first arm.
-/
theorem coxeter_right_angle_collinear_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A A' O B : Geo.Point)
    (hOA : Not (O = A))
    (hOA' : Not (O = A'))
    (hCol : PrimCollinear Geo O A A')
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRight : HilbertRightAngle Geo A O B) :
    HilbertRightAngle Geo A' O B := by

  by_cases hAA' : A = A'

  · subst A'
    exact hRight

  · rcases
      hilbert_between_trichotomy
        Geo
        O A A'
        hOA
        hAA'
        hOA'
        hCol
    with
    hOAA' | hAOA' | hOA'A

    -- O-A-A': same ray.
    · have hRay :
          HilbertSameRay Geo O A A' :=
        hilbert_sameRay_of_between
          Geo O A A' hOAA'

      exact
        coxeter_right_angle_sameRay_first
          Geo
          A A' O B
          hAOB
          hRight
          hRay

    -- A-O-A': opposite rays.
    · exact
        coxeter_right_angle_opposite_first
          Geo
          A A' O B
          hAOA'
          hAOB
          hRight

    -- O-A'-A: again the same ray.
    · have hRayA'A :
          HilbertSameRay Geo O A' A :=
        hilbert_sameRay_of_between
          Geo O A' A hOA'A

      have hRayAA' :
          HilbertSameRay Geo O A A' :=
        hilbert_sameRay_symm
          Geo O A' A hRayA'A

      exact
        coxeter_right_angle_sameRay_first
          Geo
          A A' O B
          hAOB
          hRight
          hRayAA'

/--
The perpendicular foot of a point on a fixed reflection axis is unique.

The proof is neutral. If two distinct feet `H` and `K` existed, the
triangle `HKP` would have right angles at both `H` and `K`. Extending
`KH` beyond `H` produces an exterior right angle congruent to the
remote interior right angle at `K`, contradicting Hilbert's
exterior-angle theorem.
-/
theorem perpendicular_foot_unique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P H K : Geo.Point)
    (hPerpH : PerpendicularToAxis Geo axis H P)
    (hPerpK : PerpendicularToAxis Geo axis K P) :
    H = K := by

  rcases hPerpH with
    ⟨hHaxis, hPoff, R, hRaxis, hRH, hRightRHP⟩

  rcases hPerpK with
    ⟨hKaxis, _hPoffK, S, hSaxis, hSK, hRightSKP⟩

  by_contra hHK

  ----------------------------------------------------------------------
  -- At H, replace the arbitrary axis point R by K.
  ----------------------------------------------------------------------

  have hRHPnc :
      Not (PrimCollinear Geo R H P) :=
    hilbert_not_collinear_of_off_line
      Geo
      R H P
      axis.carrier
      hRH
      hRaxis
      hHaxis
      hPoff

  have hHRK :
      PrimCollinear Geo H R K :=
    ⟨axis.carrier,
      hHaxis,
      hRaxis,
      hKaxis⟩

  have hRightKHP :
      HilbertRightAngle Geo K H P :=
    coxeter_right_angle_collinear_first
      Geo
      R K H P
      (Ne.symm hRH)
      hHK
      hHRK
      hRHPnc
      hRightRHP

  ----------------------------------------------------------------------
  -- At K, replace the arbitrary axis point S by H.
  ----------------------------------------------------------------------

  have hSKPnc :
      Not (PrimCollinear Geo S K P) :=
    hilbert_not_collinear_of_off_line
      Geo
      S K P
      axis.carrier
      hSK
      hSaxis
      hKaxis
      hPoff

  have hKSH :
      PrimCollinear Geo K S H :=
    ⟨axis.carrier,
      hKaxis,
      hSaxis,
      hHaxis⟩

  have hRightHKP :
      HilbertRightAngle Geo H K P :=
    coxeter_right_angle_collinear_first
      Geo
      S H K P
      (Ne.symm hSK)
      (Ne.symm hHK)
      hKSH
      hSKPnc
      hRightSKP

  ----------------------------------------------------------------------
  -- Triangle HKP is nondegenerate.
  ----------------------------------------------------------------------

  have hHKPnc :
      Not (PrimCollinear Geo H K P) :=
    hilbert_not_collinear_of_off_line
      Geo
      H K P
      axis.carrier
      hHK
      hHaxis
      hKaxis
      hPoff

  have hKHPnc :
      Not (PrimCollinear Geo K H P) := by
    intro h
    exact
      hHKPnc
        (PrimCollinearSwap
          Geo K H P h)

  ----------------------------------------------------------------------
  -- Extend KH beyond H.
  ----------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        K H (Ne.symm hHK)
    with
    ⟨T, hKHT⟩

  have hKHTdata :=
    HilbertOrder.between_incidence
      K H T hKHT

  have hHT :
      H ≠ T :=
    hKHTdata.2.1

  have hTaxis :
      HilbertIncidence.OnLine T axis.carrier :=
    hilbert_collinear_on_line
      Geo
      K H T
      axis.carrier
      (Ne.symm hHK)
      hKaxis
      hHaxis
      hKHTdata.2.2.2.1

  ----------------------------------------------------------------------
  -- The exterior angle PHT is also right.
  ----------------------------------------------------------------------

  have hKHP_PHT :
      Geo.AngleCongruent K H P P H T :=
    hilbert_right_angle_opposite_extension
      Geo
      K H P T
      hKHPnc
      hRightKHP
      hKHT

  have hHTPnc :
      Not (PrimCollinear Geo H T P) :=
    hilbert_not_collinear_of_off_line
      Geo
      H T P
      axis.carrier
      hHT
      hHaxis
      hTaxis
      hPoff

  have hPHTnc :
      Not (PrimCollinear Geo P H T) := by
    intro h
    exact
      hHTPnc
        (PrimCollinearCycle
          Geo P H T h)

  have hRightPHT :
      HilbertRightAngle Geo P H T :=
    hilbert_right_angle_transport
      Geo
      K H P
      P H T
      hKHPnc
      hPHTnc
      hRightKHP
      hKHP_PHT

  ----------------------------------------------------------------------
  -- Hence the exterior right angle PHT is congruent to the remote
  -- interior right angle HKP.
  ----------------------------------------------------------------------

  have hCong :
      Geo.AngleCongruent P H T H K P :=
    hilbert_all_right_angles_congruent
      Geo
      P H T
      H K P
      hPHTnc
      hHKPnc
      hRightPHT
      hRightHKP

  ----------------------------------------------------------------------
  -- But Hilbert's exterior-angle theorem says precisely that these
  -- two angles cannot be congruent.
  ----------------------------------------------------------------------

  exact
    (hilbert_exterior_angle_not_congruent_other
      Geo
      H K P T
      hHKPnc
      hKHT)
      hCong

/--
A reflected point across a fixed Hilbert reflection axis is unique.

For points off the axis, the perpendicular foot is unique. Once the
common foot is identified, both reflected points lie on the same ray
from `P` through that foot and have the same total distance from `P`;
Hilbert segment-construction uniqueness then identifies them.
-/
theorem line_reflection_unique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P P₁ P₂ : Geo.Point)
    (hRef₁ : IsLineReflection Geo axis P P₁)
    (hRef₂ : IsLineReflection Geo axis P P₂) :
    P₁ = P₂ := by

  rcases hRef₁ with hFixed₁ | hOff₁
  · rcases hRef₂ with hFixed₂ | hOff₂

    -- Both are fixed points on the axis.
    · calc
        P₁ = P := hFixed₁.2
        _ = P₂ := Eq.symm hFixed₂.2

    -- First fixed, second off-axis: impossible.
    · exact
        False.elim
          (hOff₂.1 hFixed₁.1)

  · rcases hRef₂ with hFixed₂ | hOff₂

    -- First off-axis, second fixed: impossible.
    · exact
        False.elim
          (hOff₁.1 hFixed₂.1)

    -- Both are genuine off-axis reflections.
    · rcases hOff₁ with
        ⟨hPoff₁, H, hPerpH, hMid₁⟩

      rcases hOff₂ with
        ⟨_hPoff₂, K, hPerpK, hMid₂⟩

      ------------------------------------------------------------------
      -- The perpendicular foot is unique.
      ------------------------------------------------------------------

      have hHK : H = K :=
        perpendicular_foot_unique
          Geo
          axis
          P H K
          hPerpH
          hPerpK

      subst K

      ------------------------------------------------------------------
      -- Both reflected points lie on the same ray from P through H.
      ------------------------------------------------------------------

      have hRay₁ :
          HilbertSameRay Geo P H P₁ :=
        hilbert_sameRay_of_between
          Geo P H P₁ hMid₁.1

      have hRay₂ :
          HilbertSameRay Geo P H P₂ :=
        hilbert_sameRay_of_between
          Geo P H P₂ hMid₂.1

      ------------------------------------------------------------------
      -- HP₁ ~= HP₂, since both are congruent to PH.
      ------------------------------------------------------------------

      have hHP₁_PH :
          Geo.Congruent H P₁ P H :=
        hilbert_congruent_symmetry
          Geo
          P H
          H P₁
          hMid₁.2

      have hHP₁_HP₂ :
          Geo.Congruent H P₁ H P₂ :=
        hilbert_congruent_transitivity
          Geo
          H P₁
          P H
          H P₂
          hHP₁_PH
          hMid₂.2

      ------------------------------------------------------------------
      -- Therefore PP₁ ~= PP₂ by segment additivity:
      --
      --        P --- H --- P₁
      --        P --- H --- P₂
      ------------------------------------------------------------------

      have hPP₁_PP₂ :
          Geo.Congruent P P₁ P P₂ :=
        HilbertCongruence.segment_additivity
          (Geo := Geo)
          P H P₁
          P H P₂
          hMid₁.1
          hMid₂.1
          (hilbert_congruent_reflexive Geo P H)
          hHP₁_HP₂

      have hPP₂_PP₁ :
          Geo.Congruent P P₂ P P₁ :=
        hilbert_congruent_symmetry
          Geo
          P P₁
          P P₂
          hPP₁_PP₂

      ------------------------------------------------------------------
      -- Segment construction on the prescribed ray is unique.
      ------------------------------------------------------------------

      exact
        hilbert_segment_construction_unique
          Geo
          P P₁
          P H
          P₁ P₂
          hRay₁
          hRay₂
          (hilbert_congruent_reflexive Geo P P₁)
          hPP₂_PP₁

/--
The reflected point across a fixed Hilbert reflection axis.

Existence and uniqueness have already been proved, so the relation
`IsLineReflection` now determines an actual point transformation.
-/
noncomputable def lineReflect
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point) :
    Geo.Point :=
  Classical.choose
    (line_reflection_exists Geo axis P)


/--
The point selected by `lineReflect` satisfies the geometric
reflection relation.
-/
theorem lineReflect_spec
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point) :
    IsLineReflection Geo axis P
      (lineReflect Geo axis P) :=
  Classical.choose_spec
    (line_reflection_exists Geo axis P)


/--
Reflection in a line is an involution.

This is the first Coxeter relation in literal operator form:

    r_axis * r_axis = 1.
-/
theorem lineReflect_involutive
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point) :
    lineReflect Geo axis
        (lineReflect Geo axis P) = P := by

  have hForward :
      IsLineReflection Geo axis
        P
        (lineReflect Geo axis P) :=
    lineReflect_spec
      Geo axis P

  have hBack :
      IsLineReflection Geo axis
        (lineReflect Geo axis P)
        P :=
    line_reflection_symmetric
      Geo
      axis
      P
      (lineReflect Geo axis P)
      hForward

  have hCanonical :
      IsLineReflection Geo axis
        (lineReflect Geo axis P)
        (lineReflect Geo axis
          (lineReflect Geo axis P)) :=
    lineReflect_spec
      Geo
      axis
      (lineReflect Geo axis P)

  have hUnique :
      P =
        lineReflect Geo axis
          (lineReflect Geo axis P) :=
    line_reflection_unique
      Geo
      axis
      (lineReflect Geo axis P)
      P
      (lineReflect Geo axis
        (lineReflect Geo axis P))
      hBack
      hCanonical

  exact Eq.symm hUnique

/--
Reflection in a Hilbert line, viewed as a permutation of the point set.

The inverse is the same reflection, by involutivity.
-/
noncomputable def lineReflectEquiv
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo) :
    Equiv Geo.Point Geo.Point where
  toFun := lineReflect Geo axis
  invFun := lineReflect Geo axis
  left_inv := lineReflect_involutive Geo axis
  right_inv := lineReflect_involutive Geo axis


@[simp]
theorem lineReflectEquiv_apply
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point) :
    lineReflectEquiv Geo axis P =
      lineReflect Geo axis P := by
  rfl


@[simp]
theorem lineReflectEquiv_apply_twice
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (axis : ReflectionAxis Geo)
    (P : Geo.Point) :
    lineReflectEquiv Geo axis
      (lineReflectEquiv Geo axis P) = P := by
  exact lineReflect_involutive Geo axis P

end Geometry

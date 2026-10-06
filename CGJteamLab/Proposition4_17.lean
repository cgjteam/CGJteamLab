import CGJteamLab.HilbertInterfaceIV
import CGJteamLab.Proposition4_16

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid/Forder IV.17

Production module for Book IV proposition 17 and its local proof support.
Stage-labelled declarations below are private implementation details; the public
entry points use production names.
-/

private theorem hilbert_IV17_sameRay_secant_impossible_stage57
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R X A Y T S : Geo.Point)
    (chord : Geo.Line)
    (hXA : Ne X A)
    (hXchord : H.OnLine X chord)
    (hAchord : H.OnLine A chord)
    (hXcircle : HilbertCircle Geo K R X)
    (hAcircle : HilbertCircle Geo K R A)
    (hYcircle : HilbertCircle Geo K R Y)
    (hScircle : HilbertCircle Geo K R S)
    (hOppTY : HilbertOppositeSide Geo T Y chord)
    (hAngle :
      Geo.AngleCongruent X A T X Y A)
    (hRayAST :
      HilbertSameRay Geo A S T) :
    False := by

  --------------------------------------------------------------------
  -- Carrier of the common ray AS = AT.
  --------------------------------------------------------------------

  rcases hRayAST.2.2.1 with
    ⟨lineAS, hAline, hSline, hTline⟩

  have hAS :
      Ne A S :=
    hRayAST.1.symm

  have hSA :
      Ne S A :=
    hRayAST.1

  have hXoffAS :
      Not (H.OnLine X lineAS) := by
    intro hXline

    have hEq :
        lineAS = chord :=
      HilbertPlaneIncidence.line_unique
        X A hXA
        lineAS chord
        hXline hAline
        hXchord hAchord

    have hTchord :
        H.OnLine T chord := by
      rw [← hEq]
      exact hTline

    exact hOppTY.1 hTchord

  --------------------------------------------------------------------
  -- S and T are on the same side of chord AX.
  --------------------------------------------------------------------

  have hRayASS :
      HilbertSameRay Geo A S S :=
    hilbert_sameRay_refl
      Geo A S hSA

  have hSameST :
      HilbertSameSide Geo S T chord :=
    hilbert_sameRay_points_sameSide
      Geo
      A S
      S T
      X
      lineAS chord
      hAline hSline
      hAchord hXchord
      hXoffAS
      hRayASS
      hRayAST

  --------------------------------------------------------------------
  -- T opposite Y and T same-side S imply S opposite Y.
  --------------------------------------------------------------------

  have hOppYT :
      HilbertOppositeSide Geo Y T chord :=
    hilbert_oppositeSide_symm
      Geo T Y chord hOppTY

  have hSameTS :
      HilbertSameSide Geo T S chord :=
    hilbert_sameSide_symm
      Geo S T chord hSameST

  have hOppYS :
      HilbertOppositeSide Geo Y S chord :=
    hilbert_oppositeSide_transport_right
      Geo
      Y T S
      chord
      hOppYT
      hSameTS

  have hOppSY :
      HilbertOppositeSide Geo S Y chord :=
    hilbert_oppositeSide_symm
      Geo Y S chord hOppYS

  --------------------------------------------------------------------
  -- IV.16 opposite-side:
  --
  -- XSA is congruent to a supplement UYA of XYA.
  --------------------------------------------------------------------

  rcases
      hilbert_IV16_opposite_side
        Geo
        K R X A S Y
        chord
        hXA
        hXchord
        hAchord
        hXcircle
        hAcircle
        hScircle
        hYcircle
        hOppSY
    with
    ⟨U, hSuppY, hXSA_UYA⟩

  --------------------------------------------------------------------
  -- Since AS and AT are the same ray:
  --
  --   XAS ~= XAT ~= XYA,
  --
  -- hence SAX ~= XYA.
  --------------------------------------------------------------------

  have hXAS_eq_XAT :
      Geo.Angle X A S =
      Geo.Angle X A T :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      A X S T
      hRayAST

  have hXAS_XYA :
      Geo.AngleCongruent X A S X Y A := by
    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢
    rw [hXAS_eq_XAT]
    exact hAngle

  have hSAX_XYA :
      Geo.AngleCongruent S A X X Y A :=
    (Geo.angle_congruent_reverse_first
      X A S
      X Y A).mp
      hXAS_XYA

  --------------------------------------------------------------------
  -- Construct the supplement of SAX by extending SA through A:
  --
  --   S-A-V.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        S A hSA
    with
    ⟨V, hSAV⟩

  have hRayAXX :
      HilbertSameRay Geo A X X :=
    hilbert_sameRay_refl
      Geo A X hXA

  have hSuppA :
      BookZeroSupplement Geo
        S A X
        X V :=
    ⟨hRayAXX, hSAV⟩

  --------------------------------------------------------------------
  -- Properness of the two base angles.
  --------------------------------------------------------------------

  have hSAX :
      Not (PrimCollinear Geo S A X) :=
    hilbert_not_collinear_of_off_line
      Geo
      S A X
      lineAS
      hSA
      hSline
      hAline
      hXoffAS

  have hYoff :
      Not (H.OnLine Y chord) :=
    hOppTY.2.1

  have hXYA :
      Not (PrimCollinear Geo X Y A) := by
    intro h

    have hXAY :
        PrimCollinear Geo X A Y :=
      PrimCollinearRotate
        Geo X Y A h

    exact
      (hilbert_not_collinear_of_off_line
        Geo
        X A Y
        chord
        hXA
        hXchord
        hAchord
        hYoff)
        hXAY

  --------------------------------------------------------------------
  -- Supplements of congruent angles SAX ~= XYA are congruent:
  --
  --   XAV ~= AYU.
  --------------------------------------------------------------------

  have hXAV_AYU :
      Geo.AngleCongruent X A V A Y U :=
    bookZero_43_supplements
      Geo
      S A X
      X V
      X Y A
      A U
      hSAX_XYA
      hSuppA
      hSuppY
      hSAX
      hXYA

  have hXAV_UYA :
      Geo.AngleCongruent X A V U Y A :=
    (Geo.angle_congruent_reverse_second
      X A V
      A Y U).mp
      hXAV_AYU

  --------------------------------------------------------------------
  -- IV.16 gave XSA ~= UYA, so XSA ~= XAV.
  --------------------------------------------------------------------

  have hUYA_XSA :
      Geo.AngleCongruent U Y A X S A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X S A
      U Y A
      hXSA_UYA

  have hXAV_XSA :
      Geo.AngleCongruent X A V X S A :=
    Geo.angle_congruent_transitivity
      X A V
      U Y A
      X S A
      hXAV_UYA
      hUYA_XSA

  have hXSA_XAV :
      Geo.AngleCongruent X S A X A V :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X A V
      X S A
      hXAV_XSA

  --------------------------------------------------------------------
  -- Contradiction with stage 56 (Euclid I.17).
  --------------------------------------------------------------------

  exact
    (hilbert_triangle_angle_not_supplement
      Geo
      X S A V
      (by
        intro h
        exact
          hSAX
            (PrimCollinearCycle
              Geo X S A h))
      hSAV)
      hXSA_XAV

private theorem hilbert_IV17_oppositeRay_secant_impossible_stage58
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R X A Y T S : Geo.Point)
    (chord : Geo.Line)
    (hXA : Ne X A)
    (hXchord : H.OnLine X chord)
    (hAchord : H.OnLine A chord)
    (hXcircle : HilbertCircle Geo K R X)
    (hAcircle : HilbertCircle Geo K R A)
    (hYcircle : HilbertCircle Geo K R Y)
    (hScircle : HilbertCircle Geo K R S)
    (hOppTY : HilbertOppositeSide Geo T Y chord)
    (hAngle :
      Geo.AngleCongruent X A T X Y A)
    (hSAT :
      Geo.Between S A T) :
    False := by

  --------------------------------------------------------------------
  -- S is opposite T across chord AX or same-side with Y.
  --
  -- Because S-A-T and A lies on the chord, S and T are opposite
  -- sides of the chord.
  --------------------------------------------------------------------

  have hSATdata :=
    HilbertOrder.between_incidence
      S A T hSAT

  have hSA :
      Ne S A :=
    hSATdata.1

  have hAT :
      Ne A T :=
    hSATdata.2.1

  have hSATcol :
      PrimCollinear Geo S A T :=
    hSATdata.2.2.2.1

  have hSoff :
      Not (H.OnLine S chord) := by
    intro hSchord

    have hTchord :
        H.OnLine T chord :=
      hilbert_collinear_on_line
        Geo
        S A T
        chord
        hSA
        hSchord
        hAchord
        hSATcol

    exact hOppTY.1 hTchord

  have hToff :
      Not (H.OnLine T chord) :=
    hOppTY.1

  have hOppST :
      HilbertOppositeSide Geo S T chord :=
    ⟨hSoff,
      hToff,
      ⟨A, hSAT, hAchord⟩⟩

  have hOppTS :
      HilbertOppositeSide Geo T S chord :=
    hilbert_oppositeSide_symm
      Geo S T chord hOppST

  --------------------------------------------------------------------
  -- T is opposite both S and Y across chord XA.
  -- Stage 51 converts the two opposite-side relations into S,Y
  -- being on the same side.
  --------------------------------------------------------------------

  have hSameSY :
      HilbertSameSide Geo S Y chord :=
    hilbert_two_opposites_sameSide_with_carrier
      Geo
      T S Y X A
      chord
      hXA
      hXchord
      hAchord
      hOppTS
      hOppTY

  --------------------------------------------------------------------
  -- IV.16 same-side gives angle XSA ~= XYA.
  --------------------------------------------------------------------

  have hXS :
      Ne X S := by
    intro hXS
    subst S

    exact
      hSoff hXchord

  rcases
      HilbertPlaneIncidence.line_through
        X A hXA
    with
    ⟨lineXA, hXlineXA, hAlineXA⟩

  have hLineEq :
      lineXA = chord :=
    HilbertPlaneIncidence.line_unique
      X A hXA
      lineXA chord
      hXlineXA hAlineXA
      hXchord hAchord

  have hSameSY' :
      HilbertSameSide Geo S Y lineXA := by
    rw [hLineEq]
    exact hSameSY

  have hXSA_XYA :
      Geo.AngleCongruent X S A X Y A :=
    hilbert_IV16_same_side
      Geo
      K R
      X A S Y
      lineXA
      hXA
      hXlineXA
      hAlineXA
      hXcircle
      hAcircle
      hScircle
      hYcircle
      hSameSY'

  --------------------------------------------------------------------
  -- Hence XSA ~= XAT.
  --------------------------------------------------------------------

  have hXYA_XAT :
      Geo.AngleCongruent X Y A X A T :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X A T
      X Y A
      hAngle

  have hXSA_XAT :
      Geo.AngleCongruent X S A X A T :=
    Geo.angle_congruent_transitivity
      X S A
      X Y A
      X A T
      hXSA_XYA
      hXYA_XAT

  --------------------------------------------------------------------
  -- But XAT is the exterior angle of triangle XSA.
  --------------------------------------------------------------------

  have hXSA :
      Not (PrimCollinear Geo X S A) := by
    intro h

    rcases
        HilbertPlaneIncidence.line_through
          S A
          hSA
      with
      ⟨l, hSl, hAl⟩

    have hXl :
        H.OnLine X l :=
      hilbert_collinear_on_line
        Geo
        S A X
        l
        hSA
        hSl
        hAl
        (PrimCollinearCycle
          Geo X S A h)

    have hEq :
        l = chord :=
      HilbertPlaneIncidence.line_unique
        X A hXA
        l chord
        hXl hAl
        hXchord hAchord

    exact hSoff (hEq ▸ hSl)

  have hASX :
      Not (PrimCollinear Geo A S X) := by
    intro h
    exact
      hXSA
        (PrimCollinearSymm
          Geo A S X h)

  have hXAT_ASX :
      Geo.AngleCongruent X A T A S X :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A S X
      X A T
      ((Geo.angle_congruent_reverse_first
        X S A
        X A T).mp
        hXSA_XAT)

  exact
    (hilbert_exterior_angle_not_congruent_other
      Geo
      A S X T
      hASX
      hSAT)
      hXAT_ASX

private theorem hilbert_forder_IV17_tangent_converse_stage59
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV17TangentConverse
      (Geo := Geo) := by

  intro K R X A Y T chord tangent
    hXA hXchord hAchord hAtangent hTtangent hTA
    hXcircle hAcircle hYcircle hOppTY hAngle

  --------------------------------------------------------------------
  -- The circle center differs from A.
  --------------------------------------------------------------------

  have hKX_KA :
      Geo.Congruent K X K A :=
    hilbert_congruent_transitivity
      Geo
      K X
      K R
      K A
      hXcircle
      (hilbert_congruent_symmetry
        Geo
        K A
        K R
        hAcircle)

  have hKA :
      Ne K A := by
    intro hKAeq
    subst K

    have hAX_AA :
        Geo.Congruent A X A A :=
      hKX_KA

    have hAXeq :
        A = X :=
      bookZero_nullSegment1
        Geo A X A hAX_AA

    exact hXA hAXeq.symm

  --------------------------------------------------------------------
  -- Analyze line AT through the circle point A.
  --------------------------------------------------------------------

  rcases
      hilbert_circle_line_second_or_tangent
        Geo
        K R
        A T
        tangent
        hAcircle
        hKA
        hTA.symm
        hAtangent
        hTtangent
    with
    hSecant | hTangent

  --------------------------------------------------------------------
  -- Tangent alternative: exactly the conclusion.
  --------------------------------------------------------------------

  · rcases hSecant with
      ⟨S, hSA, hStangent, hScircle⟩

    by_cases hST :
        S = T

    --------------------------------------------------------------
    -- The second circle point is T itself.
    --------------------------------------------------------------

    · subst S

      have hRayATT :
          HilbertSameRay Geo A T T :=
        hilbert_sameRay_refl
          Geo A T hTA

      exact
        False.elim
          (hilbert_IV17_sameRay_secant_impossible_stage57
            Geo
            K R
            X A Y T T
            chord
            hXA
            hXchord
            hAchord
            hXcircle
            hAcircle
            hYcircle
            hScircle
            hOppTY
            hAngle
            hRayATT)

    --------------------------------------------------------------
    -- Distinct S,T: normalize their order on line AT.
    --------------------------------------------------------------

    · rcases
          hilbert_secant_ray_order_split
            Geo
            A T S
            tangent
            hTA.symm
            (by
              intro hTS
              exact hST hTS.symm)
            hSA.symm
            hAtangent
            hTtangent
            hStangent
        with
        hRayATS | hTAS

      ------------------------------------------------------------
      -- S lies on the same ray AT.
      ------------------------------------------------------------

      · exact
          False.elim
            (hilbert_IV17_sameRay_secant_impossible_stage57
              Geo
              K R
              X A Y T S
              chord
              hXA
              hXchord
              hAchord
              hXcircle
              hAcircle
              hYcircle
              hScircle
              hOppTY
              hAngle
              (hilbert_sameRay_symm
                Geo A T S hRayATS))

      ------------------------------------------------------------
      -- T-A-S, hence S-A-T.
      ------------------------------------------------------------

      · have hSAT :
            Geo.Between S A T :=
          (HilbertOrder.between_incidence
            T A S hTAS).2.2.2.2

        exact
          False.elim
            (hilbert_IV17_oppositeRay_secant_impossible_stage58
              Geo
              K R
              X A Y T S
              chord
              hXA
              hXchord
              hAchord
              hXcircle
              hAcircle
              hYcircle
              hScircle
              hOppTY
              hAngle
              hSAT)

  · exact hTangent

theorem hilbert_IV17_tangent_converse
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV17TangentConverse (Geo := Geo) :=
  hilbert_forder_IV17_tangent_converse_stage59 Geo

end Geometry

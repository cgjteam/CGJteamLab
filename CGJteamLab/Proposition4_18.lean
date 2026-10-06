import CGJteamLab.HilbertInterfaceIV
import CGJteamLab.Proposition4_17

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid/Forder IV.18

Production module for Book IV proposition 18 and its local proof support.
Stage-labelled declarations below are private implementation details; the public
entry points use production names.
-/

private theorem hilbert_forder_IV18_tangent_chord_stage61
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV18TangentChord
      (Geo := Geo) := by

  intro K R X A Y T chord tangent
    hXA hXchord hAchord
    hAtangent hTtangent hTA
    hXcircle hAcircle hYcircle
    hTan hOppTY

  --------------------------------------------------------------------
  -- T and Y are off chord AX.
  --------------------------------------------------------------------

  have hToff :
      Not (H.OnLine T chord) :=
    hOppTY.1

  have hYoff :
      Not (H.OnLine Y chord) :=
    hOppTY.2.1

  --------------------------------------------------------------------
  -- X,Y,A form a genuine angle.
  --------------------------------------------------------------------

  have hXAY :
      Not (PrimCollinear Geo X A Y) :=
    hilbert_not_collinear_of_off_line
      Geo
      X A Y
      chord
      hXA
      hXchord
      hAchord
      hYoff

  have hXYA :
      Not (PrimCollinear Geo X Y A) := by
    intro h
    exact
      hXAY
        (PrimCollinearRotate
          Geo X Y A h)

  --------------------------------------------------------------------
  -- Hilbert III.4:
  -- copy angle XYA at A on the side of chord AX containing T.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        X Y A
        X A T
        hXYA
        hXA
        chord
        hXchord
        hAchord
        hToff
    with
    ⟨T', hT'TSame, hXYA_XAT', _hUnique⟩

  have hT'off :
      Not (H.OnLine T' chord) :=
    hT'TSame.1

  have hT'A :
      Ne T' A := by
    intro hEq
    subst T'
    exact hT'off hAchord

  have hAT' :
      Ne A T' :=
    hT'A.symm

  --------------------------------------------------------------------
  -- T' is opposite Y because T' is on the same side as T.
  --------------------------------------------------------------------

  have hTT'Same :
      HilbertSameSide Geo T T' chord :=
    hilbert_sameSide_symm
      Geo T' T chord hT'TSame

  have hOppYT :
      HilbertOppositeSide Geo Y T chord :=
    hilbert_oppositeSide_symm
      Geo T Y chord hOppTY

  have hOppYT' :
      HilbertOppositeSide Geo Y T' chord :=
    hilbert_oppositeSide_transport_right
      Geo
      Y T T'
      chord
      hOppYT
      hTT'Same

  have hOppT'Y :
      HilbertOppositeSide Geo T' Y chord :=
    hilbert_oppositeSide_symm
      Geo Y T' chord hOppYT'

  --------------------------------------------------------------------
  -- Carrier of the constructed ray AT'.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A T' hAT'
    with
    ⟨tangent', hAtangent', hT'tangent'⟩

  have hXAT'_XYA :
      Geo.AngleCongruent X A T' X Y A :=
    Geo.angle_congruent_symmetry
      X Y A
      X A T'
      hXYA_XAT'

  --------------------------------------------------------------------
  -- IV.17: the constructed line AT' is tangent.
  --------------------------------------------------------------------

  have hTan' :
      HilbertCircleTangentAt
        (Geo := Geo) K A tangent' :=
    hilbert_IV17_tangent_converse
      Geo
      K R X A Y T'
      chord tangent'
      hXA
      hXchord
      hAchord
      hAtangent'
      hT'tangent'
      hT'A
      hXcircle
      hAcircle
      hYcircle
      hOppT'Y
      hXAT'_XYA

  --------------------------------------------------------------------
  -- Uniqueness of tangent carrier.
  --------------------------------------------------------------------

  have hTangents :
      tangent = tangent' :=
    hilbert_circle_tangent_carrier_unique
      Geo
      K A
      tangent tangent'
      hAtangent
      hAtangent'
      hTan
      hTan'

  have hT'tangent :
      H.OnLine T' tangent := by
    rw [hTangents]
    exact hT'tangent'

  --------------------------------------------------------------------
  -- T and T' are on the same ray from A.
  --
  -- They are collinear on the tangent.  If A were between them,
  -- segment TT' would meet chord AX at A, contradicting same-side.
  --------------------------------------------------------------------

  have hATT' :
      PrimCollinear Geo A T T' :=
    ⟨tangent,
      hAtangent,
      hTtangent,
      hT'tangent⟩

  have hNotTAT' :
      Not (Geo.Between T A T') := by
    intro hTAT'

    have hOppTT' :
        HilbertOppositeSide Geo T T' chord :=
      ⟨hToff,
       hT'off,
       ⟨A, hTAT', hAchord⟩⟩

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo T T' chord hOppTT')
        hTT'Same

  have hRayATT' :
      HilbertSameRay Geo A T T' :=
    ⟨hTA,
     hT'A,
     hATT',
     hNotTAT'⟩

  --------------------------------------------------------------------
  -- Replace T' by T on the same ray.
  --------------------------------------------------------------------

  have hAngleXAT_XAT' :
      Geo.Angle X A T =
      Geo.Angle X A T' :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      A X T T'
      hRayATT'

  unfold Geometry.Geo.AngleCongruent
    at hXAT'_XYA ⊢

  rw [hAngleXAT_XAT']
  exact hXAT'_XYA

theorem hilbert_IV18_tangent_chord
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H] :
    HilbertForderIV18TangentChord (Geo := Geo) :=
  hilbert_forder_IV18_tangent_chord_stage61 Geo

end Geometry

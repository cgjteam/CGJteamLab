import CGJteamLab.HilbertInterfaceXI
import CGJteamLab.Proposition12
import CGJteamLab.Proposition32
import CGJteamLab.HilbertAngleDecomposition
import CGJteamLab.Proposition16
import CGJteamLab.Proposition19
import CGJteamLab.Proposition2_13
import CGJteamLab.Proposition17
import CGJteamLab.HilbertThreeAnglesFourRightCyclic

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Hilbert interface for Forder Book IV circle geometry

This file contains the reusable public predicates for the circle theorems
used in the crossing-circle development.  Proofs of the numbered theorems
remain in their theorem modules.
-/

/--
A line through A is tangent to the circle with center K when some non-A
point T on the line determines a genuine, nondegenerate right angle TAK.
-/
def HilbertCircleTangentAt
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (K A : Geo.Point)
    (line : Geo.Line) : Prop :=
  exists T : Geo.Point,
    H.OnLine T line /\
    Ne T A /\
    Not (PrimCollinear Geo T A K) /\
    HilbertRightAngle Geo T A K

/--
Forder IV.12 in synthetic half-angle form.
-/
def HilbertForderIV12CentralHalf
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H] : Prop :=
  forall K R A B C : Geo.Point,
    forall chord : Geo.Line,
      Ne A B ->
      H.OnLine A chord ->
      H.OnLine B chord ->
      HilbertCircle Geo K R A ->
      HilbertCircle Geo K R B ->
      HilbertCircle Geo K R C ->
      HilbertSameSide Geo C K chord ->
      exists T : Geo.Point,
        HilbertRayMeetsSegment Geo K T A B /\
        Geo.AngleCongruent A K T B K T /\
        Geo.AngleCongruent A C B A K T

/--
Forder IV.12.1: equal angles in the same segment.
-/
def HilbertForderIV12_1SameSegment
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H] : Prop :=
  forall K R A B C D : Geo.Point,
    forall chord : Geo.Line,
      Ne A B ->
      H.OnLine A chord ->
      H.OnLine B chord ->
      HilbertCircle Geo K R A ->
      HilbertCircle Geo K R B ->
      HilbertCircle Geo K R C ->
      HilbertCircle Geo K R D ->
      HilbertSameSide Geo C K chord ->
      HilbertSameSide Geo D K chord ->
      Geo.AngleCongruent A C B A D B

/--
Forder IV.13: an angle in a semicircle is right.
-/
def HilbertForderIV13DiameterRightAngle
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H] : Prop :=
  forall K R A B C : Geo.Point,
    forall chord : Geo.Line,
      Ne A B ->
      H.OnLine A chord ->
      H.OnLine B chord ->
      H.OnLine K chord ->
      HilbertCircle Geo K R A ->
      HilbertCircle Geo K R B ->
      HilbertCircle Geo K R C ->
      Not (H.OnLine C chord) ->
      HilbertRightAngle Geo A C B

/--
Corrected crossing-rays angle transfer used by Hilbert Supplement II.
-/
def HilbertCrossingRaysTransfer
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo] : Prop :=
  forall O A C B D : Geo.Point,
    Not (PrimCollinear Geo A O B) ->
    HilbertSameRay Geo O A C ->
    HilbertSameRay Geo O B D ->
    Geo.AngleCongruent O A D O B C ->
    Geo.AngleCongruent O D C O A B

/--
Forder IV.15: opposite angles of a cyclic quadrilateral are supplementary.
-/
def HilbertForderIV15CyclicSupplement
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H] : Prop :=
  forall A B C D : Geo.Point,
    forall diagonal : Geo.Line,
      Ne B D ->
      H.OnLine B diagonal ->
      H.OnLine D diagonal ->
      HilbertConcyclic4 Geo A B C D ->
      HilbertOppositeSide Geo A C diagonal ->
      Not (PrimCollinear Geo B A D) ->
      Not (PrimCollinear Geo B C D) ->
      exists X : Geo.Point,
        BookZeroSupplement Geo
          B C D
          D X /\
        Geo.AngleCongruent
          B A D
          X C D

/--
Forder IV.16, same-side half.
-/
def HilbertForderIV16SameSide
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H] : Prop :=
  forall K R A B C E : Geo.Point,
    forall chord : Geo.Line,
      Ne A B ->
      H.OnLine A chord ->
      H.OnLine B chord ->
      HilbertCircle Geo K R A ->
      HilbertCircle Geo K R B ->
      HilbertCircle Geo K R C ->
      HilbertCircle Geo K R E ->
      HilbertSameSide Geo C E chord ->
      Geo.AngleCongruent
        A C B
        A E B

/--
Forder IV.16, opposite-side half, in supplement form.
-/
def HilbertForderIV16OppositeSide
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H] : Prop :=
  forall K R A B C E : Geo.Point,
    forall chord : Geo.Line,
      Ne A B ->
      H.OnLine A chord ->
      H.OnLine B chord ->
      HilbertCircle Geo K R A ->
      HilbertCircle Geo K R B ->
      HilbertCircle Geo K R C ->
      HilbertCircle Geo K R E ->
      HilbertOppositeSide Geo C E chord ->
      exists X : Geo.Point,
        BookZeroSupplement Geo
          A E B
          B X /\
        Geo.AngleCongruent
          A C B
          X E B

/--
Forder IV.17: tangent converse.
-/
def HilbertForderIV17TangentConverse
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H] : Prop :=
  forall K R X A Y T : Geo.Point,
    forall chord tangent : Geo.Line,
      Ne X A ->
      H.OnLine X chord ->
      H.OnLine A chord ->
      H.OnLine A tangent ->
      H.OnLine T tangent ->
      Ne T A ->
      HilbertCircle Geo K R X ->
      HilbertCircle Geo K R A ->
      HilbertCircle Geo K R Y ->
      HilbertOppositeSide Geo T Y chord ->
      Geo.AngleCongruent X A T X Y A ->
      HilbertCircleTangentAt
        (Geo := Geo) K A tangent

/--
Forder IV.18: tangent-chord theorem.
-/
def HilbertForderIV18TangentChord
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H] : Prop :=
  forall K R X A Y T : Geo.Point,
    forall chord tangent : Geo.Line,
      Ne X A ->
      H.OnLine X chord ->
      H.OnLine A chord ->
      H.OnLine A tangent ->
      H.OnLine T tangent ->
      Ne T A ->
      HilbertCircle Geo K R X ->
      HilbertCircle Geo K R A ->
      HilbertCircle Geo K R Y ->
      HilbertCircleTangentAt
        (Geo := Geo) K A tangent ->
      HilbertOppositeSide Geo T Y chord ->
      Geo.AngleCongruent
        X A T
        X Y A

/--
Forder IV.19: same-segment converse.
-/
def HilbertForderIV19CircleConverse
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H] : Prop :=
  forall C D A B : Geo.Point,
    forall chord : Geo.Line,
      Ne C D ->
      H.OnLine C chord ->
      H.OnLine D chord ->
      HilbertSameSide Geo A B chord ->
      Geo.AngleCongruent
        C A D
        C B D ->
      HilbertConcyclic4 Geo A C D B

/--
Forder IV.20: supplementary opposite-segment converse.
-/
def HilbertForderIV20CircleConverse
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H] : Prop :=
  forall C D A B X : Geo.Point,
    forall chord : Geo.Line,
      Ne C D ->
      H.OnLine C chord ->
      H.OnLine D chord ->
      HilbertOppositeSide Geo A B chord ->
      BookZeroSupplement Geo
        X A D
        D C ->
      Geo.AngleCongruent
        X A D
        C B D ->
      HilbertConcyclic4 Geo A C D B


------------------------------------------------------------------------
-- Reusable circle/order/angle support extracted during Forder IV.12
------------------------------------------------------------------------

theorem hilbert_circle_center_ne_point_of_two_distinct
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (K R A B C : Geo.Point)
    (hAB : Ne A B)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hC : HilbertCircle Geo K R C) :
    Ne K C := by

  intro hKC
  subst C

  have hKA_KK :
      Geo.Congruent K A K K :=
    hilbert_circle_center_congruent
      Geo
      K R
      A K
      hA hC

  have hKB_KK :
      Geo.Congruent K B K K :=
    hilbert_circle_center_congruent
      Geo
      K R
      B K
      hB hC

  have hKA :
      K = A :=
    bookZero_nullSegment1
      Geo K A K hKA_KK

  have hKB :
      K = B :=
    bookZero_nullSegment1
      Geo K B K hKB_KK

  exact
    hAB
      (hKA.symm.trans hKB)


------------------------------------------------------------------------
-- 2. Antipodal extension through the center.
------------------------------------------------------------------------

/--
For every point C on a nondegenerate Hilbert circle there is a point X
on the same circle with the center K strictly between C and X.

This is the synthetic antipodal-point construction needed in Forder
IV.16.
-/

theorem hilbert_circle_antipode
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (K R A B C : Geo.Point)
    (hAB : Ne A B)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B)
    (hC : HilbertCircle Geo K R C) :
    exists X : Geo.Point,
      Geo.Between C K X /\
      HilbertCircle Geo K R X := by

  have hKC :
      Ne K C :=
    hilbert_circle_center_ne_point_of_two_distinct
      Geo
      K R A B C
      hAB
      hA hB hC

  rcases
      hilbert_extend_segment_beyond
        Geo C K hKC.symm
    with
    ⟨X, hCKX, hCK_KX⟩

  have hKX_CK :
      Geo.Congruent K X C K :=
    hilbert_congruent_symmetry
      Geo
      C K
      K X
      hCK_KX

  have hKX_KC :
      Geo.Congruent K X K C :=
    (Geo.congruent_reverse_second
      K X
      C K).mp
      hKX_CK

  have hKC_KR :
      Geo.Congruent K C K R := by
    simpa [HilbertCircle] using hC

  have hKX_KR :
      Geo.Congruent K X K R :=
    hilbert_congruent_transitivity
      Geo
      K X
      K C
      K R
      hKX_KC
      hKC_KR

  have hX :
      HilbertCircle Geo K R X := by
    simpa [HilbertCircle] using hKX_KR

  exact
    ⟨X, hCKX, hX⟩

theorem hilbert_circle_center_midpoint_of_chord
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (K R A B : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKchord : H.OnLine K chord)
    (hA : HilbertCircle Geo K R A)
    (hB : HilbertCircle Geo K R B) :
    HilbertIsMidpoint Geo K A B := by

  have hKA :
      Ne K A :=
    hilbert_circle_center_ne_point_of_two_distinct
      Geo
      K R A B A
      hAB
      hA hB hA

  have hKB :
      Ne K B :=
    hilbert_circle_center_ne_point_of_two_distinct
      Geo
      K R A B B
      hAB
      hA hB hB

  have hAK :
      Ne A K :=
    hKA.symm

  have hKA_KB :
      Geo.Congruent K A K B :=
    hilbert_circle_center_congruent
      Geo
      K R
      A B
      hA hB

  have hAKBcol :
      PrimCollinear Geo A K B :=
    ⟨chord,
      hAchord,
      hKchord,
      hBchord⟩

  rcases
      hilbert_between_trichotomy
        Geo
        A K B
        hAK
        hKB
        hAB
        hAKBcol
    with
    hAKB | hKAB | hABK

  --------------------------------------------------------------------
  -- The required order A-K-B.
  --------------------------------------------------------------------

  · have hAK_KB :
        Geo.Congruent A K K B :=
      CongruentReverseFirst
        Geo
        K A
        K B
        hKA_KB

    exact
      ⟨hAKB, hAK_KB⟩

  --------------------------------------------------------------------
  -- K-A-B would give KA < KB, contradicting equal radii.
  --------------------------------------------------------------------

  · have hKA_lt_KB :
        HilbertSegmentLess Geo K A K B :=
      hilbert_segmentLess_of_between
        Geo
        K A B
        hKAB

    exact
      False.elim
        ((hilbert_segmentLess_not_congruent
            Geo
            K A
            K B
            hKA_lt_KB)
          hKA_KB)

  --------------------------------------------------------------------
  -- A-B-K gives KB < KA, again contradicting equal radii.
  --------------------------------------------------------------------

  · have hKBA :
        Geo.Between K B A :=
      (HilbertOrder.between_incidence
        A B K hABK).2.2.2.2

    have hKB_lt_KA :
        HilbertSegmentLess Geo K B K A :=
      hilbert_segmentLess_of_between
        Geo
        K B A
        hKBA

    have hKB_KA :
        Geo.Congruent K B K A :=
      hilbert_congruent_symmetry
        Geo
        K A
        K B
        hKA_KB

    exact
      False.elim
        ((hilbert_segmentLess_not_congruent
            Geo
            K B
            K A
            hKB_lt_KA)
          hKB_KA)

theorem hilbert_circle_exterior_central_half
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A C X : Geo.Point)
    (hAcircle : HilbertCircle Geo K R A)
    (hCcircle : HilbertCircle Geo K R C)
    (hAKC : Not (PrimCollinear Geo A K C))
    (hCKX : Geo.Between C K X) :
    exists T : Geo.Point,
      HilbertRayMeetsSegment Geo K T A X /\
      Geo.AngleCongruent
        A K T
        X K T /\
      Geo.AngleCongruent
        A C K
        A K T := by

  --------------------------------------------------------------------
  -- Basic nondegeneracy.
  --------------------------------------------------------------------

  have hKAC :
      Not (PrimCollinear Geo K A C) := by
    intro h
    exact
      hAKC
        (PrimCollinearSwap
          Geo K A C h)

  have hACK :
      Not (PrimCollinear Geo A C K) := by
    intro h
    exact
      hAKC
        (PrimCollinearRotate
          Geo A C K h)

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKXcol :
      PrimCollinear Geo C K X :=
    hCKXdata.2.2.2.1

  have hAKX :
      Not (PrimCollinear Geo A K X) := by
    intro hAKXcol

    have hKXC :
        PrimCollinear Geo K X C :=
      PrimCollinearCycle
        Geo C K X hCKXcol

    have hAKC' :
        PrimCollinear Geo A K C :=
      hilbert_primCollinear_trans
        Geo
        A K X C
        hKX
        hAKXcol
        hKXC

    exact hAKC hAKC'

  --------------------------------------------------------------------
  -- Triangle KAC is isosceles.
  --------------------------------------------------------------------

  have hKA_KC :
      Geo.Congruent K A K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      A C
      hAcircle
      hCcircle

  have hIso :
      Geo.AngleCongruent
        K A C
        K C A :=
    hilbert_isosceles_base_angles
      Geo
      K A C
      hKAC
      hKA_KC

  have hKAC_ACK :
      Geo.AngleCongruent
        K A C
        A C K :=
    (Geo.angle_congruent_reverse_second
      K A C
      K C A).mp
      hIso

  --------------------------------------------------------------------
  -- I.32 on triangle A-C-K, with CK extended through K to X.
  --
  -- It decomposes the exterior angle AKX into
  --
  --   angle CAK  and  angle ACK.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        A C K X
        hACK
        hCKX
    with
    ⟨T,
      hATX,
      hCAK_AKT,
      hACK_TKX⟩

  have hATXdata :=
    HilbertOrder.between_incidence
      A T X hATX

  have hAT :
      Ne A T :=
    hATXdata.1

  have hTX :
      Ne T X :=
    hATXdata.2.1

  have hATXcol :
      PrimCollinear Geo A T X :=
    hATXdata.2.2.2.1

  have hKT :
      Ne K T := by
    intro hKT
    subst T

    have hAKXcol :
        PrimCollinear Geo A K X :=
      hATXcol

    exact hAKX hAKXcol

  have hInside :
      HilbertRayMeetsSegment Geo K T A X :=
    ⟨T,
      hATX,
      hilbert_sameRay_refl
        Geo K T hKT.symm⟩

  --------------------------------------------------------------------
  -- Reverse the first remote angle from CAK to KAC.
  --------------------------------------------------------------------

  have hKAC_AKT :
      Geo.AngleCongruent
        K A C
        A K T :=
    (Geo.angle_congruent_reverse_first
      C A K
      A K T).mp
      hCAK_AKT

  --------------------------------------------------------------------
  -- Therefore AKT is congruent to ACK.
  --------------------------------------------------------------------

  have hAKT_KAC :
      Geo.AngleCongruent
        A K T
        K A C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      K A C
      A K T
      hKAC_AKT

  have hAKT_ACK :
      Geo.AngleCongruent
        A K T
        A C K :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A K T
      K A C
      A C K
      hAKT_KAC
      hKAC_ACK

  --------------------------------------------------------------------
  -- The second I.32 component is ACK ~= TKX.
  -- Reverse the second angle to obtain ACK ~= XKT.
  --------------------------------------------------------------------

  have hACK_XKT :
      Geo.AngleCongruent
        A C K
        X K T :=
    (Geo.angle_congruent_reverse_second
      A C K
      T K X).mp
      hACK_TKX

  --------------------------------------------------------------------
  -- Hence the two halves of exterior angle AKX are congruent.
  --------------------------------------------------------------------

  have hAKT_XKT :
      Geo.AngleCongruent
        A K T
        X K T :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A K T
      A C K
      X K T
      hAKT_ACK
      hACK_XKT

  have hACK_AKT :
      Geo.AngleCongruent
        A C K
        A K T :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A K T
      A C K
      hAKT_ACK

  exact
    ⟨T,
      hInside,
      hAKT_XKT,
      hACK_AKT⟩

theorem hilbert_isosceles_base_inner_point_closer
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (U C Hpt D : Geo.Point)
    (hUCD : Not (PrimCollinear Geo U C D))
    (hCHD : Geo.Between C Hpt D)
    (hUC_UD : Geo.Congruent U C U D) :
    HilbertSegmentLess Geo U Hpt U C := by

  have hCHDdata :=
    HilbertOrder.between_incidence
      C Hpt D hCHD

  have hCH :
      Ne C Hpt :=
    hCHDdata.1

  have hHD :
      Ne Hpt D :=
    hCHDdata.2.1

  have hDH :
      Ne D Hpt :=
    hHD.symm

  have hDHC :
      Geo.Between D Hpt C :=
    hCHDdata.2.2.2.2

  have hCHDcol :
      PrimCollinear Geo C Hpt D :=
    hCHDdata.2.2.2.1

  have hDHCcol :
      PrimCollinear Geo D Hpt C :=
    PrimCollinearSymm
      Geo C Hpt D hCHDcol

  --------------------------------------------------------------------
  -- Triangles U-D-H and U-C-H are nondegenerate.
  --------------------------------------------------------------------

  have hUDH :
      Not (PrimCollinear Geo U D Hpt) := by
    intro hUDHcol

    have hUDC :
        PrimCollinear Geo U D C :=
      hilbert_primCollinear_trans
        Geo
        U D Hpt C
        hDH
        hUDHcol
        hDHCcol

    exact
      hUCD
        (PrimCollinearRotate
          Geo U D C hUDC)

  have hUCH :
      Not (PrimCollinear Geo U C Hpt) := by
    intro hUCHcol

    have hUCDcol :
        PrimCollinear Geo U C D :=
      hilbert_primCollinear_trans
        Geo
        U C Hpt D
        hCH
        hUCHcol
        hCHDcol

    exact hUCD hUCDcol

  have hUHC :
      Not (PrimCollinear Geo U Hpt C) := by
    intro h
    exact
      hUCH
        (PrimCollinearRotate
          Geo U Hpt C h)

  --------------------------------------------------------------------
  -- I.16 in triangle U-D-H, with DH extended through H to C.
  --------------------------------------------------------------------

  have hUDH_UHC :
      HilbertAngleLess Geo
        U D Hpt
        U Hpt C :=
    euclid_proposition_16_second
      Geo
      U D Hpt C
      hUDH
      hDHC

  --------------------------------------------------------------------
  -- I.5 in U-C-D and transport H along the base CD.
  --------------------------------------------------------------------

  have hBase :
      Geo.AngleCongruent
        U C D
        U D C :=
    hilbert_isosceles_base_angles
      Geo
      U C D
      hUCD
      hUC_UD

  have hBaseSymm :
      Geo.AngleCongruent
        U D C
        U C D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      U C D
      U D C
      hBase

  have hRayDHC :
      HilbertSameRay Geo D Hpt C :=
    hilbert_sameRay_of_between
      Geo D Hpt C hDHC

  have hRayCHD :
      HilbertSameRay Geo C Hpt D :=
    hilbert_sameRay_of_between
      Geo C Hpt D hCHD

  have hUDH_eq_UDC :
      Geo.Angle U D Hpt =
      Geo.Angle U D C :=
    hilbert_angle_eq_of_sameRay_second
      Geo D U Hpt C hRayDHC

  have hUCH_eq_UCD :
      Geo.Angle U C Hpt =
      Geo.Angle U C D :=
    hilbert_angle_eq_of_sameRay_second
      Geo C U Hpt D hRayCHD

  have hUCH_UDH :
      Geo.AngleCongruent
        U C Hpt
        U D Hpt := by

    have hUDH_UCH :
        Geo.AngleCongruent
          U D Hpt
          U C Hpt := by
      unfold Geometry.Geo.AngleCongruent
        at hBaseSymm ⊢
      rw [hUDH_eq_UDC, hUCH_eq_UCD]
      exact hBaseSymm

    exact
      Geometry.Geo.angle_congruent_symmetry
        Geo
        U D Hpt
        U C Hpt
        hUDH_UCH

  have hUCH_UHC :
      HilbertAngleLess Geo
        U C Hpt
        U Hpt C :=
    hilbert_angleLess_transport_left
      Geo
      U D Hpt
      U C Hpt
      U Hpt C
      hUDH_UHC
      hUCH
      hUCH_UDH

  --------------------------------------------------------------------
  -- I.19 in triangle U-H-C.
  --------------------------------------------------------------------

  exact
    euclid_proposition_19
      Geo
      U Hpt C
      hUHC
      hUCH_UHC


------------------------------------------------------------------------
-- 2. Interior points of a chord are strictly inside the circle.
------------------------------------------------------------------------

/--
If A and B are distinct points of a circle centered at K, Y lies
strictly between A and B, and K is off the chord AB, then

  KY < KA.

Since KA is a radius, this is the exact synthetic content needed in
Forder IV.12 for "Y is inside the circle".
-/

theorem hilbert_circle_chord_inner_point_inside
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B Y : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hKoff : Not (H.OnLine K chord))
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hAYB : Geo.Between A Y B) :
    HilbertSegmentLess Geo K Y K A := by

  have hKAB :
      Not (PrimCollinear Geo K A B) := by
    intro h

    have hKline :
        H.OnLine K chord :=
      hilbert_collinear_on_line
        Geo
        A B K
        chord
        hAB
        hAchord
        hBchord
        (PrimCollinearCycle
          Geo K A B h)

    exact hKoff hKline

  have hKA_KB :
      Geo.Congruent K A K B :=
    hilbert_circle_center_congruent
      Geo
      K R
      A B
      hAcircle
      hBcircle

  exact
    hilbert_isosceles_base_inner_point_closer
      Geo
      K A Y B
      hKAB
      hAYB
      hKA_KB

theorem hilbert_sameSide_intersection_order
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K C Y : Geo.Point)
    (chord : Geo.Line)
    (hKC : Ne K C)
    (hYchord : H.OnLine Y chord)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hCKYcol : PrimCollinear Geo C K Y)
    (hKY_KC : HilbertSegmentLess Geo K Y K C) :
    Geo.Between C K Y := by

  have hCoff :
      Not (H.OnLine C chord) :=
    hSameCK.1

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hCY :
      Ne C Y := by
    intro hCY
    subst Y
    exact hCoff hYchord

  have hKY :
      Ne K Y := by
    intro hKY
    subst Y
    exact hKoff hYchord

  rcases
      hilbert_between_trichotomy
        Geo
        C K Y
        hKC.symm
        hKY
        hCY
        hCKYcol
    with
    hCKY | hKCY | hCYK

  --------------------------------------------------------------------
  -- Desired order.
  --------------------------------------------------------------------

  · exact hCKY

  --------------------------------------------------------------------
  -- K-C-Y would force KC < KY, contradicting KY < KC.
  --------------------------------------------------------------------

  · have hKC_KY :
        HilbertSegmentLess Geo K C K Y :=
      hilbert_segmentLess_of_between
        Geo
        K C Y
        hKCY

    exact
      False.elim
        ((hilbert_segmentLess_asymm
            Geo
            K Y
            K C
            hKY_KC)
          hKC_KY)

  --------------------------------------------------------------------
  -- C-Y-K would make C and K opposite sides of the chord.
  --------------------------------------------------------------------

  · have hOppCK :
        HilbertOppositeSide Geo C K chord :=
      ⟨hCoff,
       hKoff,
       ⟨Y,
        hCYK,
        hYchord⟩⟩

    exact
      False.elim
        ((hilbert_oppositeSide_not_sameSide
            Geo
            C K
            chord
            hOppCK)
          hSameCK)


------------------------------------------------------------------------
-- Circle-specialized wrapper used in IV.12.
------------------------------------------------------------------------

/--
If Y is an interior point of chord AB and is collinear with the center
K and a circle point C lying on the same side of AB as K, then

  C-K-Y.

The strict inequality KY < KC comes from stage 20.
-/

theorem hilbert_circle_chord_axis_order
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C Y : Geo.Point)
    (chord : Geo.Line)
    (hAB : Ne A B)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hSameCK : HilbertSameSide Geo C K chord)
    (hAYB : Geo.Between A Y B)
    (hCKYcol : PrimCollinear Geo C K Y) :
    Geo.Between C K Y := by

  have hKoff :
      Not (H.OnLine K chord) :=
    hSameCK.2.1

  have hYchord :
      H.OnLine Y chord :=
    hilbert_between_on_line
      Geo
      A Y B
      chord
      hAchord
      hBchord
      hAYB

  have hKC :
      Ne K C :=
    hilbert_circle_center_ne_point_of_two_distinct
      Geo
      K R A B C
      hAB
      hAcircle
      hBcircle
      hCcircle

  have hKY_KA :
      HilbertSegmentLess Geo K Y K A :=
    hilbert_circle_chord_inner_point_inside
      Geo
      K R A B Y
      chord
      hAB
      hAchord
      hBchord
      hKoff
      hAcircle
      hBcircle
      hAYB

  have hKA_KC :
      Geo.Congruent K A K C :=
    hilbert_circle_center_congruent
      Geo
      K R
      A C
      hAcircle
      hCcircle

  have hKY_KC :
      HilbertSegmentLess Geo K Y K C :=
    hilbert_segmentLess_congruent_right
      Geo
      K Y
      K A
      K C
      hKY_KA
      hKA_KC

  exact
    hilbert_sameSide_intersection_order
      Geo
      K C Y
      chord
      hKC
      hYchord
      hSameCK
      hCKYcol
      hKY_KC

theorem hilbert_sameRay_beyond_common_middle
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (C K X Y : Geo.Point)
    (hCKX : Geo.Between C K X)
    (hCKY : Geo.Between C K Y) :
    HilbertSameRay Geo K X Y := by

  have hCKXdata :=
    HilbertOrder.between_incidence
      C K X hCKX

  have hKX :
      Ne K X :=
    hCKXdata.2.1

  have hCKYdata :=
    HilbertOrder.between_incidence
      C K Y hCKY

  have hKY :
      Ne K Y :=
    hCKYdata.2.1

  have hRayCKX :
      HilbertSameRay Geo C K X :=
    hilbert_sameRay_of_between
      Geo C K X hCKX

  have hRayCKY :
      HilbertSameRay Geo C K Y :=
    hilbert_sameRay_of_between
      Geo C K Y hCKY

  have hRayCXY :
      HilbertSameRay Geo C X Y :=
    bookZero_36_ray3
      Geo
      C K X Y
      hRayCKX
      hRayCKY

  rcases
      hilbert_sameRay_cases
        Geo
        C X Y
        hRayCXY
    with
    hXY | hOrder

  --------------------------------------------------------------------
  -- X = Y.
  --------------------------------------------------------------------

  · subst Y
    exact
      hilbert_sameRay_refl
        Geo K X hKX.symm

  --------------------------------------------------------------------
  -- C-X-Y or C-Y-X.
  --------------------------------------------------------------------

  · rcases hOrder with hCXY | hCYX

    · have hKXY :
          Geo.Between K X Y :=
        (hilbert_between_inner_trans
          Geo
          C K X Y
          hCKX
          hCXY).1

      exact
        hilbert_sameRay_of_between
          Geo K X Y hKXY

    · have hKYX :
          Geo.Between K Y X :=
        (hilbert_between_inner_trans
          Geo
          C K Y X
          hCKY
          hCYX).1

      exact
        hilbert_sameRay_symm
          Geo
          K Y X
          (hilbert_sameRay_of_between
            Geo K Y X hKYX)


------------------------------------------------------------------------
-- 2. Forder IV.12, opposite-side axis configuration.
------------------------------------------------------------------------

/--
Addition-case geometry for Forder IV.12.

The axis through K and X separates A and B.  Its intersection Y with
AB lies beyond K from C, hence:

* ray KX meets the open segment AB;
* ray CK meets the open segment AB.

These are exactly the two interior-ray witnesses needed to decompose
the central angle AKB and the inscribed angle ACB.
-/

theorem hilbert_angle_bisector_with_interior
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O X Y : Geo.Point)
    (hXOY : Not (PrimCollinear Geo X O Y)) :
    exists M : Geo.Point,
      HilbertRayMeetsSegment Geo O M X Y /\
      Geo.AngleCongruent X O M M O Y := by

  have hOXY :
      Not (PrimCollinear Geo O X Y) := by
    intro h
    exact
      hXOY
        (PrimCollinearSwap
          Geo O X Y h)

  have hOX :
      Ne O X :=
    hilbert_noncollinear_ne_first
      Geo O X Y hOXY

  --------------------------------------------------------------------
  -- Lay off OD ~= OY on ray OX.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        O Y
        O X
        hOX
    with
    ⟨D, hRayXD, hOD_OY⟩

  have hOD :
      Ne O D :=
    hRayXD.2.1.symm

  have hOXD :
      PrimCollinear Geo O X D :=
    hRayXD.2.2.1

  have hODY :
      Not (PrimCollinear Geo O D Y) := by
    intro hODY

    have hXOD :
        PrimCollinear Geo X O D :=
      PrimCollinearSwap
        Geo O X D hOXD

    have hXOY' :
        PrimCollinear Geo X O Y :=
      hilbert_primCollinear_trans
        Geo
        X O D Y
        hOD
        hXOD
        hODY

    exact hXOY hXOY'

  have hDY :
      Ne D Y := by
    intro h
    subst D
    exact hOXY hOXD

  --------------------------------------------------------------------
  -- Let M be the midpoint of DY.
  --------------------------------------------------------------------

  rcases
      HilbertMidpointExists
        Geo D Y hDY
    with
    ⟨M, hMid⟩

  have hDMY :
      Geo.Between D M Y :=
    hMid.1

  have hDM_MY :
      Geo.Congruent D M M Y :=
    hMid.2

  have hDM :
      Ne D M :=
    (HilbertOrder.between_incidence
      D M Y hDMY).1

  have hDMYcol :
      PrimCollinear Geo D M Y :=
    (HilbertOrder.between_incidence
      D M Y hDMY).2.2.2.1

  have hODM :
      Not (PrimCollinear Geo O D M) := by
    intro hODM

    have hODY' :
        PrimCollinear Geo O D Y :=
      hilbert_primCollinear_trans
        Geo
        O D M Y
        hDM
        hODM
        hDMYcol

    exact hODY hODY'

  have hMO :
      Ne M O := by
    intro h
    subst M

    exact
      hODY
        (PrimCollinearSwap
          Geo D O Y hDMYcol)

  --------------------------------------------------------------------
  -- SSS on ODM and OYM.
  --------------------------------------------------------------------

  have hDM_YM :
      Geo.Congruent D M Y M :=
    (Geo.congruent_reverse_second
      D M M Y).mp hDM_MY

  have hOM :
      Geo.Congruent O M O M :=
    hilbert_congruent_reflexive
      Geo O M

  have hSSS :=
    HilbertSSS
      Geo
      O D M
      O Y M
      hODM
      hOD_OY
      hDM_YM
      hOM

  have hAngleDOM_YOM :
      Geo.AngleCongruent D O M Y O M :=
    hSSS.2.angleA

  have hAngleDOM_MOY :
      Geo.AngleCongruent D O M M O Y :=
    (Geo.angle_congruent_reverse_second
      D O M Y O M).mp
      hAngleDOM_YOM

  --------------------------------------------------------------------
  -- Replace the constructed ray OD by the original ray OX.
  --------------------------------------------------------------------

  have hRayDX :
      HilbertSameRay Geo O D X :=
    hilbert_sameRay_symm
      Geo O X D hRayXD

  have hAngleEq :
      Geo.Angle D O M =
      Geo.Angle X O M :=
    hilbert_angle_eq_of_sameRay_first
      Geo O D X M hRayDX

  have hBisect :
      Geo.AngleCongruent X O M M O Y := by
    unfold Geometry.Geo.AngleCongruent at hAngleDOM_MOY
    unfold Geometry.Geo.AngleCongruent
    rw [← hAngleEq]
    exact hAngleDOM_MOY

  --------------------------------------------------------------------
  -- Retain the interior-ray information.
  --------------------------------------------------------------------

  have hYOX :
      Not (PrimCollinear Geo Y O X) := by
    intro h

    have hOXY' :
        PrimCollinear Geo O X Y :=
      PrimCollinearCycle
        Geo Y O X h

    exact hOXY hOXY'

  have hYO :
      Ne Y O :=
    hilbert_noncollinear_ne_first
      Geo Y O X hYOX

  have hYY :
      HilbertSameRay Geo O Y Y :=
    hilbert_sameRay_refl
      Geo O Y hYO

  have hMeetDY :
      HilbertRayMeetsSegment Geo O M D Y :=
    ⟨M,
      hDMY,
      hilbert_sameRay_refl
        Geo O M hMO⟩

  have hDOY :
      Not (PrimCollinear Geo D O Y) := by
    intro h
    exact
      hODY
        (PrimCollinearSwap
          Geo D O Y h)

  have hMeetXY :
      HilbertRayMeetsSegment Geo O M X Y :=
    hilbert_ray_meets_segment_sameRays
      Geo
      O M
      D Y
      X Y
      hMeetDY
      hRayDX
      hYY
      hDOY
      hXOY

  exact
    ⟨M,
      hMeetXY,
      hBisect⟩

theorem hilbert_angleDecomposition_swap_components
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideD :
      HilbertRayMeetsSegment Geo O D A B) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo O E A B /\
      Geo.AngleCongruent
        A O E
        B O D /\
      Geo.AngleCongruent
        B O E
        A O D := by

  --------------------------------------------------------------------
  -- Reverse the whole angle and the crossed segment.
  --------------------------------------------------------------------

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O D A B
      hInsideD

  --------------------------------------------------------------------
  -- BOA is congruent to AOB by reversal of the first angle.
  --------------------------------------------------------------------

  have hRefl :
      Geo.AngleCongruent
        A O B
        A O B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      A O B
      hAOB

  have hWhole :
      Geo.AngleCongruent
        B O A
        A O B :=
    (Geo.angle_congruent_reverse_first
      A O B
      A O B).mp
      hRefl

  --------------------------------------------------------------------
  -- Transport the reversed decomposition back into the same whole
  -- angle.  The left and right components are thereby exchanged.
  --------------------------------------------------------------------

  rcases
      hilbert_interior_subangle_transport_both
        Geo
        O B A D
        A O B
        hBOA
        hAOB
        hInsideDrev
        hWhole
    with
    ⟨E,
      hInsideE,
      hParts⟩

  have hAOD_BOE :
      Geo.AngleCongruent
        A O D
        B O E :=
    hParts.1

  have hBOD_AOE :
      Geo.AngleCongruent
        B O D
        A O E :=
    hParts.2

  have hAOE_BOD :
      Geo.AngleCongruent
        A O E
        B O D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B O D
      A O E
      hBOD_AOE

  have hBOE_AOD :
      Geo.AngleCongruent
        B O E
        A O D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A O D
      B O E
      hAOD_BOE

  exact
    ⟨E,
      hInsideE,
      hAOE_BOD,
      hBOE_AOD⟩

theorem hilbert_angleDecomposition_nested_inside_left
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (A O B E T : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideE : HilbertRayMeetsSegment Geo O E A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T A E) :
    HilbertRayMeetsSegment Geo O T A B := by

  have hAOE_AOB :
      HilbertAngleLess Geo A O E A O B :=
    hilbert_interior_angle_less
      Geo
      O E A B
      hAOB
      hInsideE

  have hAOE :
      Not (PrimCollinear Geo A O E) :=
    hAOE_AOB.1

  have hAOT_AOE :
      HilbertAngleLess Geo A O T A O E :=
    hilbert_interior_angle_less
      Geo
      O T A E
      hAOE
      hInsideT

  have hAOT_AOB :
      HilbertAngleLess Geo A O T A O B :=
    hilbert_angleLess_trans
      Geo
      A O T
      A O E
      A O B
      hAOT_AOE
      hAOE_AOB

  have hAO :
      O ≠ A :=
    hilbert_noncollinear_ne_first
      Geo O A B
      (by
        intro h
        exact
          hAOB
            (PrimCollinearSwap
              Geo O A B h))

  rcases
      HilbertPlaneIncidence.line_through
        O A hAO
    with
    ⟨lineOA,
      hOlineOA,
      hAlineOA⟩

  have hEOA :
      Not (PrimCollinear Geo E O A) := by
    intro h
    exact
      hAOE
        (PrimCollinearSymm
          Geo E O A h)

  have hInsideTrev :
      HilbertRayMeetsSegment Geo O T E A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A E
      hInsideT

  have hTESameOA :
      HilbertSameSide Geo T E lineOA :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O T E A
      lineOA
      hOlineOA
      hAlineOA
      hEOA
      hInsideTrev

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A B
      hInsideE

  have hEBSameOA :
      HilbertSameSide Geo E B lineOA :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O E B A
      lineOA
      hOlineOA
      hAlineOA
      hBOA
      hInsideErev

  have hTBSameOA :
      HilbertSameSide Geo T B lineOA :=
    hilbert_sameSide_trans
      Geo
      T E B
      lineOA
      hTESameOA
      hEBSameOA

  exact
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      T B O A
      lineOA
      hOlineOA
      hAlineOA
      hAO
      hTBSameOA
      hAOT_AOB


------------------------------------------------------------------------
-- 2. Right-hand nesting.
------------------------------------------------------------------------

/--
If OE is interior to angle AOB and OT is interior to angle EOB,
then OT is interior to angle AOB.
-/

theorem hilbert_angleDecomposition_nested_inside_right
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (A O B E T : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideE : HilbertRayMeetsSegment Geo O E A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T E B) :
    HilbertRayMeetsSegment Geo O T A B := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A B
      hInsideE

  have hInsideTrev :
      HilbertRayMeetsSegment Geo O T B E :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T E B
      hInsideT

  have hNestedRev :
      HilbertRayMeetsSegment Geo O T B A :=
    hilbert_angleDecomposition_nested_inside_left
      Geo
      B O A E T
      hBOA
      hInsideErev
      hInsideTrev

  exact
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T B A
      hNestedRev

theorem hilbert_angleDecomposition_nested_parent_divider
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (X O C E Z : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hInsideE : HilbertRayMeetsSegment Geo O E X C)
    (hInsideZ : HilbertRayMeetsSegment Geo O Z E C) :
    HilbertRayMeetsSegment Geo O E X Z := by

  have hInsideZwhole :
      HilbertRayMeetsSegment Geo O Z X C :=
    hilbert_angleDecomposition_nested_inside_right
      Geo
      X O C E Z
      hXOC
      hInsideE
      hInsideZ

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm Geo C O X h)

  have hInsideErev :
      HilbertRayMeetsSegment Geo O E C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E X C
      hInsideE

  have hInsideZrev :
      HilbertRayMeetsSegment Geo O Z C E :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O Z E C
      hInsideZ

  have hCOE :
      Not (PrimCollinear Geo C O E) :=
    (hilbert_interior_angle_less
      Geo
      O E C X
      hCOX
      hInsideErev).1

  have hCOZ_COE :
      HilbertAngleLess Geo C O Z C O E :=
    hilbert_interior_angle_less
      Geo
      O Z C E
      hCOE
      hInsideZrev

  have hInsideZwholeRev :
      HilbertRayMeetsSegment Geo O Z C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O Z X C
      hInsideZwhole

  have hXOE_XOZ :
      HilbertAngleLess Geo X O E X O Z :=
    hilbert_angleDecomposition_complement_order_reverse
      Geo
      O C X Z E
      hCOX
      hInsideZwholeRev
      hInsideErev
      hCOZ_COE

  have hOX :
      O ≠ X :=
    hilbert_noncollinear_ne_first
      Geo
      O X C
      (by
        intro h
        exact
          hXOC
            (PrimCollinearSwap
              Geo O X C h))

  rcases
      HilbertPlaneIncidence.line_through
        O X hOX
    with
    ⟨lineOX,
      hOlineOX,
      hXlineOX⟩

  have hEDSame :
      HilbertSameSide Geo E C lineOX :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O E C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideErev

  have hZCSame :
      HilbertSameSide Geo Z C lineOX :=
    hilbert_angleDecomposition_interior_ray_sameSide_first
      Geo
      O Z C X
      lineOX
      hOlineOX
      hXlineOX
      hCOX
      hInsideZwholeRev

  have hCZSame :
      HilbertSameSide Geo C Z lineOX :=
    hilbert_sameSide_symm
      Geo
      Z C
      lineOX
      hZCSame

  have hEZSame :
      HilbertSameSide Geo E Z lineOX :=
    hilbert_sameSide_trans
      Geo
      E C Z
      lineOX
      hEDSame
      hCZSame

  exact
    hilbert_angleDecomposition_angle_less_ray_inside
      Geo
      E Z O X
      lineOX
      hOlineOX
      hXlineOX
      hOX
      hEZSame
      hXOE_XOZ


------------------------------------------------------------------------
-- 3. The middle-divider form needed for IV.12.
------------------------------------------------------------------------

/--
Suppose the rays occur in the nested configuration

  A ... T ... E ... U ... B

inside the proper angle AOB, expressed synthetically by

* OE interior to AOB,
* OT interior to AOE,
* OU interior to EOB.

Then OE is interior to angle TOU.
-/

theorem hilbert_angleDecomposition_middle_divider
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (A O B E T U : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideE : HilbertRayMeetsSegment Geo O E A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T A E)
    (hInsideU : HilbertRayMeetsSegment Geo O U E B) :
    HilbertRayMeetsSegment Geo O E T U := by

  have hInsideE_AU :
      HilbertRayMeetsSegment Geo O E A U :=
    hilbert_angleDecomposition_nested_parent_divider
      Geo
      A O B E U
      hAOB
      hInsideE
      hInsideU

  have hInsideE_UA :
      HilbertRayMeetsSegment Geo O E U A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A U
      hInsideE_AU

  have hInsideT_EA :
      HilbertRayMeetsSegment Geo O T E A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A E
      hInsideT

  have hInsideUwhole :
      HilbertRayMeetsSegment Geo O U A B :=
    hilbert_angleDecomposition_nested_inside_right
      Geo
      A O B E U
      hAOB
      hInsideE
      hInsideU

  have hAOU :
      Not (PrimCollinear Geo A O U) :=
    (hilbert_interior_angle_less
      Geo
      O U A B
      hAOB
      hInsideUwhole).1

  have hUOA :
      Not (PrimCollinear Geo U O A) := by
    intro h
    exact
      hAOU
        (PrimCollinearSymm
          Geo U O A h)

  have hInsideE_UT :
      HilbertRayMeetsSegment Geo O E U T :=
    hilbert_angleDecomposition_nested_parent_divider
      Geo
      U O A E T
      hUOA
      hInsideE_UA
      hInsideT_EA

  exact
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E U T
      hInsideE_UT

theorem hilbert_angleDecomposition_double_sum_bisector
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (A O B X T U : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hInsideX : HilbertRayMeetsSegment Geo O X A B)
    (hInsideT : HilbertRayMeetsSegment Geo O T A X)
    (hInsideU : HilbertRayMeetsSegment Geo O U X B)
    (hLeftHalf :
      Geo.AngleCongruent
        A O T
        X O T)
    (hRightHalf :
      Geo.AngleCongruent
        B O U
        X O U) :
    exists E : Geo.Point,
      HilbertRayMeetsSegment Geo O E A B /\
      HilbertRayMeetsSegment Geo O T A E /\
      HilbertRayMeetsSegment Geo O U E B /\
      Geo.AngleCongruent A O E B O E /\
      Geo.AngleCongruent T O E B O U := by

  --------------------------------------------------------------------
  -- Properness of the local left configuration.
  --------------------------------------------------------------------

  have hAOX :
      Not (PrimCollinear Geo A O X) :=
    (hilbert_interior_angle_less
      Geo
      O X A B
      hAOB
      hInsideX).1

  have hXOA :
      Not (PrimCollinear Geo X O A) := by
    intro h
    exact
      hAOX
        (PrimCollinearSymm
          Geo X O A h)

  have hInsideT_XA :
      HilbertRayMeetsSegment Geo O T X A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A X
      hInsideT

  have hXOT :
      Not (PrimCollinear Geo X O T) :=
    (hilbert_interior_angle_less
      Geo
      O T X A
      hXOA
      hInsideT_XA).1

  have hTOX :
      Not (PrimCollinear Geo T O X) := by
    intro h
    exact
      hXOT
        (PrimCollinearSymm
          Geo T O X h)

  --------------------------------------------------------------------
  -- X is interior to the middle angle TOU.
  --------------------------------------------------------------------

  have hInsideX_TU :
      HilbertRayMeetsSegment Geo O X T U :=
    hilbert_angleDecomposition_middle_divider
      Geo
      A O B X T U
      hAOB
      hInsideX
      hInsideT
      hInsideU

  --------------------------------------------------------------------
  -- The middle angle TOU is proper.
  --
  -- If T,O,U were collinear, the witness line of the ray OX would
  -- meet the line TU both at O and at the interior intersection H.
  -- This would force T,O,X collinear, contradicting hTOX.
  --------------------------------------------------------------------

  have hTOU :
      Not (PrimCollinear Geo T O U) := by
    intro hTOUcol

    rcases hInsideX_TU with
      ⟨J,
        hTJU,
        hRayOXJ⟩

    have hTJUdata :=
      HilbertOrder.between_incidence
        T J U hTJU

    have hTU :
        Ne T U :=
      hTJUdata.2.2.1

    have hTJUcol :
        PrimCollinear Geo T J U :=
      hTJUdata.2.2.2.1

    have hOTU :
        PrimCollinear Geo O T U :=
      PrimCollinearSwap
        Geo T O U hTOUcol

    have hTUJ :
        PrimCollinear Geo T U J :=
      PrimCollinearRotate
        Geo T J U hTJUcol

    have hOTJ :
        PrimCollinear Geo O T J :=
      hilbert_primCollinear_trans
        Geo
        O T U J
        hTU
        hOTU
        hTUJ

    have hTOJ :
        PrimCollinear Geo T O J :=
      PrimCollinearSwap
        Geo O T J hOTJ

    have hOJ :
        Ne O J :=
      hRayOXJ.2.1.symm

    have hOJX :
        PrimCollinear Geo O J X :=
      PrimCollinearRotate
        Geo O X J hRayOXJ.2.2.1

    have hTOXcol :
        PrimCollinear Geo T O X :=
      hilbert_primCollinear_trans
        Geo
        T O J X
        hOJ
        hTOJ
        hOJX

    exact hTOX hTOXcol

  --------------------------------------------------------------------
  -- Swap the two components of TOU around X.
  --------------------------------------------------------------------

  rcases
      hilbert_angleDecomposition_swap_components
        Geo
        O T U X
        hTOU
        hInsideX_TU
    with
    ⟨E,
      hInsideE_TU,
      hTOE_UOX,
      hUOE_TOX⟩

  --------------------------------------------------------------------
  -- Promote U and T through the nested configurations.
  --------------------------------------------------------------------

  have hInsideU_AB :
      HilbertRayMeetsSegment Geo O U A B :=
    hilbert_angleDecomposition_nested_inside_right
      Geo
      A O B X U
      hAOB
      hInsideX
      hInsideU

  have hAOU :
      Not (PrimCollinear Geo A O U) :=
    (hilbert_interior_angle_less
      Geo
      O U A B
      hAOB
      hInsideU_AB).1

  have hInsideX_AU :
      HilbertRayMeetsSegment Geo O X A U :=
    hilbert_angleDecomposition_nested_parent_divider
      Geo
      A O B X U
      hAOB
      hInsideX
      hInsideU

  have hInsideT_AU :
      HilbertRayMeetsSegment Geo O T A U :=
    hilbert_angleDecomposition_nested_inside_left
      Geo
      A O U X T
      hAOU
      hInsideX_AU
      hInsideT

  have hInsideE_AU :
      HilbertRayMeetsSegment Geo O E A U :=
    hilbert_angleDecomposition_nested_inside_right
      Geo
      A O U T E
      hAOU
      hInsideT_AU
      hInsideE_TU

  have hInsideE_AB :
      HilbertRayMeetsSegment Geo O E A B :=
    hilbert_angleDecomposition_nested_inside_left
      Geo
      A O B U E
      hAOB
      hInsideU_AB
      hInsideE_AU

  have hInsideT_AE :
      HilbertRayMeetsSegment Geo O T A E :=
    hilbert_angleDecomposition_nested_parent_divider
      Geo
      A O U T E
      hAOU
      hInsideT_AU
      hInsideE_TU

  --------------------------------------------------------------------
  -- Symmetric nesting on the B side gives U inside EOB.
  --------------------------------------------------------------------

  have hInsideT_AB :
      HilbertRayMeetsSegment Geo O T A B :=
    hilbert_angleDecomposition_nested_inside_left
      Geo
      A O B X T
      hAOB
      hInsideX
      hInsideT

  have hInsideT_BA :
      HilbertRayMeetsSegment Geo O T B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O T A B
      hInsideT_AB

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hBOT :
      Not (PrimCollinear Geo B O T) :=
    (hilbert_interior_angle_less
      Geo
      O T B A
      hBOA
      hInsideT_BA).1

  have hTOB :
      Not (PrimCollinear Geo T O B) := by
    intro h
    exact
      hBOT
        (PrimCollinearSymm
          Geo T O B h)

  have hInsideX_BA :
      HilbertRayMeetsSegment Geo O X B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O X A B
      hInsideX

  have hInsideX_BT :
      HilbertRayMeetsSegment Geo O X B T :=
    hilbert_angleDecomposition_nested_parent_divider
      Geo
      B O A X T
      hBOA
      hInsideX_BA
      hInsideT_XA

  have hInsideX_TB :
      HilbertRayMeetsSegment Geo O X T B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O X B T
      hInsideX_BT

  have hInsideU_TB :
      HilbertRayMeetsSegment Geo O U T B :=
    hilbert_angleDecomposition_nested_inside_right
      Geo
      T O B X U
      hTOB
      hInsideX_TB
      hInsideU

  have hInsideU_BT :
      HilbertRayMeetsSegment Geo O U B T :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O U T B
      hInsideU_TB

  have hInsideE_UT :
      HilbertRayMeetsSegment Geo O E U T :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E T U
      hInsideE_TU

  have hInsideU_BE :
      HilbertRayMeetsSegment Geo O U B E :=
    hilbert_angleDecomposition_nested_parent_divider
      Geo
      B O T U E
      hBOT
      hInsideU_BT
      hInsideE_UT

  have hInsideU_EB :
      HilbertRayMeetsSegment Geo O U E B :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O U B E
      hInsideU_BE

  --------------------------------------------------------------------
  -- Component congruences after the middle swap.
  --------------------------------------------------------------------

  have hEOU_TOX :
      Geo.AngleCongruent
        E O U
        T O X :=
    (Geo.angle_congruent_reverse_first
      U O E
      T O X).mp
      hUOE_TOX

  have hEOU_XOT :
      Geo.AngleCongruent
        E O U
        X O T :=
    (Geo.angle_congruent_reverse_second
      E O U
      T O X).mp
      hEOU_TOX

  have hXOT_EOU :
      Geo.AngleCongruent
        X O T
        E O U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E O U
      X O T
      hEOU_XOT

  have hAOT_EOU :
      Geo.AngleCongruent
        A O T
        E O U :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A O T
      X O T
      E O U
      hLeftHalf
      hXOT_EOU

  have hTOE_XOU :
      Geo.AngleCongruent
        T O E
        X O U :=
    (Geo.angle_congruent_reverse_second
      T O E
      U O X).mp
      hTOE_UOX

  have hXOU_BOU :
      Geo.AngleCongruent
        X O U
        B O U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B O U
      X O U
      hRightHalf

  have hTOE_BOU :
      Geo.AngleCongruent
        T O E
        B O U :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      T O E
      X O U
      B O U
      hTOE_XOU
      hXOU_BOU

  have hTOE_UOB :
      Geo.AngleCongruent
        T O E
        U O B :=
    (Geo.angle_congruent_reverse_second
      T O E
      B O U).mp
      hTOE_BOU

  --------------------------------------------------------------------
  -- Add the matching alpha and beta components.
  --------------------------------------------------------------------

  have hAOE :
      Not (PrimCollinear Geo A O E) :=
    (hilbert_interior_angle_less
      Geo
      O E A B
      hAOB
      hInsideE_AB).1

  have hInsideE_BA :
      HilbertRayMeetsSegment Geo O E B A :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O E A B
      hInsideE_AB

  have hBOE :
      Not (PrimCollinear Geo B O E) :=
    (hilbert_interior_angle_less
      Geo
      O E B A
      hBOA
      hInsideE_BA).1

  have hEOB :
      Not (PrimCollinear Geo E O B) := by
    intro h
    exact
      hBOE
        (PrimCollinearSymm
          Geo E O B h)

  have hAOE_EOB :
      Geo.AngleCongruent
        A O E
        E O B :=
    hilbert_angleDecomposition_angle_addition_interior
      Geo
      O A E T
      O E B U
      hAOE
      hEOB
      hInsideT_AE
      hInsideU_EB
      hAOT_EOU
      hTOE_UOB

  have hBisect :
      Geo.AngleCongruent
        A O E
        B O E :=
    (Geo.angle_congruent_reverse_second
      A O E
      E O B).mp
      hAOE_EOB

  exact
    ⟨E,
      hInsideE_AB,
      hInsideT_AE,
      hInsideU_EB,
      hBisect,
      hTOE_BOU⟩


------------------------------------------------------------------------
-- 2. Forder IV.12: additive branch
------------------------------------------------------------------------

/--
Forder IV.12, additive branch.

Let A,B,C lie on the circle centered at K. Assume C and K are on the
same side of chord AB. Extend CK through K to X. If A and B lie on
opposite sides of the axis KX, then there is an interior bisector KE of
the central angle AKB such that

  angle ACB ~= angle AKE.

This is the half-central-angle conclusion of IV.12 in the branch where
the axis KX crosses the chord AB.
-/

theorem hilbert_angleDecomposition_componentwise_less_whole
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hX'O'C' : Not (PrimCollinear Geo X' O' C'))
    (hInsideD : HilbertRayMeetsSegment Geo O D X C)
    (hInsideD' : HilbertRayMeetsSegment Geo O' D' X' C')
    (hLeft : HilbertAngleLess Geo X O D X' O' D')
    (hRight : HilbertAngleLess Geo C O D C' O' D') :
    HilbertAngleLess Geo X O C X' O' C' := by

  --------------------------------------------------------------------
  -- Proper component angles used below.
  --------------------------------------------------------------------

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact hXOC
      (PrimCollinearSymm Geo C O X h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo O D X C hInsideD

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    (hilbert_interior_angle_less
      Geo O D C X hCOX hInsideDrev).1

  have hC'O'X' :
      Not (PrimCollinear Geo C' O' X') := by
    intro h
    exact hX'O'C'
      (PrimCollinearSymm Geo C' O' X' h)

  have hInsideD'rev :
      HilbertRayMeetsSegment Geo O' D' C' X' :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo O' D' X' C' hInsideD'

  have hC'O'D' :
      Not (PrimCollinear Geo C' O' D') :=
    (hilbert_interior_angle_less
      Geo O' D' C' X' hC'O'X' hInsideD'rev).1

  --------------------------------------------------------------------
  -- Trichotomy of the whole angles.
  --------------------------------------------------------------------

  rcases
      angle_trichotomy
        Geo
        X O C
        X' O' C'
        hXOC
        hX'O'C'
    with hWholeEq | hWholeOrder

  --------------------------------------------------------------------
  -- Case 1: the whole angles are congruent.
  --------------------------------------------------------------------

  · rcases
        hilbert_interior_subangle_transport_both
          Geo
          O X C D
          X' O' C'
          hXOC
          hX'O'C'
          hInsideD
          hWholeEq
      with
      ⟨E, hInsideE, hParts⟩

    have hX'O'E :
        Not (PrimCollinear Geo X' O' E) :=
      (hilbert_interior_angle_less
        Geo O' E X' C' hX'O'C' hInsideE).1

    have hInsideErev :
        HilbertRayMeetsSegment Geo O' E C' X' :=
      hilbert_angleDecomposition_ray_meets_segment_reverse
        Geo O' E X' C' hInsideE

    have hC'O'E :
        Not (PrimCollinear Geo C' O' E) :=
      (hilbert_interior_angle_less
        Geo O' E C' X' hC'O'X' hInsideErev).1

    have hX'O'E_X'O'D' :
        HilbertAngleLess Geo X' O' E X' O' D' :=
      hilbert_angleLess_transport_left
        Geo
        X O D
        X' O' E
        X' O' D'
        hLeft
        hX'O'E
        (Geometry.Geo.angle_congruent_symmetry
          Geo X O D X' O' E hParts.2)

    have hC'O'E_C'O'D' :
        HilbertAngleLess Geo C' O' E C' O' D' :=
      hilbert_angleLess_transport_left
        Geo
        C O D
        C' O' E
        C' O' D'
        hRight
        hC'O'E
        (Geometry.Geo.angle_congruent_symmetry
          Geo C O D C' O' E hParts.1)

    exact
      False.elim
        (hilbert_angleDecomposition_two_component_less_impossible
          Geo
          O' X' C' E D'
          hX'O'C'
          hInsideE
          hInsideD'
          hX'O'E_X'O'D'
          hC'O'E_C'O'D')

  --------------------------------------------------------------------
  -- Case 2: one whole angle is strictly smaller than the other.
  --------------------------------------------------------------------

  · rcases hWholeOrder with hWanted | hReverse

    · exact hWanted

    ------------------------------------------------------------------
    -- Assume, for contradiction, that the target whole is smaller.
    ------------------------------------------------------------------

    · rcases hReverse with
        ⟨_hX'O'C', _hXOC, E, hInsideE, hWholeTarget⟩

      have hXOE_less_XOC :
          HilbertAngleLess Geo X O E X O C :=
        hilbert_interior_angle_less
          Geo O E X C hXOC hInsideE

      have hXOE :
          Not (PrimCollinear Geo X O E) :=
        hXOE_less_XOC.1

      rcases
          hilbert_interior_subangle_transport_both
            Geo
            O' X' C' D'
            X O E
            hX'O'C'
            hXOE
            hInsideD'
            hWholeTarget
        with
        ⟨F, hInsideF, hTargetParts⟩

      have hXOF_less_XOE :
          HilbertAngleLess Geo X O F X O E :=
        hilbert_interior_angle_less
          Geo O F X E hXOE hInsideF

      have hXOF :
          Not (PrimCollinear Geo X O F) :=
        hXOF_less_XOE.1

      have hXOD_XOF :
          HilbertAngleLess Geo X O D X O F :=
        hilbert_angleLess_transport_right
          Geo
          X O D
          X' O' D'
          X O F
          hLeft
          hXOF
          hTargetParts.2

      have hXOD_XOE :
          HilbertAngleLess Geo X O D X O E :=
        hilbert_angleLess_trans
          Geo
          X O D
          X O F
          X O E
          hXOD_XOF
          hXOF_less_XOE

      ----------------------------------------------------------------
      -- Promote D from the whole XOC to the embedded whole XOE.
      ----------------------------------------------------------------

      have hOX : O ≠ X :=
        hilbert_noncollinear_ne_first
          Geo O X C
          (by
            intro h
            exact hXOC
              (PrimCollinearSwap Geo O X C h))

      rcases
          HilbertPlaneIncidence.line_through
            O X hOX
        with
        ⟨lineOX, hOlineOX, hXlineOX⟩

      have hDCSameOX :
          HilbertSameSide Geo D C lineOX :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O D C X
          lineOX
          hOlineOX
          hXlineOX
          hCOX
          hInsideDrev

      have hInsideErevWhole :
          HilbertRayMeetsSegment Geo O E C X :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo O E X C hInsideE

      have hECSameOX :
          HilbertSameSide Geo E C lineOX :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O E C X
          lineOX
          hOlineOX
          hXlineOX
          hCOX
          hInsideErevWhole

      have hCESameOX :
          HilbertSameSide Geo C E lineOX :=
        hilbert_sameSide_symm
          Geo E C lineOX hECSameOX

      have hDESameOX :
          HilbertSameSide Geo D E lineOX :=
        hilbert_sameSide_trans
          Geo D C E lineOX hDCSameOX hCESameOX

      have hInsideD_XE :
          HilbertRayMeetsSegment Geo O D X E :=
        hilbert_angleDecomposition_angle_less_ray_inside
          Geo
          D E O X
          lineOX
          hOlineOX
          hXlineOX
          hOX
          hDESameOX
          hXOD_XOE

      ----------------------------------------------------------------
      -- Inside XOE, D precedes F, so EOF < EOD.
      ----------------------------------------------------------------

      have hEOF_EOD :
          HilbertAngleLess Geo E O F E O D :=
        hilbert_angleDecomposition_complement_order_reverse
          Geo
          O X E D F
          hXOE
          hInsideD_XE
          hInsideF
          hXOD_XOF

      ----------------------------------------------------------------
      -- Inside XOC, D precedes E.  Therefore E lies inside DOC.
      ----------------------------------------------------------------

      have hCOE_COD :
          HilbertAngleLess Geo C O E C O D :=
        hilbert_angleDecomposition_complement_order_reverse
          Geo
          O X C D E
          hXOC
          hInsideD
          hInsideE
          hXOD_XOE

      have hOC : O ≠ C :=
        hilbert_noncollinear_ne_first
          Geo O C X
          (by
            intro h
            exact hXOC
              (PrimCollinearRotate
                Geo X C O
                (PrimCollinearSymm Geo O C X h)))

      rcases
          HilbertPlaneIncidence.line_through
            O C hOC
        with
        ⟨lineOC, hOlineOC, hClineOC⟩

      have hDXSameOC :
          HilbertSameSide Geo D X lineOC :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O D X C
          lineOC
          hOlineOC
          hClineOC
          hXOC
          hInsideD

      have hEXSameOC :
          HilbertSameSide Geo E X lineOC :=
        hilbert_angleDecomposition_interior_ray_sameSide_first
          Geo
          O E X C
          lineOC
          hOlineOC
          hClineOC
          hXOC
          hInsideE

      have hXDSameOC :
          HilbertSameSide Geo X D lineOC :=
        hilbert_sameSide_symm
          Geo D X lineOC hDXSameOC

      have hEDSameOC :
          HilbertSameSide Geo E D lineOC :=
        hilbert_sameSide_trans
          Geo E X D lineOC hEXSameOC hXDSameOC

      have hInsideE_CD :
          HilbertRayMeetsSegment Geo O E C D :=
        hilbert_angleDecomposition_angle_less_ray_inside
          Geo
          E D O C
          lineOC
          hOlineOC
          hClineOC
          hOC
          hEDSameOC
          hCOE_COD

      have hInsideE_DC :
          HilbertRayMeetsSegment Geo O E D C :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo O E C D hInsideE_CD

      have hDOC :
          Not (PrimCollinear Geo D O C) := by
        intro h
        exact hCOD
          (PrimCollinearSymm Geo D O C h)

      have hDOE_DOC :
          HilbertAngleLess Geo D O E D O C :=
        hilbert_interior_angle_less
          Geo O E D C hDOC hInsideE_DC

      have hDOE :
          Not (PrimCollinear Geo D O E) :=
        hDOE_DOC.1

      have hEOD :
          Not (PrimCollinear Geo E O D) := by
        intro h
        exact hDOE
          (PrimCollinearSymm Geo E O D h)

      have hReflDOE :
          Geo.AngleCongruent D O E D O E :=
        Geometry.Geo.angle_congruent_reflexive
          Geo D O E

      have hEOD_DOE :
          Geo.AngleCongruent E O D D O E :=
        (Geometry.Geo.angle_congruent_reverse_first
          Geo D O E D O E).mp hReflDOE

      have hEOD_DOC :
          HilbertAngleLess Geo E O D D O C :=
        hilbert_angleLess_transport_left
          Geo
          D O E
          E O D
          D O C
          hDOE_DOC
          hEOD
          hEOD_DOE

      have hReflDOC :
          Geo.AngleCongruent D O C D O C :=
        Geometry.Geo.angle_congruent_reflexive
          Geo D O C

      have hDOC_COD :
          Geo.AngleCongruent D O C C O D :=
        (Geometry.Geo.angle_congruent_reverse_second
          Geo D O C D O C).mp hReflDOC

      have hEOD_COD :
          HilbertAngleLess Geo E O D C O D :=
        hilbert_angleLess_transport_right
          Geo
          E O D
          D O C
          C O D
          hEOD_DOC
          hCOD
          hDOC_COD

      have hEOF_COD :
          HilbertAngleLess Geo E O F C O D :=
        hilbert_angleLess_trans
          Geo
          E O F
          E O D
          C O D
          hEOF_EOD
          hEOD_COD

      ----------------------------------------------------------------
      -- But the assumed second component inequality says COD < EOF.
      ----------------------------------------------------------------

      have hEOX :
          Not (PrimCollinear Geo E O X) := by
        intro h
        exact hXOE
          (PrimCollinearSymm Geo E O X h)

      have hInsideFrev :
          HilbertRayMeetsSegment Geo O F E X :=
        hilbert_angleDecomposition_ray_meets_segment_reverse
          Geo O F X E hInsideF

      have hEOF :
          Not (PrimCollinear Geo E O F) :=
        (hilbert_interior_angle_less
          Geo O F E X hEOX hInsideFrev).1

      have hCOD_EOF :
          HilbertAngleLess Geo C O D E O F :=
        hilbert_angleLess_transport_right
          Geo
          C O D
          C' O' D'
          E O F
          hRight
          hEOF
          hTargetParts.1

      have hCycle :
          HilbertAngleLess Geo C O D C O D :=
        hilbert_angleLess_trans
          Geo
          C O D
          E O F
          C O D
          hCOD_EOF
          hEOF_COD

      exact
        False.elim
          ((hilbert_angleLess_irrefl
            Geo C O D)
            hCycle)




------------------------------------------------------------------------
-- 2. Strict monotonicity of angle halves.
------------------------------------------------------------------------

/--
Strict monotonicity of synthetic angle halves.

If two proper angles are bisected by interior rays and the first whole
angle is strictly smaller than the second whole angle, then the first
half is strictly smaller than the second half.

This is the non-numerical form of

  alpha < beta  ->  alpha/2 < beta/2.
-/

theorem hilbert_angleDecomposition_half_less_of_whole_less
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O X C D O' X' C' D' : Geo.Point)
    (hXOC : Not (PrimCollinear Geo X O C))
    (hX'O'C' : Not (PrimCollinear Geo X' O' C'))
    (hInsideD : HilbertRayMeetsSegment Geo O D X C)
    (hInsideD' : HilbertRayMeetsSegment Geo O' D' X' C')
    (hBisect :
      Geo.AngleCongruent
        X O D
        C O D)
    (hBisect' :
      Geo.AngleCongruent
        X' O' D'
        C' O' D')
    (hWholeLess :
      HilbertAngleLess Geo
        X O C
        X' O' C') :
    HilbertAngleLess Geo
      X O D
      X' O' D' := by

  have hXOD :
      Not (PrimCollinear Geo X O D) :=
    (hilbert_interior_angle_less
      Geo
      O D X C
      hXOC
      hInsideD).1

  have hX'O'D' :
      Not (PrimCollinear Geo X' O' D') :=
    (hilbert_interior_angle_less
      Geo
      O' D' X' C'
      hX'O'C'
      hInsideD').1

  have hCOX :
      Not (PrimCollinear Geo C O X) := by
    intro h
    exact
      hXOC
        (PrimCollinearSymm
          Geo C O X h)

  have hC'O'X' :
      Not (PrimCollinear Geo C' O' X') := by
    intro h
    exact
      hX'O'C'
        (PrimCollinearSymm
          Geo C' O' X' h)

  have hInsideDrev :
      HilbertRayMeetsSegment Geo O D C X :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O D X C
      hInsideD

  have hInsideD'rev :
      HilbertRayMeetsSegment Geo O' D' C' X' :=
    hilbert_angleDecomposition_ray_meets_segment_reverse
      Geo
      O' D' X' C'
      hInsideD'

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    (hilbert_interior_angle_less
      Geo
      O D C X
      hCOX
      hInsideDrev).1

  have hC'O'D' :
      Not (PrimCollinear Geo C' O' D') :=
    (hilbert_interior_angle_less
      Geo
      O' D' C' X'
      hC'O'X'
      hInsideD'rev).1

  rcases
      angle_trichotomy
        Geo
        X O D
        X' O' D'
        hXOD
        hX'O'D'
    with hEq | hOrder

  --------------------------------------------------------------------
  -- Equal halves would force equal whole angles.
  --------------------------------------------------------------------

  · have hXOD_DOC :
        Geo.AngleCongruent
          X O D
          D O C :=
      (Geo.angle_congruent_reverse_second
        X O D
        C O D).mp
        hBisect

    have hX'O'D'_D'O'C' :
        Geo.AngleCongruent
          X' O' D'
          D' O' C' :=
      (Geo.angle_congruent_reverse_second
        X' O' D'
        C' O' D').mp
        hBisect'

    have hDOC_XOD :
        Geo.AngleCongruent
          D O C
          X O D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O D
        D O C
        hXOD_DOC

    have hDOC_X'O'D' :
        Geo.AngleCongruent
          D O C
          X' O' D' :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        D O C
        X O D
        X' O' D'
        hDOC_XOD
        hEq

    have hDOC_D'O'C' :
        Geo.AngleCongruent
          D O C
          D' O' C' :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        D O C
        X' O' D'
        D' O' C'
        hDOC_X'O'D'
        hX'O'D'_D'O'C'

    have hWholeEq :
        Geo.AngleCongruent
          X O C
          X' O' C' :=
      hilbert_angleDecomposition_angle_addition_interior
        Geo
        O X C D
        O' X' C' D'
        hXOC
        hX'O'C'
        hInsideD
        hInsideD'
        hEq
        hDOC_D'O'C'

    have hWholeEqSymm :
        Geo.AngleCongruent
          X' O' C'
          X O C :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        X O C
        X' O' C'
        hWholeEq

    have hCycle :
        HilbertAngleLess Geo
          X O C
          X O C :=
      hilbert_angleLess_transport_right
        Geo
        X O C
        X' O' C'
        X O C
        hWholeLess
        hXOC
        hWholeEqSymm

    exact
      False.elim
        ((hilbert_angleLess_irrefl
          Geo X O C)
          hCycle)

  --------------------------------------------------------------------
  -- Strict order of halves.
  --------------------------------------------------------------------

  · rcases hOrder with hWanted | hReverse

    · exact hWanted

    ------------------------------------------------------------------
    -- Reverse half order would force reverse whole order.
    ------------------------------------------------------------------

    · have hC'O'D'_X'O'D' :
          Geo.AngleCongruent
            C' O' D'
            X' O' D' :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          X' O' D'
          C' O' D'
          hBisect'

      have hC'O'D'_XOD :
          HilbertAngleLess Geo
            C' O' D'
            X O D :=
        hilbert_angleLess_transport_left
          Geo
          X' O' D'
          C' O' D'
          X O D
          hReverse
          hC'O'D'
          hC'O'D'_X'O'D'

      have hC'O'D'_COD :
          HilbertAngleLess Geo
            C' O' D'
            C O D :=
        hilbert_angleLess_transport_right
          Geo
          C' O' D'
          X O D
          C O D
          hC'O'D'_XOD
          hCOD
          hBisect

      have hWholeReverse :
          HilbertAngleLess Geo
            X' O' C'
            X O C :=
        hilbert_angleDecomposition_componentwise_less_whole
          Geo
          O' X' C' D'
          O X C D
          hX'O'C'
          hXOC
          hInsideD'
          hInsideD
          hReverse
          hC'O'D'_COD

      have hCycle :
          HilbertAngleLess Geo
            X O C
            X O C :=
        hilbert_angleLess_trans
          Geo
          X O C
          X' O' C'
          X O C
          hWholeLess
          hWholeReverse

      exact
        False.elim
          ((hilbert_angleLess_irrefl
            Geo X O C)
            hCycle)

/-!
## Reusable crossing-circle infrastructure

The results below are proposition-independent support lemmas extracted from
the former consolidated Book IV proof module. They form the reusable layer
below the numbered proposition modules and therefore introduce no imports
from `Proposition4_NN`.
-/

theorem hilbert_crossing_first_secant_noncollinear
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hAC : A ≠ C) :
    Not (PrimCollinear Geo A C B) := by

  intro hACB

  have hOAC :
      PrimCollinear Geo O A C :=
    hRayAC.2.2.1

  have hOAB :
      PrimCollinear Geo O A B :=
    hilbert_primCollinear_trans
      Geo
      O A C B
      hAC
      hOAC
      hACB

  have hABO :
      PrimCollinear Geo A B O :=
    PrimCollinearCycle
      Geo O A B hOAB

  have hAOB' :
      PrimCollinear Geo A O B :=
    PrimCollinearRotate
      Geo A B O hABO

  exact hAOB hAOB'

theorem hilbert_crossing_second_secant_noncollinear
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayBD : HilbertSameRay Geo O B D)
    (hBD : B ≠ D) :
    Not (PrimCollinear Geo A D B) := by

  intro hADB

  have hOBD :
      PrimCollinear Geo O B D :=
    hRayBD.2.2.1

  have hBDO :
      PrimCollinear Geo B D O :=
    PrimCollinearCycle
      Geo O B D hOBD

  have hABD :
      PrimCollinear Geo A B D :=
    PrimCollinearRotate
      Geo A D B hADB

  have hABO :
      PrimCollinear Geo A B O :=
    hilbert_primCollinear_trans
      Geo
      A B D O
      hBD
      hABD
      hBDO

  have hAOB' :
      PrimCollinear Geo A O B :=
    PrimCollinearRotate
      Geo A B O hABO

  exact hAOB hAOB'

theorem hilbert_crossing_nondegenerate_data
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D) :
    Not (PrimCollinear Geo O A D) ∧
    Not (PrimCollinear Geo O B C) ∧
    (Geo.Between O A C ∨ Geo.Between O C A) ∧
    (Geo.Between O B D ∨ Geo.Between O D B) := by

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hRayAC.1

  have hRayBB :
      HilbertSameRay Geo O B B :=
    hilbert_sameRay_refl
      Geo O B hRayBD.1

  have hAOD :
      Not (PrimCollinear Geo A O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      A D
      hAOB
      hRayAA
      hRayBD

  have hOAD :
      Not (PrimCollinear Geo O A D) := by
    intro h
    exact
      hAOD
        (PrimCollinearSwap
          Geo O A D h)

  have hCOB :
      Not (PrimCollinear Geo C O B) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C B
      hAOB
      hRayAC
      hRayBB

  have hOBC :
      Not (PrimCollinear Geo O B C) := by
    intro h
    exact
      hCOB
        (PrimCollinearRotate
          Geo
          C B O
          (PrimCollinearSymm
            Geo O B C h))

  have hOrderAC :
      Geo.Between O A C ∨
      Geo.Between O C A := by

    rcases
        hilbert_sameRay_cases
          Geo O A C hRayAC
      with hEq | hOAC | hOCA

    · exact False.elim (hAC hEq)

    · exact Or.inl hOAC

    · exact Or.inr hOCA

  have hOrderBD :
      Geo.Between O B D ∨
      Geo.Between O D B := by

    rcases
        hilbert_sameRay_cases
          Geo O B D hRayBD
      with hEq | hOBD | hODB

    · exact False.elim (hBD hEq)

    · exact Or.inl hOBD

    · exact Or.inr hODB

  exact
    ⟨hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩

theorem hilbert_crossing_angle_at_O
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D) :
    Geo.AngleCongruent
      A O D
      B O C := by

  have hAOB_AOD :
      Geo.Angle A O B =
      Geo.Angle A O D :=
    hilbert_angle_eq_of_sameRay_second
      Geo O A B D hRayBD

  have hBOA_BOC :
      Geo.Angle B O A =
      Geo.Angle B O C :=
    hilbert_angle_eq_of_sameRay_second
      Geo O B A C hRayAC

  have hAOB_BOA :
      Geo.AngleCongruent
        A O B
        B O A :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A O B
      A O B).mp
      (Geometry.Geo.angle_congruent_reflexive
        Geo A O B)

  unfold Geometry.Geo.AngleCongruent at hAOB_BOA ⊢

  rw [← hAOB_AOD, ← hBOA_BOC]

  exact hAOB_BOA

theorem hilbert_crossing_outer_outer_angles
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A C B D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hOBC : Not (PrimCollinear Geo O B C))
    (hOAC : Geo.Between O A C)
    (hOBD : Geo.Between O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    Geo.AngleCongruent
      C A D
      C B D := by

  --------------------------------------------------------------------
  -- A != D.
  --------------------------------------------------------------------

  have hADO :
      Not (PrimCollinear Geo A D O) := by

    intro h

    have hDOA :
        PrimCollinear Geo D O A :=
      PrimCollinearCycle
        Geo A D O h

    have hOAD' :
        PrimCollinear Geo O A D :=
      PrimCollinearCycle
        Geo D O A hDOA

    exact hOAD hOAD'

  have hAD :
      A ≠ D :=
    hilbert_noncollinear_ne_first
      Geo A D O hADO

  --------------------------------------------------------------------
  -- B != C.
  --------------------------------------------------------------------

  have hBCO :
      Not (PrimCollinear Geo B C O) := by

    intro h

    have hCOB :
        PrimCollinear Geo C O B :=
      PrimCollinearCycle
        Geo B C O h

    have hOBC' :
        PrimCollinear Geo O B C :=
      PrimCollinearCycle
        Geo C O B hCOB

    exact hOBC hOBC'

  have hBC :
      B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C O hBCO

  --------------------------------------------------------------------
  -- Since O-A-C, angle DAC is supplementary to OAD.
  --------------------------------------------------------------------

  have hRayADD :
      HilbertSameRay Geo A D D :=
    hilbert_sameRay_refl
      Geo A D hAD.symm

  have hSuppA :
      BookZeroSupplement Geo
        O A D
        D C :=
    ⟨hRayADD, hOAC⟩

  --------------------------------------------------------------------
  -- Since O-B-D, angle CBD is supplementary to OBC.
  --------------------------------------------------------------------

  have hRayBCC :
      HilbertSameRay Geo B C C :=
    hilbert_sameRay_refl
      Geo B C hBC.symm

  have hSuppB :
      BookZeroSupplement Geo
        O B C
        C D :=
    ⟨hRayBCC, hOBD⟩

  --------------------------------------------------------------------
  -- Supplements of congruent angles are congruent.
  --------------------------------------------------------------------

  have hDAC_CBD :
      Geo.AngleCongruent
        D A C
        C B D :=
    bookZero_43_supplements
      Geo
      O A D
      D C
      O B C
      C D
      hAngle
      hSuppA
      hSuppB
      hOAD
      hOBC

  --------------------------------------------------------------------
  -- Reverse the first angle: DAC = CAD.
  --------------------------------------------------------------------

  exact
    (Geo.angle_congruent_reverse_first
      D A C
      C B D).mp
      hDAC_CBD

theorem hilbert_crossing_inner_inner_angles
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A C B D : Geo.Point)
    (hOCA : Geo.Between O C A)
    (hODB : Geo.Between O D B)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    Geo.AngleCongruent
      C A D
      C B D := by

  have hACO :
      Geo.Between A C O :=
    (HilbertOrder.between_incidence
      O C A hOCA).2.2.2.2

  have hBDO :
      Geo.Between B D O :=
    (HilbertOrder.between_incidence
      O D B hODB).2.2.2.2

  have hRayACO :
      HilbertSameRay Geo A C O :=
    hilbert_sameRay_of_between
      Geo A C O hACO

  have hRayAOC :
      HilbertSameRay Geo A O C :=
    hilbert_sameRay_symm
      Geo A C O hRayACO

  have hRayBDO :
      HilbertSameRay Geo B D O :=
    hilbert_sameRay_of_between
      Geo B D O hBDO

  have hRayBOD :
      HilbertSameRay Geo B O D :=
    hilbert_sameRay_symm
      Geo B D O hRayBDO

  have hLeft :
      Geo.Angle O A D =
      Geo.Angle C A D :=
    hilbert_angle_eq_of_sameRay_first
      Geo A O C D hRayAOC

  have hRight :
      Geo.Angle O B C =
      Geo.Angle D B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B O D C hRayBOD

  have hCAD_DBC :
      Geo.AngleCongruent
        C A D
        D B C := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [← hLeft, ← hRight]

    exact hAngle

  exact
    (Geo.angle_congruent_reverse_second
      C A D
      D B C).mp
      hCAD_DBC

theorem hilbert_crossing_mixed_outer_inner_angle_data
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A C B D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hOAC : Geo.Between O A C)
    (hODB : Geo.Between O D B)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    BookZeroSupplement Geo
        O A D
        D C
    ∧
    Geo.AngleCongruent
        O A D
        C B D := by

  have hADO :
      Not (PrimCollinear Geo A D O) := by
    intro h
    exact
      hOAD
        (PrimCollinearRotate
          Geo
          O D A
          (PrimCollinearSymm
            Geo A D O h))

  have hAD :
      A ≠ D :=
    hilbert_noncollinear_ne_first
      Geo A D O hADO

  have hRayADD :
      HilbertSameRay Geo A D D :=
    hilbert_sameRay_refl
      Geo A D hAD.symm

  have hSuppA :
      BookZeroSupplement Geo
        O A D
        D C :=
    ⟨hRayADD, hOAC⟩

  have hBDO :
      Geo.Between B D O :=
    (HilbertOrder.between_incidence
      O D B hODB).2.2.2.2

  have hRayBDO :
      HilbertSameRay Geo B D O :=
    hilbert_sameRay_of_between
      Geo B D O hBDO

  have hRayBOD :
      HilbertSameRay Geo B O D :=
    hilbert_sameRay_symm
      Geo B D O hRayBDO

  have hRight :
      Geo.Angle O B C =
      Geo.Angle D B C :=
    hilbert_angle_eq_of_sameRay_first
      Geo B O D C hRayBOD

  have hOAD_DBC :
      Geo.AngleCongruent
        O A D
        D B C := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [← hRight]

    exact hAngle

  have hOAD_CBD :
      Geo.AngleCongruent
        O A D
        C B D :=
    (Geo.angle_congruent_reverse_second
      O A D
      D B C).mp
      hOAD_DBC

  exact
    ⟨hSuppA, hOAD_CBD⟩

theorem hilbert_crossing_mixed_inner_outer_angle_data
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (O A C B D : Geo.Point)
    (hOBC : Not (PrimCollinear Geo O B C))
    (hOCA : Geo.Between O C A)
    (hOBD : Geo.Between O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    Geo.AngleCongruent
        C A D
        O B C
    ∧
    BookZeroSupplement Geo
        O B C
        C D := by

  --------------------------------------------------------------------
  -- Transport OAD to CAD, since O-C-A.
  --------------------------------------------------------------------

  have hACO :
      Geo.Between A C O :=
    (HilbertOrder.between_incidence
      O C A hOCA).2.2.2.2

  have hRayACO :
      HilbertSameRay Geo A C O :=
    hilbert_sameRay_of_between
      Geo A C O hACO

  have hRayAOC :
      HilbertSameRay Geo A O C :=
    hilbert_sameRay_symm
      Geo A C O hRayACO

  have hLeft :
      Geo.Angle O A D =
      Geo.Angle C A D :=
    hilbert_angle_eq_of_sameRay_first
      Geo A O C D hRayAOC

  have hCAD_OBC :
      Geo.AngleCongruent
        C A D
        O B C := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle ⊢

    rw [← hLeft]

    exact hAngle

  --------------------------------------------------------------------
  -- Since O-B-D, CBD is supplementary to OBC.
  --------------------------------------------------------------------

  have hBCO :
      Not (PrimCollinear Geo B C O) := by
    intro h

    have hCOB :
        PrimCollinear Geo C O B :=
      PrimCollinearCycle
        Geo B C O h

    have hOBC' :
        PrimCollinear Geo O B C :=
      PrimCollinearCycle
        Geo C O B hCOB

    exact hOBC hOBC'

  have hBC :
      B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C O hBCO

  have hRayBCC :
      HilbertSameRay Geo B C C :=
    hilbert_sameRay_refl
      Geo B C hBC.symm

  have hSuppB :
      BookZeroSupplement Geo
        O B C
        C D :=
    ⟨hRayBCC, hOBD⟩

  exact
    ⟨hCAD_OBC, hSuppB⟩

theorem hilbert_crossing_nondegenerate_angle_classification
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    (
      Geo.AngleCongruent
        C A D
        C B D
    )
    ∨
    (
      BookZeroSupplement Geo
        O A D
        D C
      ∧
      Geo.AngleCongruent
        O A D
        C B D
    )
    ∨
    (
      Geo.AngleCongruent
        C A D
        O B C
      ∧
      BookZeroSupplement Geo
        O B C
        C D
    ) := by

  rcases
      hilbert_crossing_nondegenerate_data
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
    with
    ⟨hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩

  rcases hOrderAC with hOAC | hOCA

  --------------------------------------------------------------------
  -- O-A-C
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-A-C and O-B-D
    --------------------------------------------------------------

    · left

      exact
        hilbert_crossing_outer_outer_angles
          Geo
          O A C B D
          hOAD
          hOBC
          hOAC
          hOBD
          hAngle

    --------------------------------------------------------------
    -- O-A-C and O-D-B
    --------------------------------------------------------------

    · right
      left

      exact
        hilbert_crossing_mixed_outer_inner_angle_data
          Geo
          O A C B D
          hOAD
          hOAC
          hODB
          hAngle

  --------------------------------------------------------------------
  -- O-C-A
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-C-A and O-B-D
    --------------------------------------------------------------

    · right
      right

      exact
        hilbert_crossing_mixed_inner_outer_angle_data
          Geo
          O A C B D
          hOBC
          hOCA
          hOBD
          hAngle

    --------------------------------------------------------------
    -- O-C-A and O-D-B
    --------------------------------------------------------------

    · left

      exact
        hilbert_crossing_inner_inner_angles
          Geo
          O A C B D
          hOCA
          hODB
          hAngle


------------------------------------------------------------------------
-- Circumcircle of the three already controlled points A,C,D.

theorem hilbert_crossing_acd_circumcircle
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C D : Geo.Point)
    (hOAD : Not (PrimCollinear Geo O A D))
    (hRayAC : HilbertSameRay Geo O A C)
    (hAC : A ≠ C) :
    ∃ K : Geo.Point,
      HilbertCircle Geo K A A ∧
      HilbertCircle Geo K A C ∧
      HilbertCircle Geo K A D := by

  have hOAC :
      PrimCollinear Geo O A C :=
    hRayAC.2.2.1

  have hACD :
      Not (PrimCollinear Geo A C D) := by
    intro hACD
    have hOAD' :
        PrimCollinear Geo O A D :=
      hilbert_primCollinear_trans
        Geo
        O A C D
        hAC
        hOAC
        hACD
    exact hOAD hOAD'

  rcases
      hilbert_triangle_circumcenter_exists_XI
        Geo
        A C D
        hACD
    with
    ⟨K, hKA_KC, hKA_KD⟩

  refine
    ⟨K, ?_, ?_, ?_⟩

  · unfold HilbertCircle
    exact
      hilbert_congruent_reflexive
        Geo K A

  · unfold HilbertCircle
    exact
      hilbert_congruent_symmetry
        Geo
        K A K C
        hKA_KC

  · unfold HilbertCircle
    exact
      hilbert_congruent_symmetry
        Geo
        K A K D
        hKA_KD


------------------------------------------------------------------------
-- Combined nondegenerate certificate.

theorem hilbert_crossing_nondegenerate_certificate
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    ∃ K : Geo.Point,
      HilbertCircle Geo K A A ∧
      HilbertCircle Geo K A C ∧
      HilbertCircle Geo K A D ∧
      (
        Geo.AngleCongruent
          C A D
          C B D
        ∨
        (
          BookZeroSupplement Geo
            O A D
            D C
          ∧
          Geo.AngleCongruent
            O A D
            C B D
        )
        ∨
        (
          Geo.AngleCongruent
            C A D
            O B C
          ∧
          BookZeroSupplement Geo
            O B C
            C D
        )
      ) := by

  rcases
      hilbert_crossing_nondegenerate_data
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
    with
    ⟨hOAD, _hOBC, _hOrderAC, _hOrderBD⟩

  rcases
      hilbert_crossing_acd_circumcircle
        Geo
        O A C D
        hOAD
        hRayAC
        hAC
    with
    ⟨K, hA, hC, hD⟩

  have hClass :=
    hilbert_crossing_nondegenerate_angle_classification
      Geo
      O A C B D
      hAOB
      hRayAC
      hRayBD
      hAC
      hBD
      hAngle

  exact
    ⟨K,
      hA,
      hC,
      hD,
      hClass⟩

theorem hilbert_crossing_concyclic_degenerate
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hDeg : A = C ∨ B = D) :
    HilbertConcyclic4 Geo A C D B := by

  rcases hDeg with hACeq | hBDeq

  --------------------------------------------------------------------
  -- A = C.
  --------------------------------------------------------------------

  · subst C

    by_cases hBD : B = D

    --------------------------------------------------------------
    -- A = C and B = D.
    --------------------------------------------------------------

    · subst D

      rcases
          hilbert_triangle_circumcenter_exists_XI
            Geo
            A O B
            hAOB
        with
        ⟨K, _hKA_KO, hKA_KB⟩

      refine
        ⟨K, ?_, ?_, ?_⟩

      · exact
          hilbert_congruent_reflexive
            Geo K A

      · exact hKA_KB

      · exact hKA_KB

    --------------------------------------------------------------
    -- A = C, B != D.
    --------------------------------------------------------------

    · have hADB :
          Not (PrimCollinear Geo A D B) :=
        hilbert_crossing_second_secant_noncollinear
          Geo
          O A B D
          hAOB
          hRayBD
          hBD

      rcases
          hilbert_triangle_circumcenter_exists_XI
            Geo
            A D B
            hADB
        with
        ⟨K, hKA_KD, hKA_KB⟩

      refine
        ⟨K, ?_, ?_, ?_⟩

      · exact
          hilbert_congruent_reflexive
            Geo K A

      · exact hKA_KD

      · exact hKA_KB

  --------------------------------------------------------------------
  -- B = D.
  --------------------------------------------------------------------

  · subst D

    by_cases hAC : A = C

    --------------------------------------------------------------
    -- Again A = C and B = D.
    --------------------------------------------------------------

    · subst C

      rcases
          hilbert_triangle_circumcenter_exists_XI
            Geo
            A O B
            hAOB
        with
        ⟨K, _hKA_KO, hKA_KB⟩

      refine
        ⟨K, ?_, ?_, ?_⟩

      · exact
          hilbert_congruent_reflexive
            Geo K A

      · exact hKA_KB

      · exact hKA_KB

    --------------------------------------------------------------
    -- B = D, A != C.
    --------------------------------------------------------------

    · have hACB :
          Not (PrimCollinear Geo A C B) :=
        hilbert_crossing_first_secant_noncollinear
          Geo
          O A C B
          hAOB
          hRayAC
          hAC

      rcases
          hilbert_triangle_circumcenter_exists_XI
            Geo
            A C B
            hACB
        with
        ⟨K, hKA_KC, hKA_KB⟩

      refine
        ⟨K, ?_, ?_, ?_⟩

      · exact hKA_KC

      · exact hKA_KB

      · exact hKA_KB


------------------------------------------------------------------------
-- 2. Outer/outer: A and B are on the same side of chord CD.

theorem hilbert_crossing_outer_outer_sameSide_chord
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOAC : Geo.Between O A C)
    (hOBD : Geo.Between O B D) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      HilbertSameSide Geo A B chord := by

  have hRayAC :
      HilbertSameRay Geo O A C :=
    hilbert_sameRay_of_between
      Geo O A C hOAC

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_of_between
      Geo O B D hOBD

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hOCD :
      Not (PrimCollinear Geo O C D) := by
    intro h
    apply hCOD
    exact
      PrimCollinearRotate
        Geo C D O
        (PrimCollinearCycle
          Geo O C D h)

  have hODC :
      Not (PrimCollinear Geo O D C) := by
    intro h
    exact
      hOCD
        (PrimCollinearRotate
          Geo O D C h)

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    apply hOCD
    exact
      PrimCollinearCycle
        Geo D O C
        (PrimCollinearCycle
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        O A D C
        hOAC
        hOCD
    with
    ⟨chord1, hDchord1, hCchord1, hOA⟩

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        O B C D
        hOBD
        hODC
    with
    ⟨chord2, hCchord2, hDchord2, hOB⟩

  have hChordEq :
      chord1 = chord2 :=
    HilbertPlaneIncidence.line_unique
      C D hCD
      chord1 chord2
      hCchord1
      hDchord1
      hCchord2
      hDchord2

  rw [← hChordEq] at hOB

  have hAO :
      HilbertSameSide Geo A O chord1 :=
    hilbert_sameSide_symm
      Geo O A chord1 hOA

  have hAB :
      HilbertSameSide Geo A B chord1 :=
    hilbert_sameSide_trans
      Geo A O B chord1
      hAO
      hOB

  exact
    ⟨chord1,
      hCchord1,
      hDchord1,
      hAB⟩


------------------------------------------------------------------------
-- 3. Inner/inner: A and B are on the same side of chord CD.

theorem hilbert_crossing_inner_inner_sameSide_chord
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOCA : Geo.Between O C A)
    (hODB : Geo.Between O D B) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      HilbertSameSide Geo A B chord := by

  have hRayCA :
      HilbertSameRay Geo O C A :=
    hilbert_sameRay_of_between
      Geo O C A hOCA

  have hRayAC :
      HilbertSameRay Geo O A C :=
    hilbert_sameRay_symm
      Geo O C A hRayCA

  have hRayDB :
      HilbertSameRay Geo O D B :=
    hilbert_sameRay_of_between
      Geo O D B hODB

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_symm
      Geo O D B hRayDB

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  rcases
      HilbertPlaneIncidence.line_through
        C D hCD
    with
    ⟨chord, hCchord, hDchord⟩

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h
    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  have hSame :
      HilbertSameSide Geo A B chord :=
    hilbert_third_side_endpoints_sameSide
      Geo
      O A B
      C D
      chord
      hOAB
      hOCA
      hODB
      hCchord
      hDchord

  exact
    ⟨chord,
      hCchord,
      hDchord,
      hSame⟩


------------------------------------------------------------------------
-- 4. Mixed outer/inner: A and B are on opposite sides of chord CD.

theorem hilbert_crossing_mixed_outer_inner_oppositeSide_chord
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOAC : Geo.Between O A C)
    (hODB : Geo.Between O D B) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      HilbertOppositeSide Geo A B chord := by

  have hRayAC :
      HilbertSameRay Geo O A C :=
    hilbert_sameRay_of_between
      Geo O A C hOAC

  have hRayDB :
      HilbertSameRay Geo O D B :=
    hilbert_sameRay_of_between
      Geo O D B hODB

  have hRayBD :
      HilbertSameRay Geo O B D :=
    hilbert_sameRay_symm
      Geo O D B hRayDB

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hOCD :
      Not (PrimCollinear Geo O C D) := by
    intro h
    exact
      hCOD
        (PrimCollinearSwap
          Geo O C D h)

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  rcases
      HilbertPlaneIncidence.line_through
        C D hCD
    with
    ⟨chord, hCchord, hDchord⟩

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        O A D C
        hOAC
        hOCD
    with
    ⟨chord1, hDchord1, hCchord1, hOA1⟩

  have hChordEq :
      chord1 = chord :=
    HilbertPlaneIncidence.line_unique
      C D hCD
      chord1 chord
      hCchord1
      hDchord1
      hCchord
      hDchord

  have hOA :
      HilbertSameSide Geo O A chord := by
    rw [← hChordEq]
    exact hOA1

  have hOppOB :
      HilbertOppositeSide Geo O B chord :=
    ⟨hOA.1,
      by
        intro hBchord

        have hODBData :=
          HilbertOrder.between_incidence
            O D B hODB

        have hDB :
            D ≠ B :=
          hODBData.2.1

        have hODBcol :
            PrimCollinear Geo O D B :=
          hODBData.2.2.2.1

        have hDBO :
            PrimCollinear Geo D B O :=
          PrimCollinearCycle
            Geo O D B hODBcol

        have hOchord :
            H.OnLine O chord :=
          hilbert_collinear_on_line
            Geo
            D B O
            chord
            hDB
            hDchord
            hBchord
            hDBO

        exact hOA.1 hOchord,
      ⟨D, hODB, hDchord⟩⟩

  have hOppBO :
      HilbertOppositeSide Geo B O chord :=
    hilbert_oppositeSide_symm
      Geo O B chord hOppOB

  have hOppBA :
      HilbertOppositeSide Geo B A chord :=
    hilbert_oppositeSide_transport_right
      Geo
      B O A
      chord
      hOppBO
      hOA

  have hOppAB :
      HilbertOppositeSide Geo A B chord :=
    hilbert_oppositeSide_symm
      Geo B A chord hOppBA

  exact
    ⟨chord,
      hCchord,
      hDchord,
      hOppAB⟩


------------------------------------------------------------------------
-- 5. Mixed inner/outer by symmetry.

theorem hilbert_crossing_mixed_inner_outer_oppositeSide_chord
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hOCA : Geo.Between O C A)
    (hOBD : Geo.Between O B D) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      HilbertOppositeSide Geo A B chord := by

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  rcases
      hilbert_crossing_mixed_outer_inner_oppositeSide_chord
        Geo
        O B D A C
        hBOA
        hOBD
        hOCA
    with
    ⟨chord,
      hDchord,
      hCchord,
      hOppBA⟩

  have hOppAB :
      HilbertOppositeSide Geo A B chord :=
    hilbert_oppositeSide_symm
      Geo B A chord hOppBA

  exact
    ⟨chord,
      hCchord,
      hDchord,
      hOppAB⟩


------------------------------------------------------------------------
-- 6. Exact nondegenerate chord classification.

theorem hilbert_crossing_nondegenerate_chord_classification
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : A ≠ C)
    (hBD : B ≠ D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    ∃ chord : Geo.Line,
      H.OnLine C chord ∧
      H.OnLine D chord ∧
      (
        (
          HilbertSameSide Geo A B chord ∧
          Geo.AngleCongruent
            C A D
            C B D
        )
        ∨
        (
          HilbertOppositeSide Geo A B chord ∧
          BookZeroSupplement Geo
            O A D
            D C ∧
          Geo.AngleCongruent
            O A D
            C B D
        )
        ∨
        (
          HilbertOppositeSide Geo A B chord ∧
          Geo.AngleCongruent
            C A D
            O B C ∧
          BookZeroSupplement Geo
            O B C
            C D
        )
      ) := by

  rcases
      hilbert_crossing_nondegenerate_data
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
    with
    ⟨hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩

  rcases hOrderAC with hOAC | hOCA

  --------------------------------------------------------------------
  -- O-A-C.
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-A-C and O-B-D: same side + equal angles.
    --------------------------------------------------------------

    · rcases
          hilbert_crossing_outer_outer_sameSide_chord
            Geo
            O A C B D
            hAOB
            hOAC
            hOBD
      with
      ⟨chord, hCchord, hDchord, hSame⟩

      have hEq :
          Geo.AngleCongruent
            C A D
            C B D :=
        hilbert_crossing_outer_outer_angles
          Geo
          O A C B D
          hOAD
          hOBC
          hOAC
          hOBD
          hAngle

      exact
        ⟨chord,
          hCchord,
          hDchord,
          Or.inl ⟨hSame, hEq⟩⟩

    --------------------------------------------------------------
    -- O-A-C and O-D-B: opposite side + supplement at A.
    --------------------------------------------------------------

    · rcases
          hilbert_crossing_mixed_outer_inner_oppositeSide_chord
            Geo
            O A C B D
            hAOB
            hOAC
            hODB
      with
      ⟨chord, hCchord, hDchord, hOpp⟩

      rcases
          hilbert_crossing_mixed_outer_inner_angle_data
            Geo
            O A C B D
            hOAD
            hOAC
            hODB
            hAngle
      with
      ⟨hSuppA, hCongA⟩

      exact
        ⟨chord,
          hCchord,
          hDchord,
          Or.inr
            (Or.inl
              ⟨hOpp,
                hSuppA,
                hCongA⟩)⟩

  --------------------------------------------------------------------
  -- O-C-A.
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    --------------------------------------------------------------
    -- O-C-A and O-B-D: opposite side + supplement at B.
    --------------------------------------------------------------

    · rcases
          hilbert_crossing_mixed_inner_outer_oppositeSide_chord
            Geo
            O A C B D
            hAOB
            hOCA
            hOBD
      with
      ⟨chord, hCchord, hDchord, hOpp⟩

      rcases
          hilbert_crossing_mixed_inner_outer_angle_data
            Geo
            O A C B D
            hOBC
            hOCA
            hOBD
            hAngle
      with
      ⟨hCongB, hSuppB⟩

      exact
        ⟨chord,
          hCchord,
          hDchord,
          Or.inr
            (Or.inr
              ⟨hOpp,
                hCongB,
                hSuppB⟩)⟩

    --------------------------------------------------------------
    -- O-C-A and O-D-B: same side + equal angles.
    --------------------------------------------------------------

    · rcases
          hilbert_crossing_inner_inner_sameSide_chord
            Geo
            O A C B D
            hAOB
            hOCA
            hODB
      with
      ⟨chord, hCchord, hDchord, hSame⟩

      have hEq :
          Geo.AngleCongruent
            C A D
            C B D :=
        hilbert_crossing_inner_inner_angles
          Geo
          O A C B D
          hOCA
          hODB
          hAngle

      exact
        ⟨chord,
          hCchord,
          hDchord,
          Or.inl ⟨hSame, hEq⟩⟩

theorem hilbert_crossing_chords_concyclic_of_forder
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV19 :
      HilbertForderIV19CircleConverse
        (Geo := Geo))
    (hIV20 :
      HilbertForderIV20CircleConverse
        (Geo := Geo))
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAngle :
      Geo.AngleCongruent
        O A D
        O B C) :
    HilbertConcyclic4 Geo A C D B := by

  by_cases hAC : A = C

  --------------------------------------------------------------------
  -- Degenerate first secant.
  --------------------------------------------------------------------

  · exact
      hilbert_crossing_concyclic_degenerate
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        (Or.inl hAC)

  by_cases hBD : B = D

  --------------------------------------------------------------------
  -- Degenerate second secant.
  --------------------------------------------------------------------

  · exact
      hilbert_crossing_concyclic_degenerate
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        (Or.inr hBD)

  --------------------------------------------------------------------
  -- Proper chord CD.
  --------------------------------------------------------------------

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  --------------------------------------------------------------------
  -- Stage 2 gives exactly the IV.19 / IV.20 alternatives.
  --------------------------------------------------------------------

  rcases
      hilbert_crossing_nondegenerate_chord_classification
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
        hAngle
    with
    ⟨chord,
      hCchord,
      hDchord,
      hClass⟩

  rcases hClass with
    hSameCase | hMixedCase

  --------------------------------------------------------------------
  -- Same side: direct Forder IV.19.
  --------------------------------------------------------------------

  · rcases hSameCase with
      ⟨hSame, hEq⟩

    exact
      hIV19
        C D A B
        chord
        hCD
        hCchord
        hDchord
        hSame
        hEq

  rcases hMixedCase with
    hMixedA | hMixedB

  --------------------------------------------------------------------
  -- Opposite sides, supplement at A: direct Forder IV.20.
  --------------------------------------------------------------------

  · rcases hMixedA with
      ⟨hOpp, hSuppA, hCongA⟩

    exact
      hIV20
        C D A B O
        chord
        hCD
        hCchord
        hDchord
        hOpp
        hSuppA
        hCongA

  --------------------------------------------------------------------
  -- Opposite sides, supplement at B.
  --
  -- Apply IV.20 after swapping
  --
  --   C <-> D
  --   A <-> B.
  --
  -- The resulting cyclic order B,D,C,A is then converted back to
  -- A,C,D,B by reversal followed by one cyclic rotation.
  --------------------------------------------------------------------

  · rcases hMixedB with
      ⟨hOpp, hCongB, hSuppB⟩

    have hOppBA :
        HilbertOppositeSide Geo B A chord :=
      hilbert_oppositeSide_symm
        Geo A B chord hOpp

    have hOBC_CAD :
        Geo.AngleCongruent
          O B C
          C A D :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        C A D
        O B C
        hCongB

    have hOBC_DAC :
        Geo.AngleCongruent
          O B C
          D A C :=
      (Geo.angle_congruent_reverse_second
        O B C
        C A D).mp
        hOBC_CAD

    have hCyclicSwap :
        HilbertConcyclic4 Geo
          B D C A :=
      hIV20
        D C B A O
        chord
        hCD.symm
        hDchord
        hCchord
        hOppBA
        hSuppB
        hOBC_DAC

    have hCyclicRev :
        HilbertConcyclic4 Geo
          B A C D :=
      hilbert_concyclic4_reverse
        Geo
        B D C A
        hCyclicSwap

    exact
      hilbert_concyclic4_rotate
        Geo
        B A C D
        hCyclicRev

theorem hilbert_circle_line_second_or_tangent
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A D : Geo.Point)
    (line : Geo.Line)
    (hA : HilbertCircle Geo K R A)
    (hKA : Ne K A)
    (hAD : Ne A D)
    (hAline : H.OnLine A line)
    (hDline : H.OnLine D line) :
    (
      exists E : Geo.Point,
        Ne E A /\
        H.OnLine E line /\
        HilbertCircle Geo K R E
    )
    \/
    HilbertCircleTangentAt
      (Geo := Geo)
      K A line := by

  have hKA_KR :
      Geo.Congruent K A K R := by
    simpa [HilbertCircle] using hA

  by_cases hKline : H.OnLine K line

  --------------------------------------------------------------------
  -- The center lies on the line: take the antipodal point.
  --------------------------------------------------------------------

  · rcases
        hilbert_extend_segment_beyond
          Geo A K hKA.symm
      with
      ⟨E, hAKE, hAK_KE⟩

    have hAKEcol :
        PrimCollinear Geo A K E :=
      (HilbertOrder.between_incidence
        A K E hAKE).2.2.2.1

    have hEline :
        H.OnLine E line :=
      hilbert_collinear_on_line
        Geo
        A K E
        line
        hKA.symm
        hAline
        hKline
        hAKEcol

    have hAE :
        Ne A E :=
      (HilbertOrder.between_incidence
        A K E hAKE).2.2.1

    have hEneA :
        Ne E A := by
      intro hEA
      exact hAE hEA.symm

    have hKE_AK :
        Geo.Congruent K E A K :=
      hilbert_congruent_symmetry
        Geo
        A K
        K E
        hAK_KE

    have hKE_KA :
        Geo.Congruent K E K A :=
      (Geo.congruent_reverse_second
        K E
        A K).mp
        hKE_AK

    have hKE_KR :
        Geo.Congruent K E K R :=
      hilbert_congruent_transitivity
        Geo
        K E
        K A
        K R
        hKE_KA
        hKA_KR

    have hE :
        HilbertCircle Geo K R E := by
      simpa [HilbertCircle] using hKE_KR

    exact
      Or.inl
        ⟨E,
          hEneA,
          hEline,
          hE⟩

  --------------------------------------------------------------------
  -- The center is off the line.  Drop KH perpendicular to the line.
  --------------------------------------------------------------------

  · rcases
        hilbert_perpendicular_from_point_exists
          Geo
          A D K
          line
          hAD
          hAline
          hDline
          hKline
      with
      ⟨M, T, hMline, hTline, hRightTMK⟩

    by_cases hMA : M = A

    ------------------------------------------------------------------
    -- The perpendicular foot is A: tangent at A.
    ------------------------------------------------------------------

    · subst M

      have hRightCopy := hRightTMK

      rcases hRightCopy with
        ⟨X, hTAX, _hAngle⟩

      have hTA :
          Ne T A :=
        (HilbertOrder.between_incidence
          T A X hTAX).1

      have hTAK :
          Not (PrimCollinear Geo T A K) :=
        hilbert_not_collinear_of_off_line
          Geo
          T A K
          line
          hTA
          hTline
          hAline
          hKline

      exact
        Or.inr
          ⟨T,
            hTline,
            hTA,
            hTAK,
            hRightTMK⟩

    ------------------------------------------------------------------
    -- The perpendicular foot M differs from A.
    -- Reflect A across M to obtain the second circle point E.
    ------------------------------------------------------------------

    · have hAM :
          Ne A M := by
        intro hAMeq
        exact hMA hAMeq.symm

      rcases
          hilbert_extend_segment_beyond
            Geo A M hAM
        with
        ⟨E, hAME, hAM_ME⟩

      have hAMEcol :
          PrimCollinear Geo A M E :=
        (HilbertOrder.between_incidence
          A M E hAME).2.2.2.1

      have hEline :
          H.OnLine E line :=
        hilbert_collinear_on_line
          Geo
          A M E
          line
          hAM
          hAline
          hMline
          hAMEcol

      have hAE :
          Ne A E :=
        (HilbertOrder.between_incidence
          A M E hAME).2.2.1

      have hEneA :
          Ne E A := by
        intro hEA
        exact hAE hEA.symm

      have hMid :
          HilbertIsMidpoint Geo M A E :=
        ⟨hAME, hAM_ME⟩

      ----------------------------------------------------------------
      -- Normalize the perpendicular from the arbitrary line point T
      -- to the actual chord point A.
      ----------------------------------------------------------------

      have hRightCopy := hRightTMK

      rcases hRightCopy with
        ⟨X, hTMX, _hAngleTMK⟩

      have hTM :
          Ne T M :=
        (HilbertOrder.between_incidence
          T M X hTMX).1

      have hTMK :
          Not (PrimCollinear Geo T M K) :=
        hilbert_not_collinear_of_off_line
          Geo
          T M K
          line
          hTM
          hTline
          hMline
          hKline

      have hMTA :
          PrimCollinear Geo M T A :=
        ⟨line,
          hMline,
          hTline,
          hAline⟩

      have hRightAMK :
          HilbertRightAngle Geo A M K :=
        hilbert_right_angle_collinear_first_XI
          Geo
          T M K A
          hTMK
          hRightTMK
          hMTA
          hMA

      ----------------------------------------------------------------
      -- K lies on the perpendicular bisector of AE.
      ----------------------------------------------------------------

      have hAMK :
          Not (PrimCollinear Geo A M K) :=
        hilbert_not_collinear_of_off_line
          Geo
          A M K
          line
          hAM
          hAline
          hMline
          hKline

      have hMK :
          Ne M K := by
        intro hEq
        apply hKline
        rw [← hEq]
        exact hMline

      rcases
          HilbertPlaneIncidence.line_through
            M K hMK
        with
        ⟨bis, hMbis, hKbis⟩

      have hKA_KE :
          Geo.Congruent K A K E :=
        hilbert_point_on_perpendicularBisector_equidistant_XI
          Geo
          A E
          M K K
          bis
          hMid
          hAMK
          hRightAMK
          hMbis
          hKbis
          hKbis

      have hKE_KA :
          Geo.Congruent K E K A :=
        hilbert_congruent_symmetry
          Geo
          K A
          K E
          hKA_KE

      have hKE_KR :
          Geo.Congruent K E K R :=
        hilbert_congruent_transitivity
          Geo
          K E
          K A
          K R
          hKE_KA
          hKA_KR

      have hEcircle :
          HilbertCircle Geo K R E := by
        simpa [HilbertCircle] using hKE_KR

      exact
        Or.inl
          ⟨E,
            hEneA,
            hEline,
            hEcircle⟩

theorem hilbert_equal_angles_same_secant_unique
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (O B Bp C : Geo.Point)
    (hOBC : Not (PrimCollinear Geo O B C))
    (hRay :
      HilbertSameRay Geo O B Bp)
    (hAngle :
      Geo.AngleCongruent
        O B C
        O Bp C) :
    B = Bp := by

  rcases
      hilbert_sameRay_cases
        Geo O B Bp hRay
    with
    hEq | hOBBp | hOBpB

  --------------------------------------------------------------------
  -- B = B'.
  --------------------------------------------------------------------

  · exact hEq

  --------------------------------------------------------------------
  -- O-B-B'.
  --------------------------------------------------------------------

  · have hOBBpData :=
      HilbertOrder.between_incidence
        O B Bp hOBBp

    have hBBp :
        Ne B Bp :=
      hOBBpData.2.1

    have hOBBpcol :
        PrimCollinear Geo O B Bp :=
      hOBBpData.2.2.2.1

    have hBBpC :
        Not (PrimCollinear Geo B Bp C) := by

      intro hBBpC

      have hOBC' :
          PrimCollinear Geo O B C :=
        hilbert_primCollinear_trans
          Geo
          O B Bp C
          hBBp
          hOBBpcol
          hBBpC

      exact hOBC hOBC'

    have hBpBO :
        Geo.Between Bp B O :=
      hOBBpData.2.2.2.2

    have hRayBpBO :
        HilbertSameRay Geo Bp B O :=
      hilbert_sameRay_of_between
        Geo Bp B O hBpBO

    have hAtBp :
        Geo.Angle B Bp C =
        Geo.Angle O Bp C :=
      hilbert_angle_eq_of_sameRay_first
        Geo
        Bp B O C
        hRayBpBO

    have hCBO_OBpC :
        Geo.AngleCongruent
          C B O
          O Bp C :=
      (Geo.angle_congruent_reverse_first
        O B C
        O Bp C).mp
        hAngle

    have hExterior :
        Geo.AngleCongruent
          C B O
          B Bp C := by

      unfold Geometry.Geo.AngleCongruent
        at hCBO_OBpC ⊢

      rw [hAtBp]

      exact hCBO_OBpC

    exact
      False.elim
        ((hilbert_exterior_angle_not_congruent_other
            Geo
            B Bp C O
            hBBpC
            hBpBO)
          hExterior)

  --------------------------------------------------------------------
  -- O-B'-B.
  --------------------------------------------------------------------

  · have hOBpBData :=
      HilbertOrder.between_incidence
        O Bp B hOBpB

    have hBpB :
        Ne Bp B :=
      hOBpBData.2.1

    have hOBpBcol :
        PrimCollinear Geo O Bp B :=
      hOBpBData.2.2.2.1

    have hBpBC :
        Not (PrimCollinear Geo Bp B C) := by

      intro hBpBC

      have hOBBpcol :
          PrimCollinear Geo O B Bp :=
        PrimCollinearRotate
          Geo O Bp B hOBpBcol

      have hBBpC :
          PrimCollinear Geo B Bp C :=
        PrimCollinearSwap
          Geo Bp B C hBpBC

      have hOBC' :
          PrimCollinear Geo O B C :=
        hilbert_primCollinear_trans
          Geo
          O B Bp C
          hBpB.symm
          hOBBpcol
          hBBpC

      exact hOBC hOBC'

    have hBBpO :
        Geo.Between B Bp O :=
      hOBpBData.2.2.2.2

    have hRayBBpO :
        HilbertSameRay Geo B Bp O :=
      hilbert_sameRay_of_between
        Geo B Bp O hBBpO

    have hAtB :
        Geo.Angle Bp B C =
        Geo.Angle O B C :=
      hilbert_angle_eq_of_sameRay_first
        Geo
        B Bp O C
        hRayBBpO

    have hSym :
        Geo.AngleCongruent
          O Bp C
          O B C :=
      Geometry.Geo.angle_congruent_symmetry
        Geo
        O B C
        O Bp C
        hAngle

    have hCBpO_OBC :
        Geo.AngleCongruent
          C Bp O
          O B C :=
      (Geo.angle_congruent_reverse_first
        O Bp C
        O B C).mp
        hSym

    have hExterior :
        Geo.AngleCongruent
          C Bp O
          Bp B C := by

      unfold Geometry.Geo.AngleCongruent
        at hCBpO_OBC ⊢

      rw [hAtB]

      exact hCBpO_OBC

    exact
      False.elim
        ((hilbert_exterior_angle_not_congruent_other
            Geo
            Bp B C O
            hBpBC
            hBBpO)
          hExterior)


------------------------------------------------------------------------
-- 3. Forder IV.19: the same-ray secant branch.

theorem hilbert_secant_ray_order_split
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H]
    (A D E : Geo.Point)
    (lineAD : Geo.Line)
    (hAD : Ne A D)
    (hDE : Ne D E)
    (hAE : Ne A E)
    (hAline : H.OnLine A lineAD)
    (hDline : H.OnLine D lineAD)
    (hEline : H.OnLine E lineAD) :
    HilbertSameRay Geo A D E \/
    Geo.Between D A E := by

  have hADEcol :
      PrimCollinear Geo A D E :=
    ⟨lineAD,
      hAline,
      hDline,
      hEline⟩

  rcases
      hilbert_between_trichotomy
        Geo A D E
        hAD
        hDE
        hAE
        hADEcol
    with
    hADE | hDEA | hEAD

  --------------------------------------------------------------------
  -- A-D-E: direct same ray.
  --------------------------------------------------------------------

  · exact
      Or.inl
        (hilbert_sameRay_of_between
          Geo A D E hADE)

  --------------------------------------------------------------------
  -- D-A-E: the opposite-ray case.
  --------------------------------------------------------------------

  · exact Or.inr hDEA

  --------------------------------------------------------------------
  -- A-E-D: E and D are still on the same ray from A.
  --------------------------------------------------------------------

  · have hRayAED :
        HilbertSameRay Geo A E D :=
      hilbert_sameRay_of_between
        Geo A E D hEAD

    exact
      Or.inl
        (hilbert_sameRay_symm
          Geo A E D hRayAED)


------------------------------------------------------------------------
-- 2. Opposite-ray branch -> opposite sides of the chord.

theorem hilbert_oppositeRay_gives_oppositeSide
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H]
    (A B C D E : Geo.Point)
    (chord lineAD : Geo.Line)
    (hAchord : H.OnLine A chord)
    (hBchord : H.OnLine B chord)
    (hAline : H.OnLine A lineAD)
    (hDline : H.OnLine D lineAD)
    (hBnotLineAD : Not (H.OnLine B lineAD))
    (hSameCD : HilbertSameSide Geo C D chord)
    (hDAE : Geo.Between D A E) :
    HilbertOppositeSide Geo C E chord := by

  have hDAEdata :=
    HilbertOrder.between_incidence
      D A E hDAE

  have hDA :
      Ne D A :=
    hDAEdata.1

  have hAE :
      Ne A E :=
    hDAEdata.2.1

  have hDAEcol :
      PrimCollinear Geo D A E :=
    hDAEdata.2.2.2.1

  have hEline :
      H.OnLine E lineAD :=
    hilbert_collinear_on_line
      Geo
      D A E
      lineAD
      hDA
      hDline
      hAline
      hDAEcol

  have hEoff :
      Not (H.OnLine E chord) := by
    intro hEchord

    have hEq :
        chord = lineAD :=
      HilbertPlaneIncidence.line_unique
        A E hAE
        chord lineAD
        hAchord hEchord
        hAline hEline

    have hBline :
        H.OnLine B lineAD := by
      rw [← hEq]
      exact hBchord

    exact hBnotLineAD hBline

  have hDoff :
      Not (H.OnLine D chord) :=
    hSameCD.2.1

  have hOppDE :
      HilbertOppositeSide Geo D E chord :=
    ⟨hDoff,
      hEoff,
      ⟨A,
        hDAE,
        hAchord⟩⟩

  have hOppED :
      HilbertOppositeSide Geo E D chord :=
    hilbert_oppositeSide_symm
      Geo D E chord hOppDE

  have hSameDC :
      HilbertSameSide Geo D C chord :=
    hilbert_sameSide_symm
      Geo C D chord hSameCD

  have hOppEC :
      HilbertOppositeSide Geo E C chord :=
    hilbert_oppositeSide_transport_right
      Geo
      E D C
      chord
      hOppED
      hSameDC

  exact
    hilbert_oppositeSide_symm
      Geo E C chord hOppEC

theorem hilbert_two_oppositeSides_sameSide
    [H : HilbertIncidence Geo]
    [_HO : @HilbertOrder Geo H]
    (P Q R : Geo.Point)
    (l : Geo.Line)
    (hPQ : HilbertOppositeSide Geo P Q l)
    (hPR : HilbertOppositeSide Geo P R l) :
    HilbertSameSide Geo Q R l := by

  by_contra hNotSame

  have hQR :
      HilbertOppositeSide Geo Q R l :=
    hilbert_oppositeSide_of_not_sameSide
      Geo
      Q R
      l
      hPQ.2.1
      hPR.2.1
      hNotSame

  rcases hPQ.2.2 with
    ⟨X, hPXQ, hXl⟩

  rcases hPR.2.2 with
    ⟨Y, hPYR, hYl⟩

  rcases hQR.2.2 with
    ⟨Z, hQZR, hZl⟩

  have hPQne :
      Ne P Q :=
    (HilbertOrder.between_incidence
      P X Q hPXQ).2.2.1

  have hPRne :
      Ne P R :=
    (HilbertOrder.between_incidence
      P Y R hPYR).2.2.1

  have hQRne :
      Ne Q R :=
    (HilbertOrder.between_incidence
      Q Z R hQZR).2.2.1

  by_cases hPQR :
      PrimCollinear Geo P Q R

  --------------------------------------------------------------------
  -- Collinear case.
  --------------------------------------------------------------------

  · rcases hPQR with
      ⟨carrier, hPcar, hQcar, hRcar⟩

    have hCol :
        PrimCollinear Geo P Q R :=
      ⟨carrier, hPcar, hQcar, hRcar⟩

    rcases
        hilbert_between_trichotomy
          Geo
          P Q R
          hPQne
          hQRne
          hPRne
          hCol
      with
      hPQRord | hQPRord | hPRQord

    --------------------------------------------------------------
    -- P-Q-R.  Use the crossing witnesses on PQ and QR.
    --------------------------------------------------------------

    · have hXcar :
          H.OnLine X carrier :=
        hilbert_between_on_line
          Geo P X Q carrier
          hPcar hQcar hPXQ

      have hZcar :
          H.OnLine Z carrier :=
        hilbert_between_on_line
          Geo Q Z R carrier
          hQcar hRcar hQZR

      have hXZ :
          Ne X Z := by
        intro hXZeq
        subst Z

        have hQXP :
            Geo.Between Q X P :=
          (HilbertOrder.between_incidence
            P X Q hPXQ).2.2.2.2

        have hRayQXP :
            HilbertSameRay Geo Q X P :=
          hilbert_sameRay_of_between
            Geo Q X P hQXP

        have hRayQXR :
            HilbertSameRay Geo Q X R :=
          hilbert_sameRay_of_between
            Geo Q X R hQZR

        have hRayQPR :
            HilbertSameRay Geo Q P R :=
          hilbert_sameRay_of_common
            Geo Q X P R
            hRayQXP hRayQXR

        exact
          (hilbert_not_sameRay_of_between_origin
            Geo P Q R hPQRord)
            hRayQPR

      have hEq :
          carrier = l :=
        HilbertPlaneIncidence.line_unique
          X Z hXZ
          carrier l
          hXcar hZcar
          hXl hZl

      have hPl :
          H.OnLine P l := by
        rw [← hEq]
        exact hPcar

      exact hPQ.1 hPl

    --------------------------------------------------------------
    -- Q-P-R.  Use the crossing witnesses on PQ and PR.
    --------------------------------------------------------------

    · have hXcar :
          H.OnLine X carrier :=
        hilbert_between_on_line
          Geo P X Q carrier
          hPcar hQcar hPXQ

      have hYcar :
          H.OnLine Y carrier :=
        hilbert_between_on_line
          Geo P Y R carrier
          hPcar hRcar hPYR

      have hXY :
          Ne X Y := by
        intro hXYeq
        subst Y

        have hRayPXQ :
            HilbertSameRay Geo P X Q :=
          hilbert_sameRay_of_between
            Geo P X Q hPXQ

        have hRayPXR :
            HilbertSameRay Geo P X R :=
          hilbert_sameRay_of_between
            Geo P X R hPYR

        have hRayPQR :
            HilbertSameRay Geo P Q R :=
          hilbert_sameRay_of_common
            Geo P X Q R
            hRayPXQ hRayPXR

        exact
          (hilbert_not_sameRay_of_between_origin
            Geo Q P R hQPRord)
            hRayPQR

      have hEq :
          carrier = l :=
        HilbertPlaneIncidence.line_unique
          X Y hXY
          carrier l
          hXcar hYcar
          hXl hYl

      have hPl :
          H.OnLine P l := by
        rw [← hEq]
        exact hPcar

      exact hPQ.1 hPl

    --------------------------------------------------------------
    -- P-R-Q.  Use the crossing witnesses on PR and QR.
    --------------------------------------------------------------

    · have hYcar :
          H.OnLine Y carrier :=
        hilbert_between_on_line
          Geo P Y R carrier
          hPcar hRcar hPYR

      have hZcar :
          H.OnLine Z carrier :=
        hilbert_between_on_line
          Geo Q Z R carrier
          hQcar hRcar hQZR

      have hYZ :
          Ne Y Z := by
        intro hYZeq
        subst Z

        have hRYP :
            Geo.Between R Y P :=
          (HilbertOrder.between_incidence
            P Y R hPYR).2.2.2.2

        have hRYQ :
            Geo.Between R Y Q :=
          (HilbertOrder.between_incidence
            Q Y R hQZR).2.2.2.2

        have hRayRYP :
            HilbertSameRay Geo R Y P :=
          hilbert_sameRay_of_between
            Geo R Y P hRYP

        have hRayRYQ :
            HilbertSameRay Geo R Y Q :=
          hilbert_sameRay_of_between
            Geo R Y Q hRYQ

        have hRayRPQ :
            HilbertSameRay Geo R P Q :=
          hilbert_sameRay_of_common
            Geo R Y P Q
            hRayRYP hRayRYQ

        exact
          (hilbert_not_sameRay_of_between_origin
            Geo P R Q hPRQord)
            hRayRPQ

      have hEq :
          carrier = l :=
        HilbertPlaneIncidence.line_unique
          Y Z hYZ
          carrier l
          hYcar hZcar
          hYl hZl

      have hPl :
          H.OnLine P l := by
        rw [← hEq]
        exact hPcar

      exact hPQ.1 hPl

  --------------------------------------------------------------------
  -- Noncollinear case: a line cannot cross all three open sides.
  --------------------------------------------------------------------

  · have hNoQR :
        Not (HilbertSegmentMeetsLine Geo Q R l) :=
      hilbert_line_avoids_third_triangle_side
        Geo
        P Q R
        X Y
        l
        hPQR
        hPXQ
        hPYR
        hXl
        hYl

    exact
      hNoQR
        ⟨Z, hQZR, hZl⟩


------------------------------------------------------------------------
-- 2. Forder IV.20: the B-C-E secant branch is impossible.

theorem hilbert_crossing_chords_angle_nondegenerate
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (hIV16Same :
      HilbertForderIV16SameSide
        (Geo := Geo))
    (hIV16Opp :
      HilbertForderIV16OppositeSide
        (Geo := Geo))
    (O A C B D : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hRayAC : HilbertSameRay Geo O A C)
    (hRayBD : HilbertSameRay Geo O B D)
    (hAC : Ne A C)
    (hBD : Ne B D)
    (hCyclic :
      HilbertConcyclic4 Geo A C D B) :
    Geo.AngleCongruent
      O D C
      O A B := by

  --------------------------------------------------------------------
  -- Put the cyclic quadruple on one explicit circle.
  --------------------------------------------------------------------

  rcases
      hilbert_concyclic4_circle
        Geo A C D B hCyclic
    with
    ⟨K, hAcircle, hCcircle, hDcircle, hBcircle⟩

  --------------------------------------------------------------------
  -- Nondegenerate crossing data and the two strict ray orders.
  --------------------------------------------------------------------

  rcases
      hilbert_crossing_nondegenerate_data
        Geo
        O A C B D
        hAOB
        hRayAC
        hRayBD
        hAC
        hBD
    with
    ⟨_hOAD,
      hOBC,
      hOrderAC,
      hOrderBD⟩

  have hOA :
      Ne O A :=
    hRayAC.1.symm

  have hOB :
      Ne O B :=
    hRayBD.1.symm

  have hAB :
      Ne A B := by
    intro hEq
    subst B
    rcases
        HilbertPlaneIncidence.line_through
          A O hOA.symm
      with
      ⟨l, hAl, hOl⟩
    exact
      hAOB
        ⟨l, hAl, hOl, hAl⟩

  have hBC :
      Ne B C := by
    intro hEq
    subst C
    rcases
        HilbertPlaneIncidence.line_through
          O B hOB
      with
      ⟨l, hOl, hBl⟩
    exact
      hOBC
        ⟨l, hOl, hBl, hBl⟩

  have hCB :
      Ne C B :=
    hBC.symm

  have hRayAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hRayAC.1

  have hCOD :
      Not (PrimCollinear Geo C O D) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O B
      C D
      hAOB
      hRayAC
      hRayBD

  have hCDO :
      Not (PrimCollinear Geo C D O) := by
    intro h
    exact
      hCOD
        (PrimCollinearRotate
          Geo C D O h)

  have hCD :
      Ne C D :=
    hilbert_noncollinear_ne_first
      Geo C D O hCDO

  have hBOA :
      Not (PrimCollinear Geo B O A) := by
    intro h
    exact
      hAOB
        (PrimCollinearSymm
          Geo B O A h)

  have hDOA :
      Not (PrimCollinear Geo D O A) :=
    hilbert_noncollinear_of_sameRays
      Geo
      B O A
      D A
      hBOA
      hRayBD
      hRayAA

  --------------------------------------------------------------------
  -- The four strict order cases.
  --------------------------------------------------------------------

  rcases hOrderAC with hOAC | hOCA

  --------------------------------------------------------------------
  -- I. O-A-C.
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    ------------------------------------------------------------------
    -- I.a O-A-C and O-B-D.
    --
    -- For chord BC, D and A are on opposite sides.
    -- IV.16 says BDC is congruent to a supplement of BAC.
    -- OAB is also a supplement of CAB, while ODC = BDC.
    ------------------------------------------------------------------

    · rcases
          hilbert_crossing_mixed_inner_outer_oppositeSide_chord
            Geo
            O D B A C
            hDOA
            hOBD
            hOAC
        with
        ⟨chordBC, hBchord, hCchord, hOppDA⟩

      rcases
          hIV16Opp
            K A
            B C D A
            chordBC
            hBC
            hBchord
            hCchord
            hBcircle
            hCcircle
            hDcircle
            hAcircle
            hOppDA
        with
        ⟨X, hSuppX, hBDC_XAC⟩

      have hCAO :
          Geo.Between C A O :=
        (HilbertOrder.between_incidence
          O A C hOAC).2.2.2.2

      have hSuppO :
          BookZeroSupplement Geo
            C A B
            B O :=
        ⟨hilbert_sameRay_refl
            Geo A B hAB.symm,
          hCAO⟩

      have hBCA :
          Not (PrimCollinear Geo B C A) :=
        hilbert_not_collinear_of_off_line
          Geo
          B C A
          chordBC
          hBC
          hBchord
          hCchord
          hOppDA.2.1

      have hBAC :
          Not (PrimCollinear Geo B A C) := by
        intro h
        exact
          hBCA
            (PrimCollinearRotate
              Geo B A C h)

      have hCAB :
          Not (PrimCollinear Geo C A B) := by
        intro h
        exact
          hBCA
            (PrimCollinearCycle
              Geo A B C
              (PrimCollinearCycle
                Geo C A B h))

      have hBAC_CAB :
          Geo.AngleCongruent
            B A C
            C A B := by
        have hAtA :
            Geo.Angle B A C =
            Geo.Angle C A B :=
          Geo.angle_swap B A C
        unfold Geometry.Geo.AngleCongruent
        rw [← hAtA]
        exact
          Geometry.Geo.angle_congruent_reflexive
            Geo B A C

      have hCAX_BAO :
          Geo.AngleCongruent
            C A X
            B A O :=
        bookZero_43_supplements
          Geo
          B A C C X
          C A B B O
          hBAC_CAB
          hSuppX
          hSuppO
          hBAC
          hCAB

      have hBDC_CAX :
          Geo.AngleCongruent
            B D C
            C A X := by
        have hAtA :
            Geo.Angle X A C =
            Geo.Angle C A X :=
          Geo.angle_swap X A C
        unfold Geometry.Geo.AngleCongruent
          at hBDC_XAC ⊢
        rw [← hAtA]
        exact hBDC_XAC

      have hBDC_BAO :
          Geo.AngleCongruent
            B D C
            B A O :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          B D C
          C A X
          B A O
          hBDC_CAX
          hCAX_BAO

      have hBDC_OAB :
          Geo.AngleCongruent
            B D C
            O A B := by
        have hAtA :
            Geo.Angle B A O =
            Geo.Angle O A B :=
          Geo.angle_swap B A O
        unfold Geometry.Geo.AngleCongruent
          at hBDC_BAO ⊢
        rw [← hAtA]
        exact hBDC_BAO

      have hDBO :
          Geo.Between D B O :=
        (HilbertOrder.between_incidence
          O B D hOBD).2.2.2.2

      have hRayDBO :
          HilbertSameRay Geo D B O :=
        hilbert_sameRay_of_between
          Geo D B O hDBO

      have hRayDOB :
          HilbertSameRay Geo D O B :=
        hilbert_sameRay_symm
          Geo D B O hRayDBO

      have hAtD :
          Geo.Angle O D C =
          Geo.Angle B D C :=
        hilbert_angle_eq_of_sameRay_first
          Geo D O B C hRayDOB

      unfold Geometry.Geo.AngleCongruent
        at hBDC_OAB ⊢
      rw [hAtD]
      exact hBDC_OAB

    ------------------------------------------------------------------
    -- I.b O-A-C and O-D-B.
    --
    -- Both requested angles are supplements of the equal same-segment
    -- angles supplied by IV.16.
    ------------------------------------------------------------------

    · rcases
          hilbert_crossing_outer_outer_sameSide_chord
            Geo
            O D B A C
            hDOA
            hODB
            hOAC
        with
        ⟨chordBC, hBchord, hCchord, hSameDA⟩

      have hBDC_BAC :
          Geo.AngleCongruent
            B D C
            B A C :=
        hIV16Same
          K A
          B C D A
          chordBC
          hBC
          hBchord
          hCchord
          hBcircle
          hCcircle
          hDcircle
          hAcircle
          hSameDA

      have hBDC_CAB :
          Geo.AngleCongruent
            B D C
            C A B := by
        have hAtA :
            Geo.Angle B A C =
            Geo.Angle C A B :=
          Geo.angle_swap B A C
        unfold Geometry.Geo.AngleCongruent
          at hBDC_BAC ⊢
        rw [← hAtA]
        exact hBDC_BAC

      have hBDO :
          Geo.Between B D O :=
        (HilbertOrder.between_incidence
          O D B hODB).2.2.2.2

      have hCAO :
          Geo.Between C A O :=
        (HilbertOrder.between_incidence
          O A C hOAC).2.2.2.2

      have hSuppD :
          BookZeroSupplement Geo
            B D C
            C O :=
        ⟨hilbert_sameRay_refl
            Geo D C hCD,
          hBDO⟩

      have hSuppA :
          BookZeroSupplement Geo
            C A B
            B O :=
        ⟨hilbert_sameRay_refl
            Geo A B hAB.symm,
          hCAO⟩

      have hDoff :
          Not (H.OnLine D chordBC) :=
        hSameDA.1

      have hAoff :
          Not (H.OnLine A chordBC) :=
        hSameDA.2.1

      have hBCD :
          Not (PrimCollinear Geo B C D) :=
        hilbert_not_collinear_of_off_line
          Geo
          B C D
          chordBC
          hBC
          hBchord
          hCchord
          hDoff

      have hBDC :
          Not (PrimCollinear Geo B D C) := by
        intro h
        exact
          hBCD
            (PrimCollinearRotate
              Geo B D C h)

      have hBCA :
          Not (PrimCollinear Geo B C A) :=
        hilbert_not_collinear_of_off_line
          Geo
          B C A
          chordBC
          hBC
          hBchord
          hCchord
          hAoff

      have hCAB :
          Not (PrimCollinear Geo C A B) := by
        intro h
        exact
          hBCA
            (PrimCollinearCycle
              Geo A B C
              (PrimCollinearCycle
                Geo C A B h))

      have hCDO_BAO :
          Geo.AngleCongruent
            C D O
            B A O :=
        bookZero_43_supplements
          Geo
          B D C C O
          C A B B O
          hBDC_CAB
          hSuppD
          hSuppA
          hBDC
          hCAB

      have hODC_OAB :
          Geo.AngleCongruent
            O D C
            O A B := by
        have hAtD :
            Geo.Angle C D O =
            Geo.Angle O D C :=
          Geo.angle_swap C D O
        have hAtA :
            Geo.Angle B A O =
            Geo.Angle O A B :=
          Geo.angle_swap B A O
        unfold Geometry.Geo.AngleCongruent
          at hCDO_BAO ⊢
        rw [← hAtD, ← hAtA]
        exact hCDO_BAO

      exact hODC_OAB

  --------------------------------------------------------------------
  -- II. O-C-A.
  --------------------------------------------------------------------

  · rcases hOrderBD with hOBD | hODB

    ------------------------------------------------------------------
    -- II.a O-C-A and O-B-D.
    --
    -- Both requested rays agree directly with the corresponding
    -- inscribed-angle rays.
    ------------------------------------------------------------------

    · rcases
          hilbert_crossing_inner_inner_sameSide_chord
            Geo
            O D B A C
            hDOA
            hOBD
            hOCA
        with
        ⟨chordBC, hBchord, hCchord, hSameDA⟩

      have hBDC_BAC :
          Geo.AngleCongruent
            B D C
            B A C :=
        hIV16Same
          K A
          B C D A
          chordBC
          hBC
          hBchord
          hCchord
          hBcircle
          hCcircle
          hDcircle
          hAcircle
          hSameDA

      have hBDC_CAB :
          Geo.AngleCongruent
            B D C
            C A B := by
        have hAtA :
            Geo.Angle B A C =
            Geo.Angle C A B :=
          Geo.angle_swap B A C
        unfold Geometry.Geo.AngleCongruent
          at hBDC_BAC ⊢
        rw [← hAtA]
        exact hBDC_BAC

      have hDBO :
          Geo.Between D B O :=
        (HilbertOrder.between_incidence
          O B D hOBD).2.2.2.2

      have hRayDOB :
          HilbertSameRay Geo D O B :=
        hilbert_sameRay_symm
          Geo D B O
          (hilbert_sameRay_of_between
            Geo D B O hDBO)

      have hACO :
          Geo.Between A C O :=
        (HilbertOrder.between_incidence
          O C A hOCA).2.2.2.2

      have hRayAOC :
          HilbertSameRay Geo A O C :=
        hilbert_sameRay_symm
          Geo A C O
          (hilbert_sameRay_of_between
            Geo A C O hACO)

      have hAtD :
          Geo.Angle O D C =
          Geo.Angle B D C :=
        hilbert_angle_eq_of_sameRay_first
          Geo D O B C hRayDOB

      have hAtA :
          Geo.Angle O A B =
          Geo.Angle C A B :=
        hilbert_angle_eq_of_sameRay_first
          Geo A O C B hRayAOC

      unfold Geometry.Geo.AngleCongruent
        at hBDC_CAB ⊢
      rw [hAtD, hAtA]
      exact hBDC_CAB

    ------------------------------------------------------------------
    -- II.b O-C-A and O-D-B.
    --
    -- A is direct; the D-angle is the supplement required by IV.16.
    ------------------------------------------------------------------

    · rcases
          hilbert_crossing_mixed_outer_inner_oppositeSide_chord
            Geo
            O D B A C
            hDOA
            hODB
            hOCA
        with
        ⟨chordBC, hBchord, hCchord, hOppDA⟩

      have hOppAD :
          HilbertOppositeSide Geo A D chordBC :=
        hilbert_oppositeSide_symm
          Geo D A chordBC hOppDA

      rcases
          hIV16Opp
            K A
            B C A D
            chordBC
            hBC
            hBchord
            hCchord
            hBcircle
            hCcircle
            hAcircle
            hDcircle
            hOppAD
        with
        ⟨X, hSuppX, hBAC_XDC⟩

      have hBDO :
          Geo.Between B D O :=
        (HilbertOrder.between_incidence
          O D B hODB).2.2.2.2

      have hSuppO :
          BookZeroSupplement Geo
            B D C
            C O :=
        ⟨hilbert_sameRay_refl
            Geo D C hCD,
          hBDO⟩

      have hDoff :
          Not (H.OnLine D chordBC) :=
        hOppAD.2.1

      have hBCD :
          Not (PrimCollinear Geo B C D) :=
        hilbert_not_collinear_of_off_line
          Geo
          B C D
          chordBC
          hBC
          hBchord
          hCchord
          hDoff

      have hBDC :
          Not (PrimCollinear Geo B D C) := by
        intro h
        exact
          hBCD
            (PrimCollinearRotate
              Geo B D C h)

      have hRef :
          Geo.AngleCongruent
            B D C
            B D C :=
        Geometry.Geo.angle_congruent_reflexive
          Geo B D C

      have hCDX_CDO :
          Geo.AngleCongruent
            C D X
            C D O :=
        bookZero_43_supplements
          Geo
          B D C C X
          B D C C O
          hRef
          hSuppX
          hSuppO
          hBDC
          hBDC

      have hBAC_CDX :
          Geo.AngleCongruent
            B A C
            C D X := by
        have hAtD :
            Geo.Angle X D C =
            Geo.Angle C D X :=
          Geo.angle_swap X D C
        unfold Geometry.Geo.AngleCongruent
          at hBAC_XDC ⊢
        rw [← hAtD]
        exact hBAC_XDC

      have hBAC_CDO :
          Geo.AngleCongruent
            B A C
            C D O :=
        Geometry.Geo.angle_congruent_transitivity
          Geo
          B A C
          C D X
          C D O
          hBAC_CDX
          hCDX_CDO

      have hCAB_ODC :
          Geo.AngleCongruent
            C A B
            O D C := by
        have hAtA :
            Geo.Angle B A C =
            Geo.Angle C A B :=
          Geo.angle_swap B A C
        have hAtD :
            Geo.Angle C D O =
            Geo.Angle O D C :=
          Geo.angle_swap C D O
        unfold Geometry.Geo.AngleCongruent
          at hBAC_CDO ⊢
        rw [← hAtA, ← hAtD]
        exact hBAC_CDO

      have hODC_CAB :
          Geo.AngleCongruent
            O D C
            C A B :=
        Geometry.Geo.angle_congruent_symmetry
          Geo
          C A B
          O D C
          hCAB_ODC

      have hACO :
          Geo.Between A C O :=
        (HilbertOrder.between_incidence
          O C A hOCA).2.2.2.2

      have hRayAOC :
          HilbertSameRay Geo A O C :=
        hilbert_sameRay_symm
          Geo A C O
          (hilbert_sameRay_of_between
            Geo A C O hACO)

      have hAtA :
          Geo.Angle O A B =
          Geo.Angle C A B :=
        hilbert_angle_eq_of_sameRay_first
          Geo A O C B hRayAOC

      unfold Geometry.Geo.AngleCongruent
        at hODC_CAB ⊢
      rw [hAtA]
      exact hODC_CAB

theorem hilbert_AA_third_angle
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (A B C A' B' C' : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hA'B'C' : Not (PrimCollinear Geo A' B' C'))
    (hAngleA :
      Geo.AngleCongruent
        B A C
        B' A' C')
    (hAngleB :
      Geo.AngleCongruent
        A B C
        A' B' C') :
    Geo.AngleCongruent
      A C B
      A' C' B' := by

  --------------------------------------------------------------------
  -- Extend BC and B'C' beyond C and C'.
  --------------------------------------------------------------------

  have hBC :
      Ne B C :=
    hilbert_noncollinear_ne_first
      Geo B C A
      (by
        intro h
        exact
          hABC
            (PrimCollinearCycle
              Geo C A B
              (PrimCollinearCycle
                Geo B C A h)))

  have hB'C' :
      Ne B' C' :=
    hilbert_noncollinear_ne_first
      Geo B' C' A'
      (by
        intro h
        exact
          hA'B'C'
            (PrimCollinearCycle
              Geo C' A' B'
              (PrimCollinearCycle
                Geo B' C' A' h)))

  rcases
      HilbertOrder.between_extension
        B C hBC
    with
    ⟨D, hBCD⟩

  rcases
      HilbertOrder.between_extension
        B' C' hB'C'
    with
    ⟨D', hB'C'D'⟩

  --------------------------------------------------------------------
  -- Euclid I.32 decomposes the two exterior angles.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        A B C D
        hABC
        hBCD
    with
    ⟨R, hARD, hBAC_ACR, hABC_RCD⟩

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        A' B' C' D'
        hA'B'C'
        hB'C'D'
    with
    ⟨R', hA'R'D', hB'A'C'_A'C'R', hA'B'C'_R'C'D'⟩

  --------------------------------------------------------------------
  -- Corresponding pieces of the two exterior angles are congruent.
  --------------------------------------------------------------------

  have hACR_BAC :
      Geo.AngleCongruent
        A C R
        B A C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B A C
      A C R
      hBAC_ACR

  have hACR_B'A'C' :
      Geo.AngleCongruent
        A C R
        B' A' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C R
      B A C
      B' A' C'
      hACR_BAC
      hAngleA

  have hACR_A'C'R' :
      Geo.AngleCongruent
        A C R
        A' C' R' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A C R
      B' A' C'
      A' C' R'
      hACR_B'A'C'
      hB'A'C'_A'C'R'

  have hRCD_ABC :
      Geo.AngleCongruent
        R C D
        A B C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A B C
      R C D
      hABC_RCD

  have hRCD_A'B'C' :
      Geo.AngleCongruent
        R C D
        A' B' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      R C D
      A B C
      A' B' C'
      hRCD_ABC
      hAngleB

  have hRCD_R'C'D' :
      Geo.AngleCongruent
        R C D
        R' C' D' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      R C D
      A' B' C'
      R' C' D'
      hRCD_A'B'C'
      hA'B'C'_R'C'D'

  --------------------------------------------------------------------
  -- A,C,D and A',C',D' are genuine noncollinear triples.
  --------------------------------------------------------------------

  have hBCDdata :=
    HilbertOrder.between_incidence
      B C D hBCD

  have hCD :
      Ne C D :=
    hBCDdata.2.1

  have hBCDcol :
      PrimCollinear Geo B C D :=
    hBCDdata.2.2.2.1

  rcases hBCDcol with
    ⟨lineBC, hBlineBC, hClineBC, hDlineBC⟩

  have hAoffBC :
      Not (H.OnLine A lineBC) := by
    intro hAlineBC
    exact
      hABC
        ⟨lineBC,
          hAlineBC,
          hBlineBC,
          hClineBC⟩

  have hCDA :
      Not (PrimCollinear Geo C D A) :=
    hilbert_not_collinear_of_off_line
      Geo
      C D A
      lineBC
      hCD
      hClineBC
      hDlineBC
      hAoffBC

  have hACD :
      Not (PrimCollinear Geo A C D) := by
    intro h
    exact
      hCDA
        (PrimCollinearCycle
          Geo A C D h)

  have hB'C'D'data :=
    HilbertOrder.between_incidence
      B' C' D' hB'C'D'

  have hC'D' :
      Ne C' D' :=
    hB'C'D'data.2.1

  have hB'C'D'col :
      PrimCollinear Geo B' C' D' :=
    hB'C'D'data.2.2.2.1

  rcases hB'C'D'col with
    ⟨lineB'C', hB'line, hC'line, hD'line⟩

  have hA'off :
      Not (H.OnLine A' lineB'C') := by
    intro hA'line
    exact
      hA'B'C'
        ⟨lineB'C',
          hA'line,
          hB'line,
          hC'line⟩

  have hC'D'A' :
      Not (PrimCollinear Geo C' D' A') :=
    hilbert_not_collinear_of_off_line
      Geo
      C' D' A'
      lineB'C'
      hC'D'
      hC'line
      hD'line
      hA'off

  have hA'C'D' :
      Not (PrimCollinear Geo A' C' D') := by
    intro h
    exact
      hC'D'A'
        (PrimCollinearCycle
          Geo A' C' D' h)

  --------------------------------------------------------------------
  -- The I.32 divider rays CR and C'R' are genuine.
  --------------------------------------------------------------------

  have hARDdata :=
    HilbertOrder.between_incidence
      A R D hARD

  have hAR :
      Ne A R :=
    hARDdata.1

  have hRD :
      Ne R D :=
    hARDdata.2.1

  have hARDcol :
      PrimCollinear Geo A R D :=
    hARDdata.2.2.2.1

  have hCR :
      Ne C R := by
    intro hCR
    subst R
    exact hACD hARDcol

  rcases
      HilbertPlaneIncidence.line_through
        C R hCR
    with
    ⟨lineCR, hClineCR, hRlineCR⟩

  have hAoffCR :
      Not (H.OnLine A lineCR) := by
    intro hAlineCR

    have hDlineCR :
        H.OnLine D lineCR :=
      hilbert_collinear_on_line
        Geo
        A R D
        lineCR
        hAR
        hAlineCR
        hRlineCR
        hARDcol

    exact
      hACD
        ⟨lineCR,
          hAlineCR,
          hClineCR,
          hDlineCR⟩

  have hDoffCR :
      Not (H.OnLine D lineCR) := by
    intro hDlineCR

    have hRDA :
        PrimCollinear Geo R D A :=
      PrimCollinearCycle
        Geo A R D hARDcol

    have hAlineCR :
        H.OnLine A lineCR :=
      hilbert_collinear_on_line
        Geo
        R D A
        lineCR
        hRD
        hRlineCR
        hDlineCR
        hRDA

    exact
      hACD
        ⟨lineCR,
          hAlineCR,
          hClineCR,
          hDlineCR⟩

  have hA'R'D'data :=
    HilbertOrder.between_incidence
      A' R' D' hA'R'D'

  have hA'R' :
      Ne A' R' :=
    hA'R'D'data.1

  have hR'D' :
      Ne R' D' :=
    hA'R'D'data.2.1

  have hA'R'D'col :
      PrimCollinear Geo A' R' D' :=
    hA'R'D'data.2.2.2.1

  have hC'R' :
      Ne C' R' := by
    intro hC'R'
    subst R'
    exact hA'C'D' hA'R'D'col

  rcases
      HilbertPlaneIncidence.line_through
        C' R' hC'R'
    with
    ⟨lineC'R', hC'lineC'R', hR'lineC'R'⟩

  have hA'offC'R' :
      Not (H.OnLine A' lineC'R') := by
    intro hA'lineC'R'

    have hD'lineC'R' :
        H.OnLine D' lineC'R' :=
      hilbert_collinear_on_line
        Geo
        A' R' D'
        lineC'R'
        hA'R'
        hA'lineC'R'
        hR'lineC'R'
        hA'R'D'col

    exact
      hA'C'D'
        ⟨lineC'R',
          hA'lineC'R',
          hC'lineC'R',
          hD'lineC'R'⟩

  have hD'offC'R' :
      Not (H.OnLine D' lineC'R') := by
    intro hD'lineC'R'

    have hR'D'A' :
        PrimCollinear Geo R' D' A' :=
      PrimCollinearCycle
        Geo A' R' D' hA'R'D'col

    have hA'lineC'R' :
        H.OnLine A' lineC'R' :=
      hilbert_collinear_on_line
        Geo
        R' D' A'
        lineC'R'
        hR'D'
        hR'lineC'R'
        hD'lineC'R'
        hR'D'A'

    exact
      hA'C'D'
        ⟨lineC'R',
          hA'lineC'R',
          hC'lineC'R',
          hD'lineC'R'⟩

  --------------------------------------------------------------------
  -- In both triangles the exterior endpoints lie on opposite sides
  -- of the divider ray.  Hence the side configurations match.
  --------------------------------------------------------------------

  have hOppAD :
      HilbertOppositeSide Geo A D lineCR :=
    ⟨hAoffCR,
      hDoffCR,
      ⟨R, hARD, hRlineCR⟩⟩

  have hOppA'D' :
      HilbertOppositeSide Geo A' D' lineC'R' :=
    ⟨hA'offC'R',
      hD'offC'R',
      ⟨R', hA'R'D', hR'lineC'R'⟩⟩

  have hNotSameAD :
      Not (HilbertSameSide Geo A D lineCR) :=
    hilbert_oppositeSide_not_sameSide
      Geo A D lineCR hOppAD

  have hNotSameA'D' :
      Not (HilbertSameSide Geo A' D' lineC'R') :=
    hilbert_oppositeSide_not_sameSide
      Geo A' D' lineC'R' hOppA'D'

  have hSideConfiguration :
      HilbertSameSide Geo A D lineCR ↔
      HilbertSameSide Geo A' D' lineC'R' := by
    constructor
    · intro hSame
      exact False.elim (hNotSameAD hSame)
    · intro hSame
      exact False.elim (hNotSameA'D' hSame)

  --------------------------------------------------------------------
  -- Hilbert Theorem 15 adds the corresponding I.32 pieces:
  -- angle ACD ~= angle A'C'D'.
  --------------------------------------------------------------------

  have hACD_A'C'D' :
      Geo.AngleCongruent
        A C D
        A' C' D' :=
    hilbert_angle_addition
      Geo
      A C R D
      A' C' R' D'
      lineCR lineC'R'
      hCR
      hC'R'
      hClineCR
      hRlineCR
      hC'lineC'R'
      hR'lineC'R'
      hAoffCR
      hDoffCR
      hA'offC'R'
      hD'offC'R'
      hSideConfiguration
      hACD
      hA'C'D'
      hACR_A'C'R'
      hRCD_R'C'D'

  --------------------------------------------------------------------
  -- Reverse both exterior angles and use Hilbert Theorem 14 to pass
  -- from D,D' back to B,B'.
  --------------------------------------------------------------------

  have hDCA_D'C'A' :
      Geo.AngleCongruent
        D C A
        D' C' A' :=
    (Geo.angle_congruent_reverse_second
      D C A
      A' C' D').mp
      ((Geo.angle_congruent_reverse_first
        A C D
        A' C' D').mp
        hACD_A'C'D')

  have hDCB :
      Geo.Between D C B :=
    (HilbertOrder.between_incidence
      B C D hBCD).2.2.2.2

  have hD'C'B' :
      Geo.Between D' C' B' :=
    (HilbertOrder.between_incidence
      B' C' D' hB'C'D').2.2.2.2

  have hDCA :
      Not (PrimCollinear Geo D C A) := by
    intro h
    exact
      hACD
        (PrimCollinearSymm
          Geo D C A h)

  have hD'C'A' :
      Not (PrimCollinear Geo D' C' A') := by
    intro h
    exact
      hA'C'D'
        (PrimCollinearSymm
          Geo D' C' A' h)

  exact
    hilbert_adjacent_angles_congruent
      Geo
      D C A B
      D' C' A' B'
      hDCB
      hD'C'B'
      hDCA
      hD'C'A'
      hDCA_D'C'A'


------------------------------------------------------------------------
-- 2. Complete crossing-rays transfer.

theorem hilbert_right_triangle_third_angle_congruent
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (O A B O' A' B' : Geo.Point)
    (hRight : HilbertRightAngle Geo A O B)
    (hRight' : HilbertRightAngle Geo A' O' B')
    (hNoncol : Not (PrimCollinear Geo O A B))
    (hNoncol' : Not (PrimCollinear Geo O' A' B'))
    (hAngleB :
      Geo.AngleCongruent
        A B O
        A' B' O') :
    Geo.AngleCongruent
      O A B
      O' A' B' := by

  --------------------------------------------------------------------
  -- Extend A-O and A'-O' beyond the right-angle vertices.
  --------------------------------------------------------------------

  have hAO :
      Ne A O :=
    (hilbert_noncollinear_ne_first
      Geo O A B hNoncol).symm

  have hA'O' :
      Ne A' O' :=
    (hilbert_noncollinear_ne_first
      Geo O' A' B' hNoncol').symm

  rcases
      HilbertOrder.between_extension
        A O hAO
    with
    ⟨C, hAOC⟩

  rcases
      HilbertOrder.between_extension
        A' O' hA'O'
    with
    ⟨C', hA'O'C'⟩

  have hBAO :
      Not (PrimCollinear Geo B A O) := by
    intro h
    exact
      hNoncol
        (PrimCollinearRotate
          Geo O B A
          (PrimCollinearSwap
            Geo B O A
            (PrimCollinearRotate
              Geo B A O h)))

  have hB'A'O' :
      Not (PrimCollinear Geo B' A' O') := by
    intro h
    exact
      hNoncol'
        (PrimCollinearRotate
          Geo O' B' A'
          (PrimCollinearSwap
            Geo B' O' A'
            (PrimCollinearRotate
              Geo B' A' O' h)))

  --------------------------------------------------------------------
  -- I.32 decomposes the two exterior angles.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        B A O C
        hBAO
        hAOC
    with
    ⟨R,
      hBRC,
      hPart1,
      hPart2⟩

  rcases
      euclid_proposition_32_exterior
        (Geo := Geo)
        B' A' O' C'
        hB'A'O'
        hA'O'C'
    with
    ⟨R',
      hB'R'C',
      hPart1',
      hPart2'⟩

  --------------------------------------------------------------------
  -- The supplements of the two right angles are congruent.
  --------------------------------------------------------------------

  have hNoncolAOB :
      Not (PrimCollinear Geo A O B) := by
    intro h
    exact
      hNoncol
        (PrimCollinearSwap
          Geo A O B h)

  have hNoncolA'O'B' :
      Not (PrimCollinear Geo A' O' B') := by
    intro h
    exact
      hNoncol'
        (PrimCollinearSwap
          Geo A' O' B' h)

  have hRightCong :
      Geo.AngleCongruent
        A O B
        A' O' B' :=
    hilbert_all_right_angles_congruent
      Geo
      A O B
      A' O' B'
      hNoncolAOB
      hNoncolA'O'B'
      hRight
      hRight'

  have hSupp :
      Geo.AngleCongruent
        B O C
        B' O' C' :=
    hilbert_adjacent_angles_congruent
      Geo
      A O B C
      A' O' B' C'
      hAOC
      hA'O'C'
      hNoncolAOB
      hNoncolA'O'B'
      hRightCong

  --------------------------------------------------------------------
  -- First components of the two exterior decompositions are equal.
  --------------------------------------------------------------------

  have hBOR_ABO :
      Geo.AngleCongruent
        B O R
        A B O :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A B O
      B O R
      hPart1

  have hBOR_AngleB :
      Geo.AngleCongruent
        B O R
        A' B' O' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O R
      A B O
      A' B' O'
      hBOR_ABO
      hAngleB

  have hAngleB_B'O'R' :
      Geo.AngleCongruent
        A' B' O'
        B' O' R' :=
    hPart1'

  have hBOR_B'O'R' :
      Geo.AngleCongruent
        B O R
        B' O' R' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B O R
      A' B' O'
      B' O' R'
      hBOR_AngleB
      hAngleB_B'O'R'

  --------------------------------------------------------------------
  -- The I.32 witnesses are interior rays of the exterior angles.
  --------------------------------------------------------------------

  have hOC :
      Ne O C :=
    (HilbertOrder.between_incidence
      A O C hAOC).2.1

  have hACO :
      PrimCollinear Geo A C O :=
    PrimCollinearRotate
      Geo A O C
      (HilbertOrder.between_incidence
        A O C hAOC).2.2.2.1

  have hBOC :
      Not (PrimCollinear Geo B O C) := by
    intro h
    rcases h with
      ⟨l, hBl, hOl, hCl⟩
    rcases hACO with
      ⟨m, hAm, hCm, hOm⟩
    have hlm :
        l = m :=
      HilbertPlaneIncidence.line_unique
        O C hOC
        l m
        hOl hCl
        hOm hCm
    exact
      hNoncol
        ⟨m,
          hOm,
          hAm,
          hlm ▸ hBl⟩

  have hO'C' :
      Ne O' C' :=
    (HilbertOrder.between_incidence
      A' O' C' hA'O'C').2.1

  have hA'C'O' :
      PrimCollinear Geo A' C' O' :=
    PrimCollinearRotate
      Geo A' O' C'
      (HilbertOrder.between_incidence
        A' O' C' hA'O'C').2.2.2.1

  have hB'O'C' :
      Not (PrimCollinear Geo B' O' C') := by
    intro h
    rcases h with
      ⟨l, hB'l, hO'l, hC'l⟩
    rcases hA'C'O' with
      ⟨m, hA'm, hC'm, hO'm⟩
    have hlm :
        l = m :=
      HilbertPlaneIncidence.line_unique
        O' C' hO'C'
        l m
        hO'l hC'l
        hO'm hC'm
    exact
      hNoncol'
        ⟨m,
          hO'm,
          hA'm,
          hlm ▸ hB'l⟩

  have hRO :
      Ne R O := by
    intro h
    apply hBOC
    have hPrim :
        PrimCollinear Geo B R C :=
      (HilbertOrder.between_incidence
        B R C hBRC).2.2.2.1
    rw [h] at hPrim
    exact hPrim

  have hR'O' :
      Ne R' O' := by
    intro h
    apply hB'O'C'
    have hPrim :
        PrimCollinear Geo B' R' C' :=
      (HilbertOrder.between_incidence
        B' R' C' hB'R'C').2.2.2.1
    rw [h] at hPrim
    exact hPrim

  have hRInside :
      HilbertRayMeetsSegment Geo O R B C :=
    ⟨R,
      hBRC,
      hilbert_sameRay_refl
        Geo O R hRO⟩

  have hR'Inside :
      HilbertRayMeetsSegment Geo O' R' B' C' :=
    ⟨R',
      hB'R'C',
      hilbert_sameRay_refl
        Geo O' R' hR'O'⟩

  --------------------------------------------------------------------
  -- Clean Common-Notion subtraction.
  --------------------------------------------------------------------

  have hCOR_C'O'R' :
      Geo.AngleCongruent
        C O R
        C' O' R' :=
    hilbert_angleDecomposition_angle_subtraction_right
      Geo
      O B C R
      B' O' C' R'
      hBOC
      hB'O'C'
      hRInside
      hR'Inside
      hSupp
      hBOR_B'O'R'

  have hROC_R'O'C' :
      Geo.AngleCongruent
        R O C
        R' O' C' :=
    AngleCongruentReverse
      Geo
      C O R
      C' O' R'
      hCOR_C'O'R'

  --------------------------------------------------------------------
  -- Normalize the I.32 second components to the required third angles.
  --------------------------------------------------------------------

  have hFinal1 :
      Geo.AngleCongruent
        B A O
        R' O' C' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A O
      R O C
      R' O' C'
      hPart2
      hROC_R'O'C'

  have hFinal2 :
      Geo.AngleCongruent
        B A O
        B' A' O' :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A O
      R' O' C'
      B' A' O'
      hFinal1
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        B' A' O'
        R' O' C'
        hPart2')

  have hFinal3 :
      Geo.AngleCongruent
        O A B
        B' A' O' :=
    (Geo.angle_congruent_reverse_first
      B A O
      B' A' O').mp
      hFinal2

  exact
    (Geo.angle_congruent_reverse_second
      O A B
      B' A' O').mp
      hFinal3

theorem hilbert_circle_diameter_chord_intersection_inside
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K R A B C D : Geo.Point)
    (diameter : Geo.Line)
    (hAC : Ne A C)
    (hAdiam : H.OnLine A diameter)
    (hCdiam : H.OnLine C diameter)
    (hKdiam : H.OnLine K diameter)
    (hAcircle : HilbertCircle Geo K R A)
    (hBcircle : HilbertCircle Geo K R B)
    (hCcircle : HilbertCircle Geo K R C)
    (hDcircle : HilbertCircle Geo K R D)
    (hOppBD : HilbertOppositeSide Geo B D diameter) :
    exists Y : Geo.Point,
      Geo.Between B Y D /\
      H.OnLine Y diameter /\
      Geo.Between A Y C := by

  --------------------------------------------------------------------
  -- The diameter center is the midpoint of AC.
  --------------------------------------------------------------------

  have hMidK :
      HilbertIsMidpoint Geo K A C :=
    hilbert_circle_center_midpoint_of_chord
      Geo
      K R A C
      diameter
      hAC
      hAdiam
      hCdiam
      hKdiam
      hAcircle
      hCcircle

  have hAKC :
      Geo.Between A K C :=
    hMidK.1

  have hKA_KC :
      Geo.Congruent K A K C :=
    CongruentReverseFirst
      Geo
      A K
      K C
      hMidK.2

  --------------------------------------------------------------------
  -- Opposite-side data supplies the crossing point Y.
  --------------------------------------------------------------------

  rcases hOppBD.2.2 with
    ⟨Y, hBYD, hYdiam⟩

  have hBYDdata :=
    HilbertOrder.between_incidence
      B Y D hBYD

  have hBD :
      Ne B D :=
    hBYDdata.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        B D hBD
    with
    ⟨chord,
      hBchord,
      hDchord⟩

  have hYchord :
      H.OnLine Y chord :=
    hilbert_between_on_line
      Geo
      B Y D
      chord
      hBchord
      hDchord
      hBYD

  --------------------------------------------------------------------
  -- If K is also on chord BD, the two carriers meet at both K and Y.
  -- Hence Y = K, unless the carriers coincide; the latter would put B
  -- on the diameter, contradicting opposite-side data.
  --------------------------------------------------------------------

  by_cases hKchord :
      H.OnLine K chord

  · have hYK :
        Y = K := by
      by_contra hYK

      have hEq :
          diameter = chord :=
        HilbertPlaneIncidence.line_unique
          Y K hYK
          diameter chord
          hYdiam hKdiam
          hYchord hKchord

      have hBdiam :
          H.OnLine B diameter := by
        rw [hEq]
        exact hBchord

      exact hOppBD.1 hBdiam

    subst Y

    exact
      ⟨K,
        hBYD,
        hKdiam,
        hAKC⟩

  --------------------------------------------------------------------
  -- Otherwise Y is an interior point of a non-diameter chord BD.
  -- Stage 20 places it strictly inside the circle.
  --------------------------------------------------------------------

  · have hKY_KB :
        HilbertSegmentLess Geo K Y K B :=
      hilbert_circle_chord_inner_point_inside
        Geo
        K R B D Y
        chord
        hBD
        hBchord
        hDchord
        hKchord
        hBcircle
        hDcircle
        hBYD

    have hKB_KA :
        Geo.Congruent K B K A :=
      hilbert_circle_center_congruent
        Geo
        K R
        B A
        hBcircle
        hAcircle

    have hKY_KA :
        HilbertSegmentLess Geo K Y K A :=
      hilbert_segmentLess_congruent_right
        Geo
        K Y
        K B
        K A
        hKY_KB
        hKB_KA

    ------------------------------------------------------------------
    -- Y is a proper point distinct from the diameter endpoints.
    ------------------------------------------------------------------

    have hAY :
        Ne A Y := by
      intro hAY
      subst Y

      have hKA_KA :
          Geo.Congruent K A K A :=
        hilbert_congruent_reflexive
          Geo K A

      exact
        (hilbert_segmentLess_not_congruent
          Geo
          K A
          K A
          hKY_KA)
          hKA_KA

    have hYC :
        Ne Y C := by
      intro hYC
      subst Y

      have hKC_KA :
          Geo.Congruent K C K A :=
        hilbert_congruent_symmetry
          Geo
          K A
          K C
          hKA_KC

      exact
        (hilbert_segmentLess_not_congruent
          Geo
          K C
          K A
          hKY_KA)
          hKC_KA

    have hAYCcol :
        PrimCollinear Geo A Y C :=
      ⟨diameter,
        hAdiam,
        hYdiam,
        hCdiam⟩

    ------------------------------------------------------------------
    -- Trichotomy on the diameter carrier.
    ------------------------------------------------------------------

    rcases
        hilbert_between_trichotomy
          Geo
          A Y C
          hAY
          hYC
          hAC
          hAYCcol
      with
      hAYC | hYAC | hACY

    ------------------------------------------------------------------
    -- Desired internal order.
    ------------------------------------------------------------------

    · exact
        ⟨Y,
          hBYD,
          hYdiam,
          hAYC⟩

    ------------------------------------------------------------------
    -- Exterior order Y-A-C forces KA < KY.
    ------------------------------------------------------------------

    · have hCAY :
          Geo.Between C A Y :=
        (HilbertOrder.between_incidence
          Y A C hYAC).2.2.2.2

      have hCKA :
          Geo.Between C K A :=
        (HilbertOrder.between_incidence
          A K C hAKC).2.2.2.2

      have hKAY :
          Geo.Between K A Y :=
        (hilbert_between_inner_trans
          Geo
          C K A Y
          hCKA
          hCAY).1

      have hKA_KY :
          HilbertSegmentLess Geo K A K Y :=
        hilbert_segmentLess_of_between
          Geo
          K A Y
          hKAY

      exact
        False.elim
          ((hilbert_segmentLess_asymm
              Geo
              K Y
              K A
              hKY_KA)
            hKA_KY)

    ------------------------------------------------------------------
    -- Exterior order A-C-Y forces KC < KY, hence KA < KY.
    ------------------------------------------------------------------

    · have hKCY :
          Geo.Between K C Y :=
        (hilbert_between_inner_trans
          Geo
          A K C Y
          hAKC
          hACY).1

      have hKC_KY :
          HilbertSegmentLess Geo K C K Y :=
        hilbert_segmentLess_of_between
          Geo
          K C Y
          hKCY

      have hKA_KY :
          HilbertSegmentLess Geo K A K Y :=
        hilbert_segmentLess_congruent_left
          Geo
          K C
          K A
          K Y
          hKC_KY
          hKA_KC

      exact
        False.elim
          ((hilbert_segmentLess_asymm
              Geo
              K Y
              K A
              hKY_KA)
            hKA_KY)

theorem hilbert_oppositeSide_tail_sameSide
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (A K E B D : Geo.Point)
    (d : Geo.Line)
    (hBD : Ne B D)
    (hBd : H.OnLine B d)
    (hDd : H.OnLine D d)
    (hOppAK : HilbertOppositeSide Geo A K d)
    (hAKE : Geo.Between A K E) :
    HilbertSameSide Geo K E d := by

  have hKoff :
      Not (H.OnLine K d) :=
    hOppAK.2.1

  rcases hOppAK.2.2 with
    ⟨Y, hAYK, hYd⟩

  have hTrans :=
    hilbert_between_inner_trans
      Geo
      A Y K E
      hAYK
      hAKE

  have hYKE :
      Geo.Between Y K E :=
    hTrans.1

  have hAYE :
      Geo.Between A Y E :=
    hTrans.2

  have hYKEdata :=
    HilbertOrder.between_incidence
      Y K E hYKE

  have hYK :
      Ne Y K :=
    hYKEdata.1

  have hYE :
      Ne Y E :=
    hYKEdata.2.2.1

  rcases
      (HilbertOrder.between_incidence
        A Y E hAYE).2.2.2.1
    with
    ⟨lineYE,
      hAline,
      hYline,
      hEline⟩

  have hKline :
      H.OnLine K lineYE :=
    hilbert_between_on_line
      Geo
      Y K E
      lineYE
      hYline hEline hYKE

  have hRayYKE :
      HilbertSameRay Geo Y K E :=
    hilbert_sameRay_of_between
      Geo
      Y K E
      hYKE

  have hRayYKK :
      HilbertSameRay Geo Y K K :=
    hilbert_sameRay_refl
      Geo
      Y K
      hYK.symm

  by_cases hBline :
      H.OnLine B lineYE

  --------------------------------------------------------------------
  -- B lies on YE, so D must be off YE.
  --------------------------------------------------------------------

  · have hDoffLine :
        Not (H.OnLine D lineYE) := by
      intro hDline

      have hEq :
          lineYE = d :=
        HilbertPlaneIncidence.line_unique
          B D hBD
          lineYE d
          hBline hDline
          hBd hDd

      exact
        hKoff
          (hEq ▸ hKline)

    exact
      hilbert_sameRay_points_sameSide
        Geo
        Y K
        K E
        D
        lineYE d
        hYline hKline
        hYd hDd
        hDoffLine
        hRayYKK
        hRayYKE

  --------------------------------------------------------------------
  -- B itself is the required second point of d off YE.
  --------------------------------------------------------------------

  · exact
      hilbert_sameRay_points_sameSide
        Geo
        Y K
        K E
        B
        lineYE d
        hYline hKline
        hYd hBd
        hBline
        hRayYKK
        hRayYKE

theorem hilbert_two_opposites_sameSide_with_carrier
    [H : HilbertIncidence Geo]
    [HO : @HilbertOrder Geo H]
    (C A K B D : Geo.Point)
    (d : Geo.Line)
    (hBD : Ne B D)
    (hBd : H.OnLine B d)
    (hDd : H.OnLine D d)
    (hOppCA : HilbertOppositeSide Geo C A d)
    (hOppCK : HilbertOppositeSide Geo C K d) :
    HilbertSameSide Geo A K d := by

  by_cases hAK : A = K

  · subst K
    exact
      hilbert_sameSide_refl
        Geo
        A d
        hOppCA.2.1

  have hCA :
      Ne C A := by
    rcases hOppCA.2.2 with
      ⟨X, hCXA, _⟩
    exact
      (HilbertOrder.between_incidence
        C X A hCXA).2.2.1

  have hCK :
      Ne C K := by
    rcases hOppCK.2.2 with
      ⟨X, hCXK, _⟩
    exact
      (HilbertOrder.between_incidence
        C X K hCXK).2.2.1

  by_cases hCol :
      PrimCollinear Geo C A K

  --------------------------------------------------------------------
  -- Collinear case.
  --------------------------------------------------------------------

  · rcases
        hilbert_between_trichotomy
          Geo
          C A K
          hCA
          hAK
          hCK
          hCol
      with
      hCAK | hACK | hCKA

    --------------------------------------------------------------
    -- C-A-K.
    --------------------------------------------------------------

    · exact
        hilbert_oppositeSide_tail_sameSide
          Geo
          C A K B D
          d
          hBD
          hBd
          hDd
          hOppCA
          hCAK

    --------------------------------------------------------------
    -- A-C-K is impossible: stage 49 would make C,K same-side.
    --------------------------------------------------------------

    · have hOppAC :
          HilbertOppositeSide Geo A C d :=
        hilbert_oppositeSide_symm
          Geo C A d hOppCA

      have hSameCK :
          HilbertSameSide Geo C K d :=
        hilbert_oppositeSide_tail_sameSide
          Geo
          A C K B D
          d
          hBD
          hBd
          hDd
          hOppAC
          hACK

      exact
        False.elim
          ((hilbert_oppositeSide_not_sameSide
            Geo C K d hOppCK)
          hSameCK)

    --------------------------------------------------------------
    -- C-K-A.
    --------------------------------------------------------------

    · have hSameKA :
          HilbertSameSide Geo K A d :=
        hilbert_oppositeSide_tail_sameSide
          Geo
          C K A B D
          d
          hBD
          hBd
          hDd
          hOppCK
          hCKA

      exact
        hilbert_sameSide_symm
          Geo K A d hSameKA

  --------------------------------------------------------------------
  -- Noncollinear case: ordinary Pasch parity.
  --------------------------------------------------------------------

  · rcases hOppCA.2.2 with
      ⟨X, hCXA, hXd⟩

    rcases hOppCK.2.2 with
      ⟨Y, hCYK, hYd⟩

    exact
      hilbert_third_side_endpoints_sameSide
        Geo
        C A K
        X Y
        d
        hCol
        hCXA
        hCYK
        hXd
        hYd

theorem hilbert_triangle_angle_not_supplement
    [H : HilbertIncidence Geo]
    [HC : @HilbertCongruence Geo H]
    (X S A U : Geo.Point)
    (hXSA : Not (PrimCollinear Geo X S A))
    (hSAU : Geo.Between S A U) :
    Not (Geo.AngleCongruent X S A X A U) := by

  intro hCong

  --------------------------------------------------------------------
  -- Euclid I.17: angle XSA is strictly smaller than a supplement of
  -- angle XAS.  The witness is some E with S-A-E.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_17_ABC_ACB
        Geo
        X S A
        hXSA
    with
    ⟨E, hSAE, hLessE⟩

  --------------------------------------------------------------------
  -- E and U are both beyond A from S, hence they determine the same
  -- ray from A.
  --------------------------------------------------------------------

  have hRayAEU :
      HilbertSameRay Geo A E U :=
    hilbert_sameRay_beyond_common_middle
      Geo
      S A E U
      hSAE
      hSAU

  have hAngleEq :
      Geo.Angle X A E =
      Geo.Angle X A U :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      A X E U
      hRayAEU

  have hE_U :
      Geo.AngleCongruent X A E X A U := by
    unfold Geometry.Geo.AngleCongruent
    rw [hAngleEq]
    exact Relation.EqvGen.refl _

  --------------------------------------------------------------------
  -- The target angle XAU is proper.
  --------------------------------------------------------------------

  have hSAUdata :=
    HilbertOrder.between_incidence
      S A U hSAU

  have hAU :
      Ne A U :=
    hSAUdata.2.1

  have hSAUcol :
      PrimCollinear Geo S A U :=
    hSAUdata.2.2.2.1

  have hAUS :
      PrimCollinear Geo A U S :=
    PrimCollinearCycle
      Geo S A U hSAUcol

  have hXAU :
      Not (PrimCollinear Geo X A U) := by
    intro h

    rcases
        HilbertPlaneIncidence.line_through
          A U hAU
      with
      ⟨l, hAl, hUl⟩

    have hSl :
        H.OnLine S l :=
      hilbert_collinear_on_line
        Geo
        A U S
        l
        hAU
        hAl
        hUl
        hAUS

    have hAUX :
        PrimCollinear Geo A U X :=
      PrimCollinearCycle
        Geo X A U h

    have hXl :
        H.OnLine X l :=
      hilbert_collinear_on_line
        Geo
        A U X
        l
        hAU
        hAl
        hUl
        hAUX

    exact
      hXSA
        ⟨l,
          hXl,
          hSl,
          hAl⟩

  --------------------------------------------------------------------
  -- Transport the I.17 strict inequality from XAE to XAU.
  --------------------------------------------------------------------

  have hLessU :
      HilbertAngleLess Geo
        X S A
        X A U :=
    hilbert_angleLess_transport_right
      Geo
      X S A
      X A E
      X A U
      hLessE
      hXAU
      hE_U

  --------------------------------------------------------------------
  -- If XSA ~= XAU, transport once more and obtain XSA < XSA.
  --------------------------------------------------------------------

  have hU_S :
      Geo.AngleCongruent X A U X S A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X S A
      X A U
      hCong

  have hCycle :
      HilbertAngleLess Geo
        X S A
        X S A :=
    hilbert_angleLess_transport_right
      Geo
      X S A
      X A U
      X S A
      hLessU
      hXSA
      hU_S

  exact
    hilbert_angleLess_irrefl
      Geo
      X S A
      hCycle

theorem hilbert_two_right_angles_same_first_arm_collinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (F O M N : Geo.Point)
    (base : Geo.Line)
    (hFO : Ne F O)
    (hFbase : HilbertIncidence.OnLine F base)
    (hObase : HilbertIncidence.OnLine O base)
    (hFOM : Not (PrimCollinear Geo F O M))
    (hFON : Not (PrimCollinear Geo F O N))
    (hRightM : HilbertRightAngle Geo F O M)
    (hRightN : HilbertRightAngle Geo F O N) :
    PrimCollinear Geo M O N := by

  have hMoff :
      Not (HilbertIncidence.OnLine M base) := by
    intro hMbase
    exact hFOM
      ⟨base, hFbase, hObase, hMbase⟩

  have hNoff :
      Not (HilbertIncidence.OnLine N base) := by
    intro hNbase
    exact hFON
      ⟨base, hFbase, hObase, hNbase⟩

  by_cases hSameMN :
      HilbertSameSide Geo M N base

  · have hAngles :
        Geo.AngleCongruent F O M F O N :=
      hilbert_all_right_angles_congruent
        Geo
        F O M
        F O N
        hFOM hFON
        hRightM hRightN

    rcases
        hilbert_angle_unique_common_ray
          Geo
          F O M N
          base
          hFO
          hFbase hObase
          hMoff
          hSameMN
          hAngles with
      ⟨X, hRayXM, hRayXN⟩

    have hOX :
        Ne O X :=
      hRayXM.1.symm

    have hOXM :
        PrimCollinear Geo O X M :=
      hRayXM.2.2.1

    have hMOX :
        PrimCollinear Geo M O X :=
      PrimCollinearCycle
        Geo X M O
        (PrimCollinearCycle
          Geo O X M hOXM)

    have hOXN :
        PrimCollinear Geo O X N :=
      hRayXN.2.2.1

    exact
      hilbert_primCollinear_trans
        Geo
        M O X N
        hOX
        hMOX
        hOXN

  · have hOppMN :
        HilbertOppositeSide Geo M N base :=
      hilbert_oppositeSide_of_not_sameSide
        Geo
        M N base
        hMoff hNoff
        hSameMN

    have hMO : Ne M O := by
      intro hEq
      subst M
      exact hFOM
        ⟨base, hFbase, hObase, hObase⟩

    rcases
        HilbertOrder.between_extension
          (Geo := Geo)
          M O hMO with
      ⟨M', hMOM'⟩

    by_contra hMON

    have hSameNM' :
        HilbertSameSide Geo N M' base :=
      hilbert_sameSide_after_opposite_extension
        Geo
        M O N M'
        base
        hObase
        hMON
        hMOM'
        hOppMN

    have hM'off :
        Not (HilbertIncidence.OnLine M' base) :=
      hSameNM'.2.1

    have hFOM' :
        Not (PrimCollinear Geo F O M') :=
      hilbert_not_collinear_of_off_line
        Geo
        F O M'
        base
        hFO
        hFbase hObase
        hM'off

    have hMOF :
        Not (PrimCollinear Geo M O F) := by
      intro h
      exact hFOM
        (PrimCollinearSymm
          Geo M O F h)

    have hRightMOF :
        HilbertRightAngle Geo M O F :=
      hilbert_right_angle_swap_XI
        Geo
        F O M
        hFOM
        hRightM

    have hAngleMOF_FOM' :
        Geo.AngleCongruent M O F F O M' :=
      hilbert_right_angle_opposite_extension
        Geo
        M O F M'
        hMOF
        hRightMOF
        hMOM'

    have hRightM' :
        HilbertRightAngle Geo F O M' :=
      hilbert_right_angle_transport
        Geo
        M O F
        F O M'
        hMOF
        hFOM'
        hRightMOF
        hAngleMOF_FOM'

    have hSameM'N :
        HilbertSameSide Geo M' N base :=
      hilbert_sameSide_symm
        Geo N M' base hSameNM'

    have hAngles' :
        Geo.AngleCongruent F O M' F O N :=
      hilbert_all_right_angles_congruent
        Geo
        F O M'
        F O N
        hFOM' hFON
        hRightM' hRightN

    rcases
        hilbert_angle_unique_common_ray
          Geo
          F O M' N
          base
          hFO
          hFbase hObase
          hM'off
          hSameM'N
          hAngles' with
      ⟨X, hRayXM', hRayXN⟩

    have hOX :
        Ne O X :=
      hRayXM'.1.symm

    have hOXM' :
        PrimCollinear Geo O X M' :=
      hRayXM'.2.2.1

    have hM'OX :
        PrimCollinear Geo M' O X :=
      PrimCollinearCycle
        Geo X M' O
        (PrimCollinearCycle
          Geo O X M' hOXM')

    have hOXN :
        PrimCollinear Geo O X N :=
      hRayXN.2.2.1

    have hM'ON :
        PrimCollinear Geo M' O N :=
      hilbert_primCollinear_trans
        Geo
        M' O X N
        hOX
        hM'OX
        hOXN

    have hOM'N :
        PrimCollinear Geo O M' N :=
      PrimCollinearSwap
        Geo M' O N hM'ON

    have hMOM'Data :=
      HilbertOrder.between_incidence
        (Geo := Geo)
        M O M' hMOM'

    have hOM' : Ne O M' :=
      hMOM'Data.2.1

    have hMOM'col :
        PrimCollinear Geo M O M' :=
      hMOM'Data.2.2.2.1

    exact hMON
      (hilbert_primCollinear_trans
        Geo
        M O M' N
        hOM'
        hMOM'col
        hOM'N)

theorem hilbert_circle_tangent_carrier_unique
    [H : HilbertIncidence Geo]
    [HE : @HilbertEuclideanPlane Geo H]
    (K A : Geo.Point)
    (l m : Geo.Line)
    (hAl : H.OnLine A l)
    (hAm : H.OnLine A m)
    (hTanL :
      HilbertCircleTangentAt
        (Geo := Geo) K A l)
    (hTanM :
      HilbertCircleTangentAt
        (Geo := Geo) K A m) :
    l = m := by

  rcases hTanL with
    ⟨U, hUl, hUA, hUAK, hRightUAK⟩

  rcases hTanM with
    ⟨V, hVm, hVA, hVAK, hRightVAK⟩

  have hKAU :
      Not (PrimCollinear Geo K A U) := by
    intro h
    exact
      hUAK
        (PrimCollinearSymm
          Geo K A U h)

  have hKAV :
      Not (PrimCollinear Geo K A V) := by
    intro h
    exact
      hVAK
        (PrimCollinearSymm
          Geo K A V h)

  have hRightKAU :
      HilbertRightAngle Geo K A U :=
    hilbert_right_angle_swap_XI
      Geo
      U A K
      hUAK
      hRightUAK

  have hRightKAV :
      HilbertRightAngle Geo K A V :=
    hilbert_right_angle_swap_XI
      Geo
      V A K
      hVAK
      hRightVAK

  have hKA :
      Ne K A :=
    hilbert_noncollinear_ne_first
      Geo K A U hKAU

  rcases
      HilbertPlaneIncidence.line_through
        K A hKA
    with
    ⟨base, hKbase, hAbase⟩

  have hUAV :
      PrimCollinear Geo U A V :=
    hilbert_two_right_angles_same_first_arm_collinear
      Geo
      K A U V
      base
      hKA
      hKbase
      hAbase
      hKAU
      hKAV
      hRightKAU
      hRightKAV

  have hAU :
      Ne A U :=
    hUA.symm

  have hAUV :
      PrimCollinear Geo A U V :=
    PrimCollinearSwap
      Geo U A V hUAV

  have hVl :
      H.OnLine V l :=
    hilbert_collinear_on_line
      Geo
      A U V
      l
      hAU
      hAl
      hUl
      hAUV

  have hAV :
      Ne A V :=
    hVA.symm

  exact
    HilbertPlaneIncidence.line_unique
      A V hAV
      l m
      hAl hVl
      hAm hVm

end Geometry

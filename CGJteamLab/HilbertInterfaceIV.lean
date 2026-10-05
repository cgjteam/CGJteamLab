import CGJteamLab.HilbertInterfaceXI

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
Backward-compatible name used by the development stages.
-/
abbrev HilbertCircleTangentAtStage4
    [H : HilbertIncidence Geo]
    [_HC : @HilbertCongruence Geo H]
    (K A : Geo.Point)
    (line : Geo.Line) : Prop :=
  HilbertCircleTangentAt
    (Geo := Geo) K A line


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

end Geometry

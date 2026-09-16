import CGJteamLab.HilbertAngleDecomposition

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Synthetic comparison of a sum of two angles with one angle

This module contains the dimension-free planar comparison relation used
first in Euclid XI.20 and later in XI.21 and XI.22.

No numerical angle measure and no global angle-addition operation are
introduced.

The intended meaning is

    angle AOB + angle CPD > angle EQF.

The relation is represented synthetically by three cases:

1. the target angle is already smaller than the first summand;
2. the target angle is congruent to the first summand;
3. the target angle is decomposed by an interior ray, the first summand
   fills the first part, and the second summand is larger than the
   remaining part.

This file is deliberately independent of all three-dimensional spatial
interfaces.
-/

/--
Synthetic meaning of

    angle AOB + angle CPD > angle EQF.

All three angles are explicitly required to be proper.
-/
def HilbertTwoAnglesGreaterThanAngle
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point) : Prop :=
  Not (PrimCollinear Geo A O B) /\
  Not (PrimCollinear Geo C P D) /\
  Not (PrimCollinear Geo E Q F) /\
  (
    HilbertAngleLess Geo E Q F A O B
    \/
    Geo.AngleCongruent E Q F A O B
    \/
    exists X : Geo.Point,
      HilbertRayMeetsSegment Geo Q X E F /\
      Geo.AngleCongruent A O B E Q X /\
      HilbertAngleLess Geo X Q F C P D
  )


------------------------------------------------------------------------
-- Accessors
------------------------------------------------------------------------

theorem hilbertTwoAnglesGreaterThanAngle_first_proper
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F) :
    Not (PrimCollinear Geo A O B) :=
  h.1


theorem hilbertTwoAnglesGreaterThanAngle_second_proper
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F) :
    Not (PrimCollinear Geo C P D) :=
  h.2.1


theorem hilbertTwoAnglesGreaterThanAngle_target_proper
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F) :
    Not (PrimCollinear Geo E Q F) :=
  h.2.2.1


------------------------------------------------------------------------
-- Elementary constructors
------------------------------------------------------------------------

theorem hilbertTwoAnglesGreaterThanAngle_of_first_greater
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (hFirst :
      Not (PrimCollinear Geo A O B))
    (hSecond :
      Not (PrimCollinear Geo C P D))
    (hTarget :
      Not (PrimCollinear Geo E Q F))
    (hLess :
      HilbertAngleLess Geo E Q F A O B) :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A O B
      C P D
      E Q F := by
  exact
    And.intro hFirst
      (And.intro hSecond
        (And.intro hTarget
          (Or.inl hLess)))


theorem hilbertTwoAnglesGreaterThanAngle_of_first_equal
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (hFirst :
      Not (PrimCollinear Geo A O B))
    (hSecond :
      Not (PrimCollinear Geo C P D))
    (hTarget :
      Not (PrimCollinear Geo E Q F))
    (hEq :
      Geo.AngleCongruent E Q F A O B) :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A O B
      C P D
      E Q F := by
  exact
    And.intro hFirst
      (And.intro hSecond
        (And.intro hTarget
          (Or.inr (Or.inl hEq))))


theorem hilbertTwoAnglesGreaterThanAngle_of_decomposition
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F X : Geo.Point)
    (hFirst :
      Not (PrimCollinear Geo A O B))
    (hSecond :
      Not (PrimCollinear Geo C P D))
    (hTarget :
      Not (PrimCollinear Geo E Q F))
    (hInside :
      HilbertRayMeetsSegment Geo Q X E F)
    (hFirstPart :
      Geo.AngleCongruent A O B E Q X)
    (hRemainder :
      HilbertAngleLess Geo X Q F C P D) :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A O B
      C P D
      E Q F := by
  exact
    And.intro hFirst
      (And.intro hSecond
        (And.intro hTarget
          (Or.inr
            (Or.inr
              (Exists.intro X
                (And.intro hInside
                  (And.intro hFirstPart hRemainder)))))))


------------------------------------------------------------------------
-- Congruence transport
------------------------------------------------------------------------

/--
Replace the first summand by a congruent proper angle.
-/
theorem hilbertTwoAnglesGreaterThanAngle_transport_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B A' O' B' C P D E Q F : Geo.Point)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hFirst' : Not (PrimCollinear Geo A' O' B'))
    (hFirstCong :
      Geo.AngleCongruent
        A O B
        A' O' B') :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A' O' B'
      C P D
      E Q F := by

  have hSecond :
      Not (PrimCollinear Geo C P D) :=
    h.2.1

  have hTarget :
      Not (PrimCollinear Geo E Q F) :=
    h.2.2.1

  have hCore :=
    h.2.2.2

  refine
    And.intro hFirst'
      (And.intro hSecond
        (And.intro hTarget ?_))

  cases hCore with
  | inl hLess =>
      have hLess' :
          HilbertAngleLess
            Geo
            E Q F
            A' O' B' :=
        hilbert_angleLess_transport_right
          Geo
          E Q F
          A O B
          A' O' B'
          hLess
          hFirst'
          hFirstCong

      exact Or.inl hLess'

  | inr hRest =>
      cases hRest with
      | inl hEq =>
          have hEq' :
              Geo.AngleCongruent
                E Q F
                A' O' B' :=
            Geometry.Geo.angle_congruent_transitivity
              Geo
              E Q F
              A O B
              A' O' B'
              hEq
              hFirstCong

          exact Or.inr (Or.inl hEq')

      | inr hDecomp =>
          cases hDecomp with
          | intro X hData =>
              have hInside :
                  HilbertRayMeetsSegment Geo Q X E F :=
                hData.1

              have hFirstPart :
                  Geo.AngleCongruent A O B E Q X :=
                hData.2.1

              have hRemainder :
                  HilbertAngleLess Geo X Q F C P D :=
                hData.2.2

              have hFirstCongSymm :
                  Geo.AngleCongruent
                    A' O' B'
                    A O B :=
                Geometry.Geo.angle_congruent_symmetry
                  Geo
                  A O B
                  A' O' B'
                  hFirstCong

              have hFirstPart' :
                  Geo.AngleCongruent
                    A' O' B'
                    E Q X :=
                Geometry.Geo.angle_congruent_transitivity
                  Geo
                  A' O' B'
                  A O B
                  E Q X
                  hFirstCongSymm
                  hFirstPart

              exact
                Or.inr
                  (Or.inr
                    (Exists.intro X
                      (And.intro hInside
                        (And.intro hFirstPart' hRemainder))))


/--
Replace the second summand by a congruent proper angle.
-/
theorem hilbertTwoAnglesGreaterThanAngle_transport_second
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D C' P' D' E Q F : Geo.Point)
    (h :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O B
        C P D
        E Q F)
    (hSecond' : Not (PrimCollinear Geo C' P' D'))
    (hSecondCong :
      Geo.AngleCongruent
        C P D
        C' P' D') :
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A O B
      C' P' D'
      E Q F := by

  have hFirst :
      Not (PrimCollinear Geo A O B) :=
    h.1

  have hTarget :
      Not (PrimCollinear Geo E Q F) :=
    h.2.2.1

  have hCore :=
    h.2.2.2

  refine
    And.intro hFirst
      (And.intro hSecond'
        (And.intro hTarget ?_))

  cases hCore with
  | inl hLess =>
      exact Or.inl hLess

  | inr hRest =>
      cases hRest with
      | inl hEq =>
          exact Or.inr (Or.inl hEq)

      | inr hDecomp =>
          cases hDecomp with
          | intro X hData =>
              have hInside :
                  HilbertRayMeetsSegment Geo Q X E F :=
                hData.1

              have hFirstPart :
                  Geo.AngleCongruent A O B E Q X :=
                hData.2.1

              have hRemainder :
                  HilbertAngleLess Geo X Q F C P D :=
                hData.2.2

              have hRemainder' :
                  HilbertAngleLess
                    Geo
                    X Q F
                    C' P' D' :=
                hilbert_angleLess_transport_right
                  Geo
                  X Q F
                  C P D
                  C' P' D'
                  hRemainder
                  hSecond'
                  hSecondCong

              exact
                Or.inr
                  (Or.inr
                    (Exists.intro X
                      (And.intro hInside
                        (And.intro hFirstPart hRemainder'))))

end Geometry

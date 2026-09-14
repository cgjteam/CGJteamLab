import CGJteamLab.Hilbert3DInterface
import CGJteamLab.HilbertAngleDecomposition

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
A proper trihedral configuration with vertex `O` and three rays
`OA`, `OB`, `OC`.

The three face angles are required to be proper, and the four points
`O, A, B, C` are not contained in one plane.

This is the neutral Hilbert 3D language intended for Euclid XI.20.
It contains no numerical angle measure.
-/
def HilbertTrihedralConfiguration
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point) : Prop :=
  Not (PrimCollinear Geo A O B) /\
  Not (PrimCollinear Geo B O C) /\
  Not (PrimCollinear Geo C O A) /\
  Not
    (exists pi : S.Plane,
      S.OnPlane O pi /\
      S.OnPlane A pi /\
      S.OnPlane B pi /\
      S.OnPlane C pi)


/--
Synthetic meaning of

    angle AOB + angle CPD > angle EQF.

No numerical angle addition is introduced.

The relation is witnessed in one of three ways.

1. The target angle is already strictly smaller than the first angle.
2. The target angle is congruent to the first angle; the proper
   second angle then makes the sum strictly larger.
3. The target angle is decomposed by an interior ray `QX`:
      angle AOB ~= angle EQX
   and
      angle XQF < angle CPD.
   Thus the first angle fills the first component of the target,
   while the second angle is strictly larger than the remaining
   component.

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


/--
The three cyclic inequalities asserted by Euclid XI.20 for the
trihedral configuration `O; A, B, C`.

They are written in the cyclic form

    AOB + BOC > AOC,
    BOC + COA > BOA,
    COA + AOB > COB.
-/
def HilbertTrihedralAngleInequalities
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (O A B C : Geo.Point) : Prop :=
  HilbertTwoAnglesGreaterThanAngle
      Geo
      A O B
      B O C
      A O C
  /\
  HilbertTwoAnglesGreaterThanAngle
      Geo
      B O C
      C O A
      B O A
  /\
  HilbertTwoAnglesGreaterThanAngle
      Geo
      C O A
      A O B
      C O B


------------------------------------------------------------------------
-- Accessors for the trihedral configuration
------------------------------------------------------------------------

theorem hilbertTrihedralConfiguration_face_AB
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point)
    (h :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    Not (PrimCollinear Geo A O B) :=
  h.1


theorem hilbertTrihedralConfiguration_face_BC
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point)
    (h :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    Not (PrimCollinear Geo B O C) :=
  h.2.1


theorem hilbertTrihedralConfiguration_face_CA
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point)
    (h :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    Not (PrimCollinear Geo C O A) :=
  h.2.2.1


theorem hilbertTrihedralConfiguration_not_coplanar
    [HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (O A B C : Geo.Point)
    (h :
      HilbertTrihedralConfiguration
        Geo O A B C) :
    Not
      (exists pi : S.Plane,
        S.OnPlane O pi /\
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi) :=
  h.2.2.2


------------------------------------------------------------------------
-- Accessors for the synthetic angle-sum comparison
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
    ⟨hFirst,
      hSecond,
      hTarget,
      Or.inl hLess⟩


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
    ⟨hFirst,
      hSecond,
      hTarget,
      Or.inr (Or.inl hEq)⟩


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
    ⟨hFirst,
      hSecond,
      hTarget,
      Or.inr
        (Or.inr
          ⟨X,
            hInside,
            hFirstPart,
            hRemainder⟩)⟩


end Geometry

import CGJteamLab.HilbertTrihedralAngleMetric

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Synthetic three-angle bound by four right angles

This module contains the common planar language needed for Euclid XI.21.

No numerical angle measure and no general addition operation on angles are
introduced.

For proper angles alpha, beta, gamma, the classical inequality

    alpha + beta + gamma < 4R

is represented by choosing supplements of alpha and beta and requiring

    supplement(alpha) + supplement(beta) > gamma.

The final comparison is expressed by the already established
`HilbertTwoAnglesGreaterThanAngle` relation from XI.20.

This representation is intended to be shared by the Hilbert and
Hilbert-Wyler proofs of XI.21.
-/

/--
Synthetic meaning of

    angle AOB + angle CPD + angle EQF < four right angles.

Choose X and Y so that

    B - O - X,
    D - P - Y.

Then AOX and CPY are supplements of AOB and CPD.  The required bound is
represented by

    angle AOX + angle CPY > angle EQF.

All three original angles are required to be proper.
-/
def HilbertThreeAnglesLessThanFourRightAngles
    [HilbertIncidence Geo]
    (A O B C P D E Q F : Geo.Point) : Prop :=
  Not (PrimCollinear Geo A O B) /\
  Not (PrimCollinear Geo C P D) /\
  Not (PrimCollinear Geo E Q F) /\
  exists X Y : Geo.Point,
    Geo.Between B O X /\
    Geo.Between D P Y /\
    HilbertTwoAnglesGreaterThanAngle
      Geo
      A O X
      C P Y
      E Q F


/--
Constructor for the synthetic three-angle bound.
-/
theorem hilbertThreeAnglesLessThanFourRightAngles_intro
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F X Y : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hCPD : Not (PrimCollinear Geo C P D))
    (hEQF : Not (PrimCollinear Geo E Q F))
    (hBOX : Geo.Between B O X)
    (hDPY : Geo.Between D P Y)
    (hCompare :
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O X
        C P Y
        E Q F) :
    HilbertThreeAnglesLessThanFourRightAngles
      Geo
      A O B
      C P D
      E Q F := by
  exact
    And.intro hAOB
      (And.intro hCPD
        (And.intro hEQF
          (Exists.intro X
            (Exists.intro Y
              (And.intro hBOX
                (And.intro hDPY hCompare))))))


/--
The three original angles in the synthetic bound are proper.
-/
theorem hilbertThreeAnglesLessThanFourRightAngles_proper
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    Not (PrimCollinear Geo A O B) /\
    Not (PrimCollinear Geo C P D) /\
    Not (PrimCollinear Geo E Q F) := by
  exact
    And.intro h.1
      (And.intro h.2.1 h.2.2.1)


/--
Extract the two supplement witnesses and the XI.20-style comparison.
-/
theorem hilbertThreeAnglesLessThanFourRightAngles_elim
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B C P D E Q F : Geo.Point)
    (h :
      HilbertThreeAnglesLessThanFourRightAngles
        Geo
        A O B
        C P D
        E Q F) :
    exists X Y : Geo.Point,
      Geo.Between B O X /\
      Geo.Between D P Y /\
      HilbertTwoAnglesGreaterThanAngle
        Geo
        A O X
        C P Y
        E Q F := by
  exact h.2.2.2


/--
Proposition-level XI.21 predicate for the three face angles at A.

The complement certificate is stored in the order

    CAD, BAC, DAB.

This order is chosen because it is produced directly by XI.20 after
replacing the ray AC by its opposite ray.
-/
def HilbertTrihedralAnglesLessThanFourRightAngles
    [HilbertIncidence Geo]
    (A B C D : Geo.Point) : Prop :=
  HilbertThreeAnglesLessThanFourRightAngles
    Geo
    C A D
    B A C
    D A B

end Geometry

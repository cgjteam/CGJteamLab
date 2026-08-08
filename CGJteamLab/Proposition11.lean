import CGJteamLab.HilbertBookZero

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition I.11.

Given a point C lying between A and B, there exists a ray from C
which forms a right angle with the line AB.
-/
theorem euclid_proposition_11
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A C B : Geo.Point)
    (hACB : Geo.Between A C B) :
    ∃ X : Geo.Point,
      HilbertRightAngle Geo A C X := by

  exact
    hilbert_right_angle_exists
      Geo A C B hACB

end Geometry
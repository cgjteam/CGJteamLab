import CGJteamLab.HilbertInterface

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition I.10.

To bisect a given finite straight line.
-/
theorem euclid_proposition_10
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ M : Geo.Point,
      HilbertIsMidpoint Geo M A B := by

  exact
    HilbertMidpointExists
      Geo A B hAB

end Geometry

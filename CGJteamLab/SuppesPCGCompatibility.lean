import CGJteamLab.SuppesInterface
import CGJteamLab.SuppesIntersection

/-!
# Compatibility between Suppes 2000 and Moler-Suppes 1968

This module states compatibility conditions between:

* SuppesGeometry: midpoint/doubling geometry of Suppes (2000),
* SuppesPCG: constructive plane geometry of Moler-Suppes (1968).

These are not axioms of either source theory separately.
They express that both structures on the same type Point describe
the same underlying geometry.
-/

namespace Geometry
namespace Suppes

universe u

class SuppesPCGCompatibility
    (Point : Type u)
    [SuppesGeometry Point]
    [SuppesPCG Point] : Prop where

  /--
  The primitive collinearity relation of Suppes (2000)
  agrees with the collinearity relation defined from S
  in Moler-Suppes (1968).
  -/
  collinear_iff :
    ∀ A B C : Point,
      SuppesGeometry.Collinear A B C ↔
      PCGCollinear A B C

  /--
  The midpoint operation of Suppes (2000) agrees with
  the betweenness structure of Moler-Suppes (1968):
  the midpoint of AB lies between A and B.
  -/
  midpoint_between :
    ∀ A B : Point,
      PCGBetween
        A
        (SuppesGeometry.operation_midpoint A B)
        B

end Suppes
end Geometry

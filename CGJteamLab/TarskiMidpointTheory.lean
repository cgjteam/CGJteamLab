import CGJteamLab.TarskiInterface

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Tarski.Geo)

/-!
# Tarski Midpoint Theory

This module collects definitions and theorems concerning midpoints
in Tarski geometry.

At the present stage, the basic definition `TarskiIsMidpoint` and
the existing midpoint lemmas are imported from `TarskiInterface`.

The module will gradually become the independent theory of midpoints.
-/

/--
A midpoint lies on the segment determined by its endpoints.
-/
theorem tarski_midpoint_between
    (M A B : Geo.Point)
    (hM : TarskiIsMidpoint Geo M A B) :
    Geo.Between A M B :=
  hM.1

/--
The two halves determined by a midpoint are congruent.
-/
theorem tarski_midpoint_congruent
    (M A B : Geo.Point)
    (hM : TarskiIsMidpoint Geo M A B) :
    Geo.Congruent A M M B :=
  hM.2

end Tarski

end Geometry

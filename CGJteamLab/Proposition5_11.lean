import CGJteamLab.HilbertInterfaceV

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


------------------------------------------------------------------------
-- Euclid V.11
------------------------------------------------------------------------

/--
Euclid V.11: ratios equal to the same ratio are equal to one another.

For the Eudoxus interface this is transitivity of Def.5.
-/
theorem euclid_proposition_5_11
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d e f : HilbertPositiveSegmentClass Geo)
    (h1 : HilbertEudoxusProportion Geo a b c d)
    (h2 : HilbertEudoxusProportion Geo c d e f) :
    HilbertEudoxusProportion Geo a b e f := by

  exact
    hilbertEudoxusProportion_trans
      Geo a b c d e f h1 h2

end Geometry

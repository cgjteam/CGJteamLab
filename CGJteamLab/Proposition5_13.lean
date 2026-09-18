import CGJteamLab.HilbertInterfaceV

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


------------------------------------------------------------------------
-- Euclid V.13
------------------------------------------------------------------------

/--
Euclid V.13: equality of ratios transports a greater-ratio witness.
-/
theorem euclid_proposition_5_13
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d e f : HilbertPositiveSegmentClass Geo)
    (hProp :
      HilbertEudoxusProportion Geo a b c d)
    (hGreater :
      HilbertEudoxusGreaterRatio Geo c d e f) :
    HilbertEudoxusGreaterRatio Geo a b e f := by

  rcases hGreater with
    ⟨m, n, hCD, hNotEF⟩

  refine
    ⟨m, n, ?_, hNotEF⟩

  exact
    (hilbertEudoxusProportion_gt_iff
      Geo
      a b c d
      hProp
      m n).2
      hCD

end Geometry

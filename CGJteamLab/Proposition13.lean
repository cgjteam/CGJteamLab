import CGJteamLab.HilbertBookZero

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Hilbert/Book Zero form of Euclid I.13.

If a ray BA stands on the straight line CBD, then the two adjacent
angles CBA and ABD are supplementary.
-/
theorem euclid_proposition_13
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (C B D A : Geo.Point)
    (hCBD : Geo.Between C B D)
    (hBA : B ≠ A) :
    BookZeroSupplement Geo C B A A D := by

  constructor

  · exact
      hilbert_sameRay_refl
        Geo B A hBA.symm

  · exact hCBD

end Geometry

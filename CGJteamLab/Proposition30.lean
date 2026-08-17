import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable {Geo : Geometry.Geo.{u}}

theorem euclid_proposition_30
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hAB_EF : Geo.Parallel A B E F)
    (hCD_EF : Geo.Parallel C D E F)
    (hDistinct :
      Geo.PointLine A B ≠ Geo.PointLine C D) :
    Geo.Parallel A B C D := by

  exact
    hilbert_parallel_transitive_distinct
      Geo
      A B C D E F
      hAB_EF
      hCD_EF
      hDistinct

end Geometry

import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable {Geo : Geometry.Geo.{u}}

theorem euclid_proposition_31
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B P : Geo.Point)
    (hAB : A ≠ B)
    (hABP : ¬ Collinear Geo A B P) :
    ∃ Q : Geo.Point,
      P ≠ Q ∧
      Geo.Parallel A B P Q := by

  exact
    hilbert_parallel_through_point_exists
      Geo
      A B P
      hAB
      hABP

end Geometry

import CGJteamLab.HilbertBookZero

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition 2.

Given a point `A`, a ray `AE`, and a nondegenerate segment `BC`,
there exists a point `D` on ray `AE` such that `AD` is congruent
to `BC`.

In Euclid's original construction the result depends on Proposition I.1
and on several auxiliary constructions. Over the Hilbert foundation it
is an immediate consequence of Book Zero #49 (`bookZero_49_layoff`).
-/
theorem euclid_proposition_2
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A E B C : Geo.Point)
    (hAE : A ≠ E)
    (hBC : B ≠ C) :
    ∃ D : Geo.Point,
      HilbertSameRay Geo A E D ∧
      Geo.Congruent A D B C := by

  exact bookZero_49_layoff Geo A E B C hAE hBC

end Geometry
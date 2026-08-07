import CGJteamLab.HilbertInterface

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition I.4 (SAS).

If two triangles have two corresponding sides congruent and the
included angles congruent, then all corresponding sides and angles
are congruent.

In the Hilbert reconstruction this is a direct application of the
previously established Side-Angle-Side theorem.
-/
theorem euclid_proposition_4
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABC : ¬ Collinear Geo A B C)
    (hDEF : ¬ Collinear Geo D E F)
    (hAB : Geo.Congruent A B D E)
    (hAngle : Geo.AngleCongruent B A C E D F)
    (hAC : Geo.Congruent A C D F) :
    TriangleCongruenceResult Geo A B C D E F := by

  exact
    TriangleCongruentFromSAS
      Geo
      A B C
      D E F
      hABC
      hDEF
      hAB
      hAngle
      hAC

end Geometry

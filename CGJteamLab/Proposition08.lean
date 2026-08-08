import CGJteamLab.HilbertInterface

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition I.8.

If two triangles have their three corresponding sides congruent,
then their corresponding angles are congruent.
-/
theorem euclid_proposition_8
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABC : ¬ Collinear Geo A B C)
    (hAB : Geo.Congruent A B D E)
    (hBC : Geo.Congruent B C E F)
    (hAC : Geo.Congruent A C D F) :
    Geo.AngleCongruent B A C E D F ∧
    Geo.AngleCongruent A B C D E F ∧
    Geo.AngleCongruent A C B D F E := by

  have hSSS :=
    HilbertSSS
      Geo
      A B C
      D E F
      hABC
      hAB
      hBC
      hAC

  exact
    ⟨hSSS.2.angleA,
      hSSS.2.angleB,
      hSSS.2.angleC⟩

end Geometry

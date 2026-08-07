import CGJteamLab.HilbertBookZero

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition 3.

Given two segments `AB` and `CD`, with `CD < AB`,
there exists a point `E` between `A` and `B` such that
`AE` is congruent to `CD`.

Over the present Hilbert/Book Zero layer this is exactly
the existential content of `HilbertSegmentLess`.
-/
theorem euclid_proposition_3
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hCDAB : HilbertSegmentLess Geo C D A B) :
    ∃ E : Geo.Point,
      Geo.Between A E B ∧
      Geo.Congruent A E C D := by

  rcases hCDAB with ⟨E, hAEB, hCDAE⟩

  exact ⟨E, hAEB,
    hilbert_congruent_symmetry Geo C D A E hCDAE⟩

end Geometry
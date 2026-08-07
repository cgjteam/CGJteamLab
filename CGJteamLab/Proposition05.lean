import CGJteamLab.HilbertInterface

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition I.5.

In an isosceles triangle the base angles are congruent.
Moreover, if the equal sides are produced, the angles below
the base are also congruent.
-/
theorem euclid_proposition_5
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E : Geo.Point)
    (hABC : ¬ Collinear Geo A B C)
    (hABAC : Geo.Congruent A B A C)
    (hABD : Geo.Between A B D)
    (hACE : Geo.Between A C E) :
    Geo.AngleCongruent A B C A C B ∧
    Geo.AngleCongruent C B D B C E := by

  have hBase :
      Geo.AngleCongruent A B C A C B :=
    hilbert_isosceles_base_angles
      Geo A B C hABC hABAC

  have hACB : ¬ Collinear Geo A C B := by
    intro h
    exact hABC (PrimCollinearRotate Geo A C B h)

  have hExterior :
      Geo.AngleCongruent C B D B C E :=
    hilbert_adjacent_angles_congruent
      Geo
      A B C D
      A C B E
      hABD
      hACE
      hABC
      hACB
      hBase

  exact ⟨hBase, hExterior⟩

end Geometry

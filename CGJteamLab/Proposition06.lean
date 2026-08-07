import CGJteamLab.HilbertInterface

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition I.6.

If two angles of a nondegenerate triangle are congruent,
then the sides opposite those angles are congruent.
-/
theorem euclid_proposition_6
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ Collinear Geo A B C)
    (hAngles : Geo.AngleCongruent A B C A C B) :
    Geo.Congruent A B A C := by

  have hBCA : ¬ Collinear Geo B C A := by
    intro h
    exact hABC
      (PrimCollinearCycle Geo C A B
        (PrimCollinearCycle Geo B C A h))

  have hCBA : ¬ Collinear Geo C B A := by
    intro h
    exact hABC
      (PrimCollinearSymm Geo C B A h)

  have hBC :
      Geo.Congruent B C C B := by
    exact
      (Geo.congruent_reverse_second
        B C B C).mp
        (hilbert_congruent_reflexive Geo B C)

  have hAngleB :
      Geo.AngleCongruent C B A B C A := by
    exact
      (Geo.angle_congruent_reverse_second
        C B A A C B).mp
        ((Geo.angle_congruent_reverse_first
          A B C A C B).mp hAngles)

  have hAngleC :
      Geo.AngleCongruent B C A C B A := by
    exact
      Geometry.Geo.angle_congruent_symmetry
        Geo
        C B A
        B C A
        hAngleB

  have hASA :=
    hilbert_asa_sides
      Geo
      B C A
      C B A
      hBCA
      hCBA
      hBC
      hAngleB
      hAngleC

  exact
    (Geo.congruent_reverse_second
      A B C A).mp
      ((Geo.congruent_reverse_first
        B A C A).mp hASA.1)

end Geometry

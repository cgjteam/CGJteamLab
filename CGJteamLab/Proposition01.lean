import CGJteamLab.HilbertBookZero

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Temporary existence principle for Euclid Book I, Proposition 1.

For every nondegenerate segment `AB` there exists a point `C`
equidistant from both endpoints:

* `AC ≅ AB`
* `BC ≅ AB`

This axiom provides only the existence of such a point.
The proof that `A`, `B` and `C` are not collinear is a theorem
of Book Zero and is proved in `euclid_proposition_1`.

The axiom is introduced only to unblock the reconstruction of
Euclid Book I. It is intended to be replaced by a theorem after
developing the Hilbert continuity layer (for example via a
circle-intersection theorem derived from an appropriate
continuity principle).
-/
axiom hilbert_equidistant_point_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ C : Geo.Point,
      Geo.Congruent A C A B ∧
      Geo.Congruent B C A B


theorem euclid_proposition_1
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : A ≠ B) :
    ∃ C : Geo.Point,
      ¬ PrimCollinear Geo A B C ∧
      Geo.Congruent A C A B ∧
      Geo.Congruent B C A B := by

  obtain ⟨C, hAC, hBC⟩ :=
    hilbert_equidistant_point_exists Geo A B hAB

  have hACne : A ≠ C := by
    intro hEq
    subst C

    have hABAA : Geo.Congruent A B A A :=
      hilbert_congruent_symmetry
        Geo A A A B hAC

    exact
      hAB
        (bookZero_nullSegment1
          Geo A B A hABAA)

  have hBCne : B ≠ C := by
    intro hEq
    subst C

    have hABBB : Geo.Congruent A B B B :=
      hilbert_congruent_symmetry
        Geo B B A B hBC

    exact
      hAB
        (bookZero_nullSegment1
          Geo A B B hABBB)

  refine ⟨C, ?_, hAC, hBC⟩

  intro hCol

  rcases
      hilbert_between_trichotomy
        Geo
        A B C
        hAB
        hBCne
        hACne
        hCol with
    hABC | hBAC | hACB

  ·
    have hNot : ¬ Geo.Congruent A B A C :=
      bookZero_45_partNotEqualWhole
        Geo A B C hABC

    exact
      hNot
        (hilbert_congruent_symmetry
          Geo A C A B hAC)

  ·
    have hNot : ¬ Geo.Congruent B A B C :=
      bookZero_45_partNotEqualWhole
        Geo B A C hBAC

    have hBAAB : Geo.Congruent B A A B :=
      (bookZero_congruenceFlip
        Geo A B A B
        (hilbert_congruent_reflexive Geo A B)).2.1

    have hABBC : Geo.Congruent A B B C :=
      hilbert_congruent_symmetry
        Geo B C A B hBC

    have hBABC : Geo.Congruent B A B C :=
      hilbert_congruent_transitivity
        Geo B A A B B C
        hBAAB hABBC

    exact hNot hBABC

  ·
    have hNot : ¬ Geo.Congruent A C A B :=
      bookZero_45_partNotEqualWhole
        Geo A C B hACB

    exact hNot hAC

end Geometry

import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)


------------------------------------------------------------------------
-- Book Zero: Logical preliminaries
------------------------------------------------------------------------

/-
Book Zero 1: equalitysymmetric

BNW statement:
  B = A -> A = B

This is ordinary symmetry of equality and does not depend on any
geometric axiom.
-/

theorem bookZero_equalitySymmetric
    (A B : Geo.Point)
    (h : B = A) :
    A = B := by
  exact h.symm


/-
Book Zero 2: inequalitysymmetric

BNW statement:
  A ≠ B -> B ≠ A

This is ordinary symmetry of inequality and does not depend on any
geometric axiom.
-/

theorem bookZero_inequalitySymmetric
    (A B : Geo.Point)
    (h : A ≠ B) :
    B ≠ A := by
  intro hBA
  exact h hBA.symm

/--
Book Zero 3: congruencesymmetric

Symmetry of segment congruence. In the Hilbert development this is
already derived from the congruence axioms.
-/
theorem bookZero_congruenceSymmetric
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent C D A B := by
  exact CongruentSymmetry Geo A B C D h

/--
Book Zero 4: congruencetransitive
-/
theorem bookZero_congruenceTransitive
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (h1 : Geo.Congruent A B C D)
    (h2 : Geo.Congruent C D E F) :
    Geo.Congruent A B E F := by
  exact hilbert_congruent_transitivity Geo A B C D E F h1 h2

/--
Book Zero 6: 3.6a

If B lies between A and C, and C lies between A and D,
then C lies between B and D.

This is the first conclusion of Hilbert's inner transitivity theorem.
-/
theorem bookZero_3_6a
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hACD : Geo.Between A C D) :
    Geo.Between B C D := by
  exact
    (hilbert_between_inner_trans
      Geo A B C D hABC hACD).1

/--
Book Zero 7: betweennotequal

If B lies between A and C, then A and B are distinct.

This is a direct component of Hilbert's order axiom II.1.
-/
theorem bookZero_betweenNotEqual
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    A ≠ B := by
  exact (HilbertOrder.between_incidence A B C hABC).1

/--
Book Zero 8: extensionunique

If B lies between A and E and between A and F, and BE is congruent
to BF, then E = F.

The two betweenness assumptions place E and F on the same ray AB.
Hilbert III.3 first gives AE congruent to AF, and uniqueness of segment
construction on that ray then gives E = F.
-/
theorem bookZero_extensionUnique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B E F : Geo.Point)
    (hABE : Geo.Between A B E)
    (hABF : Geo.Between A B F)
    (hBEBF : Geo.Congruent B E B F) :
    E = F := by
  have hABAB : Geo.Congruent A B A B :=
    hilbert_congruent_reflexive Geo A B

  have hAEAF : Geo.Congruent A E A F :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A B E
      A B F
      hABE
      hABF
      hABAB
      hBEBF

  have hRayE : HilbertSameRay Geo A B E :=
    hilbert_sameRay_of_between Geo A B E hABE

  have hRayF : HilbertSameRay Geo A B F :=
    hilbert_sameRay_of_between Geo A B F hABF

  exact
    hilbert_segment_construction_unique
      Geo
      A E
      A B
      E F
      hRayE
      hRayF
      (hilbert_congruent_reflexive Geo A E)
      (hilbert_congruent_symmetry Geo A E A F hAEAF)

/--
Book Zero 9: 3.7a

If B lies between A and C, and C lies between B and D,
then C lies between A and D.

This is the first conclusion of Hilbert's Theorem 5,
already represented by `hilbert_between_outer_trans`.
-/
theorem bookZero_3_7a
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hBCD : Geo.Between B C D) :
    Geo.Between A C D := by
  exact
    (hilbert_between_outer_trans
      Geo A B C D hABC hBCD).1


/--
Book Zero 10: 3.5b

If B lies between A and D, and C lies between B and D,
then C lies between A and D.

This follows from Hilbert's two transitivity principles for betweenness.
-/
theorem bookZero_3_5b
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABD : Geo.Between A B D)
    (hBCD : Geo.Between B C D) :
    Geo.Between A C D := by
  have hDCB : Geo.Between D C B :=
    (HilbertOrder.between_incidence B C D hBCD).2.2.2.2

  have hDBA : Geo.Between D B A :=
    (HilbertOrder.between_incidence A B D hABD).2.2.2.2

  have hCBA : Geo.Between C B A :=
    (hilbert_between_inner_trans
      Geo D C B A hDCB hDBA).1

  have hABC : Geo.Between A B C :=
    (HilbertOrder.between_incidence C B A hCBA).2.2.2.2

  exact
    (hilbert_between_outer_trans
      Geo A B C D hABC hBCD).1

/--
Book Zero 11: 3.6b

If B lies between A and C, and C lies between A and D,
then B lies between A and D.

Together with Book Zero 6 (3.6a), this is exactly the second conclusion
of Hilbert's inner transitivity theorem.
-/
theorem bookZero_3_6b
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hACD : Geo.Between A C D) :
    Geo.Between A B D := by
  exact
    (hilbert_between_inner_trans
      Geo A B C D hABC hACD).2

/--
Book Zero 12: 3.7b

If B lies between A and C, and C lies between B and D,
then B lies between A and D.

Together with Book Zero 9 (3.7a), this is exactly the second conclusion
of Hilbert's outer transitivity theorem.
-/
theorem bookZero_3_7b
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hBCD : Geo.Between B C D) :
    Geo.Between A B D := by
  exact
    (hilbert_between_outer_trans
      Geo A B C D hABC hBCD).2

/--
Book Zero 13: doublereverse

From AB congruent CD we obtain both:
  DC congruent BA,
  BA congruent DC.

In the Hilbert implementation endpoint reversal is definitional,
because segments are represented as unordered pairs.
-/
theorem bookZero_doubleReverse
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent D C B A ∧
    Geo.Congruent B A D C := by
  have hBADC : Geo.Congruent B A D C :=
    CongruentReverseBoth Geo A B C D h

  have hDCBA : Geo.Congruent D C B A :=
    CongruentSymmetry Geo B A D C hBADC

  exact ⟨hDCBA, hBADC⟩

/--
Book Zero 14: congruenceflip

From AB congruent CD we obtain all endpoint-reversal variants:
  BA congruent DC,
  BA congruent CD,
  AB congruent DC.

In the Hilbert implementation these are representational consequences
of treating a segment as an unordered pair of endpoints.
-/
theorem bookZero_congruenceFlip
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent B A D C ∧
    Geo.Congruent B A C D ∧
    Geo.Congruent A B D C := by
  constructor
  · exact CongruentReverseBoth Geo A B C D h
  · constructor
    · exact CongruentReverseFirst Geo A B C D h
    · exact CongruentSwapSecond Geo A B C D h


end Geometry

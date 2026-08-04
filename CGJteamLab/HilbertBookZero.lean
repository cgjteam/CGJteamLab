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
BNW auxiliary axiom: nullsegment1

A segment congruent to a null segment is itself null.

This principle is not included explicitly in the historical Hilbert
axioms used by the project. It is added locally in Book Zero because
the BNW language permits degenerate segments.
-/
axiom bookZero_nullSegment1
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (h : Geo.Congruent A B C C) :
    A = B


/--
Book Zero 5: nullsegment3

A non-null segment cannot be congruent to a null segment.

BNW proof:
  NE A B
  EE A B C D
  EQ C D
  EE A B C C
  EQ A B
  contradiction
-/
theorem bookZero_nullSegment3
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hAB : A ≠ B)
    (hCong : Geo.Congruent A B C D) :
    C ≠ D := by
  intro hCD

  have hNull : Geo.Congruent A B C C := by
    simpa [hCD] using hCong

  have hEq : A = B :=
    bookZero_nullSegment1 Geo A B C hNull

  exact hAB hEq

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


/--
Book Zero 15: sumofparts

If B lies between A and C, b lies between a and c,
AB is congruent to ab, and BC is congruent to bc,
then AC is congruent to ac.

This is exactly Hilbert's congruence axiom III.3:
additivity of adjacent congruent segments.
-/
theorem bookZero_sumOfParts
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABab : Geo.Congruent A B a b)
    (hBCbc : Geo.Congruent B C b c)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c) :
    Geo.Congruent A C a c := by
  exact
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A B C
      a b c
      hABC
      habc
      hABab
      hBCbc

------------------------------------------------------------------------
-- Hilbert working layer: subtraction of congruent segment parts
------------------------------------------------------------------------

/--
Hilbert segment subtraction.

If B lies between A and C, b lies between a and c,
AB is congruent to ab, and AC is congruent to ac,
then BC is congruent to bc.

This is the cancellation counterpart of Hilbert III.3.
-/
theorem hilbert_segment_subtraction
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c) :
    Geo.Congruent B C b c := by

  have hbc : b ≠ c :=
    (HilbertOrder.between_incidence a b c habc).2.1

  obtain ⟨X, hRayX, hBXBC⟩ :=
    HilbertCongruence.segment_construction
      (Geo := Geo)
      B C b c hbc

  have hSymmBetween :
      ∀ P Q R : Geo.Point,
        Geo.Between P Q R →
        Geo.Between R Q P :=
    fun P Q R h =>
      (HilbertOrder.between_incidence P Q R h).2.2.2.2

  have habX : Geo.Between a b X := by
    rcases hilbert_sameRay_cases Geo b c X hRayX with
      hXc | hbcX | hbXc

    · subst X
      exact habc

    · exact
        (hilbert_between_outer_trans
          Geo a b c X habc hbcX).2

    · have hcXb : Geo.Between c X b :=
        hSymmBetween b X c hbXc

      have hcbA : Geo.Between c b a :=
        hSymmBetween a b c habc

      have hXba : Geo.Between X b a :=
        (hilbert_between_inner_trans
          Geo c X b a hcXb hcbA).1

      exact hSymmBetween X b a hXba

  have hBCbX : Geo.Congruent B C b X :=
    hilbert_congruent_symmetry Geo b X B C hBXBC

  have hACaX : Geo.Congruent A C a X :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A B C
      a b X
      hABC
      habX
      hABab
      hBCbX

  have hRayAX : HilbertSameRay Geo a b X :=
    hilbert_sameRay_of_between Geo a b X habX

  have hRayAC : HilbertSameRay Geo a b c :=
    hilbert_sameRay_of_between Geo a b c habc

  have haXAC : Geo.Congruent a X A C :=
    hilbert_congruent_symmetry Geo A C a X hACaX

  have hacAC : Geo.Congruent a c A C :=
    hilbert_congruent_symmetry Geo A C a c hACac

  have hXc : X = c :=
    hilbert_segment_construction_unique
      Geo
      A C
      a b
      X c
      hRayAX
      hRayAC
      haXAC
      hacAC

  subst X

  exact
    hilbert_congruent_symmetry Geo b c B C hBXBC

/--
Book Zero 16: differenceofparts

If corresponding whole segments and their initial parts are congruent,
then the remaining parts are congruent.

This is an immediate instance of Hilbert segment subtraction.
-/
theorem bookZero_differenceOfParts
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c) :
    Geo.Congruent B C b c := by
  exact
    hilbert_segment_subtraction
      Geo A B C a b c
      hABC habc hABab hACac


/--
Hilbert Theorem 11.

If AB is congruent to AC in a noncollinear triangle ABC,
then the base angles at B and C are congruent.
-/
theorem hilbert_isosceles_base_angles
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hNC : ¬ Collinear Geo A B C)
    (hABAC : Geo.Congruent A B A C) :
    Geo.AngleCongruent A B C A C B := by

  have hNC' : ¬ Collinear Geo A C B := by
    intro hACB
    exact hNC (PrimCollinearRotate Geo A C B hACB)

  have hBAC : ¬ PrimCollinear Geo B A C := by
    intro hBAC
    apply hNC
    exact PrimCollinearSwap Geo B A C hBAC

  have hAngleA :
      Geo.AngleCongruent B A C C A B := by
    have hRefl :
        Geo.AngleCongruent B A C B A C :=
      HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo) B A C hBAC

    exact
      (Geo.angle_congruent_reverse_second
        B A C B A C).mp hRefl

  have hACAB : Geo.Congruent A C A B :=
    hilbert_congruent_symmetry Geo A B A C hABAC

  have hTriangles :=
    SAS
      Geo
      A B C
      A C B
      hNC
      hNC'
      hABAC
      hAngleA
      hACAB

  exact hTriangles.angleB

/--
If A-B-D and C is not on line AD, then A and B lie on the same
side of line CD.

This is a pure incidence/order fact.
-/
theorem hilbert_between_points_sameSide_transversal
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D : Geo.Point)
    (hABD : Geo.Between A B D)
    (hNC : ¬ PrimCollinear Geo A D C) :
    ∃ l : Geo.Line,
      HilbertIncidence.OnLine C l ∧
      HilbertIncidence.OnLine D l ∧
      HilbertSameSide Geo A B l := by

  have hAD : A ≠ D :=
    (HilbertOrder.between_incidence A B D hABD).2.2.1

  have hCD : C ≠ D := by
    intro hCD
    subst C
    apply hNC
    rcases HilbertPlaneIncidence.line_through A D hAD with
      ⟨l, hAl, hDl⟩
    exact PrimCollinear.mk (Geo := Geo) hAl hDl hDl

  rcases HilbertPlaneIncidence.line_through A D hAD with
    ⟨base, hAbase, hDbase⟩

  rcases HilbertPlaneIncidence.line_through C D hCD with
    ⟨cross, hCcross, hDcross⟩

  have hBbase : HilbertIncidence.OnLine B base :=
    hilbert_between_on_line
      Geo A B D base hAbase hDbase hABD

  have hLines : base ≠ cross := by
    intro hEq
    subst cross
    apply hNC
    exact PrimCollinear.mk (Geo := Geo) hAbase hDbase hCcross

  have hAnotcross : ¬ HilbertIncidence.OnLine A cross := by
    intro hAcross

    have hEq : base = cross :=
      HilbertPlaneIncidence.line_unique
        A D hAD
        base cross
        hAbase hDbase
        hAcross hDcross

    exact hLines hEq

  have hBD : B ≠ D :=
    (HilbertOrder.between_incidence A B D hABD).2.1

  have hBnotcross : ¬ HilbertIncidence.OnLine B cross := by
    intro hBcross

    have hEq : base = cross :=
      HilbertPlaneIncidence.line_unique
        B D hBD
        base cross
        hBbase hDbase
        hBcross hDcross

    exact hLines hEq

  have hABDcol : PrimCollinear Geo A B D :=
    (HilbertOrder.between_incidence A B D hABD).2.2.2.1

  have hNotBetween : ¬ Geo.Between A D B :=
    (HilbertOrder.between_unique A B D hABDcol hABD).2

  have hNoMeet : ¬ HilbertSegmentMeetsLine Geo A B cross :=
    hilbert_segment_not_meets_crossing_line
      Geo
      A B D
      base cross
      hLines
      hAbase
      hBbase
      hDbase
      hDcross
      hNotBetween

  have hSame : HilbertSameSide Geo A B cross := by
    exact
      ⟨hAnotcross,
       hBnotcross,
       Relation.ReflTransGen.single
         ⟨hAnotcross, hBnotcross, hNoMeet⟩⟩

  exact ⟨cross, hCcross, hDcross, hSame⟩

/--
If a-b-d, ad is congruent to ac, and bd is congruent to bc,
then a, b, c are collinear.

The proof uses Hilbert's Theorem 11 twice and the uniqueness clause
of angle construction III.4.
-/
theorem hilbert_two_centers_equal_distances_collinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : Geo.Point)
    (habd : Geo.Between a b d)
    (hadac : Geo.Congruent a d a c)
    (hbdbc : Geo.Congruent b d b c) :
    Collinear Geo a b c := by

  by_contra habc

  have habdCol : PrimCollinear Geo a b d :=
    (HilbertOrder.between_incidence a b d habd).2.2.2.1

  have hab : a ≠ b :=
    (HilbertOrder.between_incidence a b d habd).1

  have hbd : b ≠ d :=
    (HilbertOrder.between_incidence a b d habd).2.1

  have had : a ≠ d :=
    (HilbertOrder.between_incidence a b d habd).2.2.1

  have hADC : ¬ Collinear Geo a d c := by
    intro hADC

    have hBAD : PrimCollinear Geo b a d :=
      PrimCollinearSwap Geo a b d habdCol

    have hBAC : PrimCollinear Geo b a c :=
      hilbert_primCollinear_trans
        Geo b a d c had
        hBAD
        hADC

    exact habc (PrimCollinearSwap Geo b a c hBAC)

  have hBDC : ¬ Collinear Geo b d c := by
    intro hBDC

    have hABC : PrimCollinear Geo a b c :=
      hilbert_primCollinear_trans
        Geo a b d c hbd
        habdCol
        hBDC

    exact habc hABC

  have hIsoA :
      Geo.AngleCongruent a d c a c d :=
    hilbert_isosceles_base_angles
      Geo a d c hADC hadac

  have hIsoB :
      Geo.AngleCongruent b d c b c d :=
    hilbert_isosceles_base_angles
      Geo b d c hBDC hbdbc

  have hdba : Geo.Between d b a :=
    (HilbertOrder.between_incidence a b d habd).2.2.2.2

  have hRayDBA : HilbertSameRay Geo d b a :=
    hilbert_sameRay_of_between Geo d b a hdba

  have hBDC_ACD :
      Geo.AngleCongruent b d c a c d := by
    unfold Geometry.Geo.AngleCongruent at hIsoA ⊢
    rw [hilbert_angle_eq_of_sameRay_first
      Geo d b a c hRayDBA]
    exact hIsoA

  have hACD_BCD :
      Geo.AngleCongruent a c d b c d :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      a c d
      b d c
      b c d
      (Geometry.Geo.angle_congruent_symmetry
        Geo b d c a c d hBDC_ACD)
      hIsoB

  have hDCA_DCB :
      Geo.AngleCongruent d c a d c b :=
    (Geo.angle_congruent_reverse_second
      d c a b c d).mp
      ((Geo.angle_congruent_reverse_first
        a c d b c d).mp hACD_BCD)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo a b c d habd hADC with
    ⟨l, hCl, hDl, hSameAB⟩

  have hdc : d ≠ c := by
    intro hdc
    subst d
    apply hADC
    rcases HilbertPlaneIncidence.line_through a c had with
      ⟨m, ham, hcm⟩
    exact PrimCollinear.mk
      (Geo := Geo) ham hcm hcm

  have hDCA : ¬ PrimCollinear Geo d c a := by
    intro hDCA'
    apply hADC
    exact
      PrimCollinearRotate Geo a c d
        (PrimCollinearSymm Geo d c a hDCA')

  rcases HilbertCongruence.angle_construction
      (Geo := Geo)
      d c a
      d c b
      hDCA
      hdc
      l
      hDl
      hCl
      hSameAB.2.1 with
    ⟨x, hSameXB, hAngleX, hUnique⟩

  have hSameAA : HilbertSameSide Geo a a l :=
    hilbert_sameSide_refl
      Geo a l hSameAB.1

  have hRayXA : HilbertSameRay Geo c x a :=
    hUnique
      a
      hSameAB
      (HilbertCongruence.angle_congruence_reflexive
        (Geo := Geo) d c a hDCA)

  have hSameBB : HilbertSameSide Geo b b l :=
    hilbert_sameSide_refl
      Geo b l hSameAB.2.1

  have hRayXB : HilbertSameRay Geo c x b :=
    hUnique b hSameBB hDCA_DCB

  have hCXA : PrimCollinear Geo c x a :=
    hilbert_sameRay_collinear Geo c x a hRayXA

  have hCXB : PrimCollinear Geo c x b :=
    hilbert_sameRay_collinear Geo c x b hRayXB

  have hACX : PrimCollinear Geo a c x :=
    PrimCollinearRotate Geo a x c
      (PrimCollinearSymm Geo c x a hCXA)

  have hACB : PrimCollinear Geo a c b :=
    hilbert_primCollinear_trans
      Geo a c x b
      hRayXA.1.symm
      hACX
      hCXB

  exact habc (PrimCollinearRotate Geo a c b hACB)


/--
If A-B-C, the three corresponding segments of the triples
(A,B,C) and (a,b,c) are congruent, and a != b, then a,b,c
are collinear.

The explicit nondegeneracy assumption `a != b` belongs to the
Hilbert formulation: segment construction is performed on a genuine
ray. The BNW formulation derives it using its null-segment theory.
-/
theorem hilbert_congruent_triple_collinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (hab : a ≠ b)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hBCbc : Geo.Congruent B C b c) :
    Collinear Geo a b c := by

  -- Choose a reference point R beyond b on the line ab.
  rcases HilbertOrder.between_extension a b hab with
    ⟨R, habR⟩

  have hbR : b ≠ R :=
    (HilbertOrder.between_incidence a b R habR).2.1

  -- Lay off a copy of BC from b on the ray bR.
  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      B C
      b R
      hbR with
    ⟨d, hRayd, hbdBC⟩

  -- The point a is the reference point on the opposite ray from b.
  have hRayA : HilbertSameRay Geo b a a :=
    hilbert_sameRay_refl Geo b a hab

  -- Transport the order a-b-R to the constructed point d.
  have habd : Geo.Between a b d :=
    hilbert_between_transport_sameRays
      Geo
      a b R
      a d
      habR
      hRayA
      hRayd

  -- Reverse the second congruence so that III.3 has the right orientation.
  have hBCbd : Geo.Congruent B C b d :=
    hilbert_congruent_symmetry
      Geo b d B C hbdBC

  -- Hilbert III.3: AB + BC = AC and ab + bd = ad.
  have hACad : Geo.Congruent A C a d :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A B C
      a b d
      hABC
      habd
      hABab
      hBCbd

  -- Hence ad is congruent to ac.
  have hadAC : Geo.Congruent a d A C :=
    hilbert_congruent_symmetry
      Geo A C a d hACad

  have hadac : Geo.Congruent a d a c :=
    hilbert_congruent_transitivity
      Geo
      a d
      A C
      a c
      hadAC
      hACac

  -- We also have bd congruent to bc.
  have hbdbc : Geo.Congruent b d b c :=
    hilbert_congruent_transitivity
      Geo
      b d
      B C
      b c
      hbdBC
      hBCbc

  exact
    hilbert_two_centers_equal_distances_collinear
      Geo
      a b c d
      habd
      hadac
      hbdbc


/--
A proper part of a segment is not congruent to the whole segment.

If B lies between A and C, then AB is not congruent to AC.
-/
theorem hilbert_part_not_congruent_whole
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    ¬ Geo.Congruent A B A C := by
  intro hABAC

  have hAB : A ≠ B :=
    (HilbertOrder.between_incidence A B C hABC).1

  have hRayB : HilbertSameRay Geo A B B :=
    hilbert_sameRay_refl Geo A B hAB.symm

  have hRayC : HilbertSameRay Geo A B C :=
    hilbert_sameRay_of_between Geo A B C hABC

  have hACAB : Geo.Congruent A C A B :=
    hilbert_congruent_symmetry Geo A B A C hABAC

  have hBC : B = C :=
    hilbert_segment_construction_unique
      Geo
      A B
      A B
      B C
      hRayB
      hRayC
      (hilbert_congruent_reflexive Geo A B)
      hACAB

  have hBneC : B ≠ C :=
    (HilbertOrder.between_incidence A B C hABC).2.1

  exact hBneC hBC


------------------------------------------------------------------------
-- Order of segments
------------------------------------------------------------------------

/--
Hilbert's strict comparison of segments.

`HilbertSegmentLess Geo A B C D` means that the segment AB is
congruent to a proper initial part CP of the segment CD.
-/
def HilbertSegmentLess
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point) : Prop :=
  ∃ P : Geo.Point,
    Geo.Between C P D ∧
    Geo.Congruent A B C P

/--
Hilbert segment order is preserved under congruence of the
smaller segment.

Hilbert Theorem 24, left transport.
-/
theorem hilbert_segmentLess_congruent_left
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B A' B' C D : Geo.Point)
    (hLess : HilbertSegmentLess Geo A B C D)
    (hCong : Geo.Congruent A' B' A B) :
    HilbertSegmentLess Geo A' B' C D := by

  rcases hLess with ⟨P, hCPD, hABCP⟩

  have hA'B'CP : Geo.Congruent A' B' C P :=
    hilbert_congruent_transitivity
      Geo
      A' B'
      A B
      C P
      hCong
      hABCP

  exact ⟨P, hCPD, hA'B'CP⟩

/--
A segment strictly smaller than another segment cannot be congruent
to it.

This follows directly from Hilbert's definition of segment order and
the fact that a proper part is not congruent to the whole segment.
-/
theorem hilbert_segmentLess_not_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hLess : HilbertSegmentLess Geo A B C D) :
    ¬ Geo.Congruent A B C D := by

  intro hABCD

  rcases hLess with ⟨P, hCPD, hABCP⟩

  have hCPAB : Geo.Congruent C P A B :=
    hilbert_congruent_symmetry
      Geo A B C P hABCP

  have hCPCD : Geo.Congruent C P C D :=
    hilbert_congruent_transitivity
      Geo
      C P
      A B
      C D
      hCPAB
      hABCD

  exact
    hilbert_part_not_congruent_whole
      Geo C P D hCPD hCPCD
/--
A proper initial part of a segment is strictly smaller than
the whole segment.

If C-P-D, then CP < CD.
-/
theorem hilbert_segmentLess_of_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (C P D : Geo.Point)
    (hCPD : Geo.Between C P D) :
    HilbertSegmentLess Geo C P C D := by

  exact
    ⟨P,
     hCPD,
     hilbert_congruent_reflexive Geo C P⟩

/--
Hilbert Theorem 25(I): asymmetry of strict segment comparison.

If AB < CD, then CD is not smaller than AB.

The proof uses only segment additivity, construction on a ray,
the order calculus, and uniqueness of segment construction.
-/
theorem hilbert_segmentLess_asymm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABCD : HilbertSegmentLess Geo A B C D) :
    ¬ HilbertSegmentLess Geo C D A B := by

  intro hCDAB

  rcases hABCD with ⟨P, hCPD, hABCP⟩
  rcases hCDAB with ⟨Q, hAQB, hCDAQ⟩

  have hAB : A ≠ B :=
    (HilbertOrder.between_incidence A Q B hAQB).2.2.1

  -- Choose a point S beyond B on line AB.
  rcases HilbertOrder.between_extension A B hAB with
    ⟨S, hABS⟩

  have hBS : B ≠ S :=
    (HilbertOrder.between_incidence A B S hABS).2.1

  -- On ray BS lay off a copy of PD.
  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      P D
      B S
      hBS with
    ⟨R, hRayR, hBRPD⟩

  have hRayA : HilbertSameRay Geo B A A :=
    hilbert_sameRay_refl Geo B A hAB

  -- Since R lies on ray BS and A-B-S, we have A-B-R.
  have hABR : Geo.Between A B R :=
    hilbert_between_transport_sameRays
      Geo
      A B S
      A R
      hABS
      hRayA
      hRayR

  have hCPAB : Geo.Congruent C P A B :=
    hilbert_congruent_symmetry
      Geo A B C P hABCP

  have hPDBR : Geo.Congruent P D B R :=
    hilbert_congruent_symmetry
      Geo B R P D hBRPD

  -- CD = CP + PD and AR = AB + BR.
  have hCDAR : Geo.Congruent C D A R :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      C P D
      A B R
      hCPD
      hABR
      hCPAB
      hPDBR

  have hARCD : Geo.Congruent A R C D :=
    hilbert_congruent_symmetry
      Geo C D A R hCDAR

  have hAQCD : Geo.Congruent A Q C D :=
    hilbert_congruent_symmetry
      Geo C D A Q hCDAQ

  have hRayQ0 : HilbertSameRay Geo A Q B :=
    hilbert_sameRay_of_between Geo A Q B hAQB

  have hRayQ : HilbertSameRay Geo A B Q :=
    hilbert_sameRay_symm Geo A Q B hRayQ0

  have hRayR' : HilbertSameRay Geo A B R :=
    hilbert_sameRay_of_between Geo A B R hABR

  -- R and Q lie on the same ray from A and determine segments
  -- congruent to the same segment CD.
  have hRQ : R = Q :=
    hilbert_segment_construction_unique
      Geo
      C D
      A B
      R Q
      hRayR'
      hRayQ
      hARCD
      hAQCD

  subst R

  have hAQBcol : PrimCollinear Geo A Q B :=
    (HilbertOrder.between_incidence A Q B hAQB).2.2.2.1

  have hNotABQ : ¬ Geo.Between A B Q :=
    (HilbertOrder.between_unique
      A Q B hAQBcol hAQB).2

  exact hNotABQ hABR

/--
Collinear part of the three-point case of Hilbert's Theorem 27.

If A-B-C, the triples (A,B,C) and (a,b,c) have congruent
corresponding segments, and a,b,c are distinct and collinear,
then a-b-c.
-/
theorem hilbert_congruent_collinear_triple_preserves_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Collinear Geo a b c)
    (hab : a ≠ b)
    (hbc : b ≠ c)
    (hac : a ≠ c)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hBCbc : Geo.Congruent B C b c) :
    Geo.Between a b c := by

  rcases
      hilbert_between_trichotomy
        Geo a b c hab hbc hac habc with
    habcOrder | hbacOrder | hacbOrder

  · exact habcOrder

  · -- Case b-a-c.
    --
    -- Reversal gives c-a-b, hence ca < cb.
    -- Reversal of A-B-C gives C-B-A, hence CB < CA.
    --
    -- By congruence transport:
    --   CA < cb
    --   cb < CA
    --
    -- contradicting asymmetry.

    exfalso

    have hcabOrder : Geo.Between c a b :=
      (HilbertOrder.between_incidence
        b a c hbacOrder).2.2.2.2

    have hcaltcb :
        HilbertSegmentLess Geo c a c b :=
      hilbert_segmentLess_of_between
        Geo c a b hcabOrder

    have hCAca : Geo.Congruent C A c a :=
      CongruentReverseBoth Geo A C a c hACac

    have hCAltcb :
        HilbertSegmentLess Geo C A c b :=
      hilbert_segmentLess_congruent_left
        Geo
        c a
        C A
        c b
        hcaltcb
        hCAca

    have hCBA : Geo.Between C B A :=
      (HilbertOrder.between_incidence
        A B C hABC).2.2.2.2

    have hCBltCA :
        HilbertSegmentLess Geo C B C A :=
      hilbert_segmentLess_of_between
        Geo C B A hCBA

    have hCBcb : Geo.Congruent C B c b :=
      CongruentReverseBoth Geo B C b c hBCbc

    have hcbCB : Geo.Congruent c b C B :=
      hilbert_congruent_symmetry
        Geo C B c b hCBcb

    have hcbltCA :
        HilbertSegmentLess Geo c b C A :=
      hilbert_segmentLess_congruent_left
        Geo
        C B
        c b
        C A
        hCBltCA
        hcbCB

    exact
      (hilbert_segmentLess_asymm
        Geo C A c b hCAltcb)
        hcbltCA

  · -- Case a-c-b.
    --
    -- Here ac < ab, while A-B-C gives AB < AC.
    --
    -- By congruence transport:
    --   AC < ab
    --   ab < AC
    --
    -- contradicting asymmetry.

    exfalso

    have hacltab :
        HilbertSegmentLess Geo a c a b :=
      hilbert_segmentLess_of_between
        Geo a c b hacbOrder

    have hACltab :
        HilbertSegmentLess Geo A C a b :=
      hilbert_segmentLess_congruent_left
        Geo
        a c
        A C
        a b
        hacltab
        hACac

    have hABltAC :
        HilbertSegmentLess Geo A B A C :=
      hilbert_segmentLess_of_between
        Geo A B C hABC

    have habAB : Geo.Congruent a b A B :=
      hilbert_congruent_symmetry
        Geo A B a b hABab

    have habltAC :
        HilbertSegmentLess Geo a b A C :=
      hilbert_segmentLess_congruent_left
        Geo
        A B
        a b
        A C
        hABltAC
        habAB

    exact
      (hilbert_segmentLess_asymm
        Geo A C a b hACltab)
        habltAC
/--
Three-point case of Hilbert's Theorem 27.

Congruent triples preserve betweenness, provided the corresponding
Hilbert segments are genuine, i.e. the points a, b, c are pairwise
distinct.
-/
theorem hilbert_theorem27_three_points
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (hab : a ≠ b)
    (hbc : b ≠ c)
    (hac : a ≠ c)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hBCbc : Geo.Congruent B C b c) :
    Geo.Between a b c := by

  have habc : Collinear Geo a b c :=
    hilbert_congruent_triple_collinear
      Geo
      A B C
      a b c
      hABC
      hab
      hABab
      hACac
      hBCbc

  exact
    hilbert_congruent_collinear_triple_preserves_between
      Geo
      A B C
      a b c
      hABC
      habc
      hab
      hbc
      hac
      hABab
      hACac
      hBCbc

/--
Book Zero #17 / Hilbert Theorem 27 (three points).

If two ordered triples of points have congruent corresponding
segments, then betweenness is preserved.
-/
theorem bookZero_17_three_points
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABC : Geo.Between A B C)
    (hab : a ≠ b)
    (hbc : b ≠ c)
    (hac : a ≠ c)
    (hABab : Geo.Congruent A B a b)
    (hACac : Geo.Congruent A C a c)
    (hBCbc : Geo.Congruent B C b c) :
    Geo.Between a b c := by

  exact
    hilbert_theorem27_three_points
      Geo
      A B C
      a b c
      hABC
      hab
      hbc
      hac
      hABab
      hACac
      hBCbc

/-
Book Zero #18: outerconnectivity.

If B lies between A and C and also between A and D,
then C and D are comparable beyond B. If neither C lies
between B and D nor D lies between B and C, then C = D.
-/
theorem bookZero_18_outerConnectivity
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hABD : Geo.Between A B D)
    (hNotBCD : ¬ Geo.Between B C D)
    (hNotBDC : ¬ Geo.Between B D C) :
    C = D := by

  by_contra hCD

  have hABCData :=
    HilbertOrder.between_incidence A B C hABC

  have hABDData :=
    HilbertOrder.between_incidence A B D hABD

  have hAB : A ≠ B :=
    hABCData.1

  have hAC : A ≠ C :=
    hABCData.2.2.1

  have hAD : A ≠ D :=
    hABDData.2.2.1

  have hColACD : PrimCollinear Geo A C D := by
    rcases hABCData.2.2.2.1 with
      ⟨l, hAl, hBl, hCl⟩

    rcases hABDData.2.2.2.1 with
      ⟨m, hAm, hBm, hDm⟩

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        A B hAB l m
        hAl hBl
        hAm hBm

    subst m
    exact ⟨l, hAl, hCl, hDm⟩

  rcases
      hilbert_between_trichotomy
        Geo A C D
        hAC
        hCD
        hAD
        hColACD with
    hACD | hCAD | hADC

  · have hBCD :=
      (hilbert_between_inner_trans
        Geo A B C D hABC hACD).1

    exact hNotBCD hBCD

  · have hCBA :=
      hABCData.2.2.2.2

    have hBAD :=
      (hilbert_between_inner_trans
        Geo C B A D hCBA hCAD).1

    have hColABD :=
      hABDData.2.2.2.1

    have hNotBAD :=
      (HilbertOrder.between_unique
        A B D hColABD hABD).1

    exact hNotBAD hBAD

  · have hBDC :=
      (hilbert_between_inner_trans
        Geo A B D C hABD hADC).1

    exact hNotBDC hBDC
/-
Book Zero #19: interior5.
-/

/-
BNW auxiliary principle: 5-line.

This is the five-segment principle used in the original BNW proof
of Book Zero #19 (`interior5`).

It is kept local to HilbertBookZero.  It is not added to the
historical Hilbert axiom layer.
-/
axiom bookZero_fiveLine
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hBD : Geo.Congruent B D b d) :
    Geo.Congruent C D c d

/--
Book Zero #19: interior5.
-/
theorem bookZero_19_interior5
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hCD : Geo.Congruent C D c d) :
    Geo.Congruent B D b d := by

  have hCA : C ≠ A :=
    (HilbertOrder.between_incidence A B C hABC).2.2.1.symm

  have hca : c ≠ a :=
    (HilbertOrder.between_incidence a b c habc).2.2.1.symm

  ----------------------------------------------------------------------
  -- Construct M beyond A on the line CA, with AM congruent to BC.
  ----------------------------------------------------------------------

  rcases HilbertOrder.between_extension C A hCA with
    ⟨R, hCAR⟩

  have hAR : A ≠ R :=
    (HilbertOrder.between_incidence C A R hCAR).2.1

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      B C
      A R
      hAR with
    ⟨M, hRayM, hAMBC⟩

  have hRayC : HilbertSameRay Geo A C C :=
    hilbert_sameRay_refl Geo A C hCA

  have hCAM : Geo.Between C A M :=
    hilbert_between_transport_sameRays
      Geo
      C A R
      C M
      hCAR
      hRayC
      hRayM

  ----------------------------------------------------------------------
  -- Construct m beyond a on the line ca, with am congruent to bc.
  ----------------------------------------------------------------------

  rcases HilbertOrder.between_extension c a hca with
    ⟨r, hcar⟩

  have har : a ≠ r :=
    (HilbertOrder.between_incidence c a r hcar).2.1

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      b c
      a r
      har with
    ⟨m, hRaym, hambc⟩

  have hRayc : HilbertSameRay Geo a c c :=
    hilbert_sameRay_refl Geo a c hca

  have hcam : Geo.Between c a m :=
    hilbert_between_transport_sameRays
      Geo
      c a r
      c m
      hcar
      hRayc
      hRaym

  ----------------------------------------------------------------------
  -- Corresponding constructed segments AM and am are congruent.
  ----------------------------------------------------------------------

  have hbcam : Geo.Congruent b c a m :=
    hilbert_congruent_symmetry Geo a m b c hambc

  have hAMbc : Geo.Congruent A M b c :=
    hilbert_congruent_transitivity
      Geo A M B C b c
      hAMBC
      hBC

  have hAMam : Geo.Congruent A M a m :=
    hilbert_congruent_transitivity
      Geo A M b c a m
      hAMbc
      hbcam

  ----------------------------------------------------------------------
  -- AC is congruent to ac by additivity.
  ----------------------------------------------------------------------

  have hAC : Geo.Congruent A C a c := by
    exact
      HilbertCongruence.segment_additivity
        (Geo := Geo)
        A B C
        a b c
        hABC
        habc
        hAB
        hBC

  have hCAca : Geo.Congruent C A c a := by
    exact
      hilbert_congruent_symmetry
        Geo c a C A
        (bookZero_doubleReverse Geo A C a c hAC).1

  ----------------------------------------------------------------------
  -- First five-line application: MD congruent to md.
  ----------------------------------------------------------------------

  have hMDmd : Geo.Congruent M D m d :=
    bookZero_fiveLine
      Geo
      C A M
      c a m
      D d
      hCAM
      hcam
      hCAca
      hAMam
      hCD
      hAD

  ----------------------------------------------------------------------
  -- Obtain M-A-B and m-a-b from the original order relations.
  ----------------------------------------------------------------------

  have hCBA : Geo.Between C B A :=
    (HilbertOrder.between_incidence A B C hABC).2.2.2.2

  have hBAM : Geo.Between B A M :=
    bookZero_3_6a
      Geo C B A M
      hCBA
      hCAM

  have hMAB : Geo.Between M A B :=
    (HilbertOrder.between_incidence B A M hBAM).2.2.2.2

  have hcba : Geo.Between c b a :=
    (HilbertOrder.between_incidence a b c habc).2.2.2.2

  have hbam : Geo.Between b a m :=
    bookZero_3_6a
      Geo c b a m
      hcba
      hcam

  have hmab : Geo.Between m a b :=
    (HilbertOrder.between_incidence b a m hbam).2.2.2.2

  ----------------------------------------------------------------------
  -- Orient the congruences for the second five-line application.
  ----------------------------------------------------------------------

  have hMAma : Geo.Congruent M A m a := by
    exact
      hilbert_congruent_symmetry
        Geo m a M A
        (bookZero_doubleReverse Geo A M a m hAMam).1

  ----------------------------------------------------------------------
  -- Second five-line application gives BD congruent to bd.
  ----------------------------------------------------------------------

  exact
    bookZero_fiveLine
      Geo
      M A B
      m a b
      D d
      hMAB
      hmab
      hMAma
      hAB
      hMDmd
      hAD

/--
Book Zero #20: collinear1.

Collinearity is preserved when the first two points are exchanged.
-/
theorem bookZero_20_collinear1
    [HilbertIncidence Geo]
    (A B C : Geo.Point)
    (hABC : PrimCollinear Geo A B C) :
    PrimCollinear Geo B A C := by
  rcases hABC with ⟨l, hAl, hBl, hCl⟩
  exact ⟨l, hBl, hAl, hCl⟩

/--
Book Zero #21: collinear2.

Collinearity is preserved under cyclic permutation.
-/
theorem bookZero_21_collinear2
    [HilbertIncidence Geo]
    (A B C : Geo.Point)
    (hABC : PrimCollinear Geo A B C) :
    PrimCollinear Geo B C A := by
  rcases hABC with ⟨l, hAl, hBl, hCl⟩
  exact ⟨l, hBl, hCl, hAl⟩

/--
Book Zero #22: collinearorder.

All permutations of a collinear triple are collinear.
-/
theorem bookZero_22_collinearOrder
    [HilbertIncidence Geo]
    (A B C : Geo.Point)
    (hABC : PrimCollinear Geo A B C) :
    PrimCollinear Geo B A C ∧
    PrimCollinear Geo B C A ∧
    PrimCollinear Geo C A B ∧
    PrimCollinear Geo A C B ∧
    PrimCollinear Geo C B A := by

  have hBAC : PrimCollinear Geo B A C :=
    bookZero_20_collinear1 Geo A B C hABC

  have hBCA : PrimCollinear Geo B C A :=
    bookZero_21_collinear2 Geo A B C hABC

  have hCAB : PrimCollinear Geo C A B :=
    bookZero_21_collinear2 Geo B C A hBCA

  have hACB : PrimCollinear Geo A C B :=
    bookZero_21_collinear2 Geo B A C hBAC

  have hCBA : PrimCollinear Geo C B A :=
    bookZero_20_collinear1 Geo B C A hBCA

  exact ⟨hBAC, hBCA, hCAB, hACB, hCBA⟩

/--
Book Zero #23: NCorder.

All permutations of a non-collinear triple are non-collinear.
-/
theorem bookZero_23_NCorder
    [HilbertIncidence Geo]
    (A B C : Geo.Point)
    (hNC : ¬ PrimCollinear Geo A B C) :
    (¬ PrimCollinear Geo B A C) ∧
    (¬ PrimCollinear Geo B C A) ∧
    (¬ PrimCollinear Geo C A B) ∧
    (¬ PrimCollinear Geo A C B) ∧
    (¬ PrimCollinear Geo C B A) := by

  constructor
  · intro hBAC

    rcases bookZero_22_collinearOrder Geo B A C hBAC with
      ⟨hABC, _, _, _, _⟩

    exact hNC hABC

  constructor
  · intro hBCA

    rcases bookZero_22_collinearOrder Geo B C A hBCA with
      ⟨_, _, hABC, _, _⟩

    exact hNC hABC

  constructor
  · intro hCAB

    rcases bookZero_22_collinearOrder Geo C A B hCAB with
      ⟨_, hABC, _, _, _⟩

    exact hNC hABC

  constructor
  · intro hACB

    rcases bookZero_22_collinearOrder Geo A C B hACB with
      ⟨_, _, _, hABC, _⟩

    exact hNC hABC

  · intro hCBA

    rcases bookZero_22_collinearOrder Geo C B A hCBA with
      ⟨_, _, _, _, hABC⟩

    exact hNC hABC

/--
Book Zero #24: collinear4.

If A, B, C are collinear and A, B, D are collinear,
with A and B distinct, then B, C, D are collinear.
-/
theorem bookZero_24_collinear4
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B C D : Geo.Point)
    (hABC : PrimCollinear Geo A B C)
    (hABD : PrimCollinear Geo A B D)
    (hAB : A ≠ B) :
    PrimCollinear Geo B C D := by

  rcases hABC with ⟨l, hAl, hBl, hCl⟩
  rcases hABD with ⟨m, hAm, hBm, hDm⟩

  have hlm : l = m :=
    HilbertPlaneIncidence.line_unique
      A B hAB
      l m
      hAl hBl
      hAm hBm

  subst m

  exact ⟨l, hBl, hCl, hDm⟩

/--
Book Zero #25: collinear5.

If A and B are distinct, and C, D, E are all collinear
with A and B, then C, D, E are collinear.
-/
theorem bookZero_25_collinear5
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B C D E : Geo.Point)
    (hAB : A ≠ B)
    (hABC : PrimCollinear Geo A B C)
    (hABD : PrimCollinear Geo A B D)
    (hABE : PrimCollinear Geo A B E) :
    PrimCollinear Geo C D E := by

  rcases hABC with ⟨l, hAl, hBl, hCl⟩
  rcases hABD with ⟨m, hAm, hBm, hDm⟩
  rcases hABE with ⟨n, hAn, hBn, hEn⟩

  have hlm : l = m :=
    HilbertPlaneIncidence.line_unique
      A B hAB
      l m
      hAl hBl
      hAm hBm

  have hln : l = n :=
    HilbertPlaneIncidence.line_unique
      A B hAB
      l n
      hAl hBl
      hAn hBn

  subst m
  subst n

  exact ⟨l, hCl, hDm, hEn⟩

/--
Book Zero #26: NCdistinct.

Three noncollinear points are pairwise distinct,
in both orientations.
-/
theorem bookZero_26_NCdistinct
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B C : Geo.Point)
    (hNC : ¬ PrimCollinear Geo A B C) :
    A ≠ B ∧
    B ≠ C ∧
    A ≠ C ∧
    B ≠ A ∧
    C ≠ B ∧
    C ≠ A := by

  rcases bookZero_23_NCorder Geo A B C hNC with
    ⟨hBAC, hBCA, hCAB, hACB, hCBA⟩

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first Geo A B C hNC

  have hBC : B ≠ C :=
    hilbert_noncollinear_ne_first Geo B C A hBCA

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first Geo A C B hACB

  exact
    ⟨hAB,
     hBC,
     hAC,
     hAB.symm,
     hBC.symm,
     hAC.symm⟩

/--
Book Zero #27: NChelper.

If A, B, C are noncollinear, P and Q lie on the line AB,
and P and Q are distinct, then P, Q, C are noncollinear.
-/
theorem bookZero_27_NChelper
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B C P Q : Geo.Point)
    (hNCABC : ¬ PrimCollinear Geo A B C)
    (hABP : PrimCollinear Geo A B P)
    (hABQ : PrimCollinear Geo A B Q)
    (hPQ : P ≠ Q) :
    ¬ PrimCollinear Geo P Q C := by

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first Geo A B C hNCABC

  intro hPQC

  have hPQB : PrimCollinear Geo P Q B := by
    have hBPQ : PrimCollinear Geo B P Q :=
      bookZero_24_collinear4
        Geo
        A B P Q
        hABP
        hABQ
        hAB

    rcases bookZero_22_collinearOrder Geo B P Q hBPQ with
      ⟨_, hPQB, _, _, _⟩

    exact hPQB

  have hPQA : PrimCollinear Geo P Q A := by
    have hBAP : PrimCollinear Geo B A P :=
      bookZero_20_collinear1 Geo A B P hABP

    have hBAQ : PrimCollinear Geo B A Q :=
      bookZero_20_collinear1 Geo A B Q hABQ

    have hAPQ : PrimCollinear Geo A P Q :=
      bookZero_24_collinear4
        Geo
        B A P Q
        hBAP
        hBAQ
        hAB.symm

    rcases bookZero_22_collinearOrder Geo A P Q hAPQ with
      ⟨_, hPQA, _, _, _⟩

    exact hPQA

  have hABC : PrimCollinear Geo A B C :=
    bookZero_25_collinear5
      Geo
      P Q A B C
      hPQ
      hPQA
      hPQB
      hPQC

  exact hNCABC hABC


end Geometry

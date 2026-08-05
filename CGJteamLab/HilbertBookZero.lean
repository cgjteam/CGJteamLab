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

/--
Book Zero #28: fiveline.

A convenient collinear form of the BNW five-line principle.
-/
theorem bookZero_28_fiveline
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hCol : PrimCollinear Geo A B C)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hCD : Geo.Congruent C D c d)
    (hAC : Geo.Congruent A C a c)
    (hACne : A ≠ C) :
    Geo.Congruent B D b d := by

  by_cases hABeq : A = B

  · subst B

    have habeq : a = b :=
      bookZero_nullSegment1 Geo a b A
        (hilbert_congruent_symmetry Geo A A a b hAB)

    subst b

    exact hAD

  · by_cases hBCeq : B = C

    · subst C

      have hbceq : b = c :=
        bookZero_nullSegment1 Geo b c B
          (hilbert_congruent_symmetry Geo B B b c hBC)

      subst c

      exact hCD

    ·
      have hBCne : B ≠ C := hBCeq

      rcases
          hilbert_between_trichotomy
            Geo A B C
            hABeq
            hBCne
            hACne
            hCol with
        hABC | hBAC | hACB

      ------------------------------------------------------------------
      -- Case A-B-C.
      ------------------------------------------------------------------

      · have hab : a ≠ b :=
          bookZero_nullSegment3
            Geo A B a b
            hABeq
            hAB

        have hbc : b ≠ c :=
          bookZero_nullSegment3
            Geo B C b c
            hBCne
            hBC

        have hac : a ≠ c :=
          bookZero_nullSegment3
            Geo A C a c
            hACne
            hAC

        have habc : Geo.Between a b c :=
          bookZero_17_three_points
            Geo
            A B C
            a b c
            hABC
            hab
            hbc
            hac
            hAB
            hAC
            hBC

        exact
          bookZero_19_interior5
            Geo
            A B C
            a b c
            D d
            hABC
            habc
            hAB
            hBC
            hAD
            hCD

      ------------------------------------------------------------------
      -- Case B-A-C. Reverse the order and use C-A-B.
      ------------------------------------------------------------------

      · have hCAB : Geo.Between C A B :=
          (HilbertOrder.between_incidence B A C hBAC).2.2.2.2

        have hab : a ≠ b :=
          bookZero_nullSegment3
            Geo A B a b
            hABeq
            hAB

        have hbc : b ≠ c :=
          bookZero_nullSegment3
            Geo B C b c
            hBCne
            hBC

        have hac : a ≠ c :=
          bookZero_nullSegment3
            Geo A C a c
            hACne
            hAC

        have hca : c ≠ a := by
          intro hcaEq
          exact hac hcaEq.symm

        have hcb : c ≠ b := by
          intro hcbEq
          exact hbc hcbEq.symm

        have hCAca : Geo.Congruent C A c a := by
          exact
            hilbert_congruent_symmetry
              Geo c a C A
              (bookZero_doubleReverse Geo A C a c hAC).1

        have hCBcb : Geo.Congruent C B c b := by
          exact
            hilbert_congruent_symmetry
              Geo c b C B
              (bookZero_doubleReverse Geo B C b c hBC).1

        have hcab : Geo.Between c a b :=
          bookZero_17_three_points
            Geo
            C A B
            c a b
            hCAB
            hca
            hab
            hcb
            hCAca
            hCBcb
            hAB

        exact
          bookZero_fiveLine
            Geo
            C A B
            c a b
            D d
            hCAB
            hcab
            hCAca
            hAB
            hCD
            hAD


      ------------------------------------------------------------------
      -- Case A-C-B.
      ------------------------------------------------------------------

      · have hab : a ≠ b :=
          bookZero_nullSegment3
            Geo A B a b
            hABeq
            hAB

        have hbc : b ≠ c :=
          bookZero_nullSegment3
            Geo B C b c
            hBCne
            hBC

        have hac : a ≠ c :=
          bookZero_nullSegment3
            Geo A C a c
            hACne
            hAC

        have hcb : c ≠ b := by
          intro hcbEq
          exact hbc hcbEq.symm

        have hCBcb : Geo.Congruent C B c b := by
          exact
            hilbert_congruent_symmetry
              Geo c b C B
              (bookZero_doubleReverse Geo B C b c hBC).1

        have hacb : Geo.Between a c b :=
          bookZero_17_three_points
            Geo
            A C B
            a c b
            hACB
            hac
            hcb
            hab
            hAC
            hAB
            hCBcb

        exact
          bookZero_fiveLine
            Geo
            A C B
            a c b
            D d
            hACB
            hacb
            hAC
            hCBcb
            hAD
            hCD


/--
BNW relation `CU A B C D E`.

The segments AB and CD cut each other at E.
-/
def BookZeroCut
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    (A B C D E : Geo.Point) : Prop :=
  Geo.Between A E B ∧
  Geo.Between C E D ∧
  ¬ PrimCollinear Geo A B C ∧
  ¬ PrimCollinear Geo A B D


/--
Book Zero #29: twolines.

Two distinct lines have at most one common intersection point.
-/
theorem bookZero_29_twoLines
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D E F : Geo.Point)
    (hCutE : BookZeroCut Geo A B C D E)
    (hCutF : BookZeroCut Geo A B C D F)
    (hNCBCD : ¬ PrimCollinear Geo B C D) :
    E = F := by

  rcases hCutE with
    ⟨hAEB, hCED, hNCABC, hNCABD⟩

  rcases hCutF with
    ⟨hAFB, hCFD, _, _⟩

  by_contra hEF

  have hAB : A ≠ B :=
    (HilbertOrder.between_incidence A E B hAEB).2.2.1

  have hCD : C ≠ D :=
    (HilbertOrder.between_incidence C E D hCED).2.2.1

  ----------------------------------------------------------------------
  -- E and F lie on line AB.
  ----------------------------------------------------------------------

  have hABE : PrimCollinear Geo A B E := by
    rcases
        (HilbertOrder.between_incidence A E B hAEB).2.2.2.1 with
      ⟨l, hAl, hEl, hBl⟩
    exact ⟨l, hAl, hBl, hEl⟩

  have hABF : PrimCollinear Geo A B F := by
    rcases
        (HilbertOrder.between_incidence A F B hAFB).2.2.2.1 with
      ⟨l, hAl, hFl, hBl⟩
    exact ⟨l, hAl, hBl, hFl⟩

  have hBEF : PrimCollinear Geo B E F :=
    bookZero_24_collinear4
      Geo A B E F
      hABE hABF hAB

  have hEFB : PrimCollinear Geo E F B := by
    rcases bookZero_22_collinearOrder Geo B E F hBEF with
      ⟨_, hEFB, _, _, _⟩
    exact hEFB

  ----------------------------------------------------------------------
  -- E and F lie on line CD.
  ----------------------------------------------------------------------

  have hCDE : PrimCollinear Geo C D E := by
    rcases
        (HilbertOrder.between_incidence C E D hCED).2.2.2.1 with
      ⟨l, hCl, hEl, hDl⟩
    exact ⟨l, hCl, hDl, hEl⟩

  have hCDF : PrimCollinear Geo C D F := by
    rcases
        (HilbertOrder.between_incidence C F D hCFD).2.2.2.1 with
      ⟨l, hCl, hFl, hDl⟩
    exact ⟨l, hCl, hDl, hFl⟩

  have hDEF : PrimCollinear Geo D E F :=
    bookZero_24_collinear4
      Geo C D E F
      hCDE hCDF hCD

  have hEFD : PrimCollinear Geo E F D := by
    rcases bookZero_22_collinearOrder Geo D E F hDEF with
      ⟨_, hEFD, _, _, _⟩
    exact hEFD

  have hDCE : PrimCollinear Geo D C E :=
    bookZero_20_collinear1 Geo C D E hCDE

  have hDCF : PrimCollinear Geo D C F :=
    bookZero_20_collinear1 Geo C D F hCDF

  have hCEF : PrimCollinear Geo C E F :=
    bookZero_24_collinear4
      Geo D C E F
      hDCE hDCF hCD.symm

  have hEFC : PrimCollinear Geo E F C := by
    rcases bookZero_22_collinearOrder Geo C E F hCEF with
      ⟨_, hEFC, _, _, _⟩
    exact hEFC

  ----------------------------------------------------------------------
  -- If E and F were distinct, B, C and D would lie on line EF.
  ----------------------------------------------------------------------

  have hBCD : PrimCollinear Geo B C D :=
    bookZero_25_collinear5
      Geo
      E F B C D
      hEF
      hEFB
      hEFC
      hEFD

  exact hNCBCD hBCD


/--
Book Zero #30: lessthancongruence.

Strict segment comparison is preserved when the larger segment
is replaced by a congruent segment.
-/
theorem bookZero_30_lessThanCongruence
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hLess : HilbertSegmentLess Geo A B C D)
    (hCong : Geo.Congruent C D E F) :
    HilbertSegmentLess Geo A B E F := by

  rcases hLess with ⟨G, hCGD, hABCG⟩

  have hCD : C ≠ D :=
    (HilbertOrder.between_incidence C G D hCGD).2.2.1

  have hEF : E ≠ F :=
    bookZero_nullSegment3
      Geo C D E F
      hCD
      hCong

  have hFE : F ≠ E := by
    intro hFEeq
    exact hEF hFEeq.symm

  ----------------------------------------------------------------------
  -- Construct P beyond E on the line FE, with EP congruent to FE.
  ----------------------------------------------------------------------

  rcases HilbertOrder.between_extension F E hFE with
    ⟨R, hFER⟩

  have hER : E ≠ R :=
    (HilbertOrder.between_incidence F E R hFER).2.1

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      F E
      E R
      hER with
    ⟨P, hRayP, hEPFE⟩

  have hRayF : HilbertSameRay Geo E F F :=
    hilbert_sameRay_refl Geo E F hFE

  have hFEP : Geo.Between F E P :=
    hilbert_between_transport_sameRays
      Geo
      F E R
      F P
      hFER
      hRayF
      hRayP

  have hPEF : Geo.Between P E F :=
    (HilbertOrder.between_incidence F E P hFEP).2.2.2.2

  have hPE : P ≠ E :=
    (HilbertOrder.between_incidence P E F hPEF).1

  ----------------------------------------------------------------------
  -- Construct Q beyond C on the line DC, with CQ congruent to EP.
  ----------------------------------------------------------------------

  have hDC : D ≠ C := by
    intro hDCeq
    exact hCD hDCeq.symm

  rcases HilbertOrder.between_extension D C hDC with
    ⟨S, hDCS⟩

  have hCS : C ≠ S :=
    (HilbertOrder.between_incidence D C S hDCS).2.1

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      E P
      C S
      hCS with
    ⟨Q, hRayQ, hCQEP⟩

  have hRayD : HilbertSameRay Geo C D D :=
  hilbert_sameRay_refl Geo C D hDC

  have hDCQ : Geo.Between D C Q :=
    hilbert_between_transport_sameRays
      Geo
      D C S
      D Q
      hDCS
      hRayD
      hRayQ

  have hQCD : Geo.Between Q C D :=
    (HilbertOrder.between_incidence D C Q hDCQ).2.2.2.2

  have hQCPE : Geo.Congruent Q C P E :=
    CongruentReverseBoth Geo C Q E P hCQEP

  ----------------------------------------------------------------------
  -- Construct H beyond E on the line PE, with EH congruent to AB.
  ----------------------------------------------------------------------

  rcases HilbertOrder.between_extension P E hPE with
    ⟨T, hPET⟩

  have hET : E ≠ T :=
    (HilbertOrder.between_incidence P E T hPET).2.1

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      A B
      E T
      hET with
    ⟨H, hRayH, hEHAB⟩

  have hRayP' : HilbertSameRay Geo E P P :=
    hilbert_sameRay_refl Geo E P hPE

  have hPEH : Geo.Between P E H :=
    hilbert_between_transport_sameRays
      Geo
      P E T
      P H
      hPET
      hRayP'
      hRayH

  ----------------------------------------------------------------------
  -- QD is congruent to PF by addition of corresponding parts.
  ----------------------------------------------------------------------

  have hQDPF : Geo.Congruent Q D P F :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      Q C D
      P E F
      hQCD
      hPEF
      hQCPE
      hCong

  ----------------------------------------------------------------------
  -- CG is congruent to EH.
  ----------------------------------------------------------------------

  have hCGAB : Geo.Congruent C G A B :=
    hilbert_congruent_symmetry Geo A B C G hABCG

  have hABEH : Geo.Congruent A B E H :=
    hilbert_congruent_symmetry Geo E H A B hEHAB

  have hCGEH : Geo.Congruent C G E H :=
    hilbert_congruent_transitivity
      Geo
      C G
      A B
      E H
      hCGAB
      hABEH

  ----------------------------------------------------------------------
  -- Since Q-C-D and C-G-D, we have Q-C-G.
  ----------------------------------------------------------------------

  have hDGC : Geo.Between D G C :=
    (HilbertOrder.between_incidence C G D hCGD).2.2.2.2

  have hDCQ' : Geo.Between D C Q :=
    (HilbertOrder.between_incidence Q C D hQCD).2.2.2.2

  have hGCQ : Geo.Between G C Q :=
    (hilbert_between_inner_trans
      Geo D G C Q hDGC hDCQ').1

  have hQCG : Geo.Between Q C G :=
    (HilbertOrder.between_incidence G C Q hGCQ).2.2.2.2

  ----------------------------------------------------------------------
  -- Apply the primitive five-line principle.
  ----------------------------------------------------------------------

  have hGDHF : Geo.Congruent G D H F :=
    bookZero_fiveLine
      Geo
      Q C G
      P E H
      D F
      hQCG
      hPEH
      hQCPE
      hCGEH
      hQDPF
      hCong

  have hDGFH : Geo.Congruent D G F H :=
    (bookZero_congruenceFlip Geo G D H F hGDHF).1

  ----------------------------------------------------------------------
  -- Transfer C-G-D to E-H-F.
  ----------------------------------------------------------------------

  have hEH : E ≠ H :=
    (HilbertOrder.between_incidence P E H hPEH).2.1

  have hGD : G ≠ D :=
    (HilbertOrder.between_incidence C G D hCGD).2.1

  have hFH : F ≠ H :=
    bookZero_nullSegment3
      Geo D G F H
      hGD.symm
      hDGFH

  have hHF : H ≠ F := by
    intro hHFeq
    exact hFH hHFeq.symm

  have hEHF : Geo.Between E H F :=
    bookZero_17_three_points
      Geo
      C G D
      E H F
      hCGD
      hEH
      hHF
      hEF
      hCGEH
      hCong
      hGDHF

  ----------------------------------------------------------------------
  -- AB is congruent to EH, so H witnesses AB < EF.
  ----------------------------------------------------------------------

  have hABEH' : Geo.Congruent A B E H :=
    hilbert_congruent_transitivity
      Geo
      A B
      C G
      E H
      hABCG
      hCGEH

  exact ⟨H, hEHF, hABEH'⟩


/--
Book Zero #31: trichotomy1.

Two non-null segments which are not strictly shorter than one another
are congruent.
-/
theorem bookZero_31_trichotomy1
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hNotABCD : ¬ HilbertSegmentLess Geo A B C D)
    (hNotCDAB : ¬ HilbertSegmentLess Geo C D A B)
    (hAB : A ≠ B)
    (hCD : C ≠ D) :
    Geo.Congruent A B C D := by

  ----------------------------------------------------------------------
  -- Lay off CD from A on ray AB.
  ----------------------------------------------------------------------

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      C D
      A B
      hAB with
    ⟨E, hRayE, hAECD⟩

  have hCDAE : Geo.Congruent C D A E :=
    hilbert_congruent_symmetry
      Geo A E C D hAECD

  have hAE : A ≠ E :=
    bookZero_nullSegment3
      Geo C D A E
      hCD
      hCDAE

  ----------------------------------------------------------------------
  -- Points B and E lie on the same ray from A.
  ----------------------------------------------------------------------

  rcases hilbert_sameRay_cases Geo A B E hRayE with
    hBE | hABE | hAEB

  ----------------------------------------------------------------------
  -- Case B = E.
  ----------------------------------------------------------------------

  · subst E
    exact hAECD

  ----------------------------------------------------------------------
  -- Case A-B-E: then AB < AE congruent to CD.
  ----------------------------------------------------------------------

  · have hABAE : HilbertSegmentLess Geo A B A E :=
      ⟨B, hABE, hilbert_congruent_reflexive Geo A B⟩

    have hABCD : HilbertSegmentLess Geo A B C D :=
      bookZero_30_lessThanCongruence
        Geo
        A B A E C D
        hABAE
        hAECD

    exact (hNotABCD hABCD).elim

  ----------------------------------------------------------------------
  -- Case A-E-B: then CD congruent to AE < AB.
  ----------------------------------------------------------------------

  · have hAEAB : HilbertSegmentLess Geo A E A B :=
      ⟨E, hAEB, hilbert_congruent_reflexive Geo A E⟩

    have hCDAB : HilbertSegmentLess Geo C D A B := by
      exact
        hilbert_segmentLess_congruent_left
          Geo
          A E
          C D
          A B
          hAEAB
          hCDAE

    exact (hNotCDAB hCDAB).elim

/--
Book Zero #32: lessthancongruence2.

Strict segment comparison is preserved when the smaller segment
is replaced by a congruent segment.
-/
theorem bookZero_32_lessThanCongruence2
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hLess : HilbertSegmentLess Geo A B C D)
    (hCong : Geo.Congruent A B E F) :
    HilbertSegmentLess Geo E F C D := by
  exact
    hilbert_segmentLess_congruent_left
      Geo
      A B
      E F
      C D
      hLess
      (hilbert_congruent_symmetry Geo A B E F hCong)

/--
Book Zero #33: ray2.

If C lies on the ray AB, then A and B are distinct.
-/
theorem bookZero_33_ray2
    [HilbertIncidence Geo]
    (A B C : Geo.Point)
    (hRay : HilbertSameRay Geo A B C) :
    A ≠ B := by
  exact hRay.1.symm

/--
Book Zero #34: ray.

If P lies on ray AB, P is distinct from B, and P is not
between A and B, then B lies between A and P.
-/
theorem bookZero_34_ray
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B P : Geo.Point)
    (hRay : HilbertSameRay Geo A B P)
    (hPB : P ≠ B)
    (hNotAPB : ¬ Geo.Between A P B) :
    Geo.Between A B P := by

  rcases hilbert_sameRay_cases Geo A B P hRay with
    hBP | hABP | hAPB

  · exact False.elim (hPB hBP.symm)

  · exact hABP

  · exact False.elim (hNotAPB hAPB)

/--
Book Zero #35: ray1.

A point P on ray AB either lies between A and B,
coincides with B, or lies beyond B.
-/
theorem bookZero_35_ray1
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B P : Geo.Point)
    (hRay : HilbertSameRay Geo A B P) :
    Geo.Between A P B ∨
    B = P ∨
    Geo.Between A B P := by

  rcases hilbert_sameRay_cases Geo A B P hRay with
    hBP | hABP | hAPB

  · exact Or.inr (Or.inl hBP)

  · exact Or.inr (Or.inr hABP)

  · exact Or.inl hAPB

/--
Book Zero #36: ray3.

If D and V lie on ray BC, then V lies on ray BD.
-/
theorem bookZero_36_ray3
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (B C D V : Geo.Point)
    (hBCD : HilbertSameRay Geo B C D)
    (hBCV : HilbertSameRay Geo B C V) :
    HilbertSameRay Geo B D V := by

  have hDB : D ≠ B :=
    hBCD.2.1

  have hVB : V ≠ B :=
    hBCV.2.1

  have hBC : B ≠ C := by
    intro hBCeq
    exact hBCD.1 hBCeq.symm

  have hBDV : PrimCollinear Geo B D V := by
    rcases hBCD.2.2.1 with
      ⟨l, hBl, hCl, hDl⟩

    rcases hBCV.2.2.1 with
      ⟨m, hBm, hCm, hVm⟩

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        B C hBC
        l m
        hBl hCl
        hBm hCm

    subst m
    exact ⟨l, hBl, hDl, hVm⟩

  have hNotDBV : ¬ Geo.Between D B V := by
    intro hDBV

    have hBDC : HilbertSameRay Geo B D C :=
      hilbert_sameRay_symm Geo B C D hBCD

    have hBVC : HilbertSameRay Geo B V C :=
      hilbert_sameRay_symm Geo B C V hBCV

    have hCBC : Geo.Between C B C :=
      hilbert_between_transport_sameRays
        Geo
        D B V
        C C
        hDBV
        hBDC
        hBVC

    exact
      (HilbertOrder.between_incidence C B C hCBC).2.2.1 rfl

  exact
    ⟨hDB, hVB, hBDV, hNotDBV⟩

/--
Book Zero #37: raystrict.

If C lies on ray AB, then A and C are distinct.
-/
theorem bookZero_37_raystrict
    [HilbertIncidence Geo]
    (A B C : Geo.Point)
    (hRay : HilbertSameRay Geo A B C) :
    A ≠ C := by
  exact hRay.2.1.symm

/--
Book Zero #38: ray4.

If E lies between A and B, coincides with B,
or lies beyond B, and A != B, then E lies on ray AB.
-/
theorem bookZero_38_ray4
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B E : Geo.Point)
    (hPos :
      Geo.Between A E B ∨
      E = B ∨
      Geo.Between A B E)
    (hAB : A ≠ B) :
    HilbertSameRay Geo A B E := by

  rcases hPos with hAEB | hEB | hABE

  · have hAEBRay : HilbertSameRay Geo A E B :=
      hilbert_sameRay_of_between Geo A E B hAEB

    exact
      hilbert_sameRay_symm Geo A E B hAEBRay

  · subst E
    exact
      hilbert_sameRay_refl Geo A B hAB.symm

  · exact
      hilbert_sameRay_of_between Geo A B E hABE

/--
Book Zero #39: ray5.

If C lies on ray AB, then B lies on ray AC.
-/
theorem bookZero_39_ray5
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C : Geo.Point)
    (hRay : HilbertSameRay Geo A B C) :
    HilbertSameRay Geo A C B := by
  exact
    hilbert_sameRay_symm Geo A B C hRay

/--
Book Zero #40: rayimpliescollinear.

If C lies on ray AB, then A, B and C are collinear.
-/
theorem bookZero_40_rayImpliesCollinear
    [HilbertIncidence Geo]
    (A B C : Geo.Point)
    (hRay : HilbertSameRay Geo A B C) :
    PrimCollinear Geo A B C := by
  exact hRay.2.2.1

/--
Book Zero #41: tworays.

If C lies on ray AB and also on ray BA,
then C lies between A and B.
-/
theorem bookZero_41_twoRays
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : HilbertSameRay Geo A B C)
    (hBAC : HilbertSameRay Geo B A C) :
    Geo.Between A C B := by

  have hBC : B ≠ C :=
    bookZero_37_raystrict Geo B A C hBAC

  have hAC : A ≠ C :=
    bookZero_37_raystrict Geo A B C hABC

  rcases bookZero_35_ray1 Geo A B C hABC with
    hACB | hBCeq | hABCbet

  · exact hACB

  · exact (hBC hBCeq).elim

  · rcases bookZero_35_ray1 Geo B A C hBAC with
      hBCA | hACeq | hBACbet

    · exact
        (HilbertOrder.between_incidence
          B C A hBCA).2.2.2.2

    · exact (hAC hACeq).elim

    ·
      have hColABC : PrimCollinear Geo A B C :=
        (HilbertOrder.between_incidence
          A B C hABCbet).2.2.2.1

      have hNotBAC : ¬ Geo.Between B A C :=
        (HilbertOrder.between_unique
          A B C
          hColABC
          hABCbet).1

      exact (hNotBAC hBACbet).elim

/--
Book Zero #42: twolines2.

If P and Q both lie on two distinct lines AB and CD,
then P = Q.
-/
theorem bookZero_42_twoLines2
    [HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B C D P Q : Geo.Point)
    (hAB : A ≠ B)
    (hCD : C ≠ D)
    (hPAB : PrimCollinear Geo P A B)
    (hPCD : PrimCollinear Geo P C D)
    (hQAB : PrimCollinear Geo Q A B)
    (hQCD : PrimCollinear Geo Q C D)
    (hDistinct :
      ¬ (PrimCollinear Geo A C D ∧
         PrimCollinear Geo B C D)) :
    P = Q := by

  by_contra hPQ

  rcases hPAB with
    ⟨l, hPl, hAl, hBl⟩

  rcases hQAB with
    ⟨l', hQl', hAl', hBl'⟩

  have hll' : l = l' :=
    HilbertPlaneIncidence.line_unique
      A B hAB
      l l'
      hAl hBl
      hAl' hBl'

  subst l'

  rcases hPCD with
    ⟨m, hPm, hCm, hDm⟩

  rcases hQCD with
    ⟨m', hQm', hCm', hDm'⟩

  have hmm' : m = m' :=
    HilbertPlaneIncidence.line_unique
      C D hCD
      m m'
      hCm hDm
      hCm' hDm'

  subst m'

  have hlm : l = m :=
    HilbertPlaneIncidence.line_unique
      P Q hPQ
      l m
      hPl hQl'
      hPm hQm'

  subst m

  have hACD : PrimCollinear Geo A C D :=
    ⟨l, hAl, hCm, hDm⟩

  have hBCD : PrimCollinear Geo B C D :=
    ⟨l, hBl, hCm, hDm⟩

  exact hDistinct ⟨hACD, hBCD⟩

/--
BNW relation `SU A B C D F`.

The angle DBF is supplementary to ABC:
D lies on ray BC and A-B-F.
-/
def BookZeroSupplement
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    (A B C D F : Geo.Point) : Prop :=
  HilbertSameRay Geo B C D ∧
  Geo.Between A B F


/--
Book Zero #43: supplements.

Angles supplementary to congruent angles are congruent.
-/
theorem bookZero_43_supplements
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D F a b c d f : Geo.Point)
    (hAngle : Geo.AngleCongruent A B C a b c)
    (hSupp : BookZeroSupplement Geo A B C D F)
    (hsupp : BookZeroSupplement Geo a b c d f)
    (hNCABC : ¬ PrimCollinear Geo A B C)
    (hNCabc : ¬ PrimCollinear Geo a b c) :
    Geo.AngleCongruent D B F d b f := by

  rcases hSupp with ⟨hBCD, hABF⟩
  rcases hsupp with ⟨hbcd, habf⟩

  have hCBF_cbf :
      Geo.AngleCongruent C B F c b f :=
    hilbert_adjacent_angles_congruent
      Geo
      A B C F
      a b c f
      hABF
      habf
      hNCABC
      hNCabc
      hAngle

  have hLeft :
      Geo.Angle D B F = Geo.Angle C B F := by
    exact
      (hilbert_angle_eq_of_sameRay_first
        Geo B C D F hBCD).symm

  have hRight :
      Geo.Angle d b f = Geo.Angle c b f := by
    exact
      (hilbert_angle_eq_of_sameRay_first
        Geo b c d f hbcd).symm

  unfold Geometry.Geo.AngleCongruent at hCBF_cbf ⊢
  rw [hLeft, hRight]
  exact hCBF_cbf

/--
Book Zero #44: supplementsymmetric.

The supplementary-angle relation is symmetric:
if DBE is supplementary to ABC, then CBA is
supplementary to DBE.
-/
theorem bookZero_44_supplementSymmetric
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C E D : Geo.Point)
    (hSupp : BookZeroSupplement Geo A B C E D) :
    BookZeroSupplement Geo D B E C A := by

  rcases hSupp with ⟨hBCE, hABD⟩

  have hBEC : HilbertSameRay Geo B E C :=
    bookZero_39_ray5 Geo B C E hBCE

  have hDBA : Geo.Between D B A :=
    (HilbertOrder.between_incidence
      A B D hABD).2.2.2.2

  exact ⟨hBEC, hDBA⟩

/--
Book Zero #45: partnotequalwhole.

If B lies between A and C, then the proper part AB
is not congruent to the whole segment AC.
-/
theorem bookZero_45_partNotEqualWhole
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    ¬ Geo.Congruent A B A C := by

  intro hABAC

  have hABltAC : HilbertSegmentLess Geo A B A C :=
    ⟨B, hABC, hilbert_congruent_reflexive Geo A B⟩

  exact
    hilbert_segmentLess_not_congruent
      Geo
      A B A C
      hABltAC
      hABAC

/--
Book Zero #46: collinearitypreserved.

If two triples have congruent corresponding segments
and A, B, C are collinear, then a, b, c are collinear.
-/
theorem bookZero_46_collinearityPreserved
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (hABCcol : PrimCollinear Geo A B C)
    (hAB : Geo.Congruent A B a b)
    (hAC : Geo.Congruent A C a c)
    (hBC : Geo.Congruent B C b c) :
    PrimCollinear Geo a b c := by

  ----------------------------------------------------------------------
  -- A repeated point always gives a collinear triple.
  ----------------------------------------------------------------------

  have collinear_of_eq12 :
      ∀ X Y Z : Geo.Point,
        X = Y →
        PrimCollinear Geo X Y Z := by
    intro X Y Z hXY
    subst Y

    by_cases hXZ : X = Z

    · subst Z

      rcases hilbert_line_through_point Geo X with
        ⟨l, hXl⟩

      exact ⟨l, hXl, hXl, hXl⟩

    · rcases
          HilbertPlaneIncidence.line_through
            X Z hXZ with
        ⟨l, hXl, hZl⟩

      exact ⟨l, hXl, hXl, hZl⟩

  ----------------------------------------------------------------------
  -- Degenerate source triples.
  ----------------------------------------------------------------------

  by_cases hABeq : A = B

  · subst B

    have hab : a = b :=
      bookZero_nullSegment1
        Geo a b A
        (hilbert_congruent_symmetry Geo A A a b hAB)

    exact collinear_of_eq12 a b c hab

  · by_cases hACeq : A = C

    · subst C

      have hac : a = c :=
        bookZero_nullSegment1
          Geo a c A
          (hilbert_congruent_symmetry Geo A A a c hAC)

      have hca : c = a := hac.symm

      have hcab : PrimCollinear Geo c a b :=
        collinear_of_eq12 c a b hca

      exact
        bookZero_21_collinear2
          Geo c a b hcab

    · by_cases hBCeq : B = C

      · subst C

        have hbc : b = c :=
          bookZero_nullSegment1
            Geo b c B
            (hilbert_congruent_symmetry Geo B B b c hBC)

        have hbca : PrimCollinear Geo b c a :=
          collinear_of_eq12 b c a hbc

        have hcab : PrimCollinear Geo c a b :=
          bookZero_21_collinear2
            Geo b c a hbca

        exact
          bookZero_21_collinear2
            Geo c a b hcab

      ·
        ----------------------------------------------------------------
        -- Nondegenerate source triple: use the order trichotomy.
        ----------------------------------------------------------------

        have hBAba : Geo.Congruent B A b a := by
          exact
            hilbert_congruent_symmetry
              Geo b a B A
              (bookZero_doubleReverse
                Geo A B a b hAB).1

        have hCAca : Geo.Congruent C A c a := by
          exact
            hilbert_congruent_symmetry
              Geo c a C A
              (bookZero_doubleReverse
                Geo A C a c hAC).1

        have hCBcb : Geo.Congruent C B c b := by
          exact
            hilbert_congruent_symmetry
              Geo c b C B
              (bookZero_doubleReverse
                Geo B C b c hBC).1

        have hab : a ≠ b :=
          bookZero_nullSegment3
            Geo A B a b hABeq hAB

        have hac : a ≠ c :=
          bookZero_nullSegment3
            Geo A C a c hACeq hAC

        have hbc : b ≠ c :=
          bookZero_nullSegment3
            Geo B C b c hBCeq hBC

        rcases
            hilbert_between_trichotomy
              Geo
              A B C
              hABeq
              hBCeq
              hACeq
              hABCcol with
          hABC | hBAC | hACB

        --------------------------------------------------------------
        -- Case A-B-C.
        --------------------------------------------------------------

        · have habc : Geo.Between a b c :=
            bookZero_17_three_points
              Geo
              A B C
              a b c
              hABC
              hab
              hbc
              hac
              hAB
              hAC
              hBC

          exact
            (HilbertOrder.between_incidence
              a b c habc).2.2.2.1

        --------------------------------------------------------------
        -- Case B-A-C.
        --------------------------------------------------------------

        · have hbac : Geo.Between b a c :=
            bookZero_17_three_points
              Geo
              B A C
              b a c
              hBAC
              hab.symm
              hac
              hbc
              hBAba
              hBC
              hAC

          have hbacCol : PrimCollinear Geo b a c :=
            (HilbertOrder.between_incidence
              b a c hbac).2.2.2.1

          exact
            bookZero_20_collinear1
              Geo b a c hbacCol

        --------------------------------------------------------------
        -- Case A-C-B.
        --------------------------------------------------------------

        · have hacb : Geo.Between a c b :=
            bookZero_17_three_points
              Geo
              A C B
              a c b
              hACB
              hac
              hbc.symm
              hab
              hAC
              hAB
              hCBcb

          have hacbCol : PrimCollinear Geo a c b :=
            (HilbertOrder.between_incidence
              a c b hacb).2.2.2.1

          exact
            PrimCollinearRotate
              Geo a c b hacbCol

/--
Book Zero #47: trichotomy2.

If AB is shorter than CD, then CD is not shorter than AB.
-/
theorem bookZero_47_trichotomy2
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABCD : HilbertSegmentLess Geo A B C D) :
    ¬ HilbertSegmentLess Geo C D A B := by

  exact
    hilbert_segmentLess_asymm
      Geo
      A B C D
      hABCD

/--
Book Zero #48: lessthannotequal.

If AB is shorter than CD, then both AB and CD
are nondegenerate.
-/
theorem bookZero_48_lessThanNotEqual
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hLess : HilbertSegmentLess Geo A B C D) :
    A ≠ B ∧ C ≠ D := by

  rcases hLess with ⟨E, hCED, hABCE⟩

  have hCE : C ≠ E :=
    (HilbertOrder.between_incidence C E D hCED).1

  have hCD : C ≠ D :=
  (HilbertOrder.between_incidence C E D hCED).2.2.1

  have hAB : A ≠ B :=
    bookZero_nullSegment3
      Geo
      C E A B
      hCE
      (hilbert_congruent_symmetry Geo A B C E hABCE)

  exact ⟨hAB, hCD⟩

/--
Book Zero #49: layoff.

Given A != B and C != D, there exists a point X on ray AB
such that AX is congruent to CD.
-/
theorem bookZero_49_layoff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hAB : A ≠ B)
    (_hCD : C ≠ D) :
    ∃ X : Geo.Point,
      HilbertSameRay Geo A B X ∧
      Geo.Congruent A X C D := by

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      C D
      A B
      hAB with
    ⟨X, hRayX, hAXCD⟩

  exact ⟨X, hRayX, hAXCD⟩

/--
Book Zero #50: layoffunique.

Two points on the same ray from A, at congruent
distances from A, are equal.
-/
theorem bookZero_50_layoffUnique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABC : HilbertSameRay Geo A B C)
    (hABD : HilbertSameRay Geo A B D)
    (hACAD : Geo.Congruent A C A D) :
    C = D := by

  exact
    hilbert_segment_construction_unique
      Geo
      A C
      A B
      C D
      hABC
      hABD
      (hilbert_congruent_reflexive Geo A C)
      (hilbert_congruent_symmetry Geo A C A D hACAD)

/--
Book Zero #51: lessthanbetween.

If AB < AC and C lies on ray AB, then B lies
between A and C.
-/
theorem bookZero_51_lessThanBetween
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hLess : HilbertSegmentLess Geo A B A C)
    (hRay : HilbertSameRay Geo A B C) :
    Geo.Between A B C := by

  rcases hLess with ⟨M, hAMC, hABAM⟩

  have hAM : A ≠ M :=
    (HilbertOrder.between_incidence A M C hAMC).1

  have hAMC_or :
      Geo.Between A M C ∨
      M = C ∨
      Geo.Between A C M :=
    Or.inl hAMC

  have hACM : HilbertSameRay Geo A C M :=
    bookZero_38_ray4
      Geo A C M
      hAMC_or
      (HilbertOrder.between_incidence A M C hAMC).2.2.1

  have hACB : HilbertSameRay Geo A C B :=
    bookZero_39_ray5
      Geo A B C hRay

  have hAMAB : Geo.Congruent A M A B :=
    hilbert_congruent_symmetry
      Geo A B A M hABAM

  have hMB : M = B :=
    bookZero_50_layoffUnique
      Geo A C M B
      hACM
      hACB
      hAMAB

  simpa [hMB] using hAMC

/--
Book Zero #52: lessthantransitive.

If AB < CD and CD < EF, then AB < EF.
-/
theorem bookZero_52_lessThanTransitive
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABCD : HilbertSegmentLess Geo A B C D)
    (hCDEF : HilbertSegmentLess Geo C D E F) :
    HilbertSegmentLess Geo A B E F := by

  rcases hABCD with ⟨G, hCGD, hABCG⟩
  rcases hCDEF with ⟨H, hEHF, hCDEH⟩

  have hEH : E ≠ H :=
    (HilbertOrder.between_incidence E H F hEHF).1

  have hCG : C ≠ G :=
    (HilbertOrder.between_incidence C G D hCGD).1

  ----------------------------------------------------------------------
  -- Lay off CG on ray EH.
  ----------------------------------------------------------------------

  rcases
      bookZero_49_layoff
        Geo E H C G hEH hCG with
    ⟨K, hEHK, hEKCG⟩

  have hCGEK : Geo.Congruent C G E K :=
    hilbert_congruent_symmetry
      Geo E K C G hEKCG

  ----------------------------------------------------------------------
  -- First show CG < EH.
  ----------------------------------------------------------------------

  have hCGCD : HilbertSegmentLess Geo C G C D :=
    ⟨G, hCGD, hilbert_congruent_reflexive Geo C G⟩

  have hCGEH : HilbertSegmentLess Geo C G E H :=
    bookZero_30_lessThanCongruence
      Geo
      C G C D E H
      hCGCD
      hCDEH

  ----------------------------------------------------------------------
  -- Replace the smaller segment CG by the congruent segment EK.
  ----------------------------------------------------------------------

  have hEKEH : HilbertSegmentLess Geo E K E H :=
    bookZero_32_lessThanCongruence2
      Geo
      C G E H E K
      hCGEH
      hCGEK

  ----------------------------------------------------------------------
  -- K lies on ray EH, hence H lies on ray EK.
  ----------------------------------------------------------------------

  have hEKH : HilbertSameRay Geo E K H :=
    bookZero_39_ray5
      Geo E H K hEHK

  have hEKHbet : Geo.Between E K H :=
    bookZero_51_lessThanBetween
      Geo E K H
      hEKEH
      hEKH

  ----------------------------------------------------------------------
  -- Since E-K-H and E-H-F, also E-K-F.
  ----------------------------------------------------------------------

  have hEKF : Geo.Between E K F :=
    bookZero_3_6b
      Geo E K H F
      hEKHbet
      hEHF

  ----------------------------------------------------------------------
  -- AB is congruent to EK.
  ----------------------------------------------------------------------

  have hABEK : Geo.Congruent A B E K :=
    hilbert_congruent_transitivity
      Geo
      A B
      C G
      E K
      hABCG
      hCGEK

  exact ⟨K, hEKF, hABEK⟩

/--
Book Zero #53: lessthanadditive.

If AB < CD, A-B-E, C-D-F, and BE is congruent to DF,
then AE < CF.
-/
theorem bookZero_53_lessThanAdditive
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABCD : HilbertSegmentLess Geo A B C D)
    (hABE : Geo.Between A B E)
    (hCDF : Geo.Between C D F)
    (hBEDF : Geo.Congruent B E D F) :
    HilbertSegmentLess Geo A E C F := by

  rcases hABCD with ⟨P, hCPD, hABCP⟩

  have hPD : P ≠ D :=
    (HilbertOrder.between_incidence C P D hCPD).2.1

  have hBE : B ≠ E :=
    (HilbertOrder.between_incidence A B E hABE).2.1

  ----------------------------------------------------------------------
  -- Lay off BE from P on ray PD.
  ----------------------------------------------------------------------

  rcases
      bookZero_49_layoff
        Geo P D B E hPD hBE with
    ⟨Q, hPDQ, hPQBE⟩

  have hPQDF : Geo.Congruent P Q D F :=
    hilbert_congruent_transitivity
      Geo
      P Q
      B E
      D F
      hPQBE
      hBEDF

  ----------------------------------------------------------------------
  -- DF is a proper part of FP.
  ----------------------------------------------------------------------

  have hPDF : Geo.Between P D F :=
    bookZero_3_6a
      Geo C P D F
      hCPD
      hCDF

  have hFDP : Geo.Between F D P :=
    (HilbertOrder.between_incidence
      P D F hPDF).2.2.2.2

  have hDFFD : Geo.Congruent D F F D :=
    (bookZero_congruenceFlip
      Geo D F D F
      (hilbert_congruent_reflexive Geo D F)).2.2

  have hDFFP : HilbertSegmentLess Geo D F F P :=
    ⟨D, hFDP, hDFFD⟩

  ----------------------------------------------------------------------
  -- Replace DF by the congruent segment PQ.
  ----------------------------------------------------------------------

  have hDFPQ : Geo.Congruent D F P Q :=
    hilbert_congruent_symmetry
      Geo P Q D F hPQDF

  have hPQFP : HilbertSegmentLess Geo P Q F P :=
    bookZero_32_lessThanCongruence2
      Geo
      D F F P P Q
      hDFFP
      hDFPQ

  ----------------------------------------------------------------------
  -- Reverse the larger segment FP to PF.
  ----------------------------------------------------------------------

  have hFPPF : Geo.Congruent F P P F :=
    (bookZero_congruenceFlip
      Geo F P F P
      (hilbert_congruent_reflexive Geo F P)).2.2

  have hPQPF : HilbertSegmentLess Geo P Q P F :=
    bookZero_30_lessThanCongruence
      Geo
      P Q F P P F
      hPQFP
      hFPPF

  ----------------------------------------------------------------------
  -- Q lies on ray PF, hence P-Q-F.
  ----------------------------------------------------------------------

  have hPDFRay : HilbertSameRay Geo P D F :=
    hilbert_sameRay_of_between
      Geo P D F hPDF

  have hPFQ : HilbertSameRay Geo P F Q :=
    bookZero_36_ray3
      Geo
      P D F Q
      hPDFRay
      hPDQ

  have hPQF_ray : HilbertSameRay Geo P Q F :=
    bookZero_39_ray5
      Geo P F Q hPFQ

  have hPQF : Geo.Between P Q F :=
    bookZero_51_lessThanBetween
      Geo P Q F
      hPQPF
      hPQF_ray

  ----------------------------------------------------------------------
  -- Derive C-P-Q and C-Q-F.
  ----------------------------------------------------------------------

  have hCPF : Geo.Between C P F :=
    bookZero_3_6b
      Geo C P D F
      hCPD
      hCDF

  have hCQF : Geo.Between C Q F :=
    bookZero_3_5b
      Geo C P Q F
      hCPF
      hPQF

  have hFQP : Geo.Between F Q P :=
    (HilbertOrder.between_incidence
      P Q F hPQF).2.2.2.2

  have hFPC : Geo.Between F P C :=
    (HilbertOrder.between_incidence
      C P F hCPF).2.2.2.2

  have hQPC : Geo.Between Q P C :=
    (hilbert_between_inner_trans
      Geo F Q P C
      hFQP
      hFPC).1

  have hCPQ : Geo.Between C P Q :=
    (HilbertOrder.between_incidence
      Q P C hQPC).2.2.2.2

  ----------------------------------------------------------------------
  -- CP + PQ is congruent to AB + BE.
  ----------------------------------------------------------------------

  have hCPAB : Geo.Congruent C P A B :=
    hilbert_congruent_symmetry
      Geo A B C P hABCP

  have hCQAE : Geo.Congruent C Q A E :=
    bookZero_sumOfParts
      Geo
      C P Q
      A B E
      hCPAB
      hPQBE
      hCPQ
      hABE

  have hAECQ : Geo.Congruent A E C Q :=
    hilbert_congruent_symmetry
      Geo C Q A E hCQAE

  exact ⟨Q, hCQF, hAECQ⟩

theorem bookZero_55_crossbar
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C E U V : Geo.Point)
    (hTriangle : ¬ PrimCollinear Geo A B C)
    (hAEC : Geo.Between A E C)
    (hBAU : HilbertSameRay Geo B A U)
    (hBCV : HilbertSameRay Geo B C V) :
    ∃ X : Geo.Point,
      HilbertSameRay Geo B E X ∧
      Geo.Between U X V := by

  ----------------------------------------------------------------------
  -- Basic nondegeneracy.
  ----------------------------------------------------------------------

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B C hTriangle

  rcases bookZero_23_NCorder Geo A B C hTriangle with
    ⟨_, hNCBCA, _, _, _⟩

  have hBC : B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C A hNCBCA

  ----------------------------------------------------------------------
  -- Construct P with B-A-P and AP congruent to BU.
  ----------------------------------------------------------------------

  rcases HilbertOrder.between_extension B A hAB.symm with
    ⟨R, hBAR⟩

  have hAR : A ≠ R :=
    (HilbertOrder.between_incidence B A R hBAR).2.1

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      B U
      A R
      hAR with
    ⟨P, hARP, hAPBU⟩

  have hABRay : HilbertSameRay Geo A B B :=
    hilbert_sameRay_refl Geo A B hAB.symm

  have hBAP : Geo.Between B A P :=
    hilbert_between_transport_sameRays
      Geo
      B A R
      B P
      hBAR
      hABRay
      hARP

  ----------------------------------------------------------------------
  -- Construct Q with B-C-Q and CQ congruent to BV.
  ----------------------------------------------------------------------

  rcases HilbertOrder.between_extension B C hBC with
    ⟨S, hBCS⟩

  have hCS : C ≠ S :=
    (HilbertOrder.between_incidence B C S hBCS).2.1

  rcases HilbertCongruence.segment_construction
      (Geo := Geo)
      B V
      C S
      hCS with
    ⟨Q, hCSQ, hCQBV⟩

  have hCBRay : HilbertSameRay Geo C B B :=
    hilbert_sameRay_refl Geo C B hBC

  have hBCQ : Geo.Between B C Q :=
    hilbert_between_transport_sameRays
      Geo
      B C S
      B Q
      hBCS
      hCBRay
      hCSQ

  have hQCB : Geo.Between Q C B :=
    (HilbertOrder.between_incidence
      B C Q hBCQ).2.2.2.2

  have hBCQcol : PrimCollinear Geo B C Q :=
    (HilbertOrder.between_incidence
      B C Q hBCQ).2.2.2.1

  have hBCC : PrimCollinear Geo B C C := by
    rcases hBCQcol with
      ⟨l, hBl, hCl, hQl⟩

    exact ⟨l, hBl, hCl, hCl⟩

  have hCQ : C ≠ Q :=
    (HilbertOrder.between_incidence
      B C Q hBCQ).2.1

  have hQC : Q ≠ C := by
    intro hQCeq
    exact hCQ hQCeq.symm

  ----------------------------------------------------------------------
  -- A, Q and C are noncollinear.
  ----------------------------------------------------------------------

  have hNCQCA : ¬ PrimCollinear Geo Q C A :=
    bookZero_27_NChelper
      Geo
      B C A Q C
      hNCBCA
      hBCQcol
      hBCC
      hQC

  have hNCAQC : ¬ PrimCollinear Geo A Q C := by
    intro hAQC

    rcases bookZero_22_collinearOrder
        Geo A Q C hAQC with
      ⟨_, hQCA, _, _, _⟩

    exact hNCQCA hQCA

  ----------------------------------------------------------------------
  -- First outer Pasch:
  --
  -- Q-C-B and A-E-C produce F with
  -- B-E-F and A-F-Q.
  ----------------------------------------------------------------------

  rcases
      hilbert_outer_pasch_strong
        Geo
        A Q C
        B E
        hNCAQC
        hQCB
        hAEC with
    ⟨F, hBEF, hAFQ⟩

  ----------------------------------------------------------------------
  -- Second outer Pasch.
  --
  -- First prove that B, P and Q are noncollinear.
  ----------------------------------------------------------------------

  have hBAPcol : PrimCollinear Geo B A P :=
    (HilbertOrder.between_incidence
      B A P hBAP).2.2.2.1

  have hBP : B ≠ P :=
    (HilbertOrder.between_incidence
      B A P hBAP).2.2.1

  have hBQ : B ≠ Q :=
    (HilbertOrder.between_incidence
      B C Q hBCQ).2.2.1

  have hBPA : PrimCollinear Geo B P A := by
    rcases bookZero_22_collinearOrder
        Geo B A P hBAPcol with
      ⟨_, _, _, hBPA, _⟩

    exact hBPA

  have hBPB : PrimCollinear Geo B P B := by
    rcases hBPA with
      ⟨l, hBl, hPl, hAl⟩

    exact ⟨l, hBl, hPl, hBl⟩

  have hBQC : PrimCollinear Geo B Q C := by
    rcases bookZero_22_collinearOrder
        Geo B C Q hBCQcol with
      ⟨_, _, _, hBQC, _⟩

    exact hBQC

  have hBQB : PrimCollinear Geo B Q B := by
    rcases hBQC with
      ⟨l, hBl, hQl, hCl⟩

    exact ⟨l, hBl, hQl, hBl⟩

  have hNCBPQ : ¬ PrimCollinear Geo B P Q := by
    intro hBPQ

    have hABQ : PrimCollinear Geo A B Q :=
      bookZero_25_collinear5
        Geo
        B P A B Q
        hBP
        hBPA
        hBPB
        hBPQ

    have hBQA : PrimCollinear Geo B Q A := by
      rcases bookZero_22_collinearOrder
          Geo A B Q hABQ with
        ⟨_, hBQA, _, _, _⟩

      exact hBQA

    have hABCcol : PrimCollinear Geo A B C :=
      bookZero_25_collinear5
        Geo
        B Q A B C
        hBQ
        hBQA
        hBQB
        hBQC

    exact hTriangle hABCcol

  ----------------------------------------------------------------------
  -- Hence Q, P and A are noncollinear.
  ----------------------------------------------------------------------

  have hAP : A ≠ P :=
    (HilbertOrder.between_incidence
      B A P hBAP).2.1

  have hAPB : PrimCollinear Geo A P B := by
    rcases bookZero_22_collinearOrder
        Geo B A P hBAPcol with
      ⟨_, hAPB, _, _, _⟩

    exact hAPB

  have hNCQPA : ¬ PrimCollinear Geo Q P A := by
    intro hQPA

    have hAPQ : PrimCollinear Geo A P Q := by
      rcases bookZero_22_collinearOrder
          Geo Q P A hQPA with
        ⟨_, _, _, _, hAPQ⟩

      exact hAPQ

    have hPBQ : PrimCollinear Geo P B Q :=
      bookZero_24_collinear4
        Geo
        A P B Q
        hAPB
        hAPQ
        hAP

    have hBPQ : PrimCollinear Geo B P Q :=
      bookZero_20_collinear1
        Geo P B Q hPBQ

    exact hNCBPQ hBPQ

  ----------------------------------------------------------------------
  -- Reverse the two betweenness hypotheses into the orientation
  -- required by outer Pasch.
  ----------------------------------------------------------------------

  have hPAB : Geo.Between P A B :=
    (HilbertOrder.between_incidence
      B A P hBAP).2.2.2.2

  have hQFA : Geo.Between Q F A :=
    (HilbertOrder.between_incidence
      A F Q hAFQ).2.2.2.2

  ----------------------------------------------------------------------
  -- Second outer Pasch:
  --
  -- triangle QPA, with P-A-B and Q-F-A,
  -- produces W such that B-F-W and Q-W-P.
  ----------------------------------------------------------------------

  rcases
      hilbert_outer_pasch_strong
        Geo
        Q P A
        B F
        hNCQPA
        hPAB
        hQFA with
    ⟨W, hBFW, hQWP⟩

  ----------------------------------------------------------------------
  -- Locate U between B and P.
  ----------------------------------------------------------------------

  have hBUAP : Geo.Congruent B U A P :=
    hilbert_congruent_symmetry
      Geo A P B U hAPBU

  have hBUPA : Geo.Congruent B U P A :=
    (bookZero_congruenceFlip
      Geo B U A P hBUAP).2.2

  have hBUPB : HilbertSegmentLess Geo B U P B :=
    ⟨A, hPAB, hBUPA⟩

  have hPBBP : Geo.Congruent P B B P :=
    (bookZero_congruenceFlip
      Geo P B P B
      (hilbert_congruent_reflexive Geo P B)).2.2

  have hBUBP : HilbertSegmentLess Geo B U B P :=
    bookZero_30_lessThanCongruence
      Geo
      B U P B B P
      hBUPB
      hPBBP

  have hBAPRay : HilbertSameRay Geo B A P :=
    hilbert_sameRay_of_between
      Geo B A P hBAP

  have hBPU : HilbertSameRay Geo B P U :=
    bookZero_36_ray3
      Geo
      B A P U
      hBAPRay
      hBAU

  have hBUP_ray : HilbertSameRay Geo B U P :=
    bookZero_39_ray5
      Geo B P U hBPU

  have hBUP : Geo.Between B U P :=
    bookZero_51_lessThanBetween
      Geo
      B U P
      hBUBP
      hBUP_ray

  ----------------------------------------------------------------------
  -- Locate V between B and Q.
  ----------------------------------------------------------------------

  have hBVCQ : Geo.Congruent B V C Q :=
    hilbert_congruent_symmetry
      Geo C Q B V hCQBV

  have hBVQC : Geo.Congruent B V Q C :=
    (bookZero_congruenceFlip
      Geo B V C Q hBVCQ).2.2

  have hBVQB : HilbertSegmentLess Geo B V Q B :=
    ⟨C, hQCB, hBVQC⟩

  have hQBBQ : Geo.Congruent Q B B Q :=
    (bookZero_congruenceFlip
      Geo Q B Q B
      (hilbert_congruent_reflexive Geo Q B)).2.2

  have hBVBQ : HilbertSegmentLess Geo B V B Q :=
    bookZero_30_lessThanCongruence
      Geo
      B V Q B B Q
      hBVQB
      hQBBQ

  have hBCQRay : HilbertSameRay Geo B C Q :=
    hilbert_sameRay_of_between
      Geo B C Q hBCQ

  have hBQV : HilbertSameRay Geo B Q V :=
    bookZero_36_ray3
      Geo
      B C Q V
      hBCQRay
      hBCV

  have hBVQ_ray : HilbertSameRay Geo B V Q :=
    bookZero_39_ray5
      Geo B Q V hBQV

  have hBVQ : Geo.Between B V Q :=
    bookZero_51_lessThanBetween
      Geo
      B V Q
      hBVBQ
      hBVQ_ray

  ----------------------------------------------------------------------
  -- We now have the two missing order relations from the BNW proof:
  --
  -- B-U-P
  -- B-V-Q
  --
  -- Next: first inner Pasch -> M,
  --       second inner Pasch -> H,
  --       then H lies on ray BE.
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- First inner Pasch.
  --
  -- From P-U-B and Q-W-P obtain M with
  -- B-M-W and Q-M-U.
  ----------------------------------------------------------------------

  have hUP : U ≠ P :=
    (HilbertOrder.between_incidence
      B U P hBUP).2.1

  have hUPB : PrimCollinear Geo U P B := by
    rcases bookZero_22_collinearOrder
        Geo B U P
        (HilbertOrder.between_incidence
          B U P hBUP).2.2.2.1 with
      ⟨_, hUPB, _, _, _⟩

    exact hUPB

  have hNCQPU : ¬ PrimCollinear Geo Q P U := by
    intro hQPU

    have hUPQ : PrimCollinear Geo U P Q := by
      rcases bookZero_22_collinearOrder
          Geo Q P U hQPU with
        ⟨_, _, _, _, hUPQ⟩

      exact hUPQ

    have hPBQ : PrimCollinear Geo P B Q :=
      bookZero_24_collinear4
        Geo
        U P B Q
        hUPB
        hUPQ
        hUP

    have hBPQ : PrimCollinear Geo B P Q :=
      bookZero_20_collinear1
        Geo P B Q hPBQ

    exact hNCBPQ hBPQ

  have hPUB : Geo.Between P U B :=
    (HilbertOrder.between_incidence
      B U P hBUP).2.2.2.2

  rcases
      hilbert_inner_pasch_strong
        Geo
        Q P U
        B W
        hNCQPU
        hPUB
        hQWP with
    ⟨M, hBMW, hQMU⟩

  ----------------------------------------------------------------------
  -- Prepare noncollinearity B-Q-M for the second inner Pasch.
  ----------------------------------------------------------------------

  have hBU : B ≠ U :=
    (HilbertOrder.between_incidence
      B U P hBUP).1

  have hBPUcol : PrimCollinear Geo B P U := by
    rcases bookZero_22_collinearOrder
        Geo B U P
        (HilbertOrder.between_incidence
          B U P hBUP).2.2.2.1 with
      ⟨_, _, _, hBPUcol, _⟩

    exact hBPUcol

  have hNCBUQ : ¬ PrimCollinear Geo B U Q :=
    bookZero_27_NChelper
      Geo
      B P Q
      B U
      hNCBPQ
      hBPB
      hBPUcol
      hBU

  have hNCUQB : ¬ PrimCollinear Geo U Q B := by
    rcases bookZero_23_NCorder
        Geo B U Q hNCBUQ with
      ⟨_, hNCUQB, _, _, _⟩

    exact hNCUQB

  have hQMUcol : PrimCollinear Geo Q M U :=
    (HilbertOrder.between_incidence
      Q M U hQMU).2.2.2.1

  have hUQMcol : PrimCollinear Geo U Q M := by
    rcases bookZero_22_collinearOrder
        Geo Q M U hQMUcol with
      ⟨_, _, hUQMcol, _, _⟩

    exact hUQMcol

  have hUQQcol : PrimCollinear Geo U Q Q := by
    rcases hUQMcol with
      ⟨l, hUl, hQl, hMl⟩

    exact ⟨l, hUl, hQl, hQl⟩

  have hMQ : M ≠ Q := by
    have hQM : Q ≠ M :=
      (HilbertOrder.between_incidence
        Q M U hQMU).1

    exact hQM.symm

  have hNCMQB : ¬ PrimCollinear Geo M Q B :=
    bookZero_27_NChelper
      Geo
      U Q B
      M Q
      hNCUQB
      hUQMcol
      hUQQcol
      hMQ

  have hNCBQM : ¬ PrimCollinear Geo B Q M := by
    rcases bookZero_23_NCorder
        Geo M Q B hNCMQB with
      ⟨_, _, _, _, hNCBQM⟩

    exact hNCBQM

  ----------------------------------------------------------------------
  -- Second inner Pasch.
  --
  -- From Q-M-U and B-V-Q obtain H with
  -- U-H-V and B-H-M.
  ----------------------------------------------------------------------

  rcases
      hilbert_inner_pasch_strong
        Geo
        B Q M
        U V
        hNCBQM
        hQMU
        hBVQ with
    ⟨H, hUHV, hBHM⟩

  ----------------------------------------------------------------------
  -- Show that H lies on ray BE.
  ----------------------------------------------------------------------

  have hBEW : Geo.Between B E W :=
    bookZero_3_6b
      Geo
      B E F W
      hBEF
      hBFW

  have hBHW : Geo.Between B H W :=
    bookZero_3_6b
      Geo
      B H M W
      hBHM
      hBMW

  have hBEWray : HilbertSameRay Geo B E W :=
    hilbert_sameRay_of_between
      Geo B E W hBEW

  have hBWE : HilbertSameRay Geo B W E :=
    bookZero_39_ray5
      Geo B E W hBEWray

  have hBHWray : HilbertSameRay Geo B H W :=
    hilbert_sameRay_of_between
      Geo B H W hBHW

  have hBWH : HilbertSameRay Geo B W H :=
    bookZero_39_ray5
      Geo B H W hBHWray

  have hBEH : HilbertSameRay Geo B E H :=
    bookZero_36_ray3
      Geo
      B W E H
      hBWE
      hBWH

  exact ⟨H, hBEH, hUHV⟩


end Geometry

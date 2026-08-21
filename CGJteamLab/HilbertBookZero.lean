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

/-
Hilbert segment subtraction.

If B lies between A and C, b lies between a and c,
AB is congruent to ab, and AC is congruent to ac,
then BC is congruent to bc.

This is the cancellation counterpart of Hilbert III.3.
-/
/-
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
-/

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




/-
If A-B-D and C is not on line AD, then A and B lie on the same
side of line CD.

This is a pure incidence/order fact.
-/
/-
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
-/

/-
If A-B-C, the three corresponding segments of the triples
(A,B,C) and (a,b,c) are congruent, and a != b, then a,b,c
are collinear.

The explicit nondegeneracy assumption `a != b` belongs to the
Hilbert formulation: segment construction is performed on a genuine
ray. The BNW formulation derives it using its null-segment theory.
-/
/-
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
-/

/-
A proper part of a segment is not congruent to the whole segment.

If B lies between A and C, then AB is not congruent to AC.
-/

/-
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
-/

------------------------------------------------------------------------
-- Order of segments
------------------------------------------------------------------------

/-
Hilbert's strict comparison of segments.

`HilbertSegmentLess Geo A B C D` means that the segment AB is
congruent to a proper initial part CP of the segment CD.
-/
/-
def HilbertSegmentLess
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point) : Prop :=
  ∃ P : Geo.Point,
    Geo.Between C P D ∧
    Geo.Congruent A B C P
-/

/-
Hilbert segment order is preserved under congruence of the
smaller segment.

Hilbert Theorem 24, left transport.
-/
/-
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
-/
/-
A segment strictly smaller than another segment cannot be congruent
to it.

This follows directly from Hilbert's definition of segment order and
the fact that a proper part is not congruent to the whole segment.
-/
/-
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
-/
/-
A proper initial part of a segment is strictly smaller than
the whole segment.

If C-P-D, then CP < CD.
-/
/-
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
-/

/-
Hilbert Theorem 25(I): asymmetry of strict segment comparison.

If AB < CD, then CD is not smaller than AB.

The proof uses only segment additivity, construction on a ray,
the order calculus, and uniqueness of segment construction.
-/
/-
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
-/

/-
Collinear part of the three-point case of Hilbert's Theorem 27.

If A-B-C, the triples (A,B,C) and (a,b,c) have congruent
corresponding segments, and a,b,c are distinct and collinear,
then a-b-c.
-/
/-
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
-/
/-
Three-point case of Hilbert's Theorem 27.

Congruent triples preserve betweenness, provided the corresponding
Hilbert segments are genuine, i.e. the points a, b, c are pairwise
distinct.
-/
/-
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

-/

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
/--
The nondegenerate case of the BNW five-line principle.

If D is not on the line AB, the result follows from SSS for
triangles ABD and abd, Hilbert's supplementary-angle theorem,
and SAS for triangles CBD and cbd.
-/
theorem bookZero_fiveLine_nondegenerate
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hBD : Geo.Congruent B D b d)
    (hABD : ¬ Collinear Geo A B D) :
    Geo.Congruent C D c d := by

  ----------------------------------------------------------------------
  -- SSS for ABD and abd.
  ----------------------------------------------------------------------

  have hSSS :=
    HilbertSSS
      Geo
      A B D
      a b d
      hABD
      hAB
      hBD
      hAD

  have habd : ¬ Collinear Geo a b d :=
    hSSS.1

  have hAngleABD :
      Geo.AngleCongruent A B D a b d :=
    hSSS.2.angleB

  ----------------------------------------------------------------------
  -- The supplementary angles DBC and dbc are congruent.
  ----------------------------------------------------------------------

  have hAngleDBC :
      Geo.AngleCongruent D B C d b c :=
    hilbert_adjacent_angles_congruent
      Geo
      A B D C
      a b d c
      hABC
      habc
      hABD
      habd
      hAngleABD

  have hAngleCBD :
      Geo.AngleCongruent C B D c b d :=
    AngleCongruentReverse
      Geo
      D B C
      d b c
      hAngleDBC

  ----------------------------------------------------------------------
  -- C,B,D and c,b,d are noncollinear.
  ----------------------------------------------------------------------

  have hCBD : ¬ Collinear Geo C B D := by
    intro hCBD

    have hABCcol : Collinear Geo A B C :=
      (HilbertOrder.between_incidence
        A B C hABC).2.2.2.1

    have hBCne : B ≠ C :=
      (HilbertOrder.between_incidence
        A B C hABC).2.1

    rcases hABCcol with
      ⟨l, hAl, hBl, hCl⟩

    rcases hCBD with
      ⟨m, hCm, hBm, hDm⟩

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        B C
        hBCne
        l m
        hBl hCl
        hBm hCm

    subst m

    exact hABD ⟨l, hAl, hBl, hDm⟩

  have hcbd : ¬ Collinear Geo c b d := by
    intro hcbd

    have habccol : Collinear Geo a b c :=
      (HilbertOrder.between_incidence
        a b c habc).2.2.2.1

    have hbcne : b ≠ c :=
      (HilbertOrder.between_incidence
        a b c habc).2.1

    rcases habccol with
      ⟨l, hal, hbl, hcl⟩

    rcases hcbd with
      ⟨m, hcm, hbm, hdm⟩

    have hlm : l = m :=
      HilbertPlaneIncidence.line_unique
        b c
        hbcne
        l m
        hbl hcl
        hbm hcm

    subst m

    exact habd ⟨l, hal, hbl, hdm⟩

  ----------------------------------------------------------------------
  -- SAS for CBD and cbd.
  ----------------------------------------------------------------------

  have hCBcb : Geo.Congruent C B c b :=
    CongruentReverseBoth
      Geo
      B C
      b c
      hBC

  have hBCD : ¬ Collinear Geo B C D := by
    intro hBCDcol
    exact hCBD (PrimCollinearSwap Geo B C D hBCDcol)

  have hbcd : ¬ Collinear Geo b c d := by
    intro hbcdcol
    exact hcbd (PrimCollinearSwap Geo b c d hbcdcol)

  have hTriangles :=
    SAS
      Geo
      B C D
      b c d
      hBCD
      hbcd
      hBC
      hAngleCBD
      hBD

  exact hTriangles.sideBC

/--
Collinearity transfers across three pairwise congruent distances.

This is the first step in the collinear case of `bookZero_fiveLine`.
-/
theorem bookZero_collinearTriple_transfer
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B D a b d : Geo.Point)
    (hABDcol : Collinear Geo A B D)
    (hAB : Geo.Congruent A B a b)
    (hAD : Geo.Congruent A D a d)
    (hBD : Geo.Congruent B D b d) :
    Collinear Geo a b d := by

  ----------------------------------------------------------------------
  -- Degenerate source segments.
  ----------------------------------------------------------------------

  by_cases hABeq : A = B

  · subst B

    have habEq : a = b :=
      bookZero_nullSegment1
        Geo
        a b A
        (hilbert_congruent_symmetry
          Geo A A a b hAB)

    subst b

    by_cases hadEq : a = d

    · subst d

      rcases hilbert_line_through_point Geo a with
        ⟨l, hal⟩

      exact ⟨l, hal, hal, hal⟩

    · rcases
          HilbertPlaneIncidence.line_through
            a d hadEq with
        ⟨l, hal, hdl⟩

      exact ⟨l, hal, hal, hdl⟩

  · by_cases hADeq : A = D

    · subst D

      have hadEq : a = d :=
        bookZero_nullSegment1
          Geo
          a d A
          (hilbert_congruent_symmetry
            Geo A A a d hAD)

      subst d

      by_cases habEq : a = b

      · subst b

        rcases hilbert_line_through_point Geo a with
          ⟨l, hal⟩

        exact ⟨l, hal, hal, hal⟩

      · rcases
            HilbertPlaneIncidence.line_through
              a b habEq with
          ⟨l, hal, hbl⟩

        exact ⟨l, hal, hbl, hal⟩

    · by_cases hBDeq : B = D

      · subst D

        have hbdEq : b = d :=
          bookZero_nullSegment1
            Geo
            b d B
            (hilbert_congruent_symmetry
              Geo B B b d hBD)

        subst d

        by_cases habEq : a = b

        · subst b

          rcases hilbert_line_through_point Geo a with
            ⟨l, hal⟩

          exact ⟨l, hal, hal, hal⟩

        · rcases
              HilbertPlaneIncidence.line_through
                a b habEq with
            ⟨l, hal, hbl⟩

          exact ⟨l, hal, hbl, hbl⟩

      ------------------------------------------------------------------
      -- Nondegenerate collinear triples.
      ------------------------------------------------------------------

      · have hab : a ≠ b :=
          bookZero_nullSegment3
            Geo A B a b hABeq hAB

        have had : a ≠ d :=
          bookZero_nullSegment3
            Geo A D a d hADeq hAD

        have hbd : b ≠ d :=
          bookZero_nullSegment3
            Geo B D b d hBDeq hBD

        rcases
            hilbert_between_trichotomy
              Geo
              A B D
              hABeq
              hBDeq
              hADeq
              hABDcol with
          hABD | hBAD | hADB

        ----------------------------------------------------------------
        -- A-B-D transfers to a-b-d.
        ----------------------------------------------------------------

        · have habd : Geo.Between a b d :=
            bookZero_17_three_points
              Geo
              A B D
              a b d
              hABD
              hab
              hbd
              had
              hAB
              hAD
              hBD

          exact
            (HilbertOrder.between_incidence
              a b d habd).2.2.2.1

        ----------------------------------------------------------------
        -- B-A-D transfers to b-a-d.
        ----------------------------------------------------------------

        · have hBAba : Geo.Congruent B A b a :=
            CongruentReverseBoth
              Geo
              A B
              a b
              hAB

          have hBAbd : Geo.Congruent B D b d :=
            hBD

          have hADad : Geo.Congruent A D a d :=
            hAD

          have hbad : Geo.Between b a d :=
            bookZero_17_three_points
              Geo
              B A D
              b a d
              hBAD
              hab.symm
              had
              hbd
              hBAba
              hBAbd
              hADad

          have hbadCol : Collinear Geo b a d :=
            (HilbertOrder.between_incidence
              b a d hbad).2.2.2.1

          exact
            PrimCollinearSwap
              Geo b a d hbadCol

        ----------------------------------------------------------------
        -- A-D-B transfers to a-d-b.
        ----------------------------------------------------------------

        · have hDBdb : Geo.Congruent D B d b :=
            CongruentReverseBoth
              Geo
              B D
              b d
              hBD

          have hadb : Geo.Between a d b :=
            bookZero_17_three_points
              Geo
              A D B
              a d b
              hADB
              had
              hbd.symm
              hab
              hAD
              hAB
              hDBdb

          have hadbCol : Collinear Geo a d b :=
            (HilbertOrder.between_incidence
              a d b hadb).2.2.2.1

          exact
            PrimCollinearRotate
              Geo a d b hadbCol




/--
The collinear case of the BNW five-line principle.

If A, B and D are collinear, the conclusion follows entirely from
betweenness, segment addition and subtraction, without triangle
congruence.
-/
theorem bookZero_fiveLine_collinear
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hBD : Geo.Congruent B D b d)
    (hABDcol : Collinear Geo A B D) :
    Geo.Congruent C D c d := by

  have hABne : A ≠ B :=
    (HilbertOrder.between_incidence
      A B C hABC).1

  have habne : a ≠ b :=
    bookZero_nullSegment3
      Geo A B a b hABne hAB

  ----------------------------------------------------------------------
  -- Degenerate case D = A.
  ----------------------------------------------------------------------

  by_cases hADeq : A = D

  · subst D

    have hadeq : a = d :=
      bookZero_nullSegment1
        Geo
        a d A
        (hilbert_congruent_symmetry
          Geo A A a d hAD)

    subst d

    have hACac : Geo.Congruent A C a c :=
      bookZero_sumOfParts
        Geo
        A B C
        a b c
        hAB
        hBC
        hABC
        habc

    exact
      CongruentReverseBoth
        Geo A C a c hACac

  ----------------------------------------------------------------------
  -- Degenerate case D = B.
  ----------------------------------------------------------------------

  · by_cases hBDeq : B = D

    · subst D

      have hbdeq : b = d :=
        bookZero_nullSegment1
          Geo
          b d B
          (hilbert_congruent_symmetry
            Geo B B b d hBD)

      subst d

      exact
        CongruentReverseBoth
          Geo B C b c hBC

    --------------------------------------------------------------------
    -- Nondegenerate collinear triples.
    --------------------------------------------------------------------

    · have habdCol : Collinear Geo a b d :=
        bookZero_collinearTriple_transfer
          Geo
          A B D
          a b d
          hABDcol
          hAB
          hAD
          hBD

      have hadne : a ≠ d :=
        bookZero_nullSegment3
          Geo A D a d hADeq hAD

      have hbdne : b ≠ d :=
        bookZero_nullSegment3
          Geo B D b d hBDeq hBD

      rcases
          hilbert_between_trichotomy
            Geo
            A B D
            hABne
            hBDeq
            hADeq
            hABDcol with
        hABD | hBAD | hADB

      ------------------------------------------------------------------
      -- Case A-B-D.
      ------------------------------------------------------------------

      · have habd : Geo.Between a b d :=
          bookZero_17_three_points
            Geo
            A B D
            a b d
            hABD
            habne
            hbdne
            hadne
            hAB
            hAD
            hBD

        by_cases hBCD : Geo.Between B C D

        --------------------------------------------------------------
        -- Case B-C-D.
        --------------------------------------------------------------

        · rcases
              HilbertOrder.between_extension
                b c
                ((HilbertOrder.between_incidence
                  a b c habc).2.1) with
            ⟨r, hbcr⟩

          have hcr : c ≠ r :=
            (HilbertOrder.between_incidence
              b c r hbcr).2.1

          rcases
              HilbertCongruence.segment_construction
                (Geo := Geo)
                C D
                c r
                hcr with
            ⟨e, hcre, hceCD⟩

          have hcbRay : HilbertSameRay Geo c b b :=
            hilbert_sameRay_refl
              Geo
              c b
              ((HilbertOrder.between_incidence
                a b c habc).2.1)

          have hbce : Geo.Between b c e :=
            hilbert_between_transport_sameRays
              Geo
              b c r
              b e
              hbcr
              hcbRay
              hcre

          have hCDce : Geo.Congruent C D c e :=
            hilbert_congruent_symmetry
              Geo c e C D hceCD

          have hBDbe : Geo.Congruent B D b e :=
            bookZero_sumOfParts
              Geo
              B C D
              b c e
              hBC
              hCDce
              hBCD
              hbce

          have hbed : Geo.Congruent b e b d :=
            hilbert_congruent_transitivity
              Geo
              b e
              B D
              b d
              (hilbert_congruent_symmetry
                Geo B D b e hBDbe)
              hBD

          have habe : Geo.Between a b e :=
            bookZero_3_7b
              Geo
              a b c e
              habc
              hbce

          have hed : e = d :=
            bookZero_extensionUnique
              Geo
              a b e d
              habe
              habd
              hbed

          subst e

          exact
            hilbert_congruent_symmetry
              Geo c d C D hceCD

        · by_cases hBDC : Geo.Between B D C

          ------------------------------------------------------------
          -- Case B-D-C.
          ------------------------------------------------------------

          · rcases
                HilbertOrder.between_extension
                  b d hbdne with
              ⟨r, hbdr⟩

            have hdr : d ≠ r :=
              (HilbertOrder.between_incidence
                b d r hbdr).2.1

            rcases
                HilbertCongruence.segment_construction
                  (Geo := Geo)
                  D C
                  d r
                  hdr with
              ⟨e, hdre, hdeDC⟩

            have hdbRay : HilbertSameRay Geo d b b :=
              hilbert_sameRay_refl
                Geo d b hbdne

            have hbde : Geo.Between b d e :=
              hilbert_between_transport_sameRays
                Geo
                b d r
                b e
                hbdr
                hdbRay
                hdre

            have hDCde : Geo.Congruent D C d e :=
              hilbert_congruent_symmetry
                Geo d e D C hdeDC

            have hBCbe : Geo.Congruent B C b e :=
              bookZero_sumOfParts
                Geo
                B D C
                b d e
                hBD
                hDCde
                hBDC
                hbde

            have hbebc : Geo.Congruent b e b c :=
              hilbert_congruent_transitivity
                Geo
                b e
                B C
                b c
                (hilbert_congruent_symmetry
                  Geo B C b e hBCbe)
                hBC

            have habe : Geo.Between a b e :=
              bookZero_3_7b
                Geo
                a b d e
                habd
                hbde

            have hec : e = c :=
              bookZero_extensionUnique
                Geo
                a b e c
                habe
                habc
                hbebc

            subst e

            have hDCdc : Geo.Congruent D C d c :=
              hilbert_congruent_symmetry
                Geo d c D C hdeDC

            exact
              CongruentReverseBoth
                Geo D C d c hDCdc

          ------------------------------------------------------------
          -- Neither B-C-D nor B-D-C.
          --
          -- Outer connectivity gives C = D.
          ------------------------------------------------------------

          · have hCD : C = D :=
              bookZero_18_outerConnectivity
                Geo
                A B C D
                hABC
                hABD
                hBCD
                hBDC

            subst D

            have hbcbd : Geo.Congruent b c b d :=
              hilbert_congruent_transitivity
                Geo
                b c
                B C
                b d
                (hilbert_congruent_symmetry
                  Geo B C b c hBC)
                hBD

            have hcd : c = d :=
              bookZero_extensionUnique
                Geo
                a b c d
                habc
                habd
                hbcbd

            subst d

            exact
              bookZero_nullSegment2
                Geo C c

      ------------------------------------------------------------------
      -- Case B-A-D, hence D-A-B-C.
      ------------------------------------------------------------------

      · have hBAba : Geo.Congruent B A b a :=
          CongruentReverseBoth
            Geo A B a b hAB

        have hbad : Geo.Between b a d :=
          bookZero_17_three_points
            Geo
            B A D
            b a d
            hBAD
            habne.symm
            hadne
            hbdne
            hBAba
            hBD
            hAD

        have hDAB : Geo.Between D A B :=
          (HilbertOrder.between_incidence
            B A D hBAD).2.2.2.2

        have hdab : Geo.Between d a b :=
          (HilbertOrder.between_incidence
            b a d hbad).2.2.2.2

        have hDAda : Geo.Congruent D A d a :=
          CongruentReverseBoth
            Geo A D a d hAD

        have hDBdb : Geo.Congruent D B d b :=
          bookZero_sumOfParts
            Geo
            D A B
            d a b
            hDAda
            hAB
            hDAB
            hdab

        have hDBC : Geo.Between D B C :=
          bookZero_3_7a
            Geo D A B C hDAB hABC

        have hdbc : Geo.Between d b c :=
          bookZero_3_7a
            Geo d a b c hdab habc

        have hDCdc : Geo.Congruent D C d c :=
          bookZero_sumOfParts
            Geo
            D B C
            d b c
            hDBdb
            hBC
            hDBC
            hdbc

        exact
          CongruentReverseBoth
            Geo D C d c hDCdc

      ------------------------------------------------------------------
      -- Case A-D-B, hence D-B-C.
      ------------------------------------------------------------------

      · have hDBdb : Geo.Congruent D B d b :=
          CongruentReverseBoth
            Geo B D b d hBD

        have hadb : Geo.Between a d b :=
          bookZero_17_three_points
            Geo
            A D B
            a d b
            hADB
            hadne
            hbdne.symm
            habne
            hAD
            hAB
            hDBdb

        have hDBC : Geo.Between D B C :=
          bookZero_3_6a
            Geo A D B C hADB hABC

        have hdbc : Geo.Between d b c :=
          bookZero_3_6a
            Geo a d b c hadb habc

        have hDCdc : Geo.Congruent D C d c :=
          bookZero_sumOfParts
            Geo
            D B C
            d b c
            hDBdb
            hBC
            hDBC
            hdbc

        exact
          CongruentReverseBoth
            Geo D C d c hDCdc

/-
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
-/
theorem bookZero_fiveLine
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c D d : Geo.Point)
    (hABC : Geo.Between A B C)
    (habc : Geo.Between a b c)
    (hAB : Geo.Congruent A B a b)
    (hBC : Geo.Congruent B C b c)
    (hAD : Geo.Congruent A D a d)
    (hBD : Geo.Congruent B D b d) :
    Geo.Congruent C D c d := by

  by_cases hABD : Collinear Geo A B D

  · exact
      bookZero_fiveLine_collinear
        Geo
        A B C
        a b c
        D d
        hABC
        habc
        hAB
        hBC
        hAD
        hBD
        hABD

  · exact
      bookZero_fiveLine_nondegenerate
        Geo
        A B C
        a b c
        D d
        hABC
        habc
        hAB
        hBC
        hAD
        hBD
        hABD
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

/--
Book Zero #56: ABCequalsCBA.

An angle is congruent to the angle obtained by reversing its two rays.
-/
theorem bookZero_56_ABCequalsCBA
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C) :
    Geo.AngleCongruent A B C C B A := by

  have hRefl :
      Geo.AngleCongruent A B C A B C :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo) A B C hABC

  exact
    (Geo.angle_congruent_reverse_second
      A B C A B C).mp hRefl

/--
Book Zero #57: equalanglessymmetric.

Angle congruence is symmetric.
-/
theorem bookZero_57_equalAnglesSymmetric
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hAngle : Geo.AngleCongruent A B C D E F) :
    Geo.AngleCongruent D E F A B C := by

  exact
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A B C
      D E F
      hAngle

/--
Book Zero #58: angledistinct.

The endpoints of two nondegenerate congruent angles
are pairwise distinct.
-/
theorem bookZero_58_angleDistinct
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (_hAngle : Geo.AngleCongruent A B C a b c)
    (hABC : ¬ PrimCollinear Geo A B C)
    (habc : ¬ PrimCollinear Geo a b c) :
    A ≠ B ∧
    B ≠ C ∧
    A ≠ C ∧
    a ≠ b ∧
    b ≠ c ∧
    a ≠ c := by

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  rcases bookZero_23_NCorder Geo A B C hABC with
    ⟨_, hBCA, _, hACB, _⟩

  have hBC : B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C A hBCA

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  have hab : a ≠ b :=
    hilbert_noncollinear_ne_first
      Geo a b c habc

  rcases bookZero_23_NCorder Geo a b c habc with
    ⟨_, hbca, _, hacb, _⟩

  have hbc : b ≠ c :=
    hilbert_noncollinear_ne_first
      Geo b c a hbca

  have hac : a ≠ c :=
    hilbert_noncollinear_ne_first
      Geo a c b hacb

  exact ⟨hAB, hBC, hAC, hab, hbc, hac⟩

/--
Book Zero #59: 4.19.

If A-D-B, AC is congruent to AD, and BD is congruent to BC,
then C = D.
-/
theorem bookZero_59_4_19
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hADB : Geo.Between A D B)
    (hACAD : Geo.Congruent A C A D)
    (hBDBC : Geo.Congruent B D B C) :
    C = D := by

  have hADAD : Geo.Congruent A D A D :=
    hilbert_congruent_reflexive Geo A D

  have hDBDB : Geo.Congruent D B D B :=
    hilbert_congruent_reflexive Geo D B

  have hBCBD : Geo.Congruent B C B D :=
    hilbert_congruent_symmetry
      Geo B D B C hBDBC

  have hDCDD : Geo.Congruent D C D D :=
    bookZero_19_interior5
      Geo
      A D B
      A D B
      C D
      hADB
      hADB
      hADAD
      hDBDB
      hACAD
      hBCBD

  have hDC : D = C :=
    bookZero_nullSegment1
      Geo D C D hDCDD

  exact hDC.symm

/--
Book Zero #60: collinearbetween.

Let A,E,B lie on one line and C,F,D on a disjoint line.
If H lies between A and D and E,F,H are collinear,
then H lies between E and F.
-/
theorem bookZero_60_collinearBetween
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A B C D E F H : Geo.Point)
    (l m : Geo.Line)
    (hAl : HilbertIncidence.OnLine A l)
    (_hBl : HilbertIncidence.OnLine B l)
    (hEl : HilbertIncidence.OnLine E l)
    (_hCm : HilbertIncidence.OnLine C m)
    (hDm : HilbertIncidence.OnLine D m)
    (hFm : HilbertIncidence.OnLine F m)
    (_hAB : A ≠ B)
    (_hCD : C ≠ D)
    (hAE : A ≠ E)
    (hFD : F ≠ D)
    (hDisjoint : HilbertLinesDisjoint Geo l m)
    (hAHD : Geo.Between A H D)
    (hEFHcol : PrimCollinear Geo E F H) :
    Geo.Between E H F := by

  ----------------------------------------------------------------------
  -- The three points E, F, H are pairwise distinct.
  ----------------------------------------------------------------------

  have hEF : E ≠ F := by
    intro hEq
    subst F

    exact hDisjoint ⟨E, hEl, hFm⟩

  have hAH : A ≠ H :=
    (HilbertOrder.between_incidence
      A H D hAHD).1

  have hHD : H ≠ D :=
    (HilbertOrder.between_incidence
      A H D hAHD).2.1

  have hAHDcol : PrimCollinear Geo A H D :=
    (HilbertOrder.between_incidence
      A H D hAHD).2.2.2.1

  have hEH : E ≠ H := by
    intro hEq
    subst H

    have hAEDcol : PrimCollinear Geo A E D := by
      simpa using hAHDcol

    have hDl : HilbertIncidence.OnLine D l :=
      hilbert_collinear_on_line
        Geo
        A E D
        l
        hAE
        hAl
        hEl
        hAEDcol

    exact hDisjoint ⟨D, hDl, hDm⟩

  have hFH : F ≠ H := by
    intro hEq
    subst H

    have hAFDcol : PrimCollinear Geo A F D := by
      simpa using hAHDcol

    have hFDAcol : PrimCollinear Geo F D A := by
      rcases bookZero_22_collinearOrder
          Geo A F D hAFDcol with
        ⟨_, hFDAcol, _, _, _⟩

      exact hFDAcol

    have hAm : HilbertIncidence.OnLine A m :=
      hilbert_collinear_on_line
        Geo
        F D A
        m
        hFD
        hFm
        hDm
        hFDAcol

    exact hDisjoint ⟨A, hAl, hAm⟩

  ----------------------------------------------------------------------
  -- Order trichotomy on the collinear triple E,F,H.
  ----------------------------------------------------------------------

  rcases
      hilbert_between_trichotomy
        Geo
        E F H
        hEF
        hFH
        hEH
        hEFHcol with
    hEFH | hFEH | hEHF

  ----------------------------------------------------------------------
  -- Case E-F-H.
  --
  -- Outer Pasch produces a common point of l and m.
  ----------------------------------------------------------------------

  · have hNCEAH : ¬ PrimCollinear Geo E A H := by
      intro hEAH

      have hHl : HilbertIncidence.OnLine H l :=
        hilbert_collinear_on_line
          Geo
          E A H
          l
          hAE.symm
          hEl
          hAl
          hEAH

      have hDl : HilbertIncidence.OnLine D l :=
        hilbert_collinear_on_line
          Geo
          A H D
          l
          hAH
          hAl
          hHl
          hAHDcol

      exact hDisjoint ⟨D, hDl, hDm⟩

    rcases
        hilbert_outer_pasch_strong
          Geo
          E A H
          D F
          hNCEAH
          hAHD
          hEFH with
      ⟨Q, hDFQ, hEQA⟩

    have hDFQcol : PrimCollinear Geo D F Q :=
      (HilbertOrder.between_incidence
        D F Q hDFQ).2.2.2.1

    have hQm : HilbertIncidence.OnLine Q m :=
      hilbert_collinear_on_line
        Geo
        D F Q
        m
        hFD.symm
        hDm
        hFm
        hDFQcol

    have hEQAcol : PrimCollinear Geo E Q A :=
      (HilbertOrder.between_incidence
        E Q A hEQA).2.2.2.1

    have hEAQcol : PrimCollinear Geo E A Q := by
      rcases bookZero_22_collinearOrder
          Geo E Q A hEQAcol with
        ⟨_, _, _, hEAQcol, _⟩

      exact hEAQcol

    have hQl : HilbertIncidence.OnLine Q l :=
      hilbert_collinear_on_line
        Geo
        E A Q
        l
        hAE.symm
        hEl
        hAl
        hEAQcol

    exact False.elim (hDisjoint ⟨Q, hQl, hQm⟩)

  ----------------------------------------------------------------------
  -- Case F-E-H.
  --
  -- The other orientation of outer Pasch again produces
  -- a common point of l and m.
  ----------------------------------------------------------------------

  · have hNCFDH : ¬ PrimCollinear Geo F D H := by
      intro hFDH

      have hHm : HilbertIncidence.OnLine H m :=
        hilbert_collinear_on_line
          Geo
          F D H
          m
          hFD
          hFm
          hDm
          hFDH

      have hDHAcol : PrimCollinear Geo D H A := by
        rcases bookZero_22_collinearOrder
            Geo A H D hAHDcol with
          ⟨_, _, _, _, hDHAcol⟩

        exact hDHAcol

      have hAm : HilbertIncidence.OnLine A m :=
        hilbert_collinear_on_line
          Geo
          D H A
          m
          hHD.symm
          hDm
          hHm
          hDHAcol

      exact hDisjoint ⟨A, hAl, hAm⟩

    have hDHA : Geo.Between D H A :=
      (HilbertOrder.between_incidence
        A H D hAHD).2.2.2.2

    rcases
        hilbert_outer_pasch_strong
          Geo
          F D H
          A E
          hNCFDH
          hDHA
          hFEH with
      ⟨R, hAER, hFRD⟩

    have hAERcol : PrimCollinear Geo A E R :=
      (HilbertOrder.between_incidence
        A E R hAER).2.2.2.1

    have hRl : HilbertIncidence.OnLine R l :=
      hilbert_collinear_on_line
        Geo
        A E R
        l
        hAE
        hAl
        hEl
        hAERcol

    have hFRDcol : PrimCollinear Geo F R D :=
      (HilbertOrder.between_incidence
        F R D hFRD).2.2.2.1

    have hFDRcol : PrimCollinear Geo F D R := by
      rcases bookZero_22_collinearOrder
          Geo F R D hFRDcol with
        ⟨_, _, _, hFDRcol, _⟩

      exact hFDRcol

    have hRm : HilbertIncidence.OnLine R m :=
      hilbert_collinear_on_line
        Geo
        F D R
        m
        hFD
        hFm
        hDm
        hFDRcol

    exact False.elim (hDisjoint ⟨R, hRl, hRm⟩)

  ----------------------------------------------------------------------
  -- The only remaining order is E-H-F.
  ----------------------------------------------------------------------

  · exact hEHF

/--
Book Zero #61: 9.5a.

If P and C are on opposite sides of line l,
R lies on l, P lies between R and Q, and R,Q,C
are noncollinear, then Q and C are on opposite sides of l.
-/
theorem bookZero_61_9_5a
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (P C R Q : Geo.Point)
    (l : Geo.Line)
    (hOppPC : HilbertOppositeSide Geo P C l)
    (hRPQ : Geo.Between R P Q)
    (hRQC : ¬ PrimCollinear Geo R Q C)
    (hRl : HilbertIncidence.OnLine R l) :
    HilbertOppositeSide Geo Q C l := by

  ----------------------------------------------------------------------
  -- Unpack P and C being on opposite sides of l.
  --
  -- There is S on l with P-S-C.
  ----------------------------------------------------------------------

  rcases hOppPC with
    ⟨hPnotl, hCnotl, S, hPSC, hSl⟩

  ----------------------------------------------------------------------
  -- Q does not lie on l.
  --
  -- Otherwise R,Q lie on l, and R-P-Q puts P on l.
  ----------------------------------------------------------------------

  have hRQ : R ≠ Q :=
    (HilbertOrder.between_incidence
      R P Q hRPQ).2.2.1

  have hRPQcol : PrimCollinear Geo R P Q :=
    (HilbertOrder.between_incidence
      R P Q hRPQ).2.2.2.1

  have hRQPcol : PrimCollinear Geo R Q P := by
    rcases bookZero_22_collinearOrder
        Geo R P Q hRPQcol with
      ⟨_, _, _, hRQPcol, _⟩

    exact hRQPcol

  have hQnotl : ¬ HilbertIncidence.OnLine Q l := by
    intro hQl

    have hPl : HilbertIncidence.OnLine P l :=
      hilbert_collinear_on_line
        Geo
        R Q P
        l
        hRQ
        hRl
        hQl
        hRQPcol

    exact hPnotl hPl

  ----------------------------------------------------------------------
  -- Derive noncollinearity C,Q,P from noncollinearity R,Q,C.
  --
  -- The points R,P,Q are collinear and P != Q.
  ----------------------------------------------------------------------

  have hPQ : P ≠ Q :=
    (HilbertOrder.between_incidence
      R P Q hRPQ).2.1

  have hRQQcol : PrimCollinear Geo R Q Q := by
    rcases hRQPcol with
      ⟨g, hRg, hQg, hPg⟩

    exact ⟨g, hRg, hQg, hQg⟩

  have hNPQC : ¬ PrimCollinear Geo P Q C :=
    bookZero_27_NChelper
      Geo
      R Q C
      P Q
      hRQC
      hRQPcol
      hRQQcol
      hPQ

  have hNCQPC : ¬ PrimCollinear Geo C Q P := by
    rcases bookZero_23_NCorder
        Geo P Q C hNPQC with
      ⟨_, _, _, _, hCQPNC⟩

    exact hCQPNC

  ----------------------------------------------------------------------
  -- Put the betweenness hypotheses in the orientation required by
  -- hilbert_outer_pasch_strong.
  ----------------------------------------------------------------------

  have hQPR : Geo.Between Q P R :=
    (HilbertOrder.between_incidence
      R P Q hRPQ).2.2.2.2

  have hCSP : Geo.Between C S P :=
    (HilbertOrder.between_incidence
      P S C hPSC).2.2.2.2

  ----------------------------------------------------------------------
  -- Outer Pasch in triangle C-Q-P:
  --
  -- Q-P-R
  -- C-S-P
  --
  -- produces F with
  --
  -- R-S-F
  -- C-F-Q.
  ----------------------------------------------------------------------

  rcases
      hilbert_outer_pasch_strong
        Geo
        C Q P
        R S
        hNCQPC
        hQPR
        hCSP with
    ⟨F, hRSF, hCFQ⟩

  ----------------------------------------------------------------------
  -- Since R and S are distinct points of l and R-S-F,
  -- the point F lies on l.
  ----------------------------------------------------------------------

  have hRS : R ≠ S :=
    (HilbertOrder.between_incidence
      R S F hRSF).1

  have hRSFcol : PrimCollinear Geo R S F :=
    (HilbertOrder.between_incidence
      R S F hRSF).2.2.2.1

  have hFl : HilbertIncidence.OnLine F l :=
    hilbert_collinear_on_line
      Geo
      R S F
      l
      hRS
      hRl
      hSl
      hRSFcol

  ----------------------------------------------------------------------
  -- Reverse C-F-Q to Q-F-C and use F as the crossing point.
  ----------------------------------------------------------------------

  have hQFC : Geo.Between Q F C :=
    (HilbertOrder.between_incidence
      C F Q hCFQ).2.2.2.2

  exact
    ⟨hQnotl,
     hCnotl,
     F,
     hQFC,
     hFl⟩

/--
Book Zero #62: 9.5b.

If P and C are on opposite sides of line l,
R lies on l, Q lies between R and P, and C,P,R
are noncollinear, then Q and C are on opposite sides of l.
-/
theorem bookZero_62_9_5b
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (P C R Q : Geo.Point)
    (l : Geo.Line)
    (hOppPC : HilbertOppositeSide Geo P C l)
    (hRQP : Geo.Between R Q P)
    (hCPR : ¬ PrimCollinear Geo C P R)
    (hRl : HilbertIncidence.OnLine R l) :
    HilbertOppositeSide Geo Q C l := by

  ----------------------------------------------------------------------
  -- Unpack the original opposite-side relation:
  -- P-S-C with S on l.
  ----------------------------------------------------------------------

  rcases hOppPC with
    ⟨hPnotl, hCnotl, S, hPSC, hSl⟩

  have hCSP : Geo.Between C S P :=
    (HilbertOrder.between_incidence
      P S C hPSC).2.2.2.2

  ----------------------------------------------------------------------
  -- Q does not lie on l.
  --
  -- Otherwise R,Q lie on l and R-Q-P forces P onto l.
  ----------------------------------------------------------------------

  have hRQ : R ≠ Q :=
    (HilbertOrder.between_incidence
      R Q P hRQP).1

  have hRQPcol : PrimCollinear Geo R Q P :=
    (HilbertOrder.between_incidence
      R Q P hRQP).2.2.2.1

  have hQnotl : ¬ HilbertIncidence.OnLine Q l := by
    intro hQl

    have hPl : HilbertIncidence.OnLine P l :=
      hilbert_collinear_on_line
        Geo
        R Q P
        l
        hRQ
        hRl
        hQl
        hRQPcol

    exact hPnotl hPl

  ----------------------------------------------------------------------
  -- Derive noncollinearity C,P,Q.
  --
  -- If C,P,Q were collinear, then the two distinct points P,Q
  -- would force R onto the same line, contradicting NC C P R.
  ----------------------------------------------------------------------

  have hQP : Q ≠ P :=
    (HilbertOrder.between_incidence
      R Q P hRQP).2.1

  have hPQR : PrimCollinear Geo P Q R := by
    rcases bookZero_22_collinearOrder
        Geo R Q P hRQPcol with
      ⟨_, _, _, _, hPQR⟩

    exact hPQR

  have hNCCPQ : ¬ PrimCollinear Geo C P Q := by
    intro hCPQ

    rcases hCPQ with
      ⟨g, hCg, hPg, hQg⟩

    rcases hPQR with
      ⟨k, hPk, hQk, hRk⟩

    have hgk : g = k :=
      HilbertPlaneIncidence.line_unique
        P Q
        hQP.symm
        g k
        hPg hQg
        hPk hQk

    subst k

    exact hCPR ⟨g, hCg, hPg, hRk⟩

  ----------------------------------------------------------------------
  -- Reverse R-Q-P to P-Q-R.
  ----------------------------------------------------------------------

  have hPQRbet : Geo.Between P Q R :=
    (HilbertOrder.between_incidence
      R Q P hRQP).2.2.2.2

  ----------------------------------------------------------------------
  -- Inner Pasch in triangle C-P-Q:
  --
  -- P-Q-R
  -- C-S-P
  --
  -- produces F with
  --
  -- R-F-S
  -- C-F-Q.
  ----------------------------------------------------------------------

  rcases
      hilbert_inner_pasch_strong
        Geo
        C P Q
        R S
        hNCCPQ
        hPQRbet
        hCSP with
    ⟨F, hRFS, hCFQ⟩

  ----------------------------------------------------------------------
  -- R and S are distinct points of l; hence F also lies on l.
  ----------------------------------------------------------------------

  have hRS : R ≠ S :=
    (HilbertOrder.between_incidence
      R F S hRFS).2.2.1

  have hRFScol : PrimCollinear Geo R F S :=
    (HilbertOrder.between_incidence
      R F S hRFS).2.2.2.1

  have hRSFcol : PrimCollinear Geo R S F := by
    rcases bookZero_22_collinearOrder
        Geo R F S hRFScol with
      ⟨_, _, _, hRSFcol, _⟩

    exact hRSFcol

  have hFl : HilbertIncidence.OnLine F l :=
    hilbert_collinear_on_line
      Geo
      R S F
      l
      hRS
      hRl
      hSl
      hRSFcol

  ----------------------------------------------------------------------
  -- Reverse C-F-Q to Q-F-C.
  ----------------------------------------------------------------------

  have hQFC : Geo.Between Q F C :=
    (HilbertOrder.between_incidence
      C F Q hCFQ).2.2.2.2

  exact
    ⟨hQnotl,
     hCnotl,
     F,
     hQFC,
     hFl⟩

/--
Book Zero #63: 9.5.

If P and C are on opposite sides of line l,
R lies on l, and P lies on ray RQ,
then Q and C are on opposite sides of l.
-/
theorem bookZero_63_9_5
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (P C R Q : Geo.Point)
    (l : Geo.Line)
    (hOppPC : HilbertOppositeSide Geo P C l)
    (hRQP : HilbertSameRay Geo R Q P)
    (hRl : HilbertIncidence.OnLine R l) :
    HilbertOppositeSide Geo Q C l := by

  have hOppPC0 : HilbertOppositeSide Geo P C l :=
    hOppPC

  rcases hOppPC with
    ⟨hPnotl, hCnotl, S, hPSC, hSl⟩

  ----------------------------------------------------------------------
  -- Q does not lie on l.
  ----------------------------------------------------------------------

  have hRQ : R ≠ Q :=
    hRQP.1.symm

  have hRQPcol : PrimCollinear Geo R Q P :=
    bookZero_40_rayImpliesCollinear
      Geo R Q P hRQP

  have hQnotl : ¬ HilbertIncidence.OnLine Q l := by
    intro hQl

    have hPl : HilbertIncidence.OnLine P l :=
      hilbert_collinear_on_line
        Geo
        R Q P
        l
        hRQ
        hRl
        hQl
        hRQPcol

    exact hPnotl hPl

  ----------------------------------------------------------------------
  -- Split according to whether C,P,R are collinear.
  ----------------------------------------------------------------------

  by_cases hCPR : PrimCollinear Geo C P R

  ----------------------------------------------------------------------
  -- Collinear case.
  --
  -- The crossing point S from OppositeSide must equal R.
  ----------------------------------------------------------------------

  · have hPSCcol : PrimCollinear Geo P S C :=
      (HilbertOrder.between_incidence
        P S C hPSC).2.2.2.1

    have hPC : P ≠ C :=
      (HilbertOrder.between_incidence
        P S C hPSC).2.2.1

    have hPCS : PrimCollinear Geo P C S := by
      rcases bookZero_22_collinearOrder
          Geo P S C hPSCcol with
        ⟨_, _, _, hPCS, _⟩

      exact hPCS

    have hPCR : PrimCollinear Geo P C R := by
      rcases bookZero_22_collinearOrder
          Geo C P R hCPR with
        ⟨hPCR, _, _, _, _⟩

      exact hPCR

    have hCSR : PrimCollinear Geo C S R :=
      bookZero_24_collinear4
        Geo
        P C S R
        hPCS
        hPCR
        hPC

    have hSR : S = R := by
      by_contra hSRne

      have hSRC : PrimCollinear Geo S R C := by
        rcases bookZero_22_collinearOrder
            Geo C S R hCSR with
          ⟨_, hSRC, _, _, _⟩

        exact hSRC

      have hCl : HilbertIncidence.OnLine C l :=
        hilbert_collinear_on_line
          Geo
          S R C
          l
          hSRne
          hSl
          hRl
          hSRC

      exact hCnotl hCl

    subst S

    have hPRC : Geo.Between P R C :=
      hPSC

    have hCRP : Geo.Between C R P :=
      (HilbertOrder.between_incidence
        P R C hPRC).2.2.2.2

    rcases bookZero_35_ray1 Geo R Q P hRQP with
      hRPQ | hQP | hRQPbet

    --------------------------------------------------------------------
    -- R-P-Q: C-R-P-Q, hence Q-R-C.
    --------------------------------------------------------------------

    · have hCRQ : Geo.Between C R Q :=
        (hilbert_between_outer_trans
          Geo
          C R P Q
          hCRP
          hRPQ).2

      have hQRC : Geo.Between Q R C :=
        (HilbertOrder.between_incidence
          C R Q hCRQ).2.2.2.2

      exact
        ⟨hQnotl,
         hCnotl,
         R,
         hQRC,
         hRl⟩

    --------------------------------------------------------------------
    -- Q = P.
    --------------------------------------------------------------------

    · subst Q

      exact hOppPC0

    --------------------------------------------------------------------
    -- R-Q-P: C-R-Q-P, hence Q-R-C.
    --------------------------------------------------------------------

    · have hPQR : Geo.Between P Q R :=
        (HilbertOrder.between_incidence
          R Q P hRQPbet).2.2.2.2

      have hQRC : Geo.Between Q R C :=
        (hilbert_between_inner_trans
          Geo
          P Q R C
          hPQR
          hPRC).1

      exact
        ⟨hQnotl,
         hCnotl,
         R,
         hQRC,
         hRl⟩

  ----------------------------------------------------------------------
  -- Noncollinear case.
  --
  -- Split the ray and apply 9.5a or 9.5b.
  ----------------------------------------------------------------------

  · rcases bookZero_35_ray1 Geo R Q P hRQP with
      hRPQ | hQP | hRQPbet

    --------------------------------------------------------------------
    -- R-P-Q: apply 9.5a.
    --------------------------------------------------------------------

    · have hRPQcol : PrimCollinear Geo R P Q :=
        (HilbertOrder.between_incidence
          R P Q hRPQ).2.2.2.1

      have hNRPC : ¬ PrimCollinear Geo R P C := by
        rcases bookZero_23_NCorder
            Geo C P R hCPR with
          ⟨_, _, _, _, hNRPC⟩

        exact hNRPC

      have hRPR : PrimCollinear Geo R P R := by
        rcases hRPQcol with
          ⟨g, hRg, hPg, hQg⟩

        exact ⟨g, hRg, hPg, hRg⟩

      have hNRQC : ¬ PrimCollinear Geo R Q C :=
        bookZero_27_NChelper
          Geo
          R P C
          R Q
          hNRPC
          hRPR
          hRPQcol
          hRQ

      exact
        bookZero_61_9_5a
          Geo
          P C R Q
          l
          hOppPC0
          hRPQ
          hNRQC
          hRl

    --------------------------------------------------------------------
    -- Q = P.
    --------------------------------------------------------------------

    · subst Q

      exact hOppPC0

    --------------------------------------------------------------------
    -- R-Q-P: apply 9.5b.
    --------------------------------------------------------------------

    · exact
        bookZero_62_9_5b
          Geo
          P C R Q
          l
          hOppPC0
          hRQPbet
          hCPR
          hRl

/--
Book Zero #64: samesidereflexive.

A point not lying on a line is on the same side of that line
as itself.
-/
theorem bookZero_64_sameSideReflexive
    [HilbertIncidence Geo]
    (A B P : Geo.Point)
    (l : Geo.Line)
    (hAl : HilbertIncidence.OnLine A l)
    (hBl : HilbertIncidence.OnLine B l)
    (hABP : ¬ PrimCollinear Geo A B P) :
    HilbertSameSide Geo P P l := by

  have hPnotl : ¬ HilbertIncidence.OnLine P l := by
    intro hPl

    exact hABP ⟨l, hAl, hBl, hPl⟩

  exact
    hilbert_sameSide_refl
      Geo P l hPnotl

/--
Book Zero #65: samesidesymmetric.

If P and Q lie on the same side of a line,
then Q and P lie on the same side of that line.
-/
theorem bookZero_65_sameSideSymmetric
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (P Q : Geo.Point)
    (l : Geo.Line)
    (hSame : HilbertSameSide Geo P Q l) :
    HilbertSameSide Geo Q P l := by

  exact
    hilbert_sameSide_symm
      Geo P Q l hSame

/--
Book Zero #66: oppositesidesymmetric.

If P and Q lie on opposite sides of a line,
then Q and P lie on opposite sides of that line.
-/
theorem bookZero_66_oppositeSideSymmetric
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (P Q : Geo.Point)
    (l : Geo.Line)
    (hOpp : HilbertOppositeSide Geo P Q l) :
    HilbertOppositeSide Geo Q P l := by

  exact
    hilbert_oppositeSide_symm
      Geo P Q l hOpp

/--
Book Zero #67: oppositesideflip.

Reversing the two points used to describe the reference line
does not change the opposite-side relation.

In the present line-based representation this is definitional:
the reference line is the same object `l`.
-/
theorem bookZero_67_oppositeSideFlip
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (P Q : Geo.Point)
    (l : Geo.Line)
    (hOpp : HilbertOppositeSide Geo P Q l) :
    HilbertOppositeSide Geo P Q l := by

  exact hOpp

/--
Book Zero #68: samesidecollinear.

Replacing one pair of points describing the reference line
by another pair of distinct collinear points does not change
the same-side relation.

In the present line-based representation the reference line
is already the same object `l`.
-/
theorem bookZero_68_sameSideCollinear
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (P Q A B C : Geo.Point)
    (l : Geo.Line)
    (hSame : HilbertSameSide Geo P Q l)
    (_hAl : HilbertIncidence.OnLine A l)
    (_hBl : HilbertIncidence.OnLine B l)
    (_hCl : HilbertIncidence.OnLine C l)
    (_hAC : A ≠ C) :
    HilbertSameSide Geo P Q l := by

  exact hSame

/--
Book Zero #69: equalanglesNC.

In BNW, noncollinearity of both angle triples is encoded in the
definition of equal angles.  In the present Hilbert representation,
AngleCongruent does not itself carry nondegeneracy, so the
noncollinearity of the second angle is explicit.
-/
theorem bookZero_69_equalAnglesNC
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b c : Geo.Point)
    (_hAngle : Geo.AngleCongruent A B C a b c)
    (_hABC : ¬ PrimCollinear Geo A B C)
    (habc : ¬ PrimCollinear Geo a b c) :
    ¬ PrimCollinear Geo a b c := by

  exact habc


--------------------------------------

/--
Transfer of an interior division point to a congruent segment.

If C lies between A and B and AB is congruent to ab,
then there exists c between a and b such that
AC is congruent to ac and CB is congruent to cb.
-/
theorem bookZero_segmentSplitTransfer
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C a b : Geo.Point)
    (hACB : Geo.Between A C B)
    (hABab : Geo.Congruent A B a b) :
    ∃ c : Geo.Point,
      Geo.Between a c b ∧
      Geo.Congruent A C a c ∧
      Geo.Congruent C B c b := by

  have hAB : A ≠ B :=
    (HilbertOrder.between_incidence
      A C B hACB).2.2.1

  have hab : a ≠ b :=
    bookZero_nullSegment3
      Geo
      A B a b
      hAB
      hABab

  have hAC : A ≠ C :=
    (HilbertOrder.between_incidence
      A C B hACB).1

  rcases
      bookZero_49_layoff
        Geo
        a b A C
        hab
        hAC with
    ⟨c, habcRay, hacAC⟩

  have hACac : Geo.Congruent A C a c :=
    hilbert_congruent_symmetry
      Geo a c A C hacAC

  have hACAB : HilbertSegmentLess Geo A C A B :=
    ⟨C,
     hACB,
     hilbert_congruent_reflexive Geo A C⟩

  have hacAB : HilbertSegmentLess Geo a c A B :=
    bookZero_32_lessThanCongruence2
      Geo
      A C A B
      a c
      hACAB
      hACac

  have hacab : HilbertSegmentLess Geo a c a b :=
    bookZero_30_lessThanCongruence
      Geo
      a c A B
      a b
      hacAB
      hABab

  have hacbRay : HilbertSameRay Geo a c b :=
    bookZero_39_ray5
      Geo a b c habcRay

  have hacb : Geo.Between a c b :=
    bookZero_51_lessThanBetween
      Geo
      a c b
      hacab
      hacbRay

  have hCBcb : Geo.Congruent C B c b :=
    hilbert_segment_subtraction
      Geo
      A C B
      a c b
      hACB
      hacb
      hACac
      hABab

  exact
    ⟨c,
     hacb,
     hACac,
     hCBcb⟩


theorem hilbert_right_angle_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A C B : Geo.Point)
    (hACB : Geo.Between A C B) :
    ∃ X : Geo.Point,
      HilbertRightAngle Geo A C X := by

  have hACBData :=
    HilbertOrder.between_incidence A C B hACB

  have hAC : A ≠ C :=
    hACBData.1

  have hCB : C ≠ B :=
    hACBData.2.1

  have hAB : A ≠ B :=
    hACBData.2.2.1

  ----------------------------------------------------------------------
  -- The given line AB.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A B hAB with
    ⟨base, hAbase, hBbase⟩

  have hCbase :
      HilbertIncidence.OnLine C base :=
    hilbert_between_on_line
      Geo A C B base
      hAbase hBbase hACB

  ----------------------------------------------------------------------
  -- Choose an arbitrary point D off AB.
  ----------------------------------------------------------------------

  rcases
      hilbert_point_off_line Geo base with
    ⟨D, hDbase⟩

  have hACD :
      ¬ Collinear Geo A C D :=
    hilbert_not_collinear_of_off_line
      Geo A C D base
      hAC
      hAbase
      hCbase
      hDbase

  have hBC : B ≠ C :=
    hCB.symm

  ----------------------------------------------------------------------
  -- Copy angle ACD onto ray CB, on the side selected by D.
  --
  -- This produces E with
  --
  --     angle ACD congruent angle BCE.
  ----------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        A C D
        B C D
        hACD
        hBC
        base
        hBbase
        hCbase
        hDbase with
    ⟨E, hEDSame, hAngleE, hUniqueE⟩
  ----------------------------------------------------------------------
  -- If C, E, D are collinear, then E and D determine the same ray
  -- from C, because they lie on the same side of the base line.
  -- In this case D already determines the required right angle.
  ----------------------------------------------------------------------

  by_cases hCED :
      Collinear Geo C E D

  · have hEC : E ≠ C := by
      intro h
      subst E
      exact hEDSame.1 hCbase

    have hDC : D ≠ C := by
      intro h
      subst D
      exact hDbase hCbase

    have hNotECD :
        ¬ Geo.Between E C D := by

      intro hECD

      have hOppED :
          HilbertOppositeSide Geo E D base :=
        ⟨hEDSame.1,
         hEDSame.2.1,
         ⟨C, hECD, hCbase⟩⟩

      exact
        (hilbert_oppositeSide_not_sameSide
          Geo E D base hOppED)
          hEDSame

    have hRayED :
        HilbertSameRay Geo C E D :=
      ⟨hEC, hDC, hCED, hNotECD⟩

    have hAngleBED :
        Geo.Angle B C E =
        Geo.Angle B C D :=
      hilbert_angle_eq_of_sameRay_second
        Geo C B E D hRayED

    have hAngleACD_BCD :
        Geo.AngleCongruent A C D B C D := by

      unfold Geometry.Geo.AngleCongruent
        at hAngleE ⊢

      rw [← hAngleBED]
      exact hAngleE

    have hAngleACD_DCB :
        Geo.AngleCongruent A C D D C B := by

      unfold Geometry.Geo.AngleCongruent
        at hAngleACD_BCD ⊢

      rw [Geometry.Geo.angle_swap Geo B C D]
        at hAngleACD_BCD

      exact hAngleACD_BCD

    refine ⟨D, ?_⟩
    refine ⟨B, hACB, ?_⟩
    exact hAngleACD_DCB

  · -- hCED : not Collinear Geo C E D

    have hCD : C ≠ D := by
      intro h
      subst D
      exact hDbase hCbase

    have hCE : C ≠ E := by
      intro h
      subst E
      exact hEDSame.1 hCbase

    ----------------------------------------------------------------------
    -- On ray CD choose F with CF congruent CE.
    ----------------------------------------------------------------------

    rcases
        HilbertCongruence.segment_construction
          (Geo := Geo)
          C E
          C D
          hCD with
      ⟨F, hRayDF, hCF_CE⟩

    have hCF : C ≠ F :=
      hRayDF.2.1.symm

    have hCDF :
        Collinear Geo C D F :=
      hRayDF.2.2.1

    ----------------------------------------------------------------------
    -- F, C, E are noncollinear.
    ----------------------------------------------------------------------

    have hFCE :
        ¬ Collinear Geo F C E := by

      intro hFCE

      have hDCF :
          Collinear Geo D C F :=
        PrimCollinearSwap
          Geo C D F hCDF

      have hCFE :
          Collinear Geo C F E :=
        PrimCollinearSwap
          Geo F C E hFCE

      have hDCE :
          Collinear Geo D C E :=
        hilbert_primCollinear_trans
          Geo
          D C F E
          hCF
          hDCF
          hCFE

      have hCED' :
          Collinear Geo C E D :=
        PrimCollinearCycle
          Geo D C E hDCE

      exact hCED hCED'

    have hFE : F ≠ E := by
      intro hFE
      subst F

      have hCED' :
          Collinear Geo C E D :=
        PrimCollinearRotate
          Geo C D E hCDF

      exact hCED hCED'
    ----------------------------------------------------------------------
    -- Let X be the midpoint of FE.
    ----------------------------------------------------------------------

    rcases
        HilbertMidpointExists
          Geo F E hFE with
      ⟨X, hMidX⟩

    have hFXE :
        Geo.Between F X E :=
      hMidX.1

    have hFX_XE :
        Geo.Congruent F X X E :=
      hMidX.2

    have hFX : F ≠ X :=
      (HilbertOrder.between_incidence
        F X E hFXE).1

    have hFXEcol :
        Collinear Geo F X E :=
      (HilbertOrder.between_incidence
        F X E hFXE).2.2.2.1

    ----------------------------------------------------------------------
    -- Triangle CFX is nondegenerate.
    ----------------------------------------------------------------------

    have hCFX :
        ¬ Collinear Geo C F X := by

      intro hCFX

      have hCFE' :
          Collinear Geo C F E :=
        hilbert_primCollinear_trans
          Geo
          C F X E
          hFX
          hCFX
          hFXEcol

      exact
        hFCE
          (PrimCollinearSwap Geo C F E hCFE')

    ----------------------------------------------------------------------
    -- SSS for triangles CFX and CEX.
    ----------------------------------------------------------------------

    have hFX_EX :
        Geo.Congruent F X E X :=
      (Geo.congruent_reverse_second
        F X X E).mp hFX_XE

    have hCX_CX :
        Geo.Congruent C X C X :=
      hilbert_congruent_reflexive
        Geo C X

    have hSSS :=
      HilbertSSS
        Geo
        C F X
        C E X
        hCFX
        hCF_CE
        hFX_EX
        hCX_CX

    have hFCX_ECX :
        Geo.AngleCongruent F C X E C X :=
      hSSS.2.angleA

    ----------------------------------------------------------------------
    -- Replace ray CF by the original ray CD.
    ----------------------------------------------------------------------

    have hRayFD :
        HilbertSameRay Geo C F D :=
      hilbert_sameRay_symm
        Geo C D F hRayDF

    have hAngleFCX_DCX :
        Geo.Angle F C X =
        Geo.Angle D C X :=
      hilbert_angle_eq_of_sameRay_first
        Geo C F D X hRayFD

    have hDCX_ECX :
        Geo.AngleCongruent D C X E C X := by

      unfold Geometry.Geo.AngleCongruent
        at hFCX_ECX ⊢

      rw [← hAngleFCX_DCX]

      exact hFCX_ECX
    ----------------------------------------------------------------------
    -- Reference lines CD and CE.
    ----------------------------------------------------------------------

    rcases
        HilbertPlaneIncidence.line_through
          C D hCD with
      ⟨lineCD, hClineCD, hDlineCD⟩

    rcases
        HilbertPlaneIncidence.line_through
          C E hCE with
      ⟨lineCE, hClineCE, hElineCE⟩

    ----------------------------------------------------------------------
    -- F lies on line CD.
    ----------------------------------------------------------------------

    have hFlineCD :
        HilbertIncidence.OnLine F lineCD :=
      hilbert_collinear_on_line
        Geo C D F lineCD
        hCD
        hClineCD
        hDlineCD
        hCDF

    ----------------------------------------------------------------------
    -- A is not on line CD.
    ----------------------------------------------------------------------

    have hAoffCD :
        ¬ HilbertIncidence.OnLine A lineCD := by

      intro hAlineCD

      exact hACD
        ⟨lineCD,
         hAlineCD,
         hClineCD,
         hDlineCD⟩

    ----------------------------------------------------------------------
    -- X is not on line CD.
    ----------------------------------------------------------------------

    have hXoffCD :
        ¬ HilbertIncidence.OnLine X lineCD := by

      intro hXlineCD

      exact hCFX
        ⟨lineCD,
         hClineCD,
         hFlineCD,
         hXlineCD⟩

    ----------------------------------------------------------------------
    -- B is not on line CE.
    ----------------------------------------------------------------------

    have hBoffCE :
        ¬ HilbertIncidence.OnLine B lineCE := by

      intro hBlineCE

      have hBaseEq :
          base = lineCE :=
        HilbertPlaneIncidence.line_unique
          B C hBC
          base lineCE
          hBbase hCbase
          hBlineCE hClineCE

      have hEbase :
          HilbertIncidence.OnLine E base := by
        rw [hBaseEq]
        exact hElineCE

      exact hEDSame.1 hEbase

    ----------------------------------------------------------------------
    -- X is not on line CE.
    ----------------------------------------------------------------------

    have hCEX :
        ¬ Collinear Geo C E X :=
      hSSS.1

    have hXoffCE :
        ¬ HilbertIncidence.OnLine X lineCE := by

      intro hXlineCE

      exact hCEX
        ⟨lineCE,
         hClineCE,
         hElineCE,
         hXlineCE⟩

    ----------------------------------------------------------------------
    -- E and X lie on the same side of line CD.
    ----------------------------------------------------------------------

    have hEXF :
        Geo.Between E X F :=
      (HilbertOrder.between_incidence
        F X E hFXE).2.2.2.2

    have hEFC :
        ¬ Collinear Geo E F C := by
      intro hEFC

      have hFCE' :
          Collinear Geo F C E :=
        PrimCollinearCycle
          Geo E F C hEFC

      exact hFCE hFCE'

    rcases
        hilbert_between_points_sameSide_transversal
          Geo E X C F hEXF hEFC with
      ⟨lineCF, hClineCF, hFlineCF, hSameEX_CF⟩

    have hLineCF_CD :
        lineCF = lineCD :=
      HilbertPlaneIncidence.line_unique
        C F hCF
        lineCF lineCD
        hClineCF hFlineCF
        hClineCD hFlineCD

    have hSameEX_CD :
        HilbertSameSide Geo E X lineCD := by
      rw [← hLineCF_CD]
      exact hSameEX_CF

    ----------------------------------------------------------------------
    -- F and X lie on the same side of line CE.
    ----------------------------------------------------------------------

    have hFEC :
        ¬ Collinear Geo F E C := by
      intro hFEC

      have hFCE' :
          Collinear Geo F C E :=
        PrimCollinearRotate
          Geo F E C hFEC

      exact hFCE hFCE'

    rcases
        hilbert_between_points_sameSide_transversal
          Geo F X C E hFXE hFEC with
      ⟨lineCE', hClineCE', hElineCE', hSameFX_CE⟩

    have hLineCE'_CE :
        lineCE' = lineCE :=
      HilbertPlaneIncidence.line_unique
        C E hCE
        lineCE' lineCE
        hClineCE' hElineCE'
        hClineCE hElineCE

    have hSameFX_CE' :
        HilbertSameSide Geo F X lineCE := by
      rw [← hLineCE'_CE]
      exact hSameFX_CE
    ----------------------------------------------------------------------
    -- Determine the order of the rays CD and CE in the half-plane
    -- bounded by the original line AB.
    ----------------------------------------------------------------------

    have hDCE :
        ¬ Collinear Geo D C E := by
      intro hDCE'
      exact
        hCED
          (PrimCollinearCycle
            Geo D C E hDCE')

    have hSameDE :
        HilbertSameSide Geo D E base :=
      hilbert_sameSide_symm
        Geo E D base hEDSame

    have hRayOrder :
        HilbertRayMeetsSegment Geo C D E A ∨
        HilbertRayMeetsSegment Geo C E D A :=
      hilbert_sameSide_rays_order
        Geo
        C D A E
        base
        hAC.symm
        hCbase
        hAbase
        hDbase
        hEDSame.1
        hSameDE
        hDCE
    rcases hRayOrder with hCaseD | hCaseE

    ----------------------------------------------------------------------
    -- Case 1: ray CD meets the open segment EA.
    ----------------------------------------------------------------------

        ----------------------------------------------------------------------
    -- Case 1: ray CD meets the open segment EA.
    ----------------------------------------------------------------------

    · rcases hCaseD with
        ⟨Y, hEYA, hRayDY⟩

      have hCY : C ≠ Y :=
        hRayDY.2.1.symm

      have hYlineCD :
          HilbertIncidence.OnLine Y lineCD := by

        rcases hRayDY.2.2.1 with
          ⟨m, hCm, hDm, hYm⟩

        have hm :
            m = lineCD :=
          HilbertPlaneIncidence.line_unique
            C D hCD
            m lineCD
            hCm hDm
            hClineCD hDlineCD

        rw [← hm]
        exact hYm

      --------------------------------------------------------------------
      -- E and A are on opposite sides of CD.
      --------------------------------------------------------------------

      have hOppEA_CD :
          HilbertOppositeSide Geo E A lineCD :=
        ⟨hSameEX_CD.1,
         hAoffCD,
         ⟨Y, hEYA, hYlineCD⟩⟩

      have hOppAE_CD :
          HilbertOppositeSide Geo A E lineCD :=
        hilbert_oppositeSide_symm
          Geo E A lineCD hOppEA_CD

      have hOppAX_CD :
          HilbertOppositeSide Geo A X lineCD :=
        hilbert_oppositeSide_transport_right
          Geo A E X lineCD
          hOppAE_CD
          hSameEX_CD

      have hNotSameAX_CD :
          ¬ HilbertSameSide Geo A X lineCD := by
        intro hSameAX

        exact
          (hilbert_oppositeSide_not_sameSide
            Geo A X lineCD hOppAX_CD)
            hSameAX

      --------------------------------------------------------------------
      -- F and Y are on the same side of CE because both lie
      -- on the same ray CD.
      --------------------------------------------------------------------

      have hSameFY_CE :
          HilbertSameSide Geo F Y lineCE := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := D)
            (X := F)
            (Y := Y)
            (C := E)
            (base := lineCD)
            (cross := lineCE)
            hClineCD
            hDlineCD
            hClineCE
            hElineCE
            hSameEX_CD.1
            hRayDF
            hRayDY

      --------------------------------------------------------------------
      -- Y and A are on the same side of CE.
      --------------------------------------------------------------------

      have hEYAData :=
        HilbertOrder.between_incidence
          E Y A hEYA

      rcases hEYAData.2.2.2.1 with
        ⟨lineEA, hElineEA, hYlineEA, hAlineEA⟩

      have hCoffEA :
          ¬ HilbertIncidence.OnLine C lineEA := by
        intro hClineEA

        have hEq :
            lineEA = base :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            lineEA base
            hAlineEA hClineEA
            hAbase hCbase

        have hEbase :
            HilbertIncidence.OnLine E base := by
          rw [← hEq]
          exact hElineEA

        exact hEDSame.1 hEbase

      have hRayEAY :
          HilbertSameRay Geo E A Y :=
        hilbert_sameRay_symm
          Geo E Y A
          (hilbert_sameRay_of_between
            Geo E Y A hEYA)


      have hAE : A ≠ E :=
        hEYAData.2.2.1.symm

      have hRayEAA :
          HilbertSameRay Geo E A A :=
        hilbert_sameRay_refl
          Geo E A hAE

      have hSameYA_CE :
          HilbertSameSide Geo Y A lineCE := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := E)
            (R := A)
            (X := Y)
            (Y := A)
            (C := C)
            (base := lineEA)
            (cross := lineCE)
            hElineEA
            hAlineEA
            hElineCE
            hClineCE
            hCoffEA
            hRayEAY
            hRayEAA

      have hSameFA_CE :
          HilbertSameSide Geo F A lineCE :=
        hilbert_sameSide_trans
          Geo F Y A lineCE
          hSameFY_CE
          hSameYA_CE

      have hSameAF_CE :
          HilbertSameSide Geo A F lineCE :=
        hilbert_sameSide_symm
          Geo F A lineCE hSameFA_CE

      --------------------------------------------------------------------
      -- A and B are on opposite sides of CE because A-C-B.
      --------------------------------------------------------------------

      have hAoffCE :
          ¬ HilbertIncidence.OnLine A lineCE := by
        intro hAlineCE

        have hEq :
            base = lineCE :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            base lineCE
            hAbase hCbase
            hAlineCE hClineCE

        have hEbase :
            HilbertIncidence.OnLine E base := by
          rw [hEq]
          exact hElineCE

        exact hEDSame.1 hEbase

      have hOppAB_CE :
          HilbertOppositeSide Geo A B lineCE :=
        ⟨hAoffCE,
         hBoffCE,
         ⟨C, hACB, hClineCE⟩⟩

      have hOppBA_CE :
          HilbertOppositeSide Geo B A lineCE :=
        hilbert_oppositeSide_symm
          Geo A B lineCE hOppAB_CE

      have hOppBF_CE :
          HilbertOppositeSide Geo B F lineCE :=
        hilbert_oppositeSide_transport_right
          Geo B A F lineCE
          hOppBA_CE
          hSameAF_CE

      have hOppBX_CE :
          HilbertOppositeSide Geo B X lineCE :=
        hilbert_oppositeSide_transport_right
          Geo B F X lineCE
          hOppBF_CE
          hSameFX_CE'

      have hNotSameBX_CE :
          ¬ HilbertSameSide Geo B X lineCE := by
        intro hSameBX

        exact
          (hilbert_oppositeSide_not_sameSide
            Geo B X lineCE hOppBX_CE)
            hSameBX

      --------------------------------------------------------------------
      -- The two angle configurations have the same side pattern.
      --------------------------------------------------------------------

      have hSideConfiguration :
          HilbertSameSide Geo A X lineCD ↔
          HilbertSameSide Geo B X lineCE := by
        constructor
        · intro hAX
          exact False.elim (hNotSameAX_CD hAX)
        · intro hBX
          exact False.elim (hNotSameBX_CE hBX)

            --------------------------------------------------------------------
      -- F and D lie on the same side of the original base.
      --------------------------------------------------------------------

      have hRayCDD :
          HilbertSameRay Geo C D D :=
        hilbert_sameRay_refl
          Geo C D hCD.symm

      have hSameFD_base :
          HilbertSameSide Geo F D base := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := D)
            (X := F)
            (Y := D)
            (C := A)
            (base := lineCD)
            (cross := base)
            hClineCD
            hDlineCD
            hCbase
            hAbase
            hAoffCD
            hRayDF
            hRayCDD

      have hSameFE_base :
          HilbertSameSide Geo F E base :=
        hilbert_sameSide_trans
          Geo F D E base
          hSameFD_base
          hSameDE

      --------------------------------------------------------------------
      -- Since X lies between F and E, and F,E are on the same side
      -- of base, X cannot lie on base.
      --------------------------------------------------------------------

      have hXoffBase :
          ¬ HilbertIncidence.OnLine X base := by
        intro hXbase

        have hOppFE_base :
            HilbertOppositeSide Geo F E base :=
          ⟨hSameFE_base.1,
           hSameFE_base.2.1,
           ⟨X, hFXE, hXbase⟩⟩

        exact
          (hilbert_oppositeSide_not_sameSide
            Geo F E base hOppFE_base)
            hSameFE_base

      --------------------------------------------------------------------
      -- Hence ACX and BCX are genuine angles.
      --------------------------------------------------------------------

      have hACX :
          ¬ Collinear Geo A C X :=
        hilbert_not_collinear_of_off_line
          Geo A C X base
          hAC
          hAbase
          hCbase
          hXoffBase

      have hBCX :
          ¬ Collinear Geo B C X :=
        hilbert_not_collinear_of_off_line
          Geo B C X base
          hBC
          hBbase
          hCbase
          hXoffBase

      --------------------------------------------------------------------
      -- Add the two congruent component angles:
      --
      --   ACD ~= BCE
      --   DCX ~= ECX
      --
      -- therefore ACX ~= BCX.
      --------------------------------------------------------------------

      have hACX_BCX :
          Geo.AngleCongruent A C X B C X :=
        hilbert_angle_addition
          Geo
          A C D X
          B C E X
          lineCD lineCE
          hCD
          hCE
          hClineCD
          hDlineCD
          hClineCE
          hElineCE
          hAoffCD
          hXoffCD
          hBoffCE
          hXoffCE
          hSideConfiguration
          hACX
          hBCX
          hAngleE
          hDCX_ECX

      have hACX_XCB :
          Geo.AngleCongruent A C X X C B :=
        (Geo.angle_congruent_reverse_second
          A C X B C X).mp hACX_BCX

      --------------------------------------------------------------------
      -- This is precisely a right angle at C.
      --------------------------------------------------------------------

      refine ⟨X, ?_⟩
      refine ⟨B, hACB, ?_⟩
      exact hACX_XCB


    ----------------------------------------------------------------------
    -- Case 2: ray CE meets the open segment DA.
    ----------------------------------------------------------------------

    · rcases hCaseE with
        ⟨Y, hDYA, hRayEY⟩

      have hCY : C ≠ Y :=
        hRayEY.2.1.symm

      have hYlineCE :
          HilbertIncidence.OnLine Y lineCE := by

        rcases hRayEY.2.2.1 with
          ⟨m, hCm, hEm, hYm⟩

        have hm :
            m = lineCE :=
          HilbertPlaneIncidence.line_unique
            C E hCE
            m lineCE
            hCm hEm
            hClineCE hElineCE

        rw [← hm]
        exact hYm

      --------------------------------------------------------------------
      -- Since Y lies between D and A and Y lies on line CE,
      -- D and A are on opposite sides of line CE.
      --------------------------------------------------------------------
      have hDoffCE :
          ¬ HilbertIncidence.OnLine D lineCE := by
        intro hDlineCE

        exact hCED
          ⟨lineCE,
           hClineCE,
           hElineCE,
           hDlineCE⟩
      have hAoffCE :
          ¬ HilbertIncidence.OnLine A lineCE := by
        intro hAlineCE

        have hBaseEq :
            base = lineCE :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            base lineCE
            hAbase hCbase
            hAlineCE hClineCE

        have hEbase :
            HilbertIncidence.OnLine E base := by
          rw [hBaseEq]
          exact hElineCE

        exact hEDSame.1 hEbase

      have hOppDA_CE :
          HilbertOppositeSide Geo D A lineCE :=
        ⟨hDoffCE,
         hAoffCE,
         ⟨Y, hDYA, hYlineCE⟩⟩

            --------------------------------------------------------------------
      -- Y and A lie on the same side of CD.
      --------------------------------------------------------------------

      have hDYAData :=
        HilbertOrder.between_incidence
          D Y A hDYA

      rcases hDYAData.2.2.2.1 with
        ⟨lineDA, hDlineDA, hYlineDA, hAlineDA⟩

      have hCoffDA :
          ¬ HilbertIncidence.OnLine C lineDA := by
        intro hClineDA

        have hEq :
            lineDA = base :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            lineDA base
            hAlineDA hClineDA
            hAbase hCbase

        have hDbase' :
            HilbertIncidence.OnLine D base := by
          rw [← hEq]
          exact hDlineDA

        exact hDbase hDbase'

      have hRayDAY :
          HilbertSameRay Geo D A Y :=
        hilbert_sameRay_symm
          Geo D Y A
          (hilbert_sameRay_of_between
            Geo D Y A hDYA)

      have hDA : A ≠ D :=
        hDYAData.2.2.1.symm

      have hRayDAA :
          HilbertSameRay Geo D A A :=
        hilbert_sameRay_refl
          Geo D A hDA

      have hSameYA_CD :
          HilbertSameSide Geo Y A lineCD := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := D)
            (R := A)
            (X := Y)
            (Y := A)
            (C := C)
            (base := lineDA)
            (cross := lineCD)
            hDlineDA
            hAlineDA
            hDlineCD
            hClineCD
            hCoffDA
            hRayDAY
            hRayDAA

      --------------------------------------------------------------------
      -- E and Y lie on the same side of CD because both lie
      -- on ray CE.
      --------------------------------------------------------------------

      have hRayCEE :
          HilbertSameRay Geo C E E :=
        hilbert_sameRay_refl
          Geo C E hCE.symm

      have hSameEY_CD :
          HilbertSameSide Geo E Y lineCD := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := E)
            (X := E)
            (Y := Y)
            (C := D)
            (base := lineCE)
            (cross := lineCD)
            hClineCE
            hElineCE
            hClineCD
            hDlineCD
            hDoffCE
            hRayCEE
            hRayEY

      have hSameEA_CD :
          HilbertSameSide Geo E A lineCD :=
        hilbert_sameSide_trans
          Geo E Y A lineCD
          hSameEY_CD
          hSameYA_CD

      have hSameAE_CD :
          HilbertSameSide Geo A E lineCD :=
        hilbert_sameSide_symm
          Geo E A lineCD hSameEA_CD

      have hSameAX_CD :
          HilbertSameSide Geo A X lineCD :=
        hilbert_sameSide_trans
          Geo A E X lineCD
          hSameAE_CD
          hSameEX_CD

      --------------------------------------------------------------------
      -- D and B lie on the same side of CE.
      --
      -- CE cuts sides AD and AB of triangle ADB at Y and C.
      --------------------------------------------------------------------

      have hAYD :
          Geo.Between A Y D :=
        hDYAData.2.2.2.2

      have hADB :
          ¬ PrimCollinear Geo A D B := by
        rintro ⟨l, hAl, hDl, hBl⟩

        have hEq :
            l = base :=
          HilbertPlaneIncidence.line_unique
            A B hAB
            l base
            hAl hBl
            hAbase hBbase

        have hDbase' :
            HilbertIncidence.OnLine D base := by
          rw [← hEq]
          exact hDl

        exact hDbase hDbase'

      have hSameDB_CE :
          HilbertSameSide Geo D B lineCE :=
        hilbert_third_side_endpoints_sameSide
          Geo
          A D B
          Y C
          lineCE
          hADB
          hAYD
          hACB
          hYlineCE
          hClineCE

      --------------------------------------------------------------------
      -- D and F are on the same side of CE because both lie
      -- on ray CD.
      --------------------------------------------------------------------

      have hRayCDD :
          HilbertSameRay Geo C D D :=
        hilbert_sameRay_refl
          Geo C D hCD.symm

      have hSameDF_CE :
          HilbertSameSide Geo D F lineCE := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := D)
            (X := D)
            (Y := F)
            (C := E)
            (base := lineCD)
            (cross := lineCE)
            hClineCD
            hDlineCD
            hClineCE
            hElineCE
            hSameEX_CD.1
            hRayCDD
            hRayDF

      have hSameBD_CE :
          HilbertSameSide Geo B D lineCE :=
        hilbert_sameSide_symm
          Geo D B lineCE hSameDB_CE

      have hSameBF_CE :
          HilbertSameSide Geo B F lineCE :=
        hilbert_sameSide_trans
          Geo B D F lineCE
          hSameBD_CE
          hSameDF_CE

      have hSameBX_CE :
          HilbertSameSide Geo B X lineCE :=
        hilbert_sameSide_trans
          Geo B F X lineCE
          hSameBF_CE
          hSameFX_CE'

      --------------------------------------------------------------------
      -- Both component configurations are same-side configurations.
      --------------------------------------------------------------------

      have hSideConfiguration :
          HilbertSameSide Geo A X lineCD ↔
          HilbertSameSide Geo B X lineCE :=
        ⟨fun _ => hSameBX_CE,
         fun _ => hSameAX_CD⟩

      --------------------------------------------------------------------
      -- X is off the original base AB.
      --------------------------------------------------------------------

      have hSameFD_base :
          HilbertSameSide Geo F D base := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := D)
            (X := F)
            (Y := D)
            (C := A)
            (base := lineCD)
            (cross := base)
            hClineCD
            hDlineCD
            hCbase
            hAbase
            hAoffCD
            hRayDF
            hRayCDD

      have hSameFE_base :
          HilbertSameSide Geo F E base :=
        hilbert_sameSide_trans
          Geo F D E base
          hSameFD_base
          hSameDE

      have hXoffBase :
          ¬ HilbertIncidence.OnLine X base := by
        intro hXbase

        have hOppFE_base :
            HilbertOppositeSide Geo F E base :=
          ⟨hSameFE_base.1,
           hSameFE_base.2.1,
           ⟨X, hFXE, hXbase⟩⟩

        exact
          (hilbert_oppositeSide_not_sameSide
            Geo F E base hOppFE_base)
            hSameFE_base

      have hACX :
          ¬ Collinear Geo A C X :=
        hilbert_not_collinear_of_off_line
          Geo A C X base
          hAC
          hAbase
          hCbase
          hXoffBase

      have hBCX :
          ¬ Collinear Geo B C X :=
        hilbert_not_collinear_of_off_line
          Geo B C X base
          hBC
          hBbase
          hCbase
          hXoffBase

      --------------------------------------------------------------------
      -- Angle addition.
      --------------------------------------------------------------------

      have hACX_BCX :
          Geo.AngleCongruent A C X B C X :=
        hilbert_angle_addition
          Geo
          A C D X
          B C E X
          lineCD lineCE
          hCD
          hCE
          hClineCD
          hDlineCD
          hClineCE
          hElineCE
          hAoffCD
          hXoffCD
          hBoffCE
          hXoffCE
          hSideConfiguration
          hACX
          hBCX
          hAngleE
          hDCX_ECX

      have hACX_XCB :
          Geo.AngleCongruent A C X X C B :=
        (Geo.angle_congruent_reverse_second
          A C X B C X).mp hACX_BCX

      refine ⟨X, ?_⟩
      refine ⟨B, hACB, ?_⟩
      exact hACX_XCB

/--
Transport an angle congruence when the first ray is replaced by
another nonvertex point of the same supporting line.

If A, B, H are distinct and collinear, then from

    angle ABP ~= angle ABQ

we obtain

    angle HBP ~= angle HBQ.

If A and H lie on the same ray from B, this is direct ray transport.
If B lies between A and H, both target angles are supplements of the
original congruent angles.
-/
theorem hilbert_collinear_angle_transport
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B H P Q : Geo.Point)
    (hAB : A ≠ B)
    (hAH : A ≠ H)
    (hBH : B ≠ H)
    (hBP : B ≠ P)
    (hBQ : B ≠ Q)
    (hABH : PrimCollinear Geo A B H)
    (hABP : ¬ PrimCollinear Geo A B P)
    (hABQ : ¬ PrimCollinear Geo A B Q)
    (hAngle : Geo.AngleCongruent A B P A B Q) :
    Geo.AngleCongruent H B P H B Q := by

  rcases
      hilbert_between_trichotomy
        Geo
        A B H
        hAB
        hBH
        hAH
        hABH with
    hABHbet | hBAHbet | hAHBbet

  ----------------------------------------------------------------------
  -- Case A-B-H.
  --
  -- BH is opposite to BA, so both target angles are supplements
  -- of the original congruent angles.
  ----------------------------------------------------------------------

  · have hRayBP :
        HilbertSameRay Geo B P P :=
      hilbert_sameRay_refl
        Geo B P hBP.symm

    have hRayBQ :
        HilbertSameRay Geo B Q Q :=
      hilbert_sameRay_refl
        Geo B Q hBQ.symm

    have hSuppP :
        BookZeroSupplement Geo
          A B P
          P H :=
      ⟨hRayBP, hABHbet⟩

    have hSuppQ :
        BookZeroSupplement Geo
          A B Q
          Q H :=
      ⟨hRayBQ, hABHbet⟩

    have hPBH_QBH :
        Geo.AngleCongruent P B H Q B H :=
      bookZero_43_supplements
        Geo
        A B P P H
        A B Q Q H
        hAngle
        hSuppP
        hSuppQ
        hABP
        hABQ

    exact
      (Geo.angle_congruent_reverse_second
        H B P Q B H).mp
        ((Geo.angle_congruent_reverse_first
          P B H Q B H).mp hPBH_QBH)

  ----------------------------------------------------------------------
  -- Case B-A-H.
  --
  -- A and H lie on the same ray from B.
  ----------------------------------------------------------------------

  · have hRayBAH :
        HilbertSameRay Geo B A H :=
      hilbert_sameRay_of_between
        Geo B A H hBAHbet

    have hLeft :
        Geo.Angle A B P =
        Geo.Angle H B P :=
      hilbert_angle_eq_of_sameRay_first
        Geo B A H P hRayBAH

    have hRight :
        Geo.Angle A B Q =
        Geo.Angle H B Q :=
      hilbert_angle_eq_of_sameRay_first
        Geo B A H Q hRayBAH

    unfold Geometry.Geo.AngleCongruent at hAngle ⊢
    rw [← hLeft, ← hRight]
    exact hAngle

  ----------------------------------------------------------------------
  -- Case A-H-B.
  --
  -- Again A and H lie on the same ray from B.
  ----------------------------------------------------------------------

  · have hBHA :
        Geo.Between B H A :=
      (HilbertOrder.between_incidence
        A H B hAHBbet).2.2.2.2

    have hRayBHA :
        HilbertSameRay Geo B H A :=
      hilbert_sameRay_of_between
        Geo B H A hBHA

    have hRayBAH :
        HilbertSameRay Geo B A H :=
      hilbert_sameRay_symm
        Geo B H A hRayBHA

    have hLeft :
        Geo.Angle A B P =
        Geo.Angle H B P :=
      hilbert_angle_eq_of_sameRay_first
        Geo B A H P hRayBAH

    have hRight :
        Geo.Angle A B Q =
        Geo.Angle H B Q :=
      hilbert_angle_eq_of_sameRay_first
        Geo B A H Q hRayBAH

    unfold Geometry.Geo.AngleCongruent at hAngle ⊢
    rw [← hLeft, ← hRight]
    exact hAngle

/--
If two distinct points A and B are equidistant from P and Q,
then the line AB bisects PQ at every point H where PQ meets AB.

This is the perpendicular-bisector property needed in the
Hilbert reconstruction of Euclid I.12.
-/
theorem hilbert_equidistant_line_bisects_segment
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B P Q H : Geo.Point)
    (base : Geo.Line)
    (hAB : A ≠ B)
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hHbase : HilbertIncidence.OnLine H base)
    (hOppPQ : HilbertOppositeSide Geo P Q base)
    (hAP_AQ : Geo.Congruent A P A Q)
    (hBP_BQ : Geo.Congruent B P B Q)
    (hPHQ : Geo.Between P H Q) :
    Geo.Congruent P H H Q := by

  ----------------------------------------------------------------------
  -- Basic incidence data for P-H-Q.
  ----------------------------------------------------------------------

  have hPHQData :=
    HilbertOrder.between_incidence
      P H Q hPHQ

  have hPH : P ≠ H :=
    hPHQData.1

  have hHQ : H ≠ Q :=
    hPHQData.2.1

  have hPQ : P ≠ Q :=
    hPHQData.2.2.1

  ----------------------------------------------------------------------
  -- Construct the line PQ.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        P Q hPQ with
    ⟨linePQ, hPlinePQ, hQlinePQ⟩

  ----------------------------------------------------------------------
  -- A and B are both equidistant from P and Q.
  -- Hilbert Theorem 17 therefore gives the symmetry of the
  -- two rays BP and BQ with respect to BA.
  ----------------------------------------------------------------------

  have hAngleABP_ABQ :
      Geo.AngleCongruent A B P A B Q :=
    hilbert_theorem_17
      Geo
      A B P Q
      base linePQ
      hAB
      hAbase
      hBbase
      hOppPQ
      hPlinePQ
      hQlinePQ
      hAP_AQ
      hBP_BQ

  ----------------------------------------------------------------------
  -- From this point we exploit H ∈ AB and P-H-Q.
  --
  -- If H = A or H = B, the midpoint congruence follows immediately
  -- from the corresponding equidistance hypothesis.
  -- Otherwise we transport the angle congruence from BA to BH.
  ----------------------------------------------------------------------

  by_cases hHA : H = A

  · subst H

    exact
      CongruentReverseFirst
        Geo A P A Q hAP_AQ

  · by_cases hHB : H = B

    · subst H

      exact
        CongruentReverseFirst
          Geo B P B Q hBP_BQ

    ·
      have hAH : A ≠ H := by
        intro h
        exact hHA h.symm

      have hBH : B ≠ H := by
        intro h
        exact hHB h.symm

      have hBP : B ≠ P := by
        intro h
        subst P
        exact hOppPQ.1 hBbase

      have hBQ : B ≠ Q := by
        intro h
        subst Q
        exact hOppPQ.2.1 hBbase

      have hABH :
          PrimCollinear Geo A B H :=
        ⟨base,
         hAbase,
         hBbase,
         hHbase⟩

      --------------------------------------------------------------------
      -- P and Q do not lie on base.
      --------------------------------------------------------------------

      have hABP :
          ¬ PrimCollinear Geo A B P := by
        intro h

        rcases h with
          ⟨l, hAl, hBl, hPl⟩

        have hEq :
            l = base :=
          HilbertPlaneIncidence.line_unique
            A B hAB
            l base
            hAl hBl
            hAbase hBbase

        have hPbase :
            HilbertIncidence.OnLine P base := by
          rw [← hEq]
          exact hPl

        exact hOppPQ.1 hPbase

      have hABQ :
          ¬ PrimCollinear Geo A B Q := by
        intro h

        rcases h with
          ⟨l, hAl, hBl, hQl⟩

        have hEq :
            l = base :=
          HilbertPlaneIncidence.line_unique
            A B hAB
            l base
            hAl hBl
            hAbase hBbase

        have hQbase :
            HilbertIncidence.OnLine Q base := by
          rw [← hEq]
          exact hQl

        exact hOppPQ.2.1 hQbase

      --------------------------------------------------------------------
      -- Transport the congruent angles from ray BA to ray BH.
      --------------------------------------------------------------------

      have hAngleHBP_HBQ :
          Geo.AngleCongruent H B P H B Q :=
        hilbert_collinear_angle_transport
          Geo
          A B H P Q
          hAB
          hAH
          hBH
          hBP
          hBQ
          hABH
          hABP
          hABQ
          hAngleABP_ABQ

      --------------------------------------------------------------------
      -- SAS for triangles BHP and BHQ.
      --------------------------------------------------------------------

      have hBHP :
          ¬ Collinear Geo B H P :=
        hilbert_not_collinear_of_off_line
          Geo
          B H P
          base
          hBH
          hBbase
          hHbase
          hOppPQ.1

      have hBHQ :
          ¬ Collinear Geo B H Q :=
        hilbert_not_collinear_of_off_line
          Geo
          B H Q
          base
          hBH
          hBbase
          hHbase
          hOppPQ.2.1

      have hBH_BH :
          Geo.Congruent B H B H :=
        hilbert_congruent_reflexive
          Geo B H

      have hSAS_BHP_BHQ :=
        SAS
          Geo
          B H P
          B H Q
          hBHP
          hBHQ
          hBH_BH
          hAngleHBP_HBQ
          hBP_BQ

      have hHP_HQ :
          Geo.Congruent H P H Q :=
        hSAS_BHP_BHQ.sideBC

      exact
        CongruentReverseFirst
          Geo H P H Q hHP_HQ

end Geometry

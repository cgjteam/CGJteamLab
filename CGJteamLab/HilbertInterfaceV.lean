import CGJteamLab.HilbertAxiomsWork
import CGJteamLab.HilbertBookZero
import CGJteamLab.HilbertSegmentArithmetic

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# HilbertInterfaceV

Reusable magnitude and Eudoxus layer needed for Euclid Book V and
the classical route to Euclid XI.23.

Architecture:

1. strict order on positive segment classes;
2. order-compatible positive addition;
3. positive differences;
4. positive natural multiples;
5. Archimedean bridge;
6. Eudoxus proportions and reusable comparison infrastructure.

This file intentionally extends the existing legacy Hilbert interface.
It does not modify the source-faithful Grundlagen layer and it does not
identify Eudoxus proportion with the existing angle-coded proportion.
-/

------------------------------------------------------------------------
-- Part I. Strict order on positive segment classes
------------------------------------------------------------------------

/--
Strict order on positive Hilbert segment classes.

The relation is the quotient lift of Hilbert's geometric strict segment
comparison.
-/
def HilbertPositiveSegmentLess
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) : Prop :=
  Quotient.liftOn₂
    a
    b
    (fun s t =>
      HilbertSegmentLess
        Geo
        s.val.1 s.val.2
        t.val.1 t.val.2)
    (by
      intro s t s' t' hs ht
      apply propext
      constructor

      · intro hst

        have hs't :
            HilbertSegmentLess
              Geo
              s'.val.1 s'.val.2
              t.val.1 t.val.2 :=
          bookZero_32_lessThanCongruence2
            Geo
            s.val.1 s.val.2
            t.val.1 t.val.2
            s'.val.1 s'.val.2
            hst
            hs

        exact
          bookZero_30_lessThanCongruence
            Geo
            s'.val.1 s'.val.2
            t.val.1 t.val.2
            t'.val.1 t'.val.2
            hs't
            ht

      · intro hs't'

        have hs_t' :
            HilbertSegmentLess
              Geo
              s.val.1 s.val.2
              t'.val.1 t'.val.2 :=
          bookZero_32_lessThanCongruence2
            Geo
            s'.val.1 s'.val.2
            t'.val.1 t'.val.2
            s.val.1 s.val.2
            hs't'
            (hilbert_congruent_symmetry
              Geo
              s.val.1 s.val.2
              s'.val.1 s'.val.2
              hs)

        exact
          bookZero_30_lessThanCongruence
            Geo
            s.val.1 s.val.2
            t'.val.1 t'.val.2
            t.val.1 t.val.2
            hs_t'
            (hilbert_congruent_symmetry
              Geo
              t.val.1 t.val.2
              t'.val.1 t'.val.2
              ht))

/--
For concrete nondegenerate representatives, quotient order is exactly
Hilbert's geometric strict segment order.
-/
theorem hilbertPositiveSegmentClassOf_less_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hAB : Ne A B)
    (hCD : Ne C D) :
    HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentClassOf Geo A B hAB)
        (hilbertPositiveSegmentClassOf Geo C D hCD)
      <->
    HilbertSegmentLess Geo A B C D := by
  rfl

/--
Strict order on positive segment classes is asymmetric.
-/
theorem hilbertPositiveSegmentLess_asymm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo)
    (hab : HilbertPositiveSegmentLess Geo a b) :
    Not (HilbertPositiveSegmentLess Geo b a) := by

  revert hab

  refine Quotient.inductionOn₂ a b ?_
  intro s t

  change
    HilbertSegmentLess
      Geo
      s.val.1 s.val.2
      t.val.1 t.val.2
      ->
    Not
      (HilbertSegmentLess
        Geo
        t.val.1 t.val.2
        s.val.1 s.val.2)

  exact
    hilbert_segmentLess_asymm
      Geo
      s.val.1 s.val.2
      t.val.1 t.val.2

/--
Strict order on positive segment classes is irreflexive.
-/
theorem hilbertPositiveSegmentLess_irrefl
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a : HilbertPositiveSegmentClass Geo) :
    Not (HilbertPositiveSegmentLess Geo a a) := by

  intro h
  exact
    (hilbertPositiveSegmentLess_asymm
      Geo a a h) h

/--
Strict order on positive segment classes is transitive.
-/
theorem hilbertPositiveSegmentLess_trans
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo)
    (hab : HilbertPositiveSegmentLess Geo a b)
    (hbc : HilbertPositiveSegmentLess Geo b c) :
    HilbertPositiveSegmentLess Geo a c := by

  revert hab hbc

  refine Quotient.inductionOn a ?_
  intro s

  refine Quotient.inductionOn b ?_
  intro t

  refine Quotient.inductionOn c ?_
  intro q

  change
    HilbertSegmentLess
      Geo
      s.val.1 s.val.2
      t.val.1 t.val.2
      ->
    HilbertSegmentLess
      Geo
      t.val.1 t.val.2
      q.val.1 q.val.2
      ->
    HilbertSegmentLess
      Geo
      s.val.1 s.val.2
      q.val.1 q.val.2

  exact
    bookZero_52_lessThanTransitive
      Geo
      s.val.1 s.val.2
      t.val.1 t.val.2
      q.val.1 q.val.2

/--
Trichotomy for positive segment classes.
-/
theorem hilbertPositiveSegmentLess_trichotomy
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentLess Geo a b \/
    a = b \/
    HilbertPositiveSegmentLess Geo b a := by

  refine Quotient.inductionOn₂ a b ?_
  intro s t

  by_cases hst :
      HilbertSegmentLess
        Geo
        s.val.1 s.val.2
        t.val.1 t.val.2

  · exact Or.inl hst

  · by_cases hts :
        HilbertSegmentLess
          Geo
          t.val.1 t.val.2
          s.val.1 s.val.2

    · exact Or.inr (Or.inr hts)

    · have hCong :
          Geo.Congruent
            s.val.1 s.val.2
            t.val.1 t.val.2 :=
        bookZero_31_trichotomy1
          Geo
          s.val.1 s.val.2
          t.val.1 t.val.2
          hst
          hts
          s.property
          t.property

      exact
        Or.inr
          (Or.inl
            (Quotient.sound hCong))

/--
Strict inequality implies inequality of positive segment classes.
-/
theorem hilbertPositiveSegmentLess_ne
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo)
    (hab : HilbertPositiveSegmentLess Geo a b) :
    Ne a b := by

  intro habEq
  subst b

  exact
    hilbertPositiveSegmentLess_irrefl
      Geo a hab

------------------------------------------------------------------------
-- Part II. Compatibility with positive addition
------------------------------------------------------------------------

/--
Adding the same positive segment class on the right preserves strict order.
-/
theorem hilbertPositiveSegment_add_lt_add_right
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo)
    (hab : HilbertPositiveSegmentLess Geo a b) :
    HilbertPositiveSegmentLess Geo (a + c) (b + c) := by

  rcases
      hilbertPositiveSegmentAdd_spec
        Geo a c
    with
    ⟨A, B, E, hABE, hABa, hBEc, hAEac⟩

  rcases
      hilbertPositiveSegmentAdd_spec
        Geo b c
    with
    ⟨C, D, F, hCDF, hCDb, hDFc, hCFbc⟩

  have hAB : Ne A B :=
    (HilbertOrder.between_incidence
      A B E hABE).1

  have hBE : Ne B E :=
    (HilbertOrder.between_incidence
      A B E hABE).2.1

  have hAE : Ne A E :=
    (HilbertOrder.between_incidence
      A B E hABE).2.2.1

  have hCD : Ne C D :=
    (HilbertOrder.between_incidence
      C D F hCDF).1

  have hDF : Ne D F :=
    (HilbertOrder.between_incidence
      C D F hCDF).2.1

  have hCF : Ne C F :=
    (HilbertOrder.between_incidence
      C D F hCDF).2.2.1

  have hABCDClass :
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentClassOf Geo A B hAB)
        (hilbertPositiveSegmentClassOf Geo C D hCD) := by
    simpa [hABa, hCDb] using hab

  have hABCD :
      HilbertSegmentLess Geo A B C D :=
    (hilbertPositiveSegmentClassOf_less_iff
      Geo A B C D hAB hCD).1
      hABCDClass

  have hBEeqDF :
      hilbertPositiveSegmentClassOf Geo B E hBE =
      hilbertPositiveSegmentClassOf Geo D F hDF :=
    hBEc.trans hDFc.symm

  have hBEDF :
      Geo.Congruent B E D F :=
    Quotient.exact hBEeqDF

  have hAECF :
      HilbertSegmentLess Geo A E C F :=
    bookZero_53_lessThanAdditive
      Geo
      A B
      C D
      E F
      hABCD
      hABE
      hCDF
      hBEDF

  have hClass :
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentClassOf Geo A E hAE)
        (hilbertPositiveSegmentClassOf Geo C F hCF) :=
    (hilbertPositiveSegmentClassOf_less_iff
      Geo A E C F hAE hCF).2
      hAECF

  change
    HilbertPositiveSegmentLess
      Geo
      (hilbertPositiveSegmentAdd Geo a c)
      (hilbertPositiveSegmentAdd Geo b c)

  rw [← hAEac, ← hCFbc]

  exact hClass

/--
Adding the same positive segment class on the left preserves strict order.
-/
theorem hilbertPositiveSegment_add_lt_add_left
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo)
    (hab : HilbertPositiveSegmentLess Geo a b) :
    HilbertPositiveSegmentLess Geo (c + a) (c + b) := by

  change
    HilbertPositiveSegmentLess
      Geo
      (hilbertPositiveSegmentAdd Geo c a)
      (hilbertPositiveSegmentAdd Geo c b)

  rw [
    hilbertPositiveSegmentAdd_comm Geo c a,
    hilbertPositiveSegmentAdd_comm Geo c b
  ]

  have hRight :
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentAdd Geo a c)
        (hilbertPositiveSegmentAdd Geo b c) := by

    have h :=
      hilbertPositiveSegment_add_lt_add_right
        Geo a b c hab

    change
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentAdd Geo a c)
        (hilbertPositiveSegmentAdd Geo b c)
      at h

    exact h

  exact hRight

/--
Strict order is reflected by adding the same positive class on the right.
-/
theorem hilbertPositiveSegment_lt_of_add_lt_add_right
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo)
    (h :
      HilbertPositiveSegmentLess
        Geo
        (a + c)
        (b + c)) :
    HilbertPositiveSegmentLess Geo a b := by

  rcases
      hilbertPositiveSegmentLess_trichotomy
        Geo a b
    with
    hab | habEq | hba

  · exact hab

  · subst b
    exact
      False.elim
        ((hilbertPositiveSegmentLess_irrefl
          Geo (a + c)) h)

  · have hReverse :
        HilbertPositiveSegmentLess
          Geo
          (b + c)
          (a + c) :=
      hilbertPositiveSegment_add_lt_add_right
        Geo b a c hba

    exact
      False.elim
        ((hilbertPositiveSegmentLess_asymm
          Geo
          (a + c)
          (b + c)
          h)
          hReverse)

/--
Right addition preserves and reflects strict order.
-/
theorem hilbertPositiveSegment_add_lt_add_right_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentLess Geo (a + c) (b + c)
      <->
    HilbertPositiveSegmentLess Geo a b := by

  constructor

  · exact
      hilbertPositiveSegment_lt_of_add_lt_add_right
        Geo a b c

  · exact
      hilbertPositiveSegment_add_lt_add_right
        Geo a b c

------------------------------------------------------------------------
-- Part III. Positive difference
------------------------------------------------------------------------

/--
Every positive summand makes a positive segment class strictly larger.
-/
theorem hilbertPositiveSegment_lt_add_right
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a c : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentLess Geo a (a + c) := by

  rcases
      hilbertPositiveSegmentAdd_spec
        Geo a c
    with
    ⟨A, B, C, hABC, hABa, hBCc, hACsum⟩

  have hAB : Ne A B :=
    (HilbertOrder.between_incidence
      A B C hABC).1

  have hAC : Ne A C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.2.1

  have hABAC :
      HilbertSegmentLess Geo A B A C :=
    hilbert_segmentLess_of_between
      Geo A B C hABC

  have hClass :
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentClassOf Geo A B hAB)
        (hilbertPositiveSegmentClassOf Geo A C hAC) :=
    (hilbertPositiveSegmentClassOf_less_iff
      Geo A B A C hAB hAC).2
      hABAC

  change
    HilbertPositiveSegmentLess
      Geo
      a
      (hilbertPositiveSegmentAdd Geo a c)

  have hClass' := hClass

  rw [hABa, hACsum] at hClass'

  exact hClass'

/--
If a positive segment class is strictly smaller than another one,
the larger class is obtained by adding a positive remainder.
-/
theorem hilbertPositiveSegment_exists_add_of_less
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo)
    (hab : HilbertPositiveSegmentLess Geo a b) :
    Exists (fun c : HilbertPositiveSegmentClass Geo =>
      a + c = b) := by

  revert hab

  refine Quotient.inductionOn a ?_
  intro s

  refine Quotient.inductionOn b ?_
  intro t hst

  change
    HilbertSegmentLess
      Geo
      s.val.1 s.val.2
      t.val.1 t.val.2
    at hst

  rcases hst with
    ⟨P, hTPU, hSTP⟩

  have hTP : Ne t.val.1 P :=
    (HilbertOrder.between_incidence
      t.val.1 P t.val.2 hTPU).1

  have hPU : Ne P t.val.2 :=
    (HilbertOrder.between_incidence
      t.val.1 P t.val.2 hTPU).2.1

  let c : HilbertPositiveSegmentClass Geo :=
    hilbertPositiveSegmentClassOf
      Geo P t.val.2 hPU

  have hTPeqS :
      hilbertPositiveSegmentClassOf
          Geo t.val.1 P hTP =
        Quotient.mk
          (hilbertPositiveSegmentSetoid Geo)
          s := by

    exact
      Quotient.sound
        (hilbert_congruent_symmetry
          Geo
          s.val.1 s.val.2
          t.val.1 P
          hSTP)

  have hSum :
      HilbertPositiveSegmentSum
        Geo
        (Quotient.mk
          (hilbertPositiveSegmentSetoid Geo)
          s)
        c
        (Quotient.mk
          (hilbertPositiveSegmentSetoid Geo)
          t) := by

    refine
      ⟨t.val.1, P, t.val.2, hTPU, ?_, ?_, ?_⟩

    · exact hTPeqS

    · rfl

    · rfl

  refine Exists.intro c ?_

  exact
    hilbertPositiveSegmentSum_unique
      Geo
      (Quotient.mk
        (hilbertPositiveSegmentSetoid Geo)
        s)
      c
      ((Quotient.mk
        (hilbertPositiveSegmentSetoid Geo)
        s) + c)
      (Quotient.mk
        (hilbertPositiveSegmentSetoid Geo)
        t)
      (hilbertPositiveSegmentAdd_spec
        Geo
        (Quotient.mk
          (hilbertPositiveSegmentSetoid Geo)
          s)
        c)
      hSum

/--
For positive segment classes, strict order is equivalent to existence
of a positive additive remainder.
-/
theorem hilbertPositiveSegment_less_iff_exists_add
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentLess Geo a b
      <->
    Exists (fun c : HilbertPositiveSegmentClass Geo =>
      a + c = b) := by

  constructor

  · exact
      hilbertPositiveSegment_exists_add_of_less
        Geo a b

  · intro h

    rcases h with ⟨c, hacb⟩

    have hlt :
        HilbertPositiveSegmentLess Geo a (a + c) :=
      hilbertPositiveSegment_lt_add_right
        Geo a c

    rw [hacb] at hlt
    exact hlt

------------------------------------------------------------------------
-- Optional notation interface
------------------------------------------------------------------------

/--
Local LT instance for positive segment classes.

No LinearOrder instance is installed here. Book V needs only the strict
order relation and its proved laws.
-/
instance hilbertPositiveSegmentClassLT
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    LT (HilbertPositiveSegmentClass Geo) where
  lt := HilbertPositiveSegmentLess Geo


------------------------------------------------------------------------
-- Part IV. Positive natural multiples
------------------------------------------------------------------------

/--
Notation-level commutativity helper for positive segment addition.

The older theorem `hilbertPositiveSegmentAdd_comm` is stated for the
explicit function `hilbertPositiveSegmentAdd`; this wrapper is more
convenient once the `Add` instance is active.
-/
theorem hilbertPositiveSegment_add_comm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    a + b = b + a := by

  change
    hilbertPositiveSegmentAdd Geo a b =
      hilbertPositiveSegmentAdd Geo b a

  exact
    hilbertPositiveSegmentAdd_comm
      Geo a b

/--
Positive natural multiple of a positive segment class.

The natural index is shifted by one:

  index 0 represents 1 * a,
  index 1 represents 2 * a,
  ...
  index n represents (n + 1) copies of a.

This avoids introducing a zero segment class into the positive-magnitude
layer.
-/
noncomputable def hilbertPositiveSegmentMultiple
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentClass Geo :=
  Nat.rec
    a
    (fun _ x => x + a)
    n

/--
Index zero is one positive copy.
-/
theorem hilbertPositiveSegmentMultiple_zero
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMultiple Geo 0 a = a := by

  simp [hilbertPositiveSegmentMultiple]

/--
Successor index adds one further positive copy.
-/
theorem hilbertPositiveSegmentMultiple_succ
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMultiple Geo (Nat.succ n) a =
      hilbertPositiveSegmentMultiple Geo n a + a := by

  simp [hilbertPositiveSegmentMultiple]

/--
A positive multiple distributes over addition.

Because index n means n+1 copies, this is the positive-magnitude
version of Euclid V.1.
-/
theorem hilbertPositiveSegmentMultiple_add
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a b : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMultiple Geo n (a + b) =
      hilbertPositiveSegmentMultiple Geo n a +
      hilbertPositiveSegmentMultiple Geo n b := by

  induction n with

  | zero =>
      simp only [hilbertPositiveSegmentMultiple_zero]

  | succ n ih =>

      let x :=
        hilbertPositiveSegmentMultiple Geo n a

      let y :=
        hilbertPositiveSegmentMultiple Geo n b

      calc
        hilbertPositiveSegmentMultiple
            Geo (Nat.succ n) (a + b) =
            hilbertPositiveSegmentMultiple Geo n (a + b) +
              (a + b) := by
          exact
            hilbertPositiveSegmentMultiple_succ
              Geo n (a + b)

        _ =
            (hilbertPositiveSegmentMultiple Geo n a +
              hilbertPositiveSegmentMultiple Geo n b) +
              (a + b) := by
          rw [ih]

        _ = (x + y) + (a + b) := by
          rfl

        _ = x + (y + (a + b)) := by
          exact
            hilbertPositiveSegment_add_assoc
              Geo x y (a + b)

        _ = x + ((y + a) + b) := by
          rw [
            ← hilbertPositiveSegment_add_assoc
              Geo y a b
          ]

        _ = x + ((a + y) + b) := by
          rw [
            hilbertPositiveSegment_add_comm
              Geo y a
          ]

        _ = x + (a + (y + b)) := by
          rw [
            hilbertPositiveSegment_add_assoc
              Geo a y b
          ]

        _ = (x + a) + (y + b) := by
          rw [
            ← hilbertPositiveSegment_add_assoc
              Geo x a (y + b)
          ]

        _ =
            (hilbertPositiveSegmentMultiple Geo n a + a) +
              (hilbertPositiveSegmentMultiple Geo n b + b) := by
          rfl

        _ =
            hilbertPositiveSegmentMultiple Geo (Nat.succ n) a +
              hilbertPositiveSegmentMultiple Geo (Nat.succ n) b := by
          rw [
            hilbertPositiveSegmentMultiple_succ,
            hilbertPositiveSegmentMultiple_succ
          ]

/--
Positive multiplication preserves strict order.
-/
theorem hilbertPositiveSegmentMultiple_lt
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a b : HilbertPositiveSegmentClass Geo)
    (hab : HilbertPositiveSegmentLess Geo a b) :
    HilbertPositiveSegmentLess
      Geo
      (hilbertPositiveSegmentMultiple Geo n a)
      (hilbertPositiveSegmentMultiple Geo n b) := by

  induction n with

  | zero =>
      simpa only [hilbertPositiveSegmentMultiple_zero] using hab

  | succ n ih =>

      have h1 :
          HilbertPositiveSegmentLess
            Geo
            (hilbertPositiveSegmentMultiple Geo n a + a)
            (hilbertPositiveSegmentMultiple Geo n b + a) :=
        hilbertPositiveSegment_add_lt_add_right
          Geo
          (hilbertPositiveSegmentMultiple Geo n a)
          (hilbertPositiveSegmentMultiple Geo n b)
          a
          ih

      have h2 :
          HilbertPositiveSegmentLess
            Geo
            (hilbertPositiveSegmentMultiple Geo n b + a)
            (hilbertPositiveSegmentMultiple Geo n b + b) :=
        hilbertPositiveSegment_add_lt_add_left
          Geo
          a
          b
          (hilbertPositiveSegmentMultiple Geo n b)
          hab

      have h3 :
          HilbertPositiveSegmentLess
            Geo
            (hilbertPositiveSegmentMultiple Geo n a + a)
            (hilbertPositiveSegmentMultiple Geo n b + b) :=
        hilbertPositiveSegmentLess_trans
          Geo
          (hilbertPositiveSegmentMultiple Geo n a + a)
          (hilbertPositiveSegmentMultiple Geo n b + a)
          (hilbertPositiveSegmentMultiple Geo n b + b)
          h1
          h2

      simpa only [hilbertPositiveSegmentMultiple_succ] using h3

/--
Positive multiplication reflects strict order.
-/
theorem hilbertPositiveSegment_lt_of_multiple_lt
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a b : HilbertPositiveSegmentClass Geo)
    (h :
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo n a)
        (hilbertPositiveSegmentMultiple Geo n b)) :
    HilbertPositiveSegmentLess Geo a b := by

  rcases
      hilbertPositiveSegmentLess_trichotomy
        Geo a b
    with
    hab | habEq | hba

  · exact hab

  · subst b

    exact
      False.elim
        ((hilbertPositiveSegmentLess_irrefl
          Geo
          (hilbertPositiveSegmentMultiple Geo n a))
          h)

  · have hReverse :
        HilbertPositiveSegmentLess
          Geo
          (hilbertPositiveSegmentMultiple Geo n b)
          (hilbertPositiveSegmentMultiple Geo n a) :=
      hilbertPositiveSegmentMultiple_lt
        Geo n b a hba

    exact
      False.elim
        ((hilbertPositiveSegmentLess_asymm
          Geo
          (hilbertPositiveSegmentMultiple Geo n a)
          (hilbertPositiveSegmentMultiple Geo n b)
          h)
          hReverse)

/--
A positive natural multiple preserves and reflects strict order.
-/
theorem hilbertPositiveSegmentMultiple_lt_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo n a)
        (hilbertPositiveSegmentMultiple Geo n b)
      <->
    HilbertPositiveSegmentLess Geo a b := by

  constructor

  · exact
      hilbertPositiveSegment_lt_of_multiple_lt
        Geo n a b

  · exact
      hilbertPositiveSegmentMultiple_lt
        Geo n a b

/--
A positive natural multiple preserves and reflects equality.
-/
theorem hilbertPositiveSegmentMultiple_eq_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a b : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMultiple Geo n a =
        hilbertPositiveSegmentMultiple Geo n b
      <->
    a = b := by

  constructor

  · intro hEq

    rcases
        hilbertPositiveSegmentLess_trichotomy
          Geo a b
      with
      hab | habEq | hba

    · have hLt :
          HilbertPositiveSegmentLess
            Geo
            (hilbertPositiveSegmentMultiple Geo n a)
            (hilbertPositiveSegmentMultiple Geo n b) :=
        hilbertPositiveSegmentMultiple_lt
          Geo n a b hab

      exact
        False.elim
          ((hilbertPositiveSegmentLess_ne
            Geo
            (hilbertPositiveSegmentMultiple Geo n a)
            (hilbertPositiveSegmentMultiple Geo n b)
            hLt)
            hEq)

    · exact habEq

    · have hLt :
          HilbertPositiveSegmentLess
            Geo
            (hilbertPositiveSegmentMultiple Geo n b)
            (hilbertPositiveSegmentMultiple Geo n a) :=
        hilbertPositiveSegmentMultiple_lt
          Geo n b a hba

      exact
        False.elim
          ((hilbertPositiveSegmentLess_ne
            Geo
            (hilbertPositiveSegmentMultiple Geo n b)
            (hilbertPositiveSegmentMultiple Geo n a)
            hLt)
            hEq.symm)

  · intro hEq
    subst b
    rfl

/--
Each successor positive multiple is strictly larger than the preceding one.
-/
theorem hilbertPositiveSegmentMultiple_lt_succ
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentLess
      Geo
      (hilbertPositiveSegmentMultiple Geo n a)
      (hilbertPositiveSegmentMultiple Geo (Nat.succ n) a) := by

  rw [hilbertPositiveSegmentMultiple_succ]

  exact
    hilbertPositiveSegment_lt_add_right
      Geo
      (hilbertPositiveSegmentMultiple Geo n a)
      a


------------------------------------------------------------------------
-- Part V. One-step normalization for weak Archimedean chains
------------------------------------------------------------------------

/--
If a positive multiple is written as `x + a`, then it is not the first
positive multiple. The remainder `x` is exactly the preceding positive
multiple.

This is the algebraic mechanism needed when a weak Hilbert segment chain
takes one step back along the same ray.
-/
theorem hilbertPositiveSegmentMultiple_eq_add_right_predecessor
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a x : HilbertPositiveSegmentClass Geo)
    (h :
      hilbertPositiveSegmentMultiple Geo n a =
        x + a) :
    Exists fun k : Nat =>
      n = Nat.succ k /\
      x = hilbertPositiveSegmentMultiple Geo k a := by

  cases n with

  | zero =>

      have hEq :
          a = x + a := by
        simpa only [
          hilbertPositiveSegmentMultiple_zero
        ] using h

      have hLt0 :
          HilbertPositiveSegmentLess
            Geo
            a
            (a + x) :=
        hilbertPositiveSegment_lt_add_right
          Geo a x

      have hLt :
          HilbertPositiveSegmentLess
            Geo
            a
            (x + a) := by
        rw [
          hilbertPositiveSegment_add_comm
            Geo x a
        ]
        exact hLt0

      exact
        False.elim
          ((hilbertPositiveSegmentLess_ne
            Geo a (x + a) hLt)
            hEq)

  | succ k =>

      refine Exists.intro k ?_
      constructor

      · rfl

      · have hCancel :
            hilbertPositiveSegmentMultiple Geo k a + a =
              x + a := by
          simpa only [
            hilbertPositiveSegmentMultiple_succ
          ] using h

        exact
          (hilbertPositiveSegment_add_right_cancel
            Geo
            (hilbertPositiveSegmentMultiple Geo k a)
            x
            a
            hCancel).symm

/--
One algebraic step of a weak equal-step walk preserves the property
"being a positive natural multiple of a".

The next radius may increase by one copy or decrease by one copy.
-/
theorem hilbertPositiveSegmentMultiple_step
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (n : Nat)
    (a p q : HilbertPositiveSegmentClass Geo)
    (hp :
      p =
        hilbertPositiveSegmentMultiple Geo n a)
    (hStep :
      q = p + a \/
      p = q + a) :
    Exists fun m : Nat =>
      q =
        hilbertPositiveSegmentMultiple Geo m a := by

  rcases hStep with hForward | hBackward

  · refine Exists.intro (Nat.succ n) ?_

    calc
      q = p + a := hForward
      _ =
          hilbertPositiveSegmentMultiple Geo n a + a := by
        rw [hp]
      _ =
          hilbertPositiveSegmentMultiple
            Geo (Nat.succ n) a := by
        symm
        exact
          hilbertPositiveSegmentMultiple_succ
            Geo n a

  · have hMul :
        hilbertPositiveSegmentMultiple Geo n a =
          q + a := by
      calc
        hilbertPositiveSegmentMultiple Geo n a = p := hp.symm
        _ = q + a := hBackward

    rcases
        hilbertPositiveSegmentMultiple_eq_add_right_predecessor
          Geo n a q hMul
      with
      ⟨k, _hn, hq⟩

    exact ⟨k, hq⟩

/--
Two distinct points on the same ray from A, separated by one copy of CD,
have radial positive segment classes which differ by exactly one copy
of CD.

This is the geometric one-step normalization lemma for the weak
`HilbertSegmentChain`: the step may point forward or backward.
-/
theorem hilbertPositiveSegment_sameRay_equalStep
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D X Y : Geo.Point)
    (hCD : Ne C D)
    (hRayX : HilbertSameRay Geo A B X)
    (hRayY : HilbertSameRay Geo A B Y)
    (hXYCD : Geo.Congruent X Y C D) :

    let hAX : Ne A X := hRayX.2.1.symm
    let hAY : Ne A Y := hRayY.2.1.symm
    let a :=
      hilbertPositiveSegmentClassOf Geo C D hCD
    let p :=
      hilbertPositiveSegmentClassOf Geo A X hAX
    let q :=
      hilbertPositiveSegmentClassOf Geo A Y hAY

    q = p + a \/
    p = q + a := by

  dsimp

  have hAX : Ne A X :=
    hRayX.2.1.symm

  have hAY : Ne A Y :=
    hRayY.2.1.symm

  have hCDXY :
      Geo.Congruent C D X Y :=
    hilbert_congruent_symmetry
      Geo X Y C D hXYCD

  have hXY : Ne X Y :=
    bookZero_nullSegment3
      Geo C D X Y hCD hCDXY

  have hRayXY :
      HilbertSameRay Geo A X Y :=
    hilbert_sameRay_common_reference
      Geo
      A B X Y
      hRayX
      hRayY

  have hCol :
      PrimCollinear Geo A X Y :=
    hRayXY.2.2.1

  have hXYClass :
      hilbertPositiveSegmentClassOf Geo X Y hXY =
        hilbertPositiveSegmentClassOf Geo C D hCD := by
    exact
      Quotient.sound hXYCD

  rcases
      hilbert_between_trichotomy
        Geo
        A X Y
        hAX
        hXY
        hAY
        hCol
    with
    hAXY | hXAY | hAYX

  · have hSum :
        HilbertPositiveSegmentSum
          Geo
          (hilbertPositiveSegmentClassOf Geo A X hAX)
          (hilbertPositiveSegmentClassOf Geo C D hCD)
          (hilbertPositiveSegmentClassOf Geo A Y hAY) := by

      have hRaw :=
        hilbertPositiveSegmentSum_of_between
          Geo A X Y hAXY

      rw [hXYClass] at hRaw

      simpa using hRaw

    have hEq :
        hilbertPositiveSegmentClassOf Geo A Y hAY =
          hilbertPositiveSegmentClassOf Geo A X hAX +
            hilbertPositiveSegmentClassOf Geo C D hCD :=
      hilbertPositiveSegmentSum_unique
        Geo
        (hilbertPositiveSegmentClassOf Geo A X hAX)
        (hilbertPositiveSegmentClassOf Geo C D hCD)
        (hilbertPositiveSegmentClassOf Geo A Y hAY)
        (hilbertPositiveSegmentClassOf Geo A X hAX +
          hilbertPositiveSegmentClassOf Geo C D hCD)
        hSum
        (hilbertPositiveSegmentAdd_spec
          Geo
          (hilbertPositiveSegmentClassOf Geo A X hAX)
          (hilbertPositiveSegmentClassOf Geo C D hCD))

    exact Or.inl hEq

  · exact
      False.elim
        (hRayXY.2.2.2 hXAY)

  · have hYX : Ne Y X :=
      hXY.symm

    have hYXClass :
        hilbertPositiveSegmentClassOf Geo Y X hYX =
          hilbertPositiveSegmentClassOf Geo C D hCD := by

      calc
        hilbertPositiveSegmentClassOf Geo Y X hYX =
            hilbertPositiveSegmentClassOf Geo X Y hXY := by
          exact
            (hilbertPositiveSegmentClassOf_swap
              Geo X Y hXY).symm

        _ =
            hilbertPositiveSegmentClassOf Geo C D hCD :=
          hXYClass

    have hSum :
        HilbertPositiveSegmentSum
          Geo
          (hilbertPositiveSegmentClassOf Geo A Y hAY)
          (hilbertPositiveSegmentClassOf Geo C D hCD)
          (hilbertPositiveSegmentClassOf Geo A X hAX) := by

      have hRaw :=
        hilbertPositiveSegmentSum_of_between
          Geo A Y X hAYX

      rw [hYXClass] at hRaw

      simpa using hRaw

    have hEq :
        hilbertPositiveSegmentClassOf Geo A X hAX =
          hilbertPositiveSegmentClassOf Geo A Y hAY +
            hilbertPositiveSegmentClassOf Geo C D hCD :=
      hilbertPositiveSegmentSum_unique
        Geo
        (hilbertPositiveSegmentClassOf Geo A Y hAY)
        (hilbertPositiveSegmentClassOf Geo C D hCD)
        (hilbertPositiveSegmentClassOf Geo A X hAX)
        (hilbertPositiveSegmentClassOf Geo A Y hAY +
          hilbertPositiveSegmentClassOf Geo C D hCD)
        hSum
        (hilbertPositiveSegmentAdd_spec
          Geo
          (hilbertPositiveSegmentClassOf Geo A Y hAY)
          (hilbertPositiveSegmentClassOf Geo C D hCD))

    exact Or.inr hEq


------------------------------------------------------------------------
-- Part VI. Normalization of weak Archimedean chains
------------------------------------------------------------------------

/--
Every positive-index point of a weak `HilbertSegmentChain` has radial
length equal to some positive natural multiple of the common step CD.

The multiple index is not asserted to equal the chain index: the weak
chain is allowed to move backward along the ray.
-/
theorem hilbertSegmentChain_point_is_positive_multiple
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (n : Nat)
    (P : Fin (n + 2) -> Geo.Point)
    (hCD : Ne C D)
    (hChain : HilbertSegmentChain Geo A B C D n P)
    (k : Nat)
    (hkPos : 1 <= k)
    (hkTop : k <= n + 1) :
    Exists fun m : Nat =>
      let hkBound : k < n + 2 :=
        Nat.lt_succ_of_le hkTop
      let iK : Fin (n + 2) :=
        ⟨k, hkBound⟩
      let hRayK : HilbertSameRay Geo A B (P iK) := by
        cases k with
        | zero =>
            exact False.elim
              ((Nat.not_succ_le_zero 0) hkPos)
        | succ j =>
            have hj : j < n + 1 :=
              Nat.lt_of_succ_le hkTop
            let i : Fin (n + 1) := ⟨j, hj⟩
            simpa [iK, i] using hChain.2.2 i
      let hAK : Ne A (P iK) :=
        hRayK.2.1.symm
      hilbertPositiveSegmentClassOf Geo A (P iK) hAK =
        hilbertPositiveSegmentMultiple
          Geo m
          (hilbertPositiveSegmentClassOf Geo C D hCD) := by

  induction k with

  | zero =>
      exact
        False.elim
          ((Nat.not_succ_le_zero 0) hkPos)

  | succ k ih =>

      cases k with

      | zero =>

          have h0lt : 0 < n + 1 :=
            Nat.zero_lt_succ n

          let i0 : Fin (n + 1) :=
            ⟨0, h0lt⟩

          have hRay1 :
              HilbertSameRay Geo A B (P i0.succ) :=
            hChain.2.2 i0

          have hA1 :
              Ne A (P i0.succ) :=
            hRay1.2.1.symm

          have hFirst :
              Geo.Congruent A (P i0.succ) C D := by
            have hStep :=
              hChain.2.1 i0
            simpa [i0, hChain.1] using hStep

          have hClass :
              hilbertPositiveSegmentClassOf
                  Geo A (P i0.succ) hA1 =
                hilbertPositiveSegmentClassOf
                  Geo C D hCD := by
            exact Quotient.sound hFirst

          refine Exists.intro 0 ?_

          dsimp

          have hTarget :
              hilbertPositiveSegmentClassOf
                  Geo A (P i0.succ) hA1 =
                hilbertPositiveSegmentMultiple
                  Geo 0
                  (hilbertPositiveSegmentClassOf
                    Geo C D hCD) := by
            simpa only [
              hilbertPositiveSegmentMultiple_zero
            ] using hClass

          simpa [i0] using hTarget

      | succ j =>

          have hkPredPos :
              1 <= Nat.succ j :=
            Nat.succ_le_succ (Nat.zero_le j)

          have hkPredTop :
              Nat.succ j <= n + 1 :=
            Nat.le_trans
              (Nat.le_succ (Nat.succ j))
              hkTop

          rcases
              ih hkPredPos hkPredTop
            with
            ⟨m, hPredMul⟩

          have hj1 :
              Nat.succ j < n + 1 :=
            Nat.lt_of_succ_le hkTop

          have hj0 :
              j < n + 1 :=
            Nat.lt_trans
              (Nat.lt_succ_self j)
              hj1

          let iPrev : Fin (n + 1) :=
            ⟨j, hj0⟩

          let iStep : Fin (n + 1) :=
            ⟨Nat.succ j, hj1⟩

          have hRayPrev :
              HilbertSameRay
                Geo A B
                (P iPrev.succ) :=
            hChain.2.2 iPrev

          have hRayNext :
              HilbertSameRay
                Geo A B
                (P iStep.succ) :=
            hChain.2.2 iStep

          have hStep :
              Geo.Congruent
                (P iStep.castSucc)
                (P iStep.succ)
                C D :=
            hChain.2.1 iStep

          have hStep' :
              Geo.Congruent
                (P iPrev.succ)
                (P iStep.succ)
                C D := by
            simpa [iPrev, iStep] using hStep

          have hPrevNe :
              Ne A (P iPrev.succ) :=
            hRayPrev.2.1.symm

          have hNextNe :
              Ne A (P iStep.succ) :=
            hRayNext.2.1.symm

          have hPredMul' :
              hilbertPositiveSegmentClassOf
                  Geo A (P iPrev.succ) hPrevNe =
                hilbertPositiveSegmentMultiple
                  Geo m
                  (hilbertPositiveSegmentClassOf
                    Geo C D hCD) := by
            simpa [iPrev] using hPredMul

          have hRadialStep :=
            hilbertPositiveSegment_sameRay_equalStep
              Geo
              A B C D
              (P iPrev.succ)
              (P iStep.succ)
              hCD
              hRayPrev
              hRayNext
              hStep'

          have hRadialStep' :
              hilbertPositiveSegmentClassOf
                    Geo A (P iStep.succ) hNextNe =
                  hilbertPositiveSegmentClassOf
                      Geo A (P iPrev.succ) hPrevNe +
                    hilbertPositiveSegmentClassOf
                      Geo C D hCD
              \/
              hilbertPositiveSegmentClassOf
                    Geo A (P iPrev.succ) hPrevNe =
                  hilbertPositiveSegmentClassOf
                      Geo A (P iStep.succ) hNextNe +
                    hilbertPositiveSegmentClassOf
                      Geo C D hCD := by
            simpa using hRadialStep

          rcases
              hilbertPositiveSegmentMultiple_step
                Geo
                m
                (hilbertPositiveSegmentClassOf Geo C D hCD)
                (hilbertPositiveSegmentClassOf
                  Geo A (P iPrev.succ) hPrevNe)
                (hilbertPositiveSegmentClassOf
                  Geo A (P iStep.succ) hNextNe)
                hPredMul'
                hRadialStep'
            with
            ⟨q, hNextMul⟩

          refine Exists.intro q ?_

          dsimp

          simpa [iStep] using hNextMul

/--
The endpoint of a weak Hilbert segment chain is some positive natural
multiple of the common step CD.
-/
theorem hilbertSegmentChain_endpoint_is_positive_multiple
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (n : Nat)
    (P : Fin (n + 2) -> Geo.Point)
    (hCD : Ne C D)
    (hChain : HilbertSegmentChain Geo A B C D n P) :
    Exists fun m : Nat =>
      let E := P (Fin.last (n + 1))
      let hRayE : HilbertSameRay Geo A B E := by
        have h :=
          hChain.2.2 (Fin.last n)
        change
          HilbertSameRay
            Geo A B
            (P ((Fin.last n).succ))
          at h
        have hIdx :
            (Fin.last n).succ =
              Fin.last (n + 1) := by
          apply Fin.ext
          rfl
        simpa [E, hIdx] using h
      let hAE : Ne A E :=
        hRayE.2.1.symm
      hilbertPositiveSegmentClassOf Geo A E hAE =
        hilbertPositiveSegmentMultiple
          Geo m
          (hilbertPositiveSegmentClassOf Geo C D hCD) := by

  have hkPos :
      1 <= n + 1 :=
    Nat.succ_le_succ (Nat.zero_le n)

  have hkTop :
      n + 1 <= n + 1 :=
    Nat.le_refl (n + 1)

  rcases
      hilbertSegmentChain_point_is_positive_multiple
        Geo
        A B C D
        n P
        hCD
        hChain
        (n + 1)
        hkPos
        hkTop
    with
    ⟨m, hm⟩

  refine Exists.intro m ?_

  dsimp at hm ⊢

  have hIdx :
      Fin.last (n + 1) =
        (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 2)) := by
    apply Fin.ext
    rfl

  cases hIdx

  exact hm

------------------------------------------------------------------------
-- Part VII. Archimedes on positive segment classes
------------------------------------------------------------------------

/--
Archimedean property for positive segment classes.

For any positive classes a and b, some positive natural multiple of a
strictly exceeds b.

This is the magnitude-level bridge needed for Eudoxus Book V.
-/
theorem hilbertPositiveSegment_archimedean
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    Exists fun m : Nat =>
      HilbertPositiveSegmentLess
        Geo
        b
        (hilbertPositiveSegmentMultiple Geo m a) := by

  refine Quotient.inductionOn₂ a b ?_

  intro sa sb

  rcases sa with
    ⟨⟨C, D⟩, hCD⟩

  rcases sb with
    ⟨⟨A, B⟩, hAB⟩

  change Ne C D at hCD
  change Ne A B at hAB

  rcases
      HilbertArchimedeanPlane.archimedes
        (Geo := Geo)
        A B C D
        hAB
        hCD
    with
    ⟨n, P, hChain, hBetween⟩

  let E : Geo.Point :=
    P (Fin.last (n + 1))

  have hAE :
      Ne A E :=
    (HilbertOrder.between_incidence
      A B E hBetween).2.2.1

  have hABAE :
      HilbertSegmentLess Geo A B A E :=
    hilbert_segmentLess_of_between
      Geo A B E hBetween

  have hClassLess :
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentClassOf Geo A B hAB)
        (hilbertPositiveSegmentClassOf Geo A E hAE) :=
    (hilbertPositiveSegmentClassOf_less_iff
      Geo A B A E hAB hAE).2
      hABAE

  rcases
      hilbertSegmentChain_endpoint_is_positive_multiple
        Geo
        A B C D
        n P
        hCD
        hChain
    with
    ⟨m, hEndMul⟩

  refine Exists.intro m ?_

  have hEndMul' :
      hilbertPositiveSegmentClassOf Geo A E hAE =
        hilbertPositiveSegmentMultiple
          Geo m
          (hilbertPositiveSegmentClassOf Geo C D hCD) := by
    simpa [E] using hEndMul

  rw [hEndMul'] at hClassLess

  exact hClassLess


------------------------------------------------------------------------
-- Part VIII. Eudoxus: definitions and elementary logic
------------------------------------------------------------------------

/--
Eudoxus equality of ratios for positive Hilbert segment classes.

Our natural-number multiple index is shifted:
index m means (m+1) copies. Hence all quantified multiples are already
positive, and no separate positivity assumptions on m,n are needed.

The three clauses encode the three possible comparisons of the
cross-multiples:
  m*a < n*b,
  m*a = n*b,
  n*b < m*a.
-/
def HilbertEudoxusProportion
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo) : Prop :=
  forall m n : Nat,
    (HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo n b)
      <->
     HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo m c)
        (hilbertPositiveSegmentMultiple Geo n d))
    /\
    (hilbertPositiveSegmentMultiple Geo m a =
        hilbertPositiveSegmentMultiple Geo n b
      <->
     hilbertPositiveSegmentMultiple Geo m c =
        hilbertPositiveSegmentMultiple Geo n d)
    /\
    (HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo n b)
        (hilbertPositiveSegmentMultiple Geo m a)
      <->
     HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo n d)
        (hilbertPositiveSegmentMultiple Geo m c))

/--
Eudoxus definition of a greater ratio.

The ratio a:b is greater than c:d when some positive multiples witness

  n*b < m*a

while the corresponding comparison on c:d does not hold:

  not (n*d < m*c).

The second condition deliberately allows equality on the c:d side.
-/
def HilbertEudoxusGreaterRatio
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo) : Prop :=
  exists m n : Nat,
    HilbertPositiveSegmentLess
      Geo
      (hilbertPositiveSegmentMultiple Geo n b)
      (hilbertPositiveSegmentMultiple Geo m a)
    /\
    Not
      (HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo n d)
        (hilbertPositiveSegmentMultiple Geo m c))

/--
A ratio is Eudoxus-equal to itself.
-/
theorem hilbertEudoxusProportion_refl
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertEudoxusProportion Geo a b a b := by

  intro m n

  exact
    ⟨Iff.rfl,
     Iff.rfl,
     Iff.rfl⟩

/--
Eudoxus equality of ratios is symmetric.
-/
theorem hilbertEudoxusProportion_symm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (h : HilbertEudoxusProportion Geo a b c d) :
    HilbertEudoxusProportion Geo c d a b := by

  intro m n

  have hmn :=
    h m n

  exact
    ⟨hmn.1.symm,
     hmn.2.1.symm,
     hmn.2.2.symm⟩

/--
Eudoxus equality of ratios is transitive.

This is the logical content of Euclid V.11 for the present definition.
-/
theorem hilbertEudoxusProportion_trans
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d e f : HilbertPositiveSegmentClass Geo)
    (h1 : HilbertEudoxusProportion Geo a b c d)
    (h2 : HilbertEudoxusProportion Geo c d e f) :
    HilbertEudoxusProportion Geo a b e f := by

  intro m n

  have hmn1 :=
    h1 m n

  have hmn2 :=
    h2 m n

  exact
    ⟨Iff.trans hmn1.1 hmn2.1,
     Iff.trans hmn1.2.1 hmn2.2.1,
     Iff.trans hmn1.2.2 hmn2.2.2⟩

/--
Extract the less-than comparison from an Eudoxus proportion.
-/
theorem hilbertEudoxusProportion_lt_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (h : HilbertEudoxusProportion Geo a b c d)
    (m n : Nat) :
    (HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo n b)
      <->
     HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo m c)
        (hilbertPositiveSegmentMultiple Geo n d)) := by

  exact (h m n).1

/--
Extract the equality comparison from an Eudoxus proportion.
-/
theorem hilbertEudoxusProportion_eq_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (h : HilbertEudoxusProportion Geo a b c d)
    (m n : Nat) :
    (hilbertPositiveSegmentMultiple Geo m a =
        hilbertPositiveSegmentMultiple Geo n b
      <->
     hilbertPositiveSegmentMultiple Geo m c =
        hilbertPositiveSegmentMultiple Geo n d) := by

  exact (h m n).2.1

/--
Extract the greater-than comparison from an Eudoxus proportion.
-/
theorem hilbertEudoxusProportion_gt_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (h : HilbertEudoxusProportion Geo a b c d)
    (m n : Nat) :
    (HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo n b)
        (hilbertPositiveSegmentMultiple Geo m a)
      <->
     HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo n d)
        (hilbertPositiveSegmentMultiple Geo m c)) := by

  exact (h m n).2.2

/--
No ratio is greater than itself in the Eudoxus sense.
-/
theorem hilbertEudoxusGreaterRatio_irrefl
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    Not (HilbertEudoxusGreaterRatio Geo a b a b) := by

  intro h

  rcases h with
    ⟨m, n, hGreater, hNotGreater⟩

  exact hNotGreater hGreater

/--
Eudoxus-equal ratios cannot stand in the Eudoxus greater-ratio
relation.
-/
theorem hilbertEudoxusProportion_not_greater
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hProp : HilbertEudoxusProportion Geo a b c d) :
    Not (HilbertEudoxusGreaterRatio Geo a b c d) := by

  intro hGreaterRatio

  rcases hGreaterRatio with
    ⟨m, n, hGreater, hNotGreater⟩

  have hTransport :
      HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo n d)
        (hilbertPositiveSegmentMultiple Geo m c) :=
    (hilbertEudoxusProportion_gt_iff
      Geo
      a b c d
      hProp
      m n).1
      hGreater

  exact hNotGreater hTransport


------------------------------------------------------------------------
-- Part IX. Least positive multiple exceeding a given magnitude
------------------------------------------------------------------------

/--
Finite least-element principle on Nat.

If P holds somewhere at or below N, then it holds at a least index m
at or below N.
-/
private theorem hilbertNat_exists_least_up_to
    (P : Nat -> Prop)
    (N : Nat)
    (h :
      Exists fun k : Nat =>
        k <= N /\ P k) :
    Exists fun m : Nat =>
      m <= N /\
      P m /\
      forall j : Nat,
        j < m ->
        Not (P j) := by

  classical

  induction N with

  | zero =>

      rcases h with
        ⟨k, hk, hPk⟩

      have hk0 :
          k = 0 :=
        Nat.eq_zero_of_le_zero hk

      subst k

      refine
        ⟨0,
         Nat.le_refl 0,
         hPk,
         ?_⟩

      intro j hj

      exact
        False.elim
          (Nat.not_lt_zero j hj)

  | succ N ih =>

      by_cases hOld :
          Exists fun k : Nat =>
            k <= N /\ P k

      · rcases ih hOld with
          ⟨m, hmN, hPm, hMin⟩

        exact
          ⟨m,
           Nat.le_trans hmN (Nat.le_succ N),
           hPm,
           hMin⟩

      · rcases h with
          ⟨k, hk, hPk⟩

        have hkEq :
            k = Nat.succ N := by

          rcases
              Nat.le_or_eq_of_le_succ hk
            with
            hkN | hkSucc

          · exact
              False.elim
                (hOld ⟨k, hkN, hPk⟩)

          · exact hkSucc

        subst k

        refine
          ⟨Nat.succ N,
           Nat.le_refl (Nat.succ N),
           hPk,
           ?_⟩

        intro j hj hPj

        have hjN :
            j <= N :=
          (Nat.lt_succ_iff).1 hj

        exact
          hOld
            ⟨j, hjN, hPj⟩

/--
For positive magnitudes a and x, there is a least positive natural
multiple of a which strictly exceeds x.

Recall that index n means (n+1) copies of a.
-/
theorem hilbertPositiveSegment_exists_least_exceeding_multiple
    [HilbertIncidence Geo]
    [HilbertArchimedeanPlane Geo]
    (a x : HilbertPositiveSegmentClass Geo) :
    Exists fun n : Nat =>
      HilbertPositiveSegmentLess
        Geo
        x
        (hilbertPositiveSegmentMultiple Geo n a)
      /\
      forall k : Nat,
        k < n ->
        Not
          (HilbertPositiveSegmentLess
            Geo
            x
            (hilbertPositiveSegmentMultiple Geo k a)) := by

  classical

  rcases
      hilbertPositiveSegment_archimedean
        Geo a x
    with
    ⟨N, hN⟩

  let P : Nat -> Prop :=
    fun k =>
      HilbertPositiveSegmentLess
        Geo
        x
        (hilbertPositiveSegmentMultiple Geo k a)

  have hBound :
      Exists fun k : Nat =>
        k <= N /\ P k := by

    exact
      ⟨N,
       Nat.le_refl N,
       hN⟩

  rcases
      hilbertNat_exists_least_up_to
        P N hBound
    with
    ⟨m, _hmN, hPm, hMin⟩

  refine
    ⟨m,
     ?_,
     ?_⟩

  · exact hPm

  · intro k hk
    exact hMin k hk


------------------------------------------------------------------------
-- Part X. Two-sided strict addition
------------------------------------------------------------------------

/--
Strict order is preserved when both summands are increased.
-/
theorem hilbertPositiveSegment_add_lt_add
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hab : HilbertPositiveSegmentLess Geo a b)
    (hcd : HilbertPositiveSegmentLess Geo c d) :
    HilbertPositiveSegmentLess Geo (a + c) (b + d) := by

  have h1 :
      HilbertPositiveSegmentLess Geo (a + c) (b + c) :=
    hilbertPositiveSegment_add_lt_add_right
      Geo a b c hab

  have h2 :
      HilbertPositiveSegmentLess Geo (b + c) (b + d) :=
    hilbertPositiveSegment_add_lt_add_left
      Geo c d b hcd

  exact
    hilbertPositiveSegmentLess_trans
      Geo
      (a + c)
      (b + c)
      (b + d)
      h1 h2

------------------------------------------------------------------------
-- Part XI. Nested positive multiples
------------------------------------------------------------------------

/--
Positive natural multiplication commutes under nesting.

Both sides represent (m+1)(n+1) copies of a, but the proof uses only
the additive recursion and distributivity already established.
-/
theorem hilbertPositiveSegmentMultiple_commute
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (m n : Nat)
    (a : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentMultiple
        Geo m
        (hilbertPositiveSegmentMultiple Geo n a) =
      hilbertPositiveSegmentMultiple
        Geo n
        (hilbertPositiveSegmentMultiple Geo m a) := by

  induction m with

  | zero =>
      simp only [
        hilbertPositiveSegmentMultiple_zero
      ]

  | succ m ih =>

      calc
        hilbertPositiveSegmentMultiple
            Geo (Nat.succ m)
            (hilbertPositiveSegmentMultiple Geo n a) =
            hilbertPositiveSegmentMultiple
                Geo m
                (hilbertPositiveSegmentMultiple Geo n a) +
              hilbertPositiveSegmentMultiple Geo n a := by
          exact
            hilbertPositiveSegmentMultiple_succ
              Geo m
              (hilbertPositiveSegmentMultiple Geo n a)

        _ =
            hilbertPositiveSegmentMultiple
                Geo n
                (hilbertPositiveSegmentMultiple Geo m a) +
              hilbertPositiveSegmentMultiple Geo n a := by
          rw [ih]

        _ =
            hilbertPositiveSegmentMultiple
              Geo n
              (hilbertPositiveSegmentMultiple Geo m a + a) := by
          symm
          exact
            hilbertPositiveSegmentMultiple_add
              Geo n
              (hilbertPositiveSegmentMultiple Geo m a)
              a

        _ =
            hilbertPositiveSegmentMultiple
              Geo n
              (hilbertPositiveSegmentMultiple
                Geo (Nat.succ m) a) := by
          rw [
            hilbertPositiveSegmentMultiple_succ
          ]

/--
Comparison of nested common multiples reduces to comparison before
the common outer multiplication.
-/
theorem hilbertPositiveSegmentMultiple_nested_lt_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (m n k : Nat)
    (a b : HilbertPositiveSegmentClass Geo) :
    (HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple
          Geo m
          (hilbertPositiveSegmentMultiple Geo k a))
        (hilbertPositiveSegmentMultiple
          Geo n
          (hilbertPositiveSegmentMultiple Geo k b))
      <->
     HilbertPositiveSegmentLess
        Geo
        (hilbertPositiveSegmentMultiple Geo m a)
        (hilbertPositiveSegmentMultiple Geo n b)) := by

  rw [
    hilbertPositiveSegmentMultiple_commute
      Geo m k a,
    hilbertPositiveSegmentMultiple_commute
      Geo n k b
  ]

  exact
    hilbertPositiveSegmentMultiple_lt_iff
      Geo k
      (hilbertPositiveSegmentMultiple Geo m a)
      (hilbertPositiveSegmentMultiple Geo n b)

/--
Equality of nested common multiples reduces to equality before
the common outer multiplication.
-/
theorem hilbertPositiveSegmentMultiple_nested_eq_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (m n k : Nat)
    (a b : HilbertPositiveSegmentClass Geo) :
    (hilbertPositiveSegmentMultiple
        Geo m
        (hilbertPositiveSegmentMultiple Geo k a) =
      hilbertPositiveSegmentMultiple
        Geo n
        (hilbertPositiveSegmentMultiple Geo k b)
      <->
     hilbertPositiveSegmentMultiple Geo m a =
      hilbertPositiveSegmentMultiple Geo n b) := by

  rw [
    hilbertPositiveSegmentMultiple_commute
      Geo m k a,
    hilbertPositiveSegmentMultiple_commute
      Geo n k b
  ]

  exact
    hilbertPositiveSegmentMultiple_eq_iff
      Geo k
      (hilbertPositiveSegmentMultiple Geo m a)
      (hilbertPositiveSegmentMultiple Geo n b)

end Geometry

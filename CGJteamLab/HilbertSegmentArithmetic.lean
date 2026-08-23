import CGJteamLab.HilbertRightAngle

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
An oriented pair of endpoints used only as a representative
of a segment congruence class.

Endpoint orientation disappears after quotienting by congruence.
-/
abbrev HilbertSegmentRep :=
  Geo.Point × Geo.Point


/--
Congruence of segments defines an equivalence relation on endpoint pairs.
-/
def hilbertSegmentSetoid
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    Setoid (HilbertSegmentRep Geo) where

  r := fun s t =>
    Geo.Congruent s.1 s.2 t.1 t.2

  iseqv := by
    constructor

    · intro s
      exact
        hilbert_congruent_reflexive
          Geo s.1 s.2

    · intro s t h
      exact
        hilbert_congruent_symmetry
          Geo
          s.1 s.2
          t.1 t.2
          h

    · intro s t q hst htq
      exact
        hilbert_congruent_transitivity
          Geo
          s.1 s.2
          t.1 t.2
          q.1 q.2
          hst
          htq


/--
A Hilbert segment length is a congruence class of segments.
-/
abbrev HilbertSegmentClass
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :=
  Quotient (hilbertSegmentSetoid Geo)


/--
The congruence class represented by the segment AB.
-/
def hilbertSegmentClassOf
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point) :
    HilbertSegmentClass Geo :=
  Quotient.mk
    (hilbertSegmentSetoid Geo)
    (A, B)

/--
Two segments determine the same Hilbert segment class
iff they are congruent.
-/
theorem hilbertSegmentClassOf_eq_iff
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point) :
    hilbertSegmentClassOf Geo A B =
        hilbertSegmentClassOf Geo C D
      <->
    Geo.Congruent A B C D := by

  constructor

  · intro h
    exact
      Quotient.exact h

  · intro h
    exact
      Quotient.sound h

/--
Reversing the endpoints does not change a Hilbert segment class.
-/
theorem hilbertSegmentClassOf_swap
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point) :
    hilbertSegmentClassOf Geo A B =
      hilbertSegmentClassOf Geo B A := by

  apply
    (hilbertSegmentClassOf_eq_iff
      Geo A B B A).2

  exact
    (Geo.congruent_reverse_second
      A B A B).mp
      (hilbert_congruent_reflexive Geo A B)

/--
All degenerate segments determine the same segment class.
-/
theorem hilbertSegmentClassOf_null_eq
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point) :
    hilbertSegmentClassOf Geo A A =
      hilbertSegmentClassOf Geo B B := by

  apply
    (hilbertSegmentClassOf_eq_iff
      Geo A A B B).2

  exact
    bookZero_nullSegment2
      Geo A B

/--
A nondegenerate segment representative.
-/
abbrev HilbertPositiveSegmentRep :=
  {s : HilbertSegmentRep Geo // Ne s.1 s.2}


/--
Congruence restricted to nondegenerate segment representatives.
-/
def hilbertPositiveSegmentSetoid
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    Setoid (HilbertPositiveSegmentRep Geo) where

  r := fun s t =>
    Geo.Congruent
      s.val.1 s.val.2
      t.val.1 t.val.2

  iseqv := by
    constructor

    · intro s
      exact
        hilbert_congruent_reflexive
          Geo s.val.1 s.val.2

    · intro s t h
      exact
        hilbert_congruent_symmetry
          Geo
          s.val.1 s.val.2
          t.val.1 t.val.2
          h

    · intro s t q hst htq
      exact
        hilbert_congruent_transitivity
          Geo
          s.val.1 s.val.2
          t.val.1 t.val.2
          q.val.1 q.val.2
          hst
          htq


/--
A positive Hilbert segment length is a congruence class
of nondegenerate segments.
-/
abbrev HilbertPositiveSegmentClass
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :=
  Quotient (hilbertPositiveSegmentSetoid Geo)


/--
The positive segment class represented by AB.
-/
def hilbertPositiveSegmentClassOf
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    HilbertPositiveSegmentClass Geo :=
  Quotient.mk
    (hilbertPositiveSegmentSetoid Geo)
    ⟨(A, B), hAB⟩

/--
Geometric addition of positive segment classes.

The relation `HilbertPositiveSegmentSum Geo a b c` means that
there is a collinear configuration A-B-C such that

  AB represents a,
  BC represents b,
  AC represents c.
-/
def HilbertPositiveSegmentSum
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo) : Prop :=
  ∃ A B C : Geo.Point,
    ∃ hABC : Geo.Between A B C,
      hilbertPositiveSegmentClassOf
          Geo A B
          (HilbertOrder.between_incidence A B C hABC).1 =
        a ∧
      hilbertPositiveSegmentClassOf
          Geo B C
          (HilbertOrder.between_incidence A B C hABC).2.1 =
        b ∧
      hilbertPositiveSegmentClassOf
          Geo A C
          (HilbertOrder.between_incidence A B C hABC).2.2.1 =
        c

/--
Every strict betweenness configuration realizes addition
of the two adjacent positive segment classes.
-/
theorem hilbertPositiveSegmentSum_of_between
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    HilbertPositiveSegmentSum
      Geo
      (hilbertPositiveSegmentClassOf
        Geo A B
        (HilbertOrder.between_incidence A B C hABC).1)
      (hilbertPositiveSegmentClassOf
        Geo B C
        (HilbertOrder.between_incidence A B C hABC).2.1)
      (hilbertPositiveSegmentClassOf
        Geo A C
        (HilbertOrder.between_incidence A B C hABC).2.2.1) := by

  exact
    ⟨A, B, C, hABC, rfl, rfl, rfl⟩

/--
The sum relation is single-valued in its third argument.
-/
theorem hilbertPositiveSegmentSum_unique
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo)
    (hc : HilbertPositiveSegmentSum Geo a b c)
    (hd : HilbertPositiveSegmentSum Geo a b d) :
    c = d := by

  rcases hc with
    ⟨A, B, C, hABC, hABa, hBCb, hACc⟩

  rcases hd with
    ⟨A', B', C', hA'B'C',
      hA'B'a, hB'C'b, hA'C'd⟩

  have hAB :
      Ne A B :=
    (HilbertOrder.between_incidence
      A B C hABC).1

  have hBC :
      Ne B C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.1

  have hAC :
      Ne A C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.2.1

  have hA'B' :
      Ne A' B' :=
    (HilbertOrder.between_incidence
      A' B' C' hA'B'C').1

  have hB'C' :
      Ne B' C' :=
    (HilbertOrder.between_incidence
      A' B' C' hA'B'C').2.1

  have hA'C' :
      Ne A' C' :=
    (HilbertOrder.between_incidence
      A' B' C' hA'B'C').2.2.1

  have hABeq :
      hilbertPositiveSegmentClassOf Geo A B hAB =
        hilbertPositiveSegmentClassOf Geo A' B' hA'B' :=
    hABa.trans hA'B'a.symm

  have hBCeq :
      hilbertPositiveSegmentClassOf Geo B C hBC =
        hilbertPositiveSegmentClassOf Geo B' C' hB'C' :=
    hBCb.trans hB'C'b.symm

  have hABcong :
      Geo.Congruent A B A' B' := by
    exact Quotient.exact hABeq

  have hBCcong :
      Geo.Congruent B C B' C' := by
    exact Quotient.exact hBCeq

  have hACcong :
      Geo.Congruent A C A' C' :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A B C
      A' B' C'
      hABC
      hA'B'C'
      hABcong
      hBCcong

  have hACeq :
      hilbertPositiveSegmentClassOf Geo A C hAC =
        hilbertPositiveSegmentClassOf Geo A' C' hA'C' := by
    exact Quotient.sound hACcong

  calc
    c =
        hilbertPositiveSegmentClassOf Geo A C hAC :=
      hACc.symm
    _ =
        hilbertPositiveSegmentClassOf Geo A' C' hA'C' :=
      hACeq
    _ = d :=
      hA'C'd

/--
Every pair of positive segment classes has a geometric sum.
-/
theorem hilbertPositiveSegmentSum_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    ∃ c : HilbertPositiveSegmentClass Geo,
      HilbertPositiveSegmentSum Geo a b c := by

  refine Quotient.inductionOn₂ a b ?_

  intro
    (sa : HilbertPositiveSegmentRep Geo)
    (sb : HilbertPositiveSegmentRep Geo)

  rcases sa with
    ⟨⟨A, B⟩, hAB⟩

  rcases sb with
    ⟨⟨C, D⟩, hCD⟩

  change Ne A B at hAB
  change Ne C D at hCD

  rcases
      HilbertOrder.between_extension
        A B hAB
    with
    ⟨E, hABE⟩

  have hBE :
      Ne B E :=
    (HilbertOrder.between_incidence
      A B E hABE).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        C D
        B E
        hBE
    with
    ⟨X, hRayBEX, hBXCD⟩

  have hRayBAA :
      HilbertSameRay Geo B A A :=
    hilbert_sameRay_refl
      Geo B A hAB

  have hABX :
      Geo.Between A B X :=
    hilbert_between_transport_sameRays
      Geo
      A B E
      A X
      hABE
      hRayBAA
      hRayBEX

  have hBX :
      Ne B X :=
    (HilbertOrder.between_incidence
      A B X hABX).2.1

  have hAX :
      Ne A X :=
    (HilbertOrder.between_incidence
      A B X hABX).2.2.1

  let c : HilbertPositiveSegmentClass Geo :=
    hilbertPositiveSegmentClassOf
      Geo A X hAX

  refine ⟨c, ?_⟩

  refine
    ⟨A, B, X, hABX, ?_, ?_, ?_⟩

  · rfl

  · exact
      Quotient.sound hBXCD

  · rfl

/--
The sum of two positive Hilbert segment classes.
-/
noncomputable def hilbertPositiveSegmentAdd
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentClass Geo :=
  Classical.choose
    (hilbertPositiveSegmentSum_exists Geo a b)


/--
The chosen sum really realizes the geometric segment-sum relation.
-/
theorem hilbertPositiveSegmentAdd_spec
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    HilbertPositiveSegmentSum
      Geo
      a b
      (hilbertPositiveSegmentAdd Geo a b) := by

  exact
    Classical.choose_spec
      (hilbertPositiveSegmentSum_exists Geo a b)

/--
Reversing endpoints does not change a positive segment class.
-/
theorem hilbertPositiveSegmentClassOf_swap
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    hilbertPositiveSegmentClassOf Geo A B hAB =
      hilbertPositiveSegmentClassOf Geo B A hAB.symm := by

  exact
    Quotient.sound
      ((Geo.congruent_reverse_second
        A B A B).mp
        (hilbert_congruent_reflexive Geo A B))

/--
Geometric addition of positive segment classes is commutative.
-/
theorem hilbertPositiveSegmentSum_comm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo)
    (h : HilbertPositiveSegmentSum Geo a b c) :
    HilbertPositiveSegmentSum Geo b a c := by

  rcases h with
    ⟨A, B, C, hABC, hABa, hBCb, hACc⟩

  have hAB : Ne A B :=
    (HilbertOrder.between_incidence
      A B C hABC).1

  have hBC : Ne B C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.1

  have hAC : Ne A C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.2.1

  have hCBA :
      Geo.Between C B A :=
    (HilbertOrder.between_incidence
      A B C hABC).2.2.2.2

  have hCBb :
      hilbertPositiveSegmentClassOf
          Geo C B hBC.symm =
        b := by
    calc
      hilbertPositiveSegmentClassOf Geo C B hBC.symm =
          hilbertPositiveSegmentClassOf Geo B C hBC :=
        (hilbertPositiveSegmentClassOf_swap
          Geo B C hBC).symm
      _ = b := by
        simpa using hBCb

  have hBAa :
      hilbertPositiveSegmentClassOf
          Geo B A hAB.symm =
        a := by
    calc
      hilbertPositiveSegmentClassOf Geo B A hAB.symm =
          hilbertPositiveSegmentClassOf Geo A B hAB :=
        (hilbertPositiveSegmentClassOf_swap
          Geo A B hAB).symm
      _ = a := by
        simpa using hABa

  have hCAc :
      hilbertPositiveSegmentClassOf
          Geo C A hAC.symm =
        c := by
    calc
      hilbertPositiveSegmentClassOf Geo C A hAC.symm =
          hilbertPositiveSegmentClassOf Geo A C hAC :=
        (hilbertPositiveSegmentClassOf_swap
          Geo A C hAC).symm
      _ = c := by
        simpa using hACc

  exact
    ⟨C, B, A, hCBA, hCBb, hBAa, hCAc⟩

/--
Addition of positive Hilbert segment classes is commutative.
-/
theorem hilbertPositiveSegmentAdd_comm
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    hilbertPositiveSegmentAdd Geo a b =
      hilbertPositiveSegmentAdd Geo b a := by

  have hSum :
      HilbertPositiveSegmentSum
        Geo
        b a
        (hilbertPositiveSegmentAdd Geo a b) :=
    hilbertPositiveSegmentSum_comm
      Geo
      a b
      (hilbertPositiveSegmentAdd Geo a b)
      (hilbertPositiveSegmentAdd_spec Geo a b)

  exact
    hilbertPositiveSegmentSum_unique
      Geo
      b a
      (hilbertPositiveSegmentAdd Geo a b)
      (hilbertPositiveSegmentAdd Geo b a)
      hSum
      (hilbertPositiveSegmentAdd_spec Geo b a)

/--
Addition on positive Hilbert segment classes.
-/
noncomputable instance hilbertPositiveSegmentClassAdd
    [HilbertIncidence Geo]
    [HilbertCongruence Geo] :
    Add (HilbertPositiveSegmentClass Geo) where
  add := hilbertPositiveSegmentAdd Geo

/--
Two successive positive segment sums can be reassociated.

If ab = a + b and abc = ab + c, then there exists bc = b + c
such that abc = a + bc.
-/
theorem hilbertPositiveSegmentSum_assoc_step
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c ab abc : HilbertPositiveSegmentClass Geo)
    (hABsum : HilbertPositiveSegmentSum Geo a b ab)
    (hABCsum : HilbertPositiveSegmentSum Geo ab c abc) :
    ∃ bc : HilbertPositiveSegmentClass Geo,
      HilbertPositiveSegmentSum Geo b c bc ∧
      HilbertPositiveSegmentSum Geo a bc abc := by

  rcases hABsum with
    ⟨A, B, C, hABC, hABa, hBCb, hACab⟩

  rcases hABCsum with
    ⟨P, Q, R, hPQR, hPQab, hQRc, hPRabc⟩

  have hAB : Ne A B :=
    (HilbertOrder.between_incidence
      A B C hABC).1

  have hBC : Ne B C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.1

  have hAC : Ne A C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.2.1

  have hPQ : Ne P Q :=
    (HilbertOrder.between_incidence
      P Q R hPQR).1

  have hQR : Ne Q R :=
    (HilbertOrder.between_incidence
      P Q R hPQR).2.1

  have hPR : Ne P R :=
    (HilbertOrder.between_incidence
      P Q R hPQR).2.2.1

  ----------------------------------------------------------------
  -- Extend BC beyond C and lay off a copy of QR there.
  ----------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        B C hBC
    with
    ⟨E, hBCE⟩

  have hCE : Ne C E :=
    (HilbertOrder.between_incidence
      B C E hBCE).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        Q R
        C E
        hCE
    with
    ⟨D, hRayCED, hCDQR⟩

  have hRayCBB :
      HilbertSameRay Geo C B B :=
    hilbert_sameRay_refl
      Geo C B hBC

  have hBCD :
      Geo.Between B C D :=
    hilbert_between_transport_sameRays
      Geo
      B C E
      B D
      hBCE
      hRayCBB
      hRayCED

  ----------------------------------------------------------------
  -- Hence the four points occur in the order A-B-C-D.
  ----------------------------------------------------------------

  have hOuter :=
    hilbert_between_outer_trans
      Geo A B C D hABC hBCD

  have hACD :
      Geo.Between A C D :=
    hOuter.1

  have hABD :
      Geo.Between A B D :=
    hOuter.2

  have hCD : Ne C D :=
    (HilbertOrder.between_incidence
      B C D hBCD).2.1

  have hBD : Ne B D :=
    (HilbertOrder.between_incidence
      A B D hABD).2.1

  have hAD : Ne A D :=
    (HilbertOrder.between_incidence
      A B D hABD).2.2.1

  ----------------------------------------------------------------
  -- AC and PQ represent the same class ab.
  ----------------------------------------------------------------

  have hACeqPQ :
      hilbertPositiveSegmentClassOf Geo A C hAC =
        hilbertPositiveSegmentClassOf Geo P Q hPQ :=
    hACab.trans hPQab.symm

  have hACPQ :
      Geo.Congruent A C P Q := by
    exact Quotient.exact hACeqPQ

  ----------------------------------------------------------------
  -- III.3: AC ~= PQ and CD ~= QR imply AD ~= PR.
  ----------------------------------------------------------------

  have hADPR :
      Geo.Congruent A D P R :=
    HilbertCongruence.segment_additivity
      (Geo := Geo)
      A C D
      P Q R
      hACD
      hPQR
      hACPQ
      hCDQR

  have hADeqPR :
      hilbertPositiveSegmentClassOf Geo A D hAD =
        hilbertPositiveSegmentClassOf Geo P R hPR := by
    exact Quotient.sound hADPR

  have hADabc :
      hilbertPositiveSegmentClassOf Geo A D hAD =
        abc :=
    hADeqPR.trans hPRabc

  ----------------------------------------------------------------
  -- BD is the intermediate class bc.
  ----------------------------------------------------------------

  let bc : HilbertPositiveSegmentClass Geo :=
    hilbertPositiveSegmentClassOf Geo B D hBD

  refine ⟨bc, ?_, ?_⟩

  ----------------------------------------------------------------
  -- B-C-D realizes b + c = bc.
  ----------------------------------------------------------------

  · refine
      ⟨B, C, D, hBCD, ?_, ?_, ?_⟩

    · simpa using hBCb

    · have hCDeqQR :
          hilbertPositiveSegmentClassOf Geo C D hCD =
            hilbertPositiveSegmentClassOf Geo Q R hQR := by
        exact Quotient.sound hCDQR

      exact hCDeqQR.trans hQRc

    · rfl

  ----------------------------------------------------------------
  -- A-B-D realizes a + bc = abc.
  ----------------------------------------------------------------

  · refine
      ⟨A, B, D, hABD, ?_, ?_, ?_⟩

    · simpa using hABa

    · rfl

    · simpa using hADabc

/--
Addition of positive Hilbert segment classes is associative.
-/
theorem hilbertPositiveSegment_add_assoc
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo) :
    (a + b) + c = a + (b + c) := by

  have hAB :
      HilbertPositiveSegmentSum
        Geo
        a b
        (a + b) :=
    hilbertPositiveSegmentAdd_spec
      Geo a b

  have hABC :
      HilbertPositiveSegmentSum
        Geo
        (a + b) c
        ((a + b) + c) :=
    hilbertPositiveSegmentAdd_spec
      Geo (a + b) c

  rcases
      hilbertPositiveSegmentSum_assoc_step
        Geo
        a b c
        (a + b)
        ((a + b) + c)
        hAB
        hABC
    with
    ⟨bc, hBC, hA_BC⟩

  have hbc :
      bc = b + c :=
    hilbertPositiveSegmentSum_unique
      Geo
      b c
      bc
      (b + c)
      hBC
      (hilbertPositiveSegmentAdd_spec
        Geo b c)

  subst bc

  exact
    hilbertPositiveSegmentSum_unique
      Geo
      a (b + c)
      ((a + b) + c)
      (a + (b + c))
      hA_BC
      (hilbertPositiveSegmentAdd_spec
        Geo a (b + c))

/--
Right cancellation for geometric addition of positive segment classes.
-/
theorem hilbertPositiveSegmentSum_cancel_right
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c x : HilbertPositiveSegmentClass Geo)
    (hac : HilbertPositiveSegmentSum Geo a c x)
    (hbc : HilbertPositiveSegmentSum Geo b c x) :
    a = b := by

  rcases hac with
    ⟨A, B, C, hABC, hABa, hBCc, hACx⟩

  rcases hbc with
    ⟨P, Q, R, hPQR, hPQb, hQRc, hPRx⟩

  have hAB : Ne A B :=
    (HilbertOrder.between_incidence
      A B C hABC).1

  have hBC : Ne B C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.1

  have hAC : Ne A C :=
    (HilbertOrder.between_incidence
      A B C hABC).2.2.1

  have hPQ : Ne P Q :=
    (HilbertOrder.between_incidence
      P Q R hPQR).1

  have hQR : Ne Q R :=
    (HilbertOrder.between_incidence
      P Q R hPQR).2.1

  have hPR : Ne P R :=
    (HilbertOrder.between_incidence
      P Q R hPQR).2.2.1

  ----------------------------------------------------------------
  -- The common right summand gives BC ~= QR.
  ----------------------------------------------------------------

  have hBCeqQR :
      hilbertPositiveSegmentClassOf Geo B C hBC =
        hilbertPositiveSegmentClassOf Geo Q R hQR :=
    hBCc.trans hQRc.symm

  have hBCQR :
      Geo.Congruent B C Q R := by
    exact Quotient.exact hBCeqQR

  ----------------------------------------------------------------
  -- The common total gives AC ~= PR.
  ----------------------------------------------------------------

  have hACeqPR :
      hilbertPositiveSegmentClassOf Geo A C hAC =
        hilbertPositiveSegmentClassOf Geo P R hPR :=
    hACx.trans hPRx.symm

  have hACPR :
      Geo.Congruent A C P R := by
    exact Quotient.exact hACeqPR

  ----------------------------------------------------------------
  -- Reverse both decompositions:
  --
  --   A-B-C       P-Q-R
  --
  -- becomes
  --
  --   C-B-A       R-Q-P.
  --
  -- Now the common right parts become the first parts.
  ----------------------------------------------------------------

  have hCBA :
      Geo.Between C B A :=
    (HilbertOrder.between_incidence
      A B C hABC).2.2.2.2

  have hRQP :
      Geo.Between R Q P :=
    (HilbertOrder.between_incidence
      P Q R hPQR).2.2.2.2

  have hCBRQ :
      Geo.Congruent C B R Q :=
    CongruentReverseBoth
      Geo B C Q R hBCQR

  have hCARP :
      Geo.Congruent C A R P :=
    CongruentReverseBoth
      Geo A C P R hACPR

  ----------------------------------------------------------------
  -- Segment subtraction:
  --
  -- CB ~= RQ
  -- CA ~= RP
  -- ----------------
  -- BA ~= QP
  ----------------------------------------------------------------

  have hBAQP :
      Geo.Congruent B A Q P :=
    hilbert_segment_subtraction
      Geo
      C B A
      R Q P
      hCBA
      hRQP
      hCBRQ
      hCARP

  have hABPQ :
      Geo.Congruent A B P Q :=
    CongruentReverseBoth
      Geo B A Q P hBAQP

  have hABeqPQ :
      hilbertPositiveSegmentClassOf Geo A B hAB =
        hilbertPositiveSegmentClassOf Geo P Q hPQ := by
    exact Quotient.sound hABPQ

  calc
    a =
        hilbertPositiveSegmentClassOf Geo A B hAB :=
      hABa.symm
    _ =
        hilbertPositiveSegmentClassOf Geo P Q hPQ :=
      hABeqPQ
    _ = b :=
      hPQb

/--
Right cancellation for addition of positive Hilbert segment classes.
-/
theorem hilbertPositiveSegment_add_right_cancel
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c : HilbertPositiveSegmentClass Geo)
    (h : a + c = b + c) :
    a = b := by

  have hac :
      HilbertPositiveSegmentSum
        Geo
        a c
        (a + c) :=
    hilbertPositiveSegmentAdd_spec
      Geo a c

  have hbc :
      HilbertPositiveSegmentSum
        Geo
        b c
        (a + c) := by
    rw [h]
    exact
      hilbertPositiveSegmentAdd_spec
        Geo b c

  exact
    hilbertPositiveSegmentSum_cancel_right
      Geo
      a b c
      (a + c)
      hac
      hbc

/--
A geometric witness for the ratio a : b of positive segment classes.

The right triangle has right angle at O.

  OB represents a
  OA represents b

Hence the angle OAB is the angle opposite the leg representing a.
-/
structure HilbertPositiveSegmentRatioWitness
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) where

  O : Geo.Point
  A : Geo.Point
  B : Geo.Point

  hOA : Ne O A
  hOB : Ne O B

  hNoncol :
    Not (PrimCollinear Geo O A B)

  hRight :
    HilbertRightAngle Geo A O B

  hFirst :
    hilbertPositiveSegmentClassOf Geo O B hOB = a

  hSecond :
    hilbertPositiveSegmentClassOf Geo O A hOA = b

/--
Equality of ratios of positive Hilbert segment classes.

The proportion

  a : b = c : d

means that right triangles representing a:b and c:d
have congruent defining acute angles.
-/
def HilbertPositiveSegmentProportion
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b c d : HilbertPositiveSegmentClass Geo) : Prop :=
  ∃ w1 : HilbertPositiveSegmentRatioWitness Geo a b,
    ∃ w2 : HilbertPositiveSegmentRatioWitness Geo c d,
      Geo.AngleCongruent
        w1.O w1.A w1.B
        w2.O w2.A w2.B


/--
Every pair of positive segment classes admits a right-triangle
representative of its ratio.
-/
theorem hilbertPositiveSegmentRatioWitness_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (a b : HilbertPositiveSegmentClass Geo) :
    Nonempty (HilbertPositiveSegmentRatioWitness Geo a b) := by

  refine
    Quotient.inductionOn₂
      a b
      (fun
        (sa : HilbertPositiveSegmentRep Geo)
        (sb : HilbertPositiveSegmentRep Geo) => ?_)

  rcases sa with
    ⟨⟨U, V⟩, hUV⟩

  rcases sb with
    ⟨⟨O, A⟩, hOA⟩

  change Ne U V at hUV
  change Ne O A at hOA

  ----------------------------------------------------------------
  -- Extend AO through O:
  --
  --     A - O - E
  ----------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        A O hOA.symm
    with
    ⟨E, hAOE⟩

  ----------------------------------------------------------------
  -- Erect a nondegenerate perpendicular at O.
  ----------------------------------------------------------------

  rcases
      hilbert_right_angle_exists_nondegenerate
        Geo A O E hAOE
    with
    ⟨X, hAOX, hRightX⟩

  ----------------------------------------------------------------
  -- O and X are distinct.
  ----------------------------------------------------------------

  have hOXA :
      Not (PrimCollinear Geo O X A) := by
    intro h

    have hAOX' :
        PrimCollinear Geo A O X :=
      PrimCollinearCycle
        Geo X A O
        (PrimCollinearCycle
          Geo O X A h)

    exact hAOX hAOX'

  have hOX :
      Ne O X :=
    hilbert_noncollinear_ne_first
      Geo O X A hOXA

  ----------------------------------------------------------------
  -- Lay off a copy of UV on the perpendicular ray OX.
  ----------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        U V
        O X
        hOX
    with
    ⟨B, hRayOXB, hOBUV⟩

  have hOB :
      Ne O B :=
    hRayOXB.2.1.symm

  ----------------------------------------------------------------
  -- Replacing X by B on the same ray preserves noncollinearity.
  ----------------------------------------------------------------

  have hRayOAA :
      HilbertSameRay Geo O A A :=
    hilbert_sameRay_refl
      Geo O A hOA.symm

  have hAOB :
      Not (PrimCollinear Geo A O B) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A O X
      A B
      hAOX
      hRayOAA
      hRayOXB

  have hOAB :
      Not (PrimCollinear Geo O A B) := by
    intro h

    exact
      hAOB
        (PrimCollinearSwap
          Geo O A B h)

  ----------------------------------------------------------------
  -- Transport the right angle from ray OX to the same ray OB.
  --
  -- We do this directly from the definition of HilbertRightAngle.
  ----------------------------------------------------------------

  rcases hRightX with
    ⟨C, hAOC, hRightCong⟩

  have hAngleLeft :
      Geo.Angle A O X =
        Geo.Angle A O B :=
    hilbert_angle_eq_of_sameRay_second
      Geo O A X B hRayOXB

  have hAngleRight :
      Geo.Angle X O C =
        Geo.Angle B O C :=
    hilbert_angle_eq_of_sameRay_first
      Geo O X B C hRayOXB

  have hRightB :
      HilbertRightAngle Geo A O B := by

    refine ⟨C, hAOC, ?_⟩

    unfold Geometry.Geo.AngleCongruent
      at hRightCong ⊢

    rw [← hAngleLeft, ← hAngleRight]

    exact hRightCong

  ----------------------------------------------------------------
  -- Package the right triangle as a ratio witness.
  ----------------------------------------------------------------

  refine
    ⟨{
      O := O
      A := A
      B := B
      hOA := hOA
      hOB := hOB
      hNoncol := hOAB
      hRight := hRightB
      hFirst := ?_
      hSecond := ?_
    }⟩

  · exact
      Quotient.sound hOBUV

  · rfl


end Geometry

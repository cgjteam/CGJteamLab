import CGJteamLab.TarskiAxioms

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Tarski.Geo)

/-!
# TarskiBase

Basic notions and derived theorems in Tarski's primitive language.

This module is independent of the Hilbert incidence interface.
-/

/--
Three points are Tarski-collinear when one of them lies between the
other two. Degenerate cases are included because Tarski betweenness is
non-strict.
-/
def TarskiCollinear (A B C : Geo.Point) : Prop :=
  Geo.Between A B C ∨
  Geo.Between B C A ∨
  Geo.Between C A B

/-- A midpoint expressed solely in Tarski's primitive language. -/
def TarskiIsMidpoint (M A B : Geo.Point) : Prop :=
  Geo.Between A M B ∧
  Geo.Congruent A M M B

theorem tarski_collinear_rotate
    (A B C : Geo.Point) :
    TarskiCollinear Geo A B C →
    TarskiCollinear Geo B C A := by
  intro h
  rcases h with hABC | hBCA | hCAB
  · exact Or.inr (Or.inr hABC)
  · exact Or.inl hBCA
  · exact Or.inr (Or.inl hCAB)

theorem tarski_collinear_cycle
    (A B C : Geo.Point) :
    TarskiCollinear Geo A B C ↔
    TarskiCollinear Geo B C A := by
  constructor
  · exact tarski_collinear_rotate Geo A B C
  · intro h
    exact
      tarski_collinear_rotate Geo C A B
        (tarski_collinear_rotate Geo B C A h)

theorem tarski_midpoint_collinear
    (M A B : Geo.Point) :
    TarskiIsMidpoint Geo M A B →
    TarskiCollinear Geo A M B := by
  intro h
  exact Or.inl h.left

/-
Derived Tarski theorem (historically Ax.12):
reflexivity of betweenness.

Mathematically:
  B(A,B,B).

Ax.12 is not part of the primitive axiom system used in
`TarskiAxioms.lean`.

It is derived here from:
  - Ax.3: identity for equidistance,
  - Ax.4: segment construction.

Construct X such that B(A,B,X) and BX == BB.
By Ax.3, B = X, hence B(A,B,B).
-/

theorem tarski_between_reflexivity
    [TarskiNeutral Geo]
    (A B : Geo.Point) :
    Geo.Between A B B := by
  obtain ⟨X, hBetween, hCong⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo) A B B B

  have hBX : B = X :=
    TarskiNeutral.congruent_identity
      (Geo := Geo) B X B hCong

  simpa [hBX] using hBetween

/-
Derived Tarski theorem (historically Ax.14):
symmetry of betweenness.

Mathematically:
  B(A,B,C) -> B(C,B,A).

Ax.14 is not part of the primitive axiom system used in
`TarskiAxioms.lean`.

It is derived here from:
  - derived Ax.12: reflexivity of betweenness,
  - Ax.6: identity for betweenness,
  - Ax.7: Inner Pasch.

Given B(A,B,C), derived Ax.12 gives B(B,C,C).
Inner Pasch yields X with B(B,X,B) and B(C,X,A).
By Ax.6, X = B, hence B(C,B,A).
-/
theorem tarski_between_symmetry
    [TarskiNeutral Geo]
    (A B C : Geo.Point)
    (hABC : Geo.Between A B C) :
    Geo.Between C B A := by

  have hBCC : Geo.Between B C C :=
    tarski_between_reflexivity (Geo := Geo) B C

  obtain ⟨X, hBXB, hCXA⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      A B C B C
      hABC hBCC

  have hBX : B = X :=
    TarskiNeutral.between_identity
      (Geo := Geo) B X hBXB

  simpa [← hBX] using hCXA

/-
Derived symmetry of Tarski collinearity.

Mathematically:
  TarskiCollinear A B C -> TarskiCollinear A C B.

This theorem is entirely internal to Tarski geometry.
It does not use Hilbert incidence or the compatibility bridge.

The proof unfolds TarskiCollinear and applies the derived
symmetry of betweenness (historically Ax.14) to each of the
three possible betweenness configurations.
-/
theorem tarski_collinear_symmetry
    [TarskiNeutral Geo]
    (A B C : Geo.Point)
    (h : TarskiCollinear Geo A B C) :
    TarskiCollinear Geo A C B := by
  rcases h with hABC | hBCA | hCAB
  · right
    left
    exact tarski_between_symmetry
      (Geo := Geo) A B C hABC
  · left
    exact tarski_between_symmetry
      (Geo := Geo) B C A hBCA
  · right
    right
    exact tarski_between_symmetry
      (Geo := Geo) C A B hCAB

/-
Derived Tarski theorem (historically Ax.15):
inner transitivity of betweenness.

Mathematically:
  B(A,B,D) and B(B,C,D) -> B(A,B,C).

Ax.15 is not part of the primitive axiom system used in
TarskiAxioms.lean.

It is derived here from:
  - Ax.6: identity for betweenness,
  - Ax.7: Inner Pasch,
  - derived Ax.14: symmetry of betweenness.

Given B(A,B,D) and B(B,C,D), Inner Pasch yields X with
B(B,X,B) and B(C,X,A). By Ax.6, X = B. Hence B(C,B,A),
and symmetry gives B(A,B,C).
-/
theorem tarski_between_inner_transitivity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABD : Geo.Between A B D)
    (hBCD : Geo.Between B C D) :
    Geo.Between A B C := by

  obtain ⟨X, hBXB, hCXA⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      A B D B C
      hABD hBCD

  have hBX : B = X :=
    TarskiNeutral.between_identity
      (Geo := Geo) B X hBXB

  have hCBA : Geo.Between C B A := by
    simpa [← hBX] using hCXA

  exact tarski_between_symmetry
    (Geo := Geo) C B A hCBA

/-
Derived exchange law for betweenness.

Mathematically:
  B(A,B,C) and B(A,C,D) -> B(B,C,D).

This theorem is entirely internal to Tarski neutral geometry.
It does not use Hilbert incidence, the compatibility bridge,
or decidable equality of points.

It is derived from:
  - Ax.6: identity for betweenness,
  - Ax.7: Inner Pasch,
  - derived Ax.14: symmetry of betweenness.

From B(A,B,C) and B(A,C,D), symmetry gives
B(C,B,A) and B(D,C,A). Inner Pasch yields X with
B(C,X,C) and B(B,X,D). By Ax.6, X = C, hence
B(B,C,D).
-/
theorem tarski_between_exchange3
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hACD : Geo.Between A C D) :
    Geo.Between B C D := by

  have hCBA : Geo.Between C B A :=
    tarski_between_symmetry (Geo := Geo) A B C hABC

  have hDCA : Geo.Between D C A :=
    tarski_between_symmetry (Geo := Geo) A C D hACD

  obtain ⟨X, hCXC, hBXD⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      D C A C B
      hDCA hCBA

  have hCX : C = X :=
    TarskiNeutral.between_identity
      (Geo := Geo) C X hCXC

  simpa [← hCX] using hBXD

/-
Derived reflexivity of segment congruence.

Mathematically:
  AB == AB.

This theorem is entirely internal to Tarski neutral geometry.
It does not use Hilbert incidence, the compatibility bridge,
or decidable equality of points.

It is derived from:
  - Ax.1: endpoint reversal for congruence,
  - Ax.2: transitivity for congruence.

Ax.1 applied to B,A gives BA == AB.
Using the same congruence twice in Ax.2 yields AB == AB.
-/
theorem tarski_congruent_reflexivity
    [TarskiNeutral Geo]
    (A B : Geo.Point) :
    Geo.Congruent A B A B := by

  have hBAAB : Geo.Congruent B A A B :=
    TarskiNeutral.congruent_reversal
      (Geo := Geo) B A

  exact TarskiNeutral.congruent_transitivity
    (Geo := Geo)
    B A A B A B
    hBAAB hBAAB

/-
Derived symmetry of segment congruence.

Mathematically:
  AB == CD -> CD == AB.

This theorem is entirely internal to Tarski neutral geometry.
It does not use Hilbert incidence, the compatibility bridge,
or decidable equality of points.

It is derived from:
  - Ax.2: transitivity for congruence,
  - derived reflexivity of segment congruence.

Given AB == CD and AB == AB, Ax.2 yields CD == AB.
-/
theorem tarski_congruent_symmetry
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABCD : Geo.Congruent A B C D) :
    Geo.Congruent C D A B := by

  have hABAB : Geo.Congruent A B A B :=
    tarski_congruent_reflexivity (Geo := Geo) A B

  exact TarskiNeutral.congruent_transitivity
    (Geo := Geo)
    A B C D A B
    hABCD hABAB

/--
Reversal of both unoriented segments.

This is a representational consequence of `Common.PairRelation`, not a
Tarski congruence theorem. No Tarski axiom instance is required.
-/
theorem tarski_congruent_reverse_both
    (A B C D : Geo.Point)
    (hABCD : Geo.Congruent A B C D) :
    Geo.Congruent B A D C := by
  exact
    (Geometry.Tarski.Geo.congruent_reverse_second Geo B A C D).mp
      ((Geometry.Tarski.Geo.congruent_reverse_first Geo A B C D).mp hABCD)

/-
Derived congruence of all zero-length segments.

Mathematically:
  AA == BB.

This theorem is entirely internal to Tarski neutral geometry.
It does not use Hilbert incidence, the compatibility bridge,
or decidable equality of points.

It is derived from:
  - Ax.3: identity for segment congruence,
  - Ax.4: segment construction.

Use Ax.4 to construct X such that B(A,A,X) and AX == BB.
By Ax.3, A = X. Hence AA == BB.
-/
theorem tarski_congruent_zero
    [TarskiNeutral Geo]
    (A B : Geo.Point) :
    Geo.Congruent A A B B := by

  obtain ⟨X, _hAAX, hAXBB⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo) A A B B

  have hAX : A = X :=
    TarskiNeutral.congruent_identity
      (Geo := Geo) A X B hAXBB

  simpa [← hAX] using hAXBB

/-
Derived nondegenerate segment-addition theorem.

Mathematically:
  B(A,B,C) and B(A',B',C'),
  A != B,
  AB == A'B' and BC == B'C'
  imply AC == A'C'.

This is the nondegenerate form of the theorem commonly
called l2_11 in developments of Tarski geometry.

The theorem is derived directly from:
  - Ax.5: Five-Segment,
  - derived congruence of zero-length segments,
  - derived reversal of both endpoints of congruent segments.

In Ax.5 take D = A and D' = A'. Then AD == A'D'
becomes AA == A'A', while BD == B'D' becomes
BA == B'A'. The conclusion CD == C'D' is therefore
CA == C'A', which is reversed to AC == A'C'.
-/
theorem tarski_l2_11_nondegenerate
    [TarskiNeutral Geo]
    (A B C A' B' C' : Geo.Point)
    (hABC : Geo.Between A B C)
    (hA'B'C' : Geo.Between A' B' C')
    (hAB : A ≠ B)
    (hCongAB : Geo.Congruent A B A' B')
    (hCongBC : Geo.Congruent B C B' C') :
    Geo.Congruent A C A' C' := by

  have hZero : Geo.Congruent A A A' A' :=
    tarski_congruent_zero (Geo := Geo) A A'

  have hReverseAB : Geo.Congruent B A B' A' :=
    tarski_congruent_reverse_both
      (Geo := Geo) A B A' B' hCongAB

  have hCA : Geo.Congruent C A C' A' :=
    TarskiNeutral.five_segment
      (Geo := Geo)
      A A' B B' C C' A A'
      hAB
      hABC
      hA'B'C'
      hCongAB
      hCongBC
      hZero
      hReverseAB

  exact tarski_congruent_reverse_both
    (Geo := Geo) C A C' A' hCA

/-
Derived uniqueness of segment construction.

Mathematically:
  Q != A,
  B(Q,A,X) and B(Q,A,Y),
  AX == BC and AY == BC
  imply X = Y.

Thus two points lying beyond A on the same ray from Q and
realizing the same prescribed segment from A must coincide.

This theorem is entirely internal to Tarski neutral geometry.
It does not use Hilbert incidence, the compatibility bridge,
or decidable equality of points.

The proof uses:
  - derived symmetry and transitivity of segment congruence,
  - derived nondegenerate l2_11,
  - Ax.5: Five-Segment,
  - Ax.3: identity for segment congruence.

First AX == BC and AY == BC imply AX == AY.
Applying nondegenerate l2_11 to Q-A-X and Q-A-Y gives
QX == QY. A final Five-Segment argument gives YX == XX.
Ax.3 then implies Y = X.
-/
theorem tarski_construction_uniqueness
    [TarskiNeutral Geo]
    (Q A X Y B C : Geo.Point)
    (hQA : Q ≠ A)
    (hQAX : Geo.Between Q A X)
    (hQAY : Geo.Between Q A Y)
    (hAXBC : Geo.Congruent A X B C)
    (hAYBC : Geo.Congruent A Y B C) :
    X = Y := by

  have hBCAY : Geo.Congruent B C A Y :=
    tarski_congruent_symmetry
      (Geo := Geo) A Y B C hAYBC

  have hAXAY : Geo.Congruent A X A Y :=
    TarskiNeutral.congruent_transitivity
      (Geo := Geo)
      B C A X A Y
      (tarski_congruent_symmetry
        (Geo := Geo) A X B C hAXBC)
      hBCAY

  have hQAQA : Geo.Congruent Q A Q A :=
    tarski_congruent_reflexivity
      (Geo := Geo) Q A

  have hQXQY : Geo.Congruent Q X Q Y :=
    tarski_l2_11_nondegenerate
      (Geo := Geo)
      Q A X Q A Y
      hQAX
      hQAY
      hQA
      hQAQA
      hAXAY

  -- Five-Segment with:
  --   A,A' = Q,Q
  --   B,B' = A,A
  --   C,C' = X,X
  --   D,D' = Y,X
  have hQYQX : Geo.Congruent Q Y Q X :=
    tarski_congruent_symmetry
      (Geo := Geo) Q X Q Y hQXQY

  have hAYAX : Geo.Congruent A Y A X :=
    tarski_congruent_symmetry
      (Geo := Geo) A X A Y hAXAY

  have hAXAX : Geo.Congruent A X A X :=
    tarski_congruent_reflexivity
      (Geo := Geo) A X

  have hXYXX : Geo.Congruent X Y X X :=
    TarskiNeutral.five_segment
      (Geo := Geo)
      Q Q A A X X Y X
      hQA
      hQAX
      hQAX
      hQAQA
      hAXAX
      hQYQX
      hAYAX

  exact TarskiNeutral.congruent_identity
    (Geo := Geo) X Y X hXYXX

/-
Derived outer transitivity variant for betweenness.

Mathematically:
  B(A,B,C) and B(B,C,D) and B != C
  imply B(A,C,D).

This theorem is entirely internal to Tarski neutral geometry.
It does not use Hilbert incidence, the compatibility bridge,
or decidable equality of points.

The proof uses:
  - Ax.4: segment construction,
  - derived exchange law for betweenness,
  - derived uniqueness of segment construction,
  - derived reflexivity of segment congruence.

Construct X such that B(A,C,X) and CX == CD.
From B(A,B,C) and B(A,C,X), the exchange law gives B(B,C,X).
Thus X and D are two points beyond C on the same ray from B,
both realizing the segment CD from C. Construction uniqueness
gives X = D, hence B(A,C,D).
-/
theorem tarski_between_outer_transitivity2
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hBCD : Geo.Between B C D)
    (hBC : B ≠ C) :
    Geo.Between A C D := by

  obtain ⟨X, hACX, hCXCD⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo) A C C D

  have hBCX : Geo.Between B C X :=
    tarski_between_exchange3
      (Geo := Geo) A B C X hABC hACX

  have hCDCD : Geo.Congruent C D C D :=
    tarski_congruent_reflexivity
      (Geo := Geo) C D

  have hXD : X = D :=
    tarski_construction_uniqueness
      (Geo := Geo)
      B C X D C D
      hBC
      hBCX
      hBCD
      hCXCD
      hCDCD

  simpa [hXD] using hACX

/-
Derived Tarski theorem (historically Ax.16):
outer transitivity of betweenness.

Mathematically:
  B(A,B,C) and B(B,C,D) and B != C
  imply B(A,B,D).

Ax.16 is not part of the primitive axiom system used in
TarskiAxioms.lean.

It is derived here from:
  - derived symmetry of betweenness,
  - derived outer transitivity variant.

Reverse both betweenness relations:
  B(D,C,B) and B(C,B,A).
Since C != B, outer transitivity variant gives B(D,B,A).
Symmetry then yields B(A,B,D).
-/
theorem tarski_between_outer_transitivity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABC : Geo.Between A B C)
    (hBCD : Geo.Between B C D)
    (hBC : B ≠ C) :
    Geo.Between A B D := by

  have hDCB : Geo.Between D C B :=
    tarski_between_symmetry
      (Geo := Geo) B C D hBCD

  have hCBA : Geo.Between C B A :=
    tarski_between_symmetry
      (Geo := Geo) A B C hABC

  have hDBA : Geo.Between D B A :=
    tarski_between_outer_transitivity2
      (Geo := Geo)
      D C B A
      hDCB
      hCBA
      hBC.symm

  exact tarski_between_symmetry
    (Geo := Geo) D B A hDBA

/-
Temporary interface assumption: Outer Connectivity (historical A18).

Mathematically:
  B(A,B,C) and B(A,B,D) and A is distinct from B
  imply
  B(A,C,D) or B(A,D,C).

This is NOT a primitive axiom of the Tarski foundation used in
TarskiAxioms.lean.

Outer Connectivity is a derived theorem of Tarski geometry,
historically known as A18 and corresponding to Satz 5.1 in SST.
Its derivation is substantially deeper than the elementary
betweenness laws A14-A16. In particular, the standard development
passes through a significant part of the derived order and
congruence theory; GeoCoq contains the corresponding result as l5_1.

For the present reconstruction of the Tarski route to Finlay's
proof, we expose Outer Connectivity explicitly at the interface
level rather than importing Hilbert incidence structure or adding
decidable equality of points to the Tarski foundation.

The full derivation of this theorem from TarskiNeutral is deferred
to a separate future development.
-/
axiom tarski_between_outer_connectivity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hAB : A ≠ B)
    (hABC : Geo.Between A B C)
    (hABD : Geo.Between A B D) :
    Geo.Between A C D ∨ Geo.Between A D C


/-
Derived outer connectivity variant.

Mathematically:
  A != B,
  B(A,B,C) and B(A,B,D)
  imply
  B(B,C,D) or B(B,D,C).

This is derived from the temporary Outer Connectivity assumption
(historical A18) and the previously derived exchange law.

It corresponds to l5_2 in the standard Tarski development.
-/
theorem tarski_between_outer_connectivity2
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hAB : A ≠ B)
    (hABC : Geo.Between A B C)
    (hABD : Geo.Between A B D) :
    Geo.Between B C D ∨ Geo.Between B D C := by

  rcases tarski_between_outer_connectivity
      (Geo := Geo) A B C D hAB hABC hABD with hACD | hADC

  · left
    exact tarski_between_exchange3
      (Geo := Geo) A B C D hABC hACD

  · right
    exact tarski_between_exchange3
      (Geo := Geo) A B D C hABD hADC

/-
Derived Tarski theorem (historically Ax.17):
inner connectivity of betweenness.

Mathematically:
  B(A,B,D) and B(A,C,D)
  imply
  B(A,B,C) or B(A,C,B).

Ax.17 is not assumed separately.

It is derived from the temporary Outer Connectivity assumption A18,
via the derived outer-connectivity variant above.

If A = D, the result is immediate from B(A,C,D).
Otherwise, construct P beyond A on the line DA. The construction
gives P != A. Transitivity places both B and C beyond A from P,
and outer connectivity then compares B and C.

Thus A18 remains the only deferred connectivity result in the
current Tarski interface.
-/
theorem tarski_between_inner_connectivity
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABD : Geo.Between A B D)
    (hACD : Geo.Between A C D) :
    Geo.Between A B C ∨ Geo.Between A C B := by

  by_cases hAD : A = D

  · subst D

    have hAB : A = B :=
      TarskiNeutral.between_identity
        (Geo := Geo) A B hABD

    subst B

    left

    have hCAA : Geo.Between C A A :=
      tarski_between_reflexivity
        (Geo := Geo) C A

    exact tarski_between_symmetry
      (Geo := Geo) C A A hCAA

  · obtain ⟨P, hDAP, hAPDA⟩ :=
      TarskiNeutral.segment_construction
        (Geo := Geo) D A D A

    have hPA : P ≠ A := by
      intro hPA
      subst P

      have hDAAA : Geo.Congruent D A A A :=
        tarski_congruent_symmetry
          (Geo := Geo) A A D A hAPDA

      have hDA : D = A :=
        TarskiNeutral.congruent_identity
          (Geo := Geo) D A A hDAAA

      exact hAD hDA.symm

    have hPAD : Geo.Between P A D :=
      tarski_between_symmetry
        (Geo := Geo) D A P hDAP

    have hPAB : Geo.Between P A B :=
      tarski_between_inner_transitivity
        (Geo := Geo) P A B D hPAD hABD

    have hPAC : Geo.Between P A C :=
      tarski_between_inner_transitivity
        (Geo := Geo) P A C D hPAD hACD

    exact tarski_between_outer_connectivity2
      (Geo := Geo)
      P A B C
      hPA
      hPAB
      hPAC

/-
Derived transitivity of Tarski collinearity.

Mathematically:
  TarskiCollinear A G P
  TarskiCollinear G P D
  G != P
  imply
  TarskiCollinear A G D.

This theorem is entirely formulated in the Tarski language.
It does not use Hilbert incidence or the compatibility bridge.

The proof reduces the two collinearity hypotheses to the nine
possible betweenness configurations and uses the derived Tarski
order theory:

  - A14: symmetry of betweenness,
  - A15: inner transitivity,
  - A16: outer transitivity,
  - A17: inner connectivity,
  - A18: outer connectivity.

A18 is currently the only deferred result in this dependency chain;
all the remaining order laws used here are derived in this file.
-/
theorem tarski_collinear_trans
    [TarskiNeutral Geo]
    (A G P D : Geo.Point)
    (hGP : G ≠ P)
    (hAGP : TarskiCollinear Geo A G P)
    (hGPD : TarskiCollinear Geo G P D) :
    TarskiCollinear Geo A G D := by

  rcases hAGP with hAGP | hGPA | hPAG

  · -- B(A,G,P)
    rcases hGPD with hGPD | hPDG | hDGP

    · -- B(G,P,D)
      left
      exact tarski_between_outer_transitivity
        (Geo := Geo)
        A G P D
        hAGP hGPD hGP

    · -- B(P,D,G)
      have hGDP : Geo.Between G D P :=
        tarski_between_symmetry
          (Geo := Geo) P D G hPDG

      left
      exact tarski_between_inner_transitivity
        (Geo := Geo)
        A G D P
        hAGP hGDP

    · -- B(D,G,P)
      have hPGA : Geo.Between P G A :=
        tarski_between_symmetry
          (Geo := Geo) A G P hAGP

      have hPGD : Geo.Between P G D :=
        tarski_between_symmetry
          (Geo := Geo) D G P hDGP

      rcases tarski_between_outer_connectivity
          (Geo := Geo)
          P G A D
          hGP.symm
          hPGA
          hPGD with hPAD | hPDA

      · have hGAD : Geo.Between G A D :=
          tarski_between_exchange3
            (Geo := Geo)
            P G A D
            hPGA hPAD

        right
        right
        exact tarski_between_symmetry
          (Geo := Geo) G A D hGAD

      · right
        left
        exact tarski_between_exchange3
          (Geo := Geo)
          P G D A
          hPGD hPDA

  · -- B(G,P,A)
    rcases hGPD with hGPD | hPDG | hDGP

    · -- B(G,P,D)
      rcases tarski_between_outer_connectivity
          (Geo := Geo)
          G P A D
          hGP
          hGPA
          hGPD with hGAD | hGDA

      · right
        right
        exact tarski_between_symmetry
          (Geo := Geo) G A D hGAD

      · right
        left
        exact hGDA

    · -- B(P,D,G)
      have hGDP : Geo.Between G D P :=
        tarski_between_symmetry
          (Geo := Geo) P D G hPDG

      by_cases hDP : D = P

      · subst D
        right
        left
        exact hGPA

      · have hDPA : Geo.Between D P A :=
          tarski_between_exchange3
            (Geo := Geo)
            G D P A
            hGDP hGPA

        right
        left
        exact tarski_between_outer_transitivity
          (Geo := Geo)
          G D P A
          hGDP hDPA hDP

    · -- B(D,G,P)
      have hDGA : Geo.Between D G A :=
        tarski_between_outer_transitivity
          (Geo := Geo)
          D G P A
          hDGP hGPA hGP

      left
      exact tarski_between_symmetry
        (Geo := Geo) D G A hDGA

  · -- B(P,A,G)
    rcases hGPD with hGPD | hPDG | hDGP

    · -- B(G,P,D)
      have hDPG : Geo.Between D P G :=
        tarski_between_symmetry
          (Geo := Geo) G P D hGPD

      by_cases hPA : P = A

      · subst P
        right
        right
        exact hDPG

      · have hDPA : Geo.Between D P A :=
          tarski_between_inner_transitivity
            (Geo := Geo)
            D P A G
            hDPG hPAG

        right
        right
        exact tarski_between_outer_transitivity2
          (Geo := Geo)
          D P A G
          hDPA hPAG hPA

    · -- B(P,D,G)
      rcases tarski_between_inner_connectivity
          (Geo := Geo)
          P A D G
          hPAG hPDG with hPAD | hPDA

      · have hADG : Geo.Between A D G :=
          tarski_between_exchange3
            (Geo := Geo)
            P A D G
            hPAD hPDG

        right
        left
        exact tarski_between_symmetry
          (Geo := Geo) A D G hADG

      · right
        right
        exact tarski_between_exchange3
          (Geo := Geo)
          P D A G
          hPDA hPAG

    · -- B(D,G,P)
      have hGAP : Geo.Between G A P :=
        tarski_between_symmetry
          (Geo := Geo) P A G hPAG

      have hDGA : Geo.Between D G A :=
        tarski_between_inner_transitivity
          (Geo := Geo)
          D G A P
          hDGP hGAP

      left
      exact tarski_between_symmetry
        (Geo := Geo) D G A hDGA

/--
A parallelogram expressed in the Tarski language by the
common-midpoint characterization of its diagonals.

The nondegeneracy condition follows the standard Tarski
definition used in the development of parallelogram theory.
-/
def TarskiParallelogram
    (A B C D : Geo.Point) : Prop :=
  (A ≠ C ∨ B ≠ D) ∧
  ∃ M : Geo.Point,
    TarskiIsMidpoint Geo M A C ∧
    TarskiIsMidpoint Geo M B D

theorem tarski_parallelogram_of_common_midpoint
    (A B C D M : Geo.Point)
    (hNondeg : A ≠ C ∨ B ≠ D)
    (hMAC : TarskiIsMidpoint Geo M A C)
    (hMBD : TarskiIsMidpoint Geo M B D) :
    TarskiParallelogram Geo A B C D := by
  constructor
  · exact hNondeg
  · exact ⟨M, hMAC, hMBD⟩

theorem tarski_midpoint_parallelogram
    [TarskiNeutral Geo]
    (A B C D M : Geo.Point)
    (hNonCol : ¬ TarskiCollinear Geo A B C)
    (hMAC : TarskiIsMidpoint Geo M A C)
    (hMBD : TarskiIsMidpoint Geo M B D) :
    TarskiParallelogram Geo A B C D := by

  have hAC : A ≠ C := by
    intro hAC
    subst C
    apply hNonCol
    right
    left
    exact tarski_between_reflexivity (Geo := Geo) B A

  exact
    tarski_parallelogram_of_common_midpoint
      Geo A B C D M
      (Or.inl hAC)
      hMAC
      hMBD
/--
Strict parallelism expressed solely in the Tarski language.

The two lines are nondegenerate and have no common point.
Since the present geometry is two-dimensional, no separate
coplanarity condition is required.
-/
def TarskiParallelStrict
    (A B C D : Geo.Point) : Prop :=
  A ≠ B ∧
  C ≠ D ∧
  ¬ ∃ X : Geo.Point,
      TarskiCollinear Geo X A B ∧
      TarskiCollinear Geo X C D

def TarskiParallel
    (A B C D : Geo.Point) : Prop :=
  TarskiParallelStrict Geo A B C D ∨
  (TarskiCollinear Geo A B C ∧
   TarskiCollinear Geo A B D)


/-
Derived construction of a point symmetric to P with respect to Q.

For arbitrary P and Q there exists X such that Q is the midpoint
of PX.

This is the Tarski analogue of the Suppes doubling construction.

It is derived from:
  - Ax.4: segment construction,
  - derived symmetry of segment congruence.
-/
/-
------------------------------------------------------------
Midpoint Construction
------------------------------------------------------------

This section contains the constructions used by the midpoint API.

The two declarations marked as temporary placeholders isolate the
remaining constructive work. They will later be replaced by proofs
from TarskiNeutral without changing the public interface.
-/

theorem tarski_symmetric_point_exists
    [TarskiNeutral Geo]
    (P Q : Geo.Point) :
    ∃ X : Geo.Point,
      TarskiIsMidpoint Geo Q P X := by

  obtain ⟨X, hPQX, hQXPQ⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo)
      P Q P Q

  have hPQQX : Geo.Congruent P Q Q X :=
    tarski_congruent_symmetry
      (Geo := Geo)
      Q X P Q
      hQXPQ

  exact ⟨X, hPQX, hPQQX⟩



/-
Temporary construction placeholders.

These declarations isolate the remaining constructive steps needed
for midpoint existence in neutral Tarski geometry.
-/


/-
Temporary placeholder for the construction of an equidistant point.

For every pair of points A and B, this statement provides a point C
such that CA is congruent to CB.

Together with tarski_isosceles_base_midpoint, this yields general
midpoint existence.

This result is not intended to remain an additional axiom of the final
theory.

Planned replacement:
  prove this statement from TarskiNeutral by an explicit construction.

Once such a proof is available, this axiom should be replaced by a
theorem with the same statement, so that no later code needs to change.
-/
/-
axiom tarski_equidistant_point_exists
    [TarskiNeutral Geo]
    (A B : Geo.Point) :
    ∃ C : Geo.Point,
      Geo.Congruent C A C B
-/


/-
Gupta configuration for the midpoint of the base of an
isosceles triangle.

Given CA == CB, construct:

  P beyond A on CA,
  Q beyond B on CB,
  R as the Inner-Pasch intersection of AQ and BP,
  X as the Inner-Pasch intersection of AB and RC.

At this stage no metric property of X is asserted.
The theorem isolates the purely constructive part of Gupta's proof.
-/

/-
theorem tarski_gupta_configuration
    [TarskiNeutral Geo]
    (A B C : Geo.Point)
    (_hCAB : Geo.Congruent C A C B) :
    ∃ P Q R X : Geo.Point,
      Geo.Between C A P ∧
      Geo.Congruent A P A C ∧
      Geo.Between C B Q ∧
      Geo.Congruent B Q A P ∧
      Geo.Between A R Q ∧
      Geo.Between B R P ∧
      Geo.Between R X C ∧
      Geo.Between A X B := by

  obtain ⟨P, hCAP, hAPAC⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo)
      C A A C

  obtain ⟨Q, hCBQ, hBQAP⟩ :=
    TarskiNeutral.segment_construction
      (Geo := Geo)
      C B A P

  have hPAC : Geo.Between P A C :=
    tarski_between_symmetry
      (Geo := Geo)
      C A P
      hCAP

  have hQBC : Geo.Between Q B C :=
    tarski_between_symmetry
      (Geo := Geo)
      C B Q
      hCBQ

  obtain ⟨R, hARQ, hBRP⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      P Q C A B
      hPAC
      hQBC

  obtain ⟨X, hRXC, hAXB⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      B C P R A
      hBRP
      hCAP

  exact
    ⟨P, Q, R, X,
      hCAP,
      hAPAC,
      hCBQ,
      hBQAP,
      hARQ,
      hBRP,
      hRXC,
      hAXB⟩
-/









/-
Existence of a midpoint for an arbitrary segment.

The degenerate case A = B is immediate.
The nondegenerate case will be obtained by constructing
a point equidistant from A and B and applying
tarski_midpoint_exists_of_equidistant.
-/


/-
------------------------------------------------------------
Midpoint Properties
------------------------------------------------------------
-/

theorem tarski_midpoint_ne_second
    [TarskiNeutral Geo]
    (P B C : Geo.Point)
    (hBC : B ≠ C)
    (hP : TarskiIsMidpoint Geo P B C) :
    P ≠ C := by
  intro hPC
  subst C

  have hBP : B = P :=
    TarskiNeutral.congruent_identity
      (Geo := Geo) B P P hP.2

  exact hBC hBP

theorem tarski_noncollinear_ne_second_third
    [TarskiNeutral Geo]
    (A B C : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C)) :
    B = C -> False := by
  intro hBC
  subst C
  apply hNonCol
  left
  exact tarski_between_reflexivity
    (Geo := Geo) A B

theorem tarski_midpoint_ne_third_of_noncollinear
    [TarskiNeutral Geo]
    (A B C P : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C) :
    P = C -> False := by

  have hBC : B = C -> False :=
    tarski_noncollinear_ne_second_third
      Geo A B C hNonCol

  exact
    tarski_midpoint_ne_second
      Geo P B C hBC hP

theorem tarski_noncollinear_midpoint_second
    [TarskiNeutral Geo]
    (A B C P : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C) :
    Not (TarskiCollinear Geo A P C) := by

  intro hAPC

  have hBC : B = C -> False :=
    tarski_noncollinear_ne_second_third
      Geo A B C hNonCol

  have hPC : P = C -> False :=
    tarski_midpoint_ne_second
      Geo P B C hBC hP

  have hPCB : TarskiCollinear Geo P C B := by
    right
    right
    exact hP.1

  have hAPB : TarskiCollinear Geo A P B :=
    tarski_collinear_trans
      Geo A P C B
      hPC
      hAPC
      hPCB

  have hABP : TarskiCollinear Geo A B P :=
    tarski_collinear_symmetry
      Geo A P B hAPB

  have hBP : B = P -> False := by
    intro hBP
    subst B

    have hPCPP : Geo.Congruent P C P P :=
      tarski_congruent_symmetry
        (Geo := Geo)
        P P P C
        hP.2

    have hPCeq : P = C :=
      TarskiNeutral.congruent_identity
        (Geo := Geo) P C P hPCPP

    exact hPC hPCeq

  have hBPC : TarskiCollinear Geo B P C := by
    left
    exact hP.1

  have hABC : TarskiCollinear Geo A B C :=
    tarski_collinear_trans
      Geo A B P C
      hBP
      hABP
      hBPC

  exact hNonCol hABC

/-
TEMPORARY DERIVED AXIOM.

Central symmetry preserves segment congruence.

If M is the midpoint of AA' and BB', then AB is congruent to A'B'.

This is a theorem of neutral Tarski geometry, corresponding to
GeoCoq lemma l7_13.  Its derivation uses the earlier congruence
and Five-Segment machinery.

It is declared temporarily as an axiom in order to continue the
reconstruction of the Tarski midsegment proof.

TODO:
Replace this declaration by a proof from TarskiNeutral.
-/
axiom tarski_central_symmetry_congruent
    [TarskiNeutral Geo]
    (M A B A' B' : Geo.Point)
    (hA : TarskiIsMidpoint Geo M A A')
    (hB : TarskiIsMidpoint Geo M B B') :
    Geo.Congruent A B A' B'

/-
Derived symmetry of the Tarski midpoint relation.

Mathematically:
  if M is the midpoint of AB,
  then M is also the midpoint of BA.
-/
theorem tarski_midpoint_symmetry
    [TarskiNeutral Geo]
    (M A B : Geo.Point)
    (hM : TarskiIsMidpoint Geo M A B) :
    TarskiIsMidpoint Geo M B A := by

  constructor

  · exact
      tarski_between_symmetry
        (Geo := Geo) A M B hM.1

  ·
    have h₁ : Geo.Congruent M A B M :=
      tarski_congruent_reverse_both
        (Geo := Geo) A M M B hM.2

    exact
      tarski_congruent_symmetry
        (Geo := Geo) M A B M h₁

/-
TEMPORARY DERIVED AXIOM.

Central symmetry maps a nondegenerate line to a strictly parallel line.

If M is the midpoint of AA' and BB', and A and B are distinct,
then AB and A'B' are strictly parallel.

This is a theorem of neutral Tarski geometry.  It is declared
temporarily in order to continue the reconstruction of the
natural Tarski proof of the Midsegment Theorem.

TODO:
Replace this declaration by a proof from TarskiNeutral.
-/

/-
TEMPORARY DERIVED AXIOM.

If M is the midpoint of AA' and BB', then the lines AB and A'B'
have no common point, unless they belong to the degenerate
collinear case.

This corresponds to GeoCoq lemma midpoint_par.
-/


axiom tarski_central_symmetry_parallel
    [TarskiNeutral Geo]
    (M A B A' B' : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B M))
    (hA : TarskiIsMidpoint Geo M A A')
    (hB : TarskiIsMidpoint Geo M B B') :
    TarskiParallelStrict Geo A B A' B'

theorem tarski_parallel_strict_collinear_right
    [TarskiNeutral Geo]
    (A X B P C : Geo.Point)
    (hPar : TarskiParallelStrict Geo A X C P)
    (hBPC : TarskiCollinear Geo B P C)
    (hBP : B = P -> False) :
    TarskiParallelStrict Geo A X B P := by

  rcases hPar with ⟨hAX, hCP, hNoInt⟩

  constructor
  · exact hAX

  constructor
  · exact hBP

  · intro hInt
    apply hNoInt

    rcases hInt with ⟨Y, hYAX, hYBP⟩

    have hYPB : TarskiCollinear Geo Y P B :=
      tarski_collinear_symmetry
        Geo Y B P hYBP

    have hPCB : TarskiCollinear Geo P C B :=
      (tarski_collinear_cycle Geo B P C).mp hBPC

    have hPBC : TarskiCollinear Geo P B C :=
      tarski_collinear_symmetry
        Geo P C B hPCB

    have hPB : P = B -> False := by
      intro hPB
      exact hBP hPB.symm

    have hYPC : TarskiCollinear Geo Y P C :=
      tarski_collinear_trans
        Geo Y P B C
        hPB
        hYPB
        hPBC

    have hYCP : TarskiCollinear Geo Y C P :=
      tarski_collinear_symmetry
        Geo Y P C hYPC

    exact ⟨Y, hYAX, hYCP⟩

theorem tarski_parallel_strict_collinear_left
    [TarskiNeutral Geo]
    (A X B P C : Geo.Point)
    (hPar : TarskiParallelStrict Geo C P A X)
    (hBPC : TarskiCollinear Geo B P C)
    (hBP : B = P -> False) :
    TarskiParallelStrict Geo B P A X := by

  rcases hPar with ⟨hCP, hAX, hNoInt⟩

  constructor
  · exact hBP

  constructor
  · exact hAX

  · intro hInt
    apply hNoInt

    rcases hInt with ⟨Y, hYBP, hYAX⟩

    have hYPB : TarskiCollinear Geo Y P B :=
      tarski_collinear_symmetry
        Geo Y B P hYBP

    have hPCB : TarskiCollinear Geo P C B :=
      (tarski_collinear_cycle Geo B P C).mp hBPC

    have hPBC : TarskiCollinear Geo P B C :=
      tarski_collinear_symmetry
        Geo P C B hPCB

    have hPB : P = B -> False := by
      intro hPB
      exact hBP hPB.symm

    have hYPC : TarskiCollinear Geo Y P C :=
      tarski_collinear_trans
        Geo Y P B C
        hPB
        hYPB
        hPBC

    have hYCP : TarskiCollinear Geo Y C P :=
      tarski_collinear_symmetry
        Geo Y P C hYPC

    exact ⟨Y, hYCP, hYAX⟩
/-
A nondegenerate midpoint is distinct from the first endpoint.

Mathematically:
  B != C and P is the midpoint of BC
  imply B != P.
-/
theorem tarski_midpoint_ne_first
    [TarskiNeutral Geo]
    (P B C : Geo.Point)
    (hBC : B = C -> False)
    (hP : TarskiIsMidpoint Geo P B C) :
    B = P -> False := by

  intro hBP
  subst B

  have hPCPP : Geo.Congruent P C P P :=
    tarski_congruent_symmetry
      (Geo := Geo)
      P P P C
      hP.2

  have hPC : P = C :=
    TarskiNeutral.congruent_identity
      (Geo := Geo) P C P hPCPP

  exact hBC hPC

/-
TEMPORARY DERIVED AXIOM.

One pair of opposite sides parallel and congruent determines
one of the two possible parallelogram orientations.

This corresponds to GeoCoq lemma par_cong_plg_2.

TODO:
Replace this declaration by a proof from TarskiNeutral.
-/
axiom tarski_parallel_congruent_parallelogram_cases
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hPar : TarskiParallelStrict Geo A B C D)
    (hCong : Geo.Congruent A B C D) :
    TarskiParallelogram Geo A B C D ∨
    TarskiParallelogram Geo A B D C

/-
TEMPORARY DERIVED AXIOM.

The midpoint of a segment is unique.

If M and N are both midpoints of AB, then M = N.

This is a theorem of neutral Tarski geometry. It is declared
temporarily in order to continue the reconstruction of the
natural Tarski proof of the Midsegment Theorem.

TODO:
Replace this declaration by a proof from TarskiNeutral.
-/
axiom tarski_midpoint_unique
    [TarskiNeutral Geo]
    (M N A B : Geo.Point)
    (hM : TarskiIsMidpoint Geo M A B)
    (hN : TarskiIsMidpoint Geo N A B) :
    M = N

/-
TEMPORARY DERIVED AXIOM.

A nondegenerate Tarski parallelogram has strictly parallel
opposite sides.

This formulation corresponds to the GeoCoq lemma
ncol134_plg__pars1423:

  not Col A C D
  parallelogram A B C D
  ---------------------
  AD strictly parallel BC

TODO:
Replace this declaration by a proof from TarskiNeutral.
-/
axiom tarski_parallelogram_opposite_parallel
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A C D))
    (hPar : TarskiParallelogram Geo A B C D) :
    TarskiParallelStrict Geo A D B C

theorem tarski_midpoint_noncol_left
    [TarskiNeutral Geo]
    (A B C P : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C) :
    Not (TarskiCollinear Geo A P B) := by

  intro hAPB

  have hBC : B = C -> False :=
    tarski_noncollinear_ne_second_third
      Geo A B C hNonCol

  have hBP : B = P -> False :=
    tarski_midpoint_ne_first
      Geo P B C hBC hP

  have hBPC : TarskiCollinear Geo B P C := by
    left
    exact hP.1
  have hABP : TarskiCollinear Geo A B P :=
    tarski_collinear_symmetry
      Geo A P B hAPB

  have hABC : TarskiCollinear Geo A B C :=
    tarski_collinear_trans
      Geo A B P C
      hBP
      hABP
      hBPC

  exact hNonCol hABC

/-
TEMPORARY DERIVED AXIOM.

Two pairs of opposite strictly parallel sides determine
a Tarski parallelogram.

This corresponds to the role of GeoCoq lemma parallel_2_plg.

TODO:
Replace this declaration by a proof from TarskiNeutral.
-/


theorem tarski_parallel_strict_symm_left
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hPar : TarskiParallelStrict Geo A B C D) :
    TarskiParallelStrict Geo B A C D := by

  rcases hPar with ⟨hAB, hCD, hNoInt⟩

  constructor
  · intro hBA
    exact hAB hBA.symm

  constructor
  · exact hCD

  · intro hInt
    apply hNoInt

    rcases hInt with ⟨X, hXBA, hXCD⟩

    have hXAB : TarskiCollinear Geo X A B :=
      tarski_collinear_symmetry
        Geo X B A hXBA

    exact ⟨X, hXAB, hXCD⟩

theorem tarski_parallel_strict_symm_right
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hPar : TarskiParallelStrict Geo A B C D) :
    TarskiParallelStrict Geo A B D C := by

  rcases hPar with ⟨hAB, hCD, hNoInt⟩

  constructor
  · exact hAB

  constructor
  · intro hDC
    exact hCD hDC.symm

  · intro hInt
    apply hNoInt

    rcases hInt with ⟨X, hXAB, hXDC⟩

    have hXCD : TarskiCollinear Geo X C D :=
      tarski_collinear_symmetry
        Geo X D C hXDC

    exact ⟨X, hXAB, hXCD⟩


theorem tarski_parallel_strict_symm_both
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hPar : TarskiParallelStrict Geo A B C D) :
    TarskiParallelStrict Geo B A D C := by

  have hLeft : TarskiParallelStrict Geo B A C D :=
    tarski_parallel_strict_symm_left
      Geo A B C D hPar

  exact
    tarski_parallel_strict_symm_right
      Geo B A C D hLeft

/-!
## Three-midpoint configuration
-/

theorem tarski_midpoint_parallelogram_construction
    [TarskiNeutral Geo]
    (A B C P Q : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C) :
    ∃ X : Geo.Point,
      TarskiIsMidpoint Geo Q P X ∧
      TarskiParallelogram Geo A P C X := by

  have hAPC : Not (TarskiCollinear Geo A P C) :=
    tarski_noncollinear_midpoint_second
      Geo A B C P hNonCol hP

  obtain ⟨X, hQPX⟩ :=
    tarski_symmetric_point_exists
      Geo P Q

  have hPar :
      TarskiParallelogram Geo A P C X :=
    tarski_midpoint_parallelogram
      Geo A P C X Q
      hAPC
      hQ
      hQPX

  exact ⟨X, hQPX, hPar⟩


theorem tarski_midsegment_aux_congruent
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    Geo.Congruent A X B P := by

  have hQXP : TarskiIsMidpoint Geo Q X P :=
    tarski_midpoint_symmetry
      Geo Q P X hQPX

  have hAXCP : Geo.Congruent A X C P :=
    tarski_central_symmetry_congruent
      Geo Q A X C P hQ hQXP

  have hPCBP : Geo.Congruent P C B P :=
    tarski_congruent_symmetry
      (Geo := Geo) B P P C hP.2

  have hPCCP : Geo.Congruent P C C P :=
    TarskiNeutral.congruent_reversal
      (Geo := Geo) P C

  have hCPBP : Geo.Congruent C P B P :=
    TarskiNeutral.congruent_transitivity
      (Geo := Geo)
      P C C P B P
      hPCCP
      hPCBP

  have hCPAX : Geo.Congruent C P A X :=
    tarski_congruent_symmetry
      (Geo := Geo) A X C P hAXCP

  exact
    TarskiNeutral.congruent_transitivity
      (Geo := Geo)
      C P A X B P
      hCPAX
      hCPBP


theorem tarski_midsegment_aux_ne
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    A = X -> False := by

  intro hAX
  subst X

  have hAPC : Not (TarskiCollinear Geo A P C) :=
    tarski_noncollinear_midpoint_second
      Geo A B C P hNonCol hP

  have hAC : A = C -> False := by
    intro hAC
    subst C
    apply hAPC
    right
    left
    exact tarski_between_reflexivity
      (Geo := Geo) P A

  have hQCA : TarskiIsMidpoint Geo Q C A :=
    tarski_midpoint_symmetry
      Geo Q A C hQ

  have hQA : Q = A -> False :=
    tarski_midpoint_ne_second
      Geo Q C A
      (fun hCA => hAC hCA.symm)
      hQCA

  have hPQA : TarskiCollinear Geo P Q A := by
    left
    exact hQPX.1

  have hQAC : TarskiCollinear Geo Q A C := by
    have hQCAcol : TarskiCollinear Geo Q C A := by
      right
      right
      exact hQ.1
    exact
      tarski_collinear_symmetry
        Geo Q C A hQCAcol

  have hPQC : TarskiCollinear Geo P Q C :=
    tarski_collinear_trans
      Geo P Q A C
      hQA
      hPQA
      hQAC

  have hAP : A = P -> False := by
    intro hAPeq
    subst P
    apply hAPC
    left

    have hCAA : Geo.Between C A A :=
      tarski_between_reflexivity
        (Geo := Geo) C A

    exact tarski_between_symmetry
      (Geo := Geo) C A A hCAA

  have hQAP : TarskiIsMidpoint Geo Q A P :=
    tarski_midpoint_symmetry
      Geo Q P A hQPX

  have hQP : Q = P -> False :=
    tarski_midpoint_ne_second
      Geo Q A P
      hAP
      hQAP

  have hAPQ : TarskiCollinear Geo A P Q := by
    have hQAPcol : TarskiCollinear Geo Q A P := by
      right
      right
      exact hQPX.1

    exact
      (tarski_collinear_cycle Geo Q A P).mp hQAPcol

  have hAPC' : TarskiCollinear Geo A P C :=
    tarski_collinear_trans
      Geo A P Q C
      (fun hPQ => hQP hPQ.symm)
      hAPQ
      hPQC

  exact hAPC hAPC'

theorem tarski_midsegment_aux_noncol
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    Not (TarskiCollinear Geo A X Q) := by

  intro hAXQ

  have hAPC : Not (TarskiCollinear Geo A P C) :=
    tarski_noncollinear_midpoint_second
      Geo A B C P hNonCol hP

  have hAC : A = C -> False :=
    fun hAC =>
      hNonCol (by
        right
        left
        rw [hAC]
        exact tarski_between_reflexivity
          (Geo := Geo) B C)

  have hAQ : A = Q -> False :=
    tarski_midpoint_ne_first
      Geo Q A C hAC hQ

  have hAQX : TarskiCollinear Geo A Q X :=
    tarski_collinear_symmetry
      Geo A X Q hAXQ

  have hQXP : TarskiCollinear Geo Q X P := by
    right
    right
    exact hQPX.1

  have hPX : P = X -> False := by
    intro hPX

    have hPQP : Geo.Between P Q P := by
      simpa [hPX] using hQPX.1

    have hPQ : P = Q :=
      TarskiNeutral.between_identity
        (Geo := Geo) P Q hPQP

    apply hAPC

    simpa [hPQ] using
      (tarski_midpoint_collinear
        Geo Q A C hQ)

  have hQX : Q = X -> False :=
    tarski_midpoint_ne_second
      Geo Q P X hPX hQPX

  have hAQP : TarskiCollinear Geo A Q P :=
    tarski_collinear_trans
      Geo A Q X P
      hQX
      hAQX
      hQXP

  have hAPQ : TarskiCollinear Geo A P Q :=
    tarski_collinear_symmetry
      Geo A Q P hAQP

  have hQAC : TarskiCollinear Geo Q A C :=
    tarski_collinear_symmetry
      Geo Q C A
      ((tarski_collinear_cycle Geo A Q C).mp
        (tarski_midpoint_collinear Geo Q A C hQ))

  have hPQC : TarskiCollinear Geo P Q C :=
    tarski_collinear_trans
      Geo P Q A C
      (fun hQA => hAQ hQA.symm)
      ((tarski_collinear_cycle Geo A P Q).mp hAPQ)
      hQAC

  have hPQ : P = Q -> False := by
    intro hPQ
    subst P

    apply hAPC

    exact tarski_midpoint_collinear
      Geo Q A C hQ

  have hAPC' : TarskiCollinear Geo A P C :=
    tarski_collinear_trans
      Geo A P Q C
      hPQ
      hAPQ
      hPQC

  exact hAPC hAPC'

theorem tarski_midsegment_aux_parallel
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A X C P := by

  have hAX : A = X -> False :=
    tarski_midsegment_aux_ne
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  have hAXQ : Not (TarskiCollinear Geo A X Q) :=
    tarski_midsegment_aux_noncol
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  have hQXP : TarskiIsMidpoint Geo Q X P :=
    tarski_midpoint_symmetry
      Geo Q P X hQPX

  exact
    tarski_central_symmetry_parallel
      Geo Q A X C P
      hAXQ
      hQ
      hQXP


theorem tarski_midsegment_aux_parallel_BP
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A X B P := by

  have hParAXCP : TarskiParallelStrict Geo A X C P :=
    tarski_midsegment_aux_parallel
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  have hBC : B = C -> False :=
    tarski_noncollinear_ne_second_third
      Geo A B C hNonCol

  have hBP : B = P -> False :=
    tarski_midpoint_ne_first
      Geo P B C hBC hP

  have hBPC : TarskiCollinear Geo B P C := by
    left
    exact hP.1

  exact
    tarski_parallel_strict_collinear_right
      Geo A X B P C
      hParAXCP
      hBPC
      hBP


theorem tarski_midsegment_parallelogram_cases
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelogram Geo A X B P ∨
    TarskiParallelogram Geo A X P B := by

  have hCong : Geo.Congruent A X B P :=
    tarski_midsegment_aux_congruent
      Geo A B C P Q X
      hP hQ hQPX

  have hPar : TarskiParallelStrict Geo A X B P :=
    tarski_midsegment_aux_parallel_BP
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  exact
    tarski_parallel_congruent_parallelogram_cases
      Geo A X B P
      hPar
      hCong


theorem tarski_midsegment_first_parallelogram_impossible
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X)
    (hPar : TarskiParallelogram Geo A X B P) :
    False := by

  rcases hPar with ⟨_hNondeg, M, hMAB, hMXP⟩

  have hQXP : TarskiIsMidpoint Geo Q X P :=
    tarski_midpoint_symmetry
      Geo Q P X hQPX

  have hMQ : M = Q :=
    tarski_midpoint_unique
      Geo M Q X P
      hMXP
      hQXP

  subst M

  have hQAB : TarskiIsMidpoint Geo Q A B :=
    hMAB

  have hAB : A = B -> False := by
    intro hABeq
    subst B
    apply hNonCol
    left

    have hCAA : Geo.Between C A A :=
      tarski_between_reflexivity
        (Geo := Geo) C A

    exact
      tarski_between_symmetry
        (Geo := Geo) C A A hCAA

  have hQBA : TarskiIsMidpoint Geo Q B A :=
    tarski_midpoint_symmetry
      Geo Q A B hQAB

  have hQA : Q = A -> False :=
    tarski_midpoint_ne_second
      Geo Q B A
      (fun hBA => hAB hBA.symm)
      hQBA

  have hQB : Q = B -> False :=
    tarski_midpoint_ne_second
      Geo Q A B
      hAB
      hQAB

  have hAQB : TarskiCollinear Geo A Q B := by
    left
    exact hQAB.1

  have hABQ : TarskiCollinear Geo A B Q :=
    tarski_collinear_symmetry
      Geo A Q B hAQB

  have hBQA : TarskiCollinear Geo B Q A :=
    (tarski_collinear_cycle Geo A B Q).mp hABQ

  have hAQC : TarskiCollinear Geo A Q C := by
    left
    exact hQ.1

  have hQCA : TarskiCollinear Geo Q C A :=
    (tarski_collinear_cycle Geo A Q C).mp hAQC

  have hQAC : TarskiCollinear Geo Q A C :=
    tarski_collinear_symmetry
      Geo Q C A hQCA

  have hBQC : TarskiCollinear Geo B Q C :=
    tarski_collinear_trans
      Geo B Q A C
      hQA
      hBQA
      hQAC

  have hBQ : B = Q -> False := by
    intro hBQ
    exact hQB hBQ.symm

  have hABC : TarskiCollinear Geo A B C :=
    tarski_collinear_trans
      Geo A B Q C
      hBQ
      hABQ
      hBQC

  exact hNonCol hABC


theorem tarski_midsegment_second_parallelogram
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelogram Geo A X P B := by

  have hCases :
      TarskiParallelogram Geo A X B P ∨
      TarskiParallelogram Geo A X P B :=
    tarski_midsegment_parallelogram_cases
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  rcases hCases with hBad | hGood

  · exact False.elim
      (tarski_midsegment_first_parallelogram_impossible
        Geo A B C P Q X
        hNonCol hQ hQPX hBad)

  · exact hGood


theorem tarski_midsegment_parallel_AB_XP
    [TarskiNeutral Geo]
    (A B C P Q X : Geo.Point)
    (hNonCol : Not (TarskiCollinear Geo A B C))
    (hP : TarskiIsMidpoint Geo P B C)
    (hQ : TarskiIsMidpoint Geo Q A C)
    (hQPX : TarskiIsMidpoint Geo Q P X) :
    TarskiParallelStrict Geo A B X P := by

  have hPar :
      TarskiParallelogram Geo A X P B :=
    tarski_midsegment_second_parallelogram
      Geo A B C P Q X
      hNonCol hP hQ hQPX

  have hAPB : Not (TarskiCollinear Geo A P B) :=
    tarski_midpoint_noncol_left
      Geo A B C P
      hNonCol hP

  exact
    tarski_parallelogram_opposite_parallel
      Geo A X P B
      hAPB
      hPar

/--
Every segment has a midpoint under the midpoint-existence extension.
-/

----------------------------------------------------
-- Five-Segment variants
----------------------------------------------------

/-
Inner Five-Segment theorem (SST, Satz 4.2).

This is the variant of the Five-Segment theorem used in
Gupta's midpoint construction.
-/

theorem tarski_inner_five_segment
    [TarskiNeutral Geo]
    (A A' B B' C C' D D' : Geo.Point)
    --(hAB : A ≠ B)
    (hABC : Geo.Between A B C)
    (hA'B'C' : Geo.Between A' B' C')
    (hAC : Geo.Congruent A C A' C')
    (hBC : Geo.Congruent B C B' C')
    (hAD : Geo.Congruent A D A' D')
    (hCD : Geo.Congruent C D C' D') :
    Geo.Congruent B D B' D' := by

  by_cases hACeq : A = C

  · subst C

    have hABeq : A = B :=
      TarskiNeutral.between_identity
        (Geo := Geo)
        A B
        hABC

    subst B

    have hA'C'AA : Geo.Congruent A' C' A A :=
      tarski_congruent_symmetry
        (Geo := Geo)
        A A A' C'
        hAC

    have hA'C'eq : A' = C' :=
      TarskiNeutral.congruent_identity
        (Geo := Geo)
        A' C' A
        hA'C'AA

    subst C'

    have hA'B'eq : A' = B' :=
      TarskiNeutral.between_identity
        (Geo := Geo)
        A' B'
        hA'B'C'

    subst B'

    exact hAD

  · obtain ⟨E, hACE, hCEAC⟩ :=
      TarskiNeutral.segment_construction
        (Geo := Geo)
        A C A C

    obtain ⟨E', hA'C'E', hC'E'AC⟩ :=
      TarskiNeutral.segment_construction
        (Geo := Geo)
        A' C' A C

    have hACCE : Geo.Congruent A C C E :=
      tarski_congruent_symmetry
        (Geo := Geo)
        C E A C
        hCEAC

    have hACC'E' : Geo.Congruent A C C' E' :=
      tarski_congruent_symmetry
        (Geo := Geo)
        C' E' A C
        hC'E'AC

    have hCEC'E' : Geo.Congruent C E C' E' :=
      TarskiNeutral.congruent_transitivity
        (Geo := Geo)
        A C C E C' E'
        hACCE
        hACC'E'

    have hEDE'D' : Geo.Congruent E D E' D' :=
      TarskiNeutral.five_segment
        (Geo := Geo)
        A A' C C' E E' D D'
        hACeq
        hACE
        hA'C'E'
        hAC
        hCEC'E'
        hAD
        hCD

    have hECA : Geo.Between E C A :=
      tarski_between_symmetry
        (Geo := Geo)
        A C E
        hACE

    have hCBA : Geo.Between C B A :=
      tarski_between_symmetry
        (Geo := Geo)
        A B C
        hABC

    have hECB : Geo.Between E C B :=
      tarski_between_inner_transitivity
        (Geo := Geo)
        E C B A
        hECA
        hCBA

    have hE'C'A' : Geo.Between E' C' A' :=
      tarski_between_symmetry
        (Geo := Geo)
        A' C' E'
        hA'C'E'

    have hC'B'A' : Geo.Between C' B' A' :=
      tarski_between_symmetry
        (Geo := Geo)
        A' B' C'
        hA'B'C'

    have hE'C'B' : Geo.Between E' C' B' :=
      tarski_between_inner_transitivity
        (Geo := Geo)
        E' C' B' A'
        hE'C'A'
        hC'B'A'

    have hEC : E ≠ C := by
      intro hEq

      subst E

      have hCCAC : Geo.Congruent C C A C :=
        hCEAC

      have hACCC : Geo.Congruent A C C C :=
        tarski_congruent_symmetry
          (Geo := Geo)
          C C A C
          hCCAC

      have hAC' : A = C :=
        TarskiNeutral.congruent_identity
          (Geo := Geo)
          A C C
          hACCC

      exact hACeq hAC'
    have hECE'C' : Geo.Congruent E C E' C' :=
      tarski_congruent_reverse_both
        (Geo := Geo)
        C E C' E'
        hCEC'E'

    have hCBC'B' : Geo.Congruent C B C' B' :=
      tarski_congruent_reverse_both
        (Geo := Geo)
        B C B' C'
        hBC

    exact
      TarskiNeutral.five_segment
        (Geo := Geo)
        E E' C C' B B' D D'
        hEC
        hECB
        hE'C'B'
        hECE'C'
        hCBC'B'
        hEDE'D'
        hCD


/-
Existence of a midpoint for an arbitrary segment.

Temporary interface axiom.

This declaration will later be replaced by the constructive
proof developed in `TarskiGupta.lean`.
-/
axiom tarski_midpoint_exists
    [TarskiNeutral Geo]
    (A B : Geo.Point) :
    ∃ M : Geo.Point,
      TarskiIsMidpoint Geo M A B



/-
Two medians of a nondegenerate triangle have a common point.

Let E be the midpoint of AC and F the midpoint of AB. Then

  C - E - A
  B - F - A

and inner Pasch applied to triangle CBA gives a point G such that

  E - G - B
  F - G - C.

Hence G lies on both median lines BE and CF.
-/
theorem tarski_two_medians_intersect
    [TarskiNeutral Geo]
    (A B C E F : Geo.Point)
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B) :
    Exists fun G : Geo.Point =>
      TarskiCollinear Geo B E G /\
      TarskiCollinear Geo C F G := by

  have hCEA : Geo.Between C E A :=
    tarski_between_symmetry
      (Geo := Geo)
      A E C
      hE.1

  have hBFA : Geo.Between B F A :=
    tarski_between_symmetry
      (Geo := Geo)
      A F B
      hF.1

  obtain ⟨G, hEGB, hFGC⟩ :=
    TarskiNeutral.inner_pasch
      (Geo := Geo)
      C B A E F
      hCEA
      hBFA

  have hBEG : TarskiCollinear Geo B E G :=
    Or.inr (Or.inl hEGB)

  have hCFG : TarskiCollinear Geo C F G :=
    Or.inr (Or.inl hFGC)

  exact ⟨G, hBEG, hCFG⟩

/-
Collinearity is preserved by equality of the three corresponding
pairwise distances.

This is the Tarski-language counterpart of the OTTER rule

  Col(A,B,C) and E3(A,B,C,A',B',C')
  imply Col(A',B',C').

The proof from the neutral Tarski axioms is still to be reconstructed.
-/

/-
Transfer of collinearity under equality of the three pairwise
distances.

This corresponds to clause 53 in the OTTER proof of SST Satz 7.25.
It is currently treated as an explicit interface assumption.
-/

/-
axiom tarski_collinear_congruence_transfer
    [TarskiPlane Geo]
    (A B C A' B' C' : Geo.Point)
    (hCol : TarskiCollinear Geo A B C)
    (hAB : Geo.Congruent A B A' B')
    (hAC : Geo.Congruent A C A' C')
    (hBC : Geo.Congruent B C B' C') :
    TarskiCollinear Geo A' B' C'
-/

/-
Uniqueness of a line determined by two distinct points.

If two nondegenerate lines contain two distinct common points,
then every point collinear with the first pair is also collinear
with the second pair.

This corresponds to clause 104 used in the OTTER proof of
SST Satz 7.25.

The derivation from the primitive Tarski plane axioms is deferred.
-/

/-
axiom tarski_collinear_two_common_points
    [TarskiPlane Geo]
    (A B P Q C D E : Geo.Point)
    (hAB : A ≠ B)
    (hPQ : P ≠ Q)
    (hABC : TarskiCollinear Geo A B C)
    (hPQC : TarskiCollinear Geo P Q C)
    (hABD : TarskiCollinear Geo A B D)
    (hPQD : TarskiCollinear Geo P Q D)
    (hCD : C ≠ D)
    (hABE : TarskiCollinear Geo A B E) :
    TarskiCollinear Geo P Q E
-/

end Tarski

end Geometry

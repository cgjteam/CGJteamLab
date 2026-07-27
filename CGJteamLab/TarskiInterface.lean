import CGJteamLab.HilbertInterface
import CGJteamLab.TarskiAxioms

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Geo)

/-!
# TarskiBase

Basic notions derived from Tarski's primitive relations and their
explicit connection to the shared language of `GeometryBase`.

This module adds no geometric axioms. The only compatibility assumption
is isolated in `TarskiGeometryBaseBridge`.
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

/--
Compatibility data between Tarski collinearity and the incidence-based
collinearity used by `GeometryBase`.

Keeping this bridge explicit avoids identifying `Geo.OnLine` with
`HilbertIncidence.OnLine` inside the axiom hierarchy.
-/
class TarskiGeometryBaseBridge (Geo : Geometry.Geo)
    [HilbertIncidence Geo] : Prop where
  collinear_iff :
    ∀ A B C : Geo.Point,
      Collinear Geo A B C ↔
      TarskiCollinear Geo A B C

variable [HilbertIncidence Geo]
variable [TarskiGeometryBaseBridge Geo]

theorem collinear_of_tarski
    (A B C : Geo.Point) :
    TarskiCollinear Geo A B C →
    Collinear Geo A B C := by
  exact
    (TarskiGeometryBaseBridge.collinear_iff
      (Geo := Geo) A B C).mpr

theorem tarski_collinear_of_geometry
    (A B C : Geo.Point) :
    Collinear Geo A B C →
    TarskiCollinear Geo A B C := by
  exact
    (TarskiGeometryBaseBridge.collinear_iff
      (Geo := Geo) A B C).mp

theorem midpoint_of_tarski
    (M A B : Geo.Point) :
    TarskiIsMidpoint Geo M A B →
    IsMidpoint Geo M A B := by
  intro h
  constructor
  · exact collinear_of_tarski Geo A M B (Or.inl h.left)
  · exact h.right

omit [TarskiGeometryBaseBridge Geo] in
theorem tarski_midpoint_of_geometry_between
    (M A B : Geo.Point)
    (hBetween : Geo.Between A M B) :
    IsMidpoint Geo M A B →
    TarskiIsMidpoint Geo M A B := by
  intro h
  exact ⟨hBetween, h.right⟩

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

omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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

/-
Derived endpoint reversal for segment congruence.

Mathematically:
  AB == CD -> BA == DC.

This theorem is entirely internal to Tarski neutral geometry.
It does not use Hilbert incidence, the compatibility bridge,
or decidable equality of points.

It is derived from:
  - Ax.1: endpoint reversal for congruence,
  - Ax.2: transitivity for congruence,
  - derived symmetry of segment congruence.

From AB == CD, symmetry gives CD == AB, while Ax.1 gives
CD == DC. Ax.2 therefore yields AB == DC.
Together with AB == BA from Ax.1, another application of
Ax.2 yields BA == DC.
-/
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
theorem tarski_congruent_reverse_both
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABCD : Geo.Congruent A B C D) :
    Geo.Congruent B A D C := by

  have hCDAB : Geo.Congruent C D A B :=
    tarski_congruent_symmetry
      (Geo := Geo) A B C D hABCD

  have hCDDC : Geo.Congruent C D D C :=
    TarskiNeutral.congruent_reversal
      (Geo := Geo) C D

  have hABDC : Geo.Congruent A B D C :=
    TarskiNeutral.congruent_transitivity
      (Geo := Geo)
      C D A B D C
      hCDAB hCDDC

  have hABBA : Geo.Congruent A B B A :=
    TarskiNeutral.congruent_reversal
      (Geo := Geo) A B

  exact TarskiNeutral.congruent_transitivity
    (Geo := Geo)
    A B B A D C
    hABBA hABDC

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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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
omit [HilbertIncidence Geo] [TarskiGeometryBaseBridge Geo] in
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

end Tarski

end Geometry

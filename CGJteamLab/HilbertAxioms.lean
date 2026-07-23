import CGJteamLab.GeometryCore

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

class HilbertIncidence where
  OnLine :
    Geo.Point → Geo.Line → Prop

def PrimCollinear
    [H : HilbertIncidence Geo]
    (A B C : Geo.Point) : Prop :=
  ∃ l : Geo.Line,
    H.OnLine A l ∧
    H.OnLine B l ∧
    H.OnLine C l

theorem PrimCollinearRotate
    [H : HilbertIncidence Geo]
    (A B C : Geo.Point) :
    PrimCollinear Geo A B C →
    PrimCollinear Geo A C B := by
  intro h
  rcases h with ⟨l, hA, hB, hC⟩
  exact ⟨l, hA, hC, hB⟩

theorem PrimCollinearSwap
    [H : HilbertIncidence Geo]
    (A B C : Geo.Point) :
    PrimCollinear Geo A B C →
    PrimCollinear Geo B A C := by
  intro h
  rcases h with ⟨l, hA, hB, hC⟩
  exact ⟨l, hB, hA, hC⟩

theorem PrimCollinearCycle
    [H : HilbertIncidence Geo]
    (A B C : Geo.Point) :
    PrimCollinear Geo A B C →
    PrimCollinear Geo B C A := by
  intro h
  rcases h with ⟨l, hA, hB, hC⟩
  exact ⟨l, hB, hC, hA⟩


theorem PrimCollinear.mk
    [H : HilbertIncidence Geo]
    {A B C : Geo.Point}
    {l : Geo.Line}
    (hA : H.OnLine A l)
    (hB : H.OnLine B l)
    (hC : H.OnLine C l) :
    PrimCollinear Geo A B C :=
by
  exact ⟨l, hA, hB, hC⟩
theorem PrimCollinear.exists_line
    [H : HilbertIncidence Geo]
    {A B C : Geo.Point}
    (h : PrimCollinear Geo A B C) :
    ∃ l : Geo.Line,
      H.OnLine A l ∧
      H.OnLine B l ∧
      H.OnLine C l :=
by
  simpa [PrimCollinear] using h

theorem PrimCollinearSymm
    [H : HilbertIncidence Geo]
    (A B C : Geo.Point) :
    PrimCollinear Geo A B C →
    PrimCollinear Geo C B A := by
  intro h
  rcases h with ⟨l, hA, hB, hC⟩
  exact ⟨l, hC, hB, hA⟩

/-!
# Hilbert's plane axiom hierarchy

The following classes formalize the plane part of the five axiom groups
from the second English edition of Hilbert's *Foundations of Geometry*.
They preserve the small `HilbertIncidence` interface used by the existing
library and add stronger layers without changing `GeometryCore`.
The field documentation retains Hilbert's original group numbering.

The present `Geometry.Geo` has points and lines but no type of planes.
Consequently, the space incidence axioms I, 4-8 are intentionally not
encoded here. Axiom V, 2 is also deferred: Hilbert's line-completeness
axiom is a maximality statement about extensions of an entire ordered
congruence structure and requires a separate model-theoretic interface.
-/

/-- Two Hilbert lines meet when they have a common point. -/
def HilbertLinesMeet
    [H : HilbertIncidence Geo]
    (l m : Geo.Line) : Prop :=
  ∃ P : Geo.Point, H.OnLine P l ∧ H.OnLine P m

/-- Two Hilbert lines are disjoint when they have no common point. -/
def HilbertLinesDisjoint
    [HilbertIncidence Geo]
    (l m : Geo.Line) : Prop :=
  ¬ HilbertLinesMeet Geo l m

/--
`P` and `Q` lie on the same ray from `O`. Betweenness is the primitive
relation inherited from `GeometryCore`.
-/
def HilbertSameRay (O P Q : Geo.Point) : Prop :=
  P ≠ O ∧
  Q ≠ O ∧
  (P = Q ∨ Geo.Between O P Q ∨ Geo.Between O Q P)

/-- The open segment `AB` meets the line `l`. -/
def HilbertSegmentMeetsLine
    [H : HilbertIncidence Geo]
    (A B : Geo.Point)
    (l : Geo.Line) : Prop :=
  ∃ X : Geo.Point, Geo.Between A X B ∧ H.OnLine X l

/--
Two points are on the same side of a line when neither lies on the line
and their open connecting segment does not meet it.
-/
def HilbertSameSide
    [H : HilbertIncidence Geo]
    (P Q : Geo.Point)
    (l : Geo.Line) : Prop :=
  ¬ H.OnLine P l ∧
  ¬ H.OnLine Q l ∧
  ¬ HilbertSegmentMeetsLine Geo P Q l

/--
Group I, axioms I, 1-3 for plane incidence.

The distinctness assumptions make explicit Hilbert's convention that
letters denoting two or more points or lines denote distinct objects.
-/
class HilbertPlaneIncidence (Geo : Geometry.Geo)
    [HilbertIncidence Geo] : Prop where
  /-- I, 1: two distinct points lie on a line. -/
  line_through :
    ∀ A B : Geo.Point,
      A ≠ B →
      ∃ l : Geo.Line,
        HilbertIncidence.OnLine A l ∧
        HilbertIncidence.OnLine B l

  /-- I, 2: two distinct points determine at most one line. -/
  line_unique :
    ∀ A B : Geo.Point,
      A ≠ B →
      ∀ l m : Geo.Line,
        HilbertIncidence.OnLine A l →
        HilbertIncidence.OnLine B l →
        HilbertIncidence.OnLine A m →
        HilbertIncidence.OnLine B m →
        l = m

  /-- First clause of I, 3: two distinct points exist on a line. -/
  two_points_on_line :
    ∃ l : Geo.Line,
      ∃ A B : Geo.Point,
        A ≠ B ∧
        HilbertIncidence.OnLine A l ∧
        HilbertIncidence.OnLine B l

  /-- Second clause of I, 3: three noncollinear points exist. -/
  three_noncollinear :
    ∃ A B C : Geo.Point,
      ¬ PrimCollinear Geo A B C

/-- Group II, axioms II, 1-4 of order. -/
class HilbertOrder (Geo : Geometry.Geo)
    [HilbertIncidence Geo] : Prop
    extends HilbertPlaneIncidence Geo where
  /--
  II, 1: betweenness implies three distinct collinear points and is
  symmetric in the endpoints.
  -/
  between_incidence :
    ∀ A B C : Geo.Point,
      Geo.Between A B C →
      A ≠ B ∧
      B ≠ C ∧
      A ≠ C ∧
      PrimCollinear Geo A B C ∧
      Geo.Between C B A

  /-- II, 2: a segment can be extended beyond either endpoint. -/
  between_extension :
    ∀ A C : Geo.Point,
      A ≠ C →
      ∃ B : Geo.Point,
        Geo.Between A C B

  /--
  II, 3: among three collinear points, no more than one lies between
  the other two.
  -/
  between_unique :
    ∀ A B C : Geo.Point,
      PrimCollinear Geo A B C →
      Geo.Between A B C →
      ¬ Geo.Between B A C ∧
      ¬ Geo.Between A C B

  /--
  II, 4: Pasch's plane axiom. A line entering a triangle through one
  side leaves it through one of the other two sides.
  -/
  pasch :
    ∀ A B C : Geo.Point,
      ¬ PrimCollinear Geo A B C →
      ∀ l : Geo.Line,
        ¬ HilbertIncidence.OnLine A l →
        ¬ HilbertIncidence.OnLine B l →
        ¬ HilbertIncidence.OnLine C l →
        HilbertSegmentMeetsLine Geo A B l →
        HilbertSegmentMeetsLine Geo A C l ∨
        HilbertSegmentMeetsLine Geo B C l

/-- Group III, axioms III, 1-5 of congruence. -/
class HilbertCongruence (Geo : Geometry.Geo)
    [HilbertIncidence Geo] : Prop
    extends HilbertOrder Geo where
  /-- III, 1: a segment can be laid off on a prescribed ray. -/
  segment_construction :
    ∀ A B O R : Geo.Point,
      O ≠ R →
      ∃ X : Geo.Point,
        HilbertSameRay Geo O R X ∧
        Geo.Congruent O X A B

  /--
  III, 2: two segments congruent to the same segment are congruent to
  each other.
  -/
  segment_congruence_common :
    ∀ A B A' B' A'' B'' : Geo.Point,
      Geo.Congruent A B A' B' →
      Geo.Congruent A B A'' B'' →
      Geo.Congruent A' B' A'' B''

  /-- III, 3: additivity of adjacent congruent segments. -/
  segment_additivity :
    ∀ A B C A' B' C' : Geo.Point,
      Geo.Between A B C →
      Geo.Between A' B' C' →
      Geo.Congruent A B A' B' →
      Geo.Congruent B C B' C' →
      Geo.Congruent A C A' C'

  /--
  III, 4: an angle can be constructed uniquely on a prescribed side
  of a prescribed ray. Uniqueness is uniqueness of the resulting ray.
  -/
  angle_construction :
    ∀ A B C A' B' S : Geo.Point,
      ¬ PrimCollinear Geo A B C →
      A' ≠ B' →
      ∀ l : Geo.Line,
        HilbertIncidence.OnLine A' l →
        HilbertIncidence.OnLine B' l →
        ¬ HilbertIncidence.OnLine S l →
        ∃ C' : Geo.Point,
          HilbertSameSide Geo C' S l ∧
          Geo.AngleCongruent A B C A' B' C' ∧
          ∀ D' : Geo.Point,
            HilbertSameSide Geo D' S l →
            Geo.AngleCongruent A B C A' B' D' →
            HilbertSameRay Geo B' C' D'

  /--
  III, 5: Hilbert's SAS axiom, stated in its original angle-conclusion
  form.
  -/
  sas :
    ∀ A B C A' B' C' : Geo.Point,
      ¬ PrimCollinear Geo A B C →
      ¬ PrimCollinear Geo A' B' C' →
      Geo.Congruent A B A' B' →
      Geo.Congruent A C A' C' →
      Geo.AngleCongruent B A C B' A' C' →
      Geo.AngleCongruent A B C A' B' C'

theorem hilbert_congruent_reflexive
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B : Geo.Point) :
    Geo.Congruent A B A B := by
  rcases HilbertPlaneIncidence.two_points_on_line (Geo := Geo) with
    ⟨_, O, R, hOR, _, _⟩
  rcases HilbertCongruence.segment_construction
      (Geo := Geo) A B O R hOR with
    ⟨X, _, hX⟩
  exact
    HilbertCongruence.segment_congruence_common
      (Geo := Geo) O X A B A B hX hX

theorem hilbert_congruent_symmetry
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent C D A B := by
  intro h
  exact
    HilbertCongruence.segment_congruence_common
      (Geo := Geo) A B C D A B h
      (hilbert_congruent_reflexive Geo A B)

theorem hilbert_congruent_transitivity
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point) :
    Geo.Congruent A B C D →
    Geo.Congruent C D E F →
    Geo.Congruent A B E F := by
  intro h₁ h₂
  exact
    HilbertCongruence.segment_congruence_common
      (Geo := Geo) C D A B E F
      (hilbert_congruent_symmetry Geo A B C D h₁)
      h₂

/-- Group IV, Hilbert's Euclidean axiom of parallels. -/
class HilbertEuclideanPlane (Geo : Geometry.Geo)
    [HilbertIncidence Geo] : Prop
    extends HilbertCongruence Geo where
  /--
  IV: through a point outside a line there is at most one line disjoint
  from the given line.
  -/
  parallel_unique :
    ∀ l : Geo.Line,
      ∀ A : Geo.Point,
        ¬ HilbertIncidence.OnLine A l →
        ∀ b c : Geo.Line,
          HilbertIncidence.OnLine A b →
          HilbertLinesDisjoint Geo b l →
          HilbertIncidence.OnLine A c →
          HilbertLinesDisjoint Geo c l →
          b = c

/--
A finite chain of copies of segment `CD`, beginning at `A`, along the
ray from `A` through `B`.
-/
def HilbertSegmentChain
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point)
    (n : Nat)
    (P : Fin (n + 2) → Geo.Point) : Prop :=
  P 0 = A ∧
  (∀ i : Fin (n + 1),
    Geo.Congruent (P i.castSucc) (P i.succ) C D) ∧
  (∀ i : Fin (n + 1),
    HilbertSameRay Geo A B (P i.succ))

/--
Group V, axiom V, 1: Hilbert's Archimedean axiom.

V, 2 (line completeness) is deliberately not folded into this class;
it requires a separate notion of extensions of ordered congruence
structures.
-/
class HilbertArchimedeanPlane (Geo : Geometry.Geo)
    [HilbertIncidence Geo] : Prop
    extends HilbertEuclideanPlane Geo where
  archimedes :
    ∀ A B C D : Geo.Point,
      A ≠ B →
      C ≠ D →
      ∃ n : Nat,
      ∃ P : Fin (n + 2) → Geo.Point,
        HilbertSegmentChain Geo A B C D n P ∧
        Geo.Between A B (P (Fin.last (n + 1)))

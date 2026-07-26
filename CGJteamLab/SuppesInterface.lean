--import CGJteamLab.HilbertInterface
import CGJteamLab.SuppesAxioms

namespace Geometry

namespace Suppes

section Suppes

variable
  {R : Type*}
  {V : Type*}
  {Point : Type*}

  [Ring R]
  [Invertible (2 : R)]
  [AddCommGroup V]
  [Module R V]
  [AddTorsor V Point]

variable [SuppesGeometry Point]

local notation "Mid" =>
  SuppesGeometry.operation_midpoint

local notation "Col" =>
  SuppesGeometry.Collinear

/-- Primitive notion of triangle. -/
def PrimTriangle (A B C : Point) : Prop :=
  ¬ Col A B C

/--
Primitive notion of parallelogram (Suppes).

P(A,B,C,D) iff T(A,B,C) and Midpoint(A,C) = Midpoint(B,D).
-/
def PrimParallelogram (A B C D : Point) : Prop :=
  PrimTriangle A B C ∧
  Mid A C = Mid B D

/-!
# Suppes Theorems

Elementary theorems derived from the quantifier-free axioms of
Patrick Suppes' constructive affine geometry.

This file contains only derived results.
The axioms are defined in `SuppesAxioms.lean`.
-/

/-- Algebraic part of Suppes' Theorem 11. -/
theorem midpoint_left_distrib
    (A B C : Point) :
    Mid A (Mid B C)
      =
    Mid (Mid A B) (Mid A C) := by
  conv_lhs =>
    rw [← midpoint_idempotent A]
  simpa using midpoint_bicommutative A A B C

/-- Geometric part of Suppes' Theorem 11. -/
theorem midpoint_triangle
    (A B C : Point)
    (h : PrimTriangle A B C) :
    PrimTriangle
      (Mid A B)
      (Mid B C)
      (Mid A C) := by
  intro hcol
  apply h
  exact LL A B C hcol

/-- Suppes, Theorem 3. -/
theorem midpoint_fixed
    (A B : Point)
    (h : Mid A B = A) :
    A = B := by
  have hBA : B = A := by
    apply midpoint_cancellation A B A
    calc
      Mid A B = A := h
      _ = Mid A A := by
        symm
        exact midpoint_idempotent A
  exact hBA.symm

/-- Suppes, Theorem 4 (Reduction). -/
local notation "Dbl" =>
  SuppesGeometry.operation_double

/-- Suppes' Theorem 4 (Reduction). -/
theorem doubling_reduction
    (A B : Point) :
    Dbl A (Mid A B) = B := by
  apply midpoint_cancellation A (Dbl A (Mid A B)) B
  calc
    Mid A (Dbl A (Mid A B))
        = Mid A B := by
          exact midpoint_double_reduction A (Mid A B)

/- Suppes' Theorem 5. -/
/-- Suppes' Theorem 5. -/
theorem parallelogram_not_crossed
    (A B C D : Point) :
    PrimParallelogram A B C D →
    ¬ PrimParallelogram A C B D := by
  intro hP hCross

  rcases hP with ⟨hTri, hAC⟩
  rcases hCross with ⟨_, hAB⟩

  have h3 :
      Mid (Mid A B) (Mid C D) =
      Mid (Mid A C) (Mid B D) := by
    exact midpoint_bicommutative A B C D

  have h4 :
      Mid A B = Mid A C := by
    calc
      Mid A B
          = Mid (Mid A B) (Mid A B) := by
              symm
              exact midpoint_idempotent (Mid A B)
      _ = Mid (Mid A B) (Mid C D) := by
              rw [hAB]
      _ = Mid (Mid A C) (Mid B D) := by
              exact h3
      _ = Mid (Mid A C) (Mid A C) := by
              rw [hAC]
      _ = Mid A C := by
              exact midpoint_idempotent (Mid A C)

  have hBC : B = C := by
    exact midpoint_cancellation A B C h4

  have hCol : Col A B C := by
    apply L2
    exact Or.inr (Or.inr hBC)

  exact hTri hCol


theorem MidpointParallelogram
    (A B C : Point)
    (h : PrimTriangle A B C) :
    PrimParallelogram
      (Mid A B)
      (Mid B C)
      (Mid A C)
      A := by
  constructor
  ·
    exact midpoint_triangle A B C h
  ·
    calc
      Mid (Mid A B) (Mid A C)
          = Mid A (Mid B C) := by
              symm
              exact midpoint_left_distrib A B C
      _ = Mid (Mid B C) A := by
              exact midpoint_commutative _ _

/-! Collinearity is invariant under permutations of points on a nontrivial line. -/
private theorem collinear_swap_last_aux
    {A B P : Point}
    (hAB : A ≠ B)
    (h : Col A B P) :
    Col A P B := by
  have hA : Col A B A := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hB : Col A B B := by
    apply L2
    exact Or.inr (Or.inr rfl)
  exact L3 A B A P B hAB hA h hB

private theorem collinear_swap_first_aux
    {A B P : Point}
    (hAB : A ≠ B)
    (h : Col A B P) :
    Col B A P := by
  have hA : Col A B A := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hB : Col A B B := by
    apply L2
    exact Or.inr (Or.inr rfl)
  exact L3 A B B A P hAB hB hA h

/-- The triangle part of the third cyclic permutation of a parallelogram. -/
theorem rotate_triangle
    {A B C D : Point} :
    PrimTriangle A B C →
    Mid A C = Mid B D →
    PrimTriangle D A B := by
  intro hTri hMid hDAB

  have hAB : A ≠ B := by
    intro hAB
    apply hTri
    apply L2
    exact Or.inl hAB

  have hAC : A ≠ C := by
    intro hAC
    apply hTri
    apply L2
    exact Or.inr (Or.inl hAC)

  have hDA : D ≠ A := by
    intro hDA
    have hMid' : Mid A C = Mid A B := by
      calc
        Mid A C = Mid B D := hMid
        _ = Mid B A := by rw [hDA]
        _ = Mid A B := midpoint_commutative B A
    have hCB : C = B := midpoint_cancellation A C B hMid'
    apply hTri
    apply L2
    exact Or.inr (Or.inr hCB.symm)

  have hDB : D ≠ B := by
    intro hDB
    have hMid' : Mid A C = B := by
      calc
        Mid A C = Mid B D := hMid
        _ = Mid B B := by rw [hDB]
        _ = B := midpoint_idempotent B
    have hACB : Col A C B := by
      rw [← hMid']
      exact midpoint_collinear A C
    apply hTri
    exact collinear_swap_last_aux hAC hACB

  have hDBA : Col D B A :=
    collinear_swap_last_aux hDA hDAB
  have hBDM : Col B D (Mid A C) := by
    rw [hMid]
    exact midpoint_collinear B D
  have hDBM : Col D B (Mid A C) :=
    collinear_swap_first_aux hDB.symm hBDM
  have hDBD : Col D B D := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hDAM : Col D A (Mid A C) :=
    L3 D B D A (Mid A C) hDB hDBD hDBA hDBM

  have hAD : A ≠ D := Ne.symm hDA
  have hADA : Col A D A := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hADB : Col A D B :=
    collinear_swap_first_aux hDA hDAB
  have hADM : Col A D (Mid A C) :=
    collinear_swap_first_aux hDA hDAM
  have hABM : Col A B (Mid A C) :=
    L3 A D A B (Mid A C) hAD hADA hADB hADM

  have hAMC : Col A (Mid A C) C :=
    collinear_swap_last_aux hAC (midpoint_collinear A C)
  have hAM : A ≠ Mid A C := by
    intro hAM
    have hAC' : A = C := midpoint_fixed A C hAM.symm
    apply hTri
    apply L2
    exact Or.inr (Or.inl hAC')
  have hAMA : Col A (Mid A C) A := by
    apply L2
    exact Or.inr (Or.inl rfl)
  have hAMB : Col A (Mid A C) B :=
    collinear_swap_last_aux hAB hABM
  exact hTri (L3 A (Mid A C) A B C hAM hAMA hAMB hAMC)

theorem parallelogram_rotate3
    {A B C D : Point} :
    PrimParallelogram A B C D →
    PrimParallelogram D A B C := by
  intro h
  rcases h with ⟨hTri, hMid⟩

  constructor
  ·
    exact rotate_triangle hTri hMid
  ·
    simpa [midpoint_commutative] using hMid.symm

/-!
## Reverse engineering of Suppes' Theorem 9
-/
/-
In a primitive parallelogram the fourth vertex cannot coincide
with the first one.

This is the first contradiction used in Suppes' proof of
Theorem 9.
-/

/-
Triangle formed by one vertex and the adjacent midpoints.

This is the analogue of Suppes' Theorem 8.
-/

/--
Suppes, Theorem 1(i): swapping the first two points
preserves collinearity.
-/

theorem collinear_swap
    {A B C : Point} :
    SuppesGeometry.Collinear A B C ->
    SuppesGeometry.Collinear B A C := by
  intro hABC
  by_cases hAB : A = B
  · simpa [hAB] using hABC
  · apply L3 A B B A C
    · exact hAB
    · apply L2
      exact Or.inr (Or.inr rfl)
    · apply L2
      exact Or.inr (Or.inl rfl)
    · exact hABC

theorem theorem11
    (A B C : Point)
    (h : PrimTriangle A B C) :
    PrimParallelogram
      A
      (Mid A B)
      (Mid B C)
      (Mid A C) := by
  have hPar :
      PrimParallelogram
        (Mid A B)
        (Mid B C)
        (Mid A C)
        A :=
    MidpointParallelogram A B C h

  exact parallelogram_rotate3 hPar

/-!
## Parallel segments

Suppes, Definition 3.
-/

/--
Suppes' primitive definition of parallel segments.

The segment AB is parallel to CD iff:
1. A, B, C form a triangle,
2. C and D are distinct,
3. A, B, Dbl A (Mid B D), D form a primitive parallelogram,
4. C, Dbl A (Mid B D), D are collinear.
-/

/-
Cyclic permutation of a primitive triangle.
Derived from Theorem 1(i) for collinearity.
-/


def SuppesParallel (A B C D : Point) : Prop :=
  PrimTriangle A B C ∧
  C ≠ D ∧
  PrimParallelogram A B (Dbl A (Mid B D)) D ∧
  Col C (Dbl A (Mid B D)) D




/--
Suppes, Theorem 1(i): cyclic permutation of collinearity.
-/

theorem collinear_rotate
    {A B C : Point} :
    Col A B C -> Col B C A := by
  intro hABC
  by_cases hAB : A = B
  · apply L2
    exact Or.inr (Or.inl hAB.symm)
  · apply L3 A B B C A
    · exact hAB
    · apply L2
      exact Or.inr (Or.inr rfl)
    · exact hABC
    · apply L2
      exact Or.inr (Or.inl rfl)

/-
Cyclic permutation of a primitive triangle.
-/
theorem triangle_rotate
    {A B C : Point} :
    PrimTriangle A B C -> PrimTriangle B C A := by
  intro hT
  unfold PrimTriangle at hT ⊢
  intro hBCA
  apply hT
  exact collinear_rotate (collinear_rotate hBCA)

theorem parallelogram_construct
    (A B C : Point)
    (hT : PrimTriangle A B C) :
    PrimParallelogram
      C A B
      (Dbl A (Mid B C)) := by
  unfold PrimParallelogram
  constructor
  · exact triangle_rotate (triangle_rotate hT)
  · calc
      Mid C B = Mid B C :=
        midpoint_commutative C B
      _ = Mid A (Dbl A (Mid B C)) :=
        (midpoint_double_reduction A (Mid B C)).symm

theorem parallelogram_parallel_second
    (A B C D : Point)
    (hP : PrimParallelogram A B C D) :
    SuppesParallel B C A D := by

  unfold SuppesParallel

  refine ⟨triangle_rotate hP.1, ?_, ?_, ?_⟩

  · -- A ≠ D
    intro hAD
    have hT : PrimTriangle D A B :=
      (parallelogram_rotate3 hP).1
    apply hT
    apply L2
    exact Or.inl hAD.symm

  · -- PrimParallelogram B C (Dbl B (Mid C D)) D
    unfold PrimParallelogram
    constructor

    · -- triangularity
      have hBCD : PrimTriangle B C D :=
        (parallelogram_rotate3
          (parallelogram_rotate3
            (parallelogram_rotate3 hP))).1

      have hConstruct :=
        parallelogram_construct B C D hBCD

      have hRot :=
        parallelogram_rotate3
          (parallelogram_rotate3
            (parallelogram_rotate3 hConstruct))

      exact hRot.1

    · exact midpoint_double_reduction B (Mid C D)

  · let X : Point := Dbl B (Mid C D)
    change Col A X D

    have hBX : Mid B X = Mid C D := by
      dsimp [X]
      exact midpoint_double_reduction B (Mid C D)

    have hAXmid : Mid A X = D := by
      apply midpoint_cancellation (Mid B C) (Mid A X) D
      calc
        Mid (Mid B C) (Mid A X)
            = Mid (Mid A X) (Mid B C) := by
                exact midpoint_commutative _ _
        _ = Mid (Mid A B) (Mid X C) := by
                exact midpoint_bicommutative A X B C
        _ = Mid (Mid A B) (Mid C X) := by
                rw [midpoint_commutative X C]
        _ = Mid (Mid A C) (Mid B X) := by
                exact midpoint_bicommutative A B C X
        _ = Mid (Mid B D) (Mid C D) := by
                rw [hP.2, hBX]
        _ = Mid (Mid B C) (Mid D D) := by
                exact midpoint_bicommutative B D C D
        _ = Mid (Mid B C) D := by
                rw [midpoint_idempotent D]

    have hX : X = Dbl A D := by
      apply midpoint_cancellation A X (Dbl A D)
      calc
        Mid A X = D := hAXmid
        _ = Mid A (Dbl A D) := by
              symm
              exact midpoint_double_reduction A D

    rw [hX]

    have hCol :
        Col A (Dbl A D) (Mid A (Dbl A D)) :=
      midpoint_collinear A (Dbl A D)

    rw [midpoint_double_reduction A D] at hCol
    exact hCol

/--
Suppes, Theorem 12.

If P(a,b,c,d), P(c,d,e,f), T(a,b,e), and T(a,b,f),
then P(a,b,f,e).

This is the constructive affine analogue of a local
transitivity property for parallelograms.
-/

theorem parallelogram_transitive
    (a b c d e f : Point)
    (hP1 : PrimParallelogram a b c d)
    (hP2 : PrimParallelogram c d e f)
    (_hTabe : PrimTriangle a b e)
    (hTabf : PrimTriangle a b f) :
    PrimParallelogram a b f e := by


  unfold PrimParallelogram at hP1 hP2 ⊢

  constructor

  · exact hTabf
  · have h1 :
        Mid a c = Mid b d :=
      hP1.2

    have h2 :
        Mid c e = Mid d f :=
      hP2.2

    apply midpoint_cancellation
      (Mid c d)
      (Mid a f)
      (Mid b e)

    calc
      Mid (Mid c d) (Mid a f)
          = Mid (Mid c a) (Mid d f) := by
              exact midpoint_bicommutative c d a f

      _ = Mid (Mid a c) (Mid d f) := by
              rw [midpoint_commutative c a]

           _ = Mid (Mid b d) (Mid c e) := by
              rw [h1, h2]

      _ = Mid (Mid b c) (Mid d e) := by
              exact midpoint_bicommutative b d c e

      _ = Mid (Mid c b) (Mid d e) := by
              rw [midpoint_commutative b c]

      _ = Mid (Mid c d) (Mid b e) := by
              exact midpoint_bicommutative c b d e


/--
Suppes, Theorem 16(iii).

If ab || pq, ab || rs, and T(p,q,r), then pq || rs.
-/
theorem parallel_transitive
    (a b p q r s : Point)
    (hPQ : SuppesParallel a b p q)
    (hRS : SuppesParallel a b r s)
    (hTpqr : PrimTriangle p q r) :
    SuppesParallel p q r s := by

  unfold SuppesParallel at hPQ hRS ⊢

  rcases hPQ with
    ⟨hTabp, hpq, hP1, hCol1⟩

  rcases hRS with
    ⟨hTabr, hrs, hP2, hCol2⟩

  refine ⟨hTpqr, hrs, ?_, ?_⟩

  · -- Suppes Theorem 16(iii): parallelogram part
    sorry

  · -- Suppes Theorem 16(iii): collinearity part
    sorry


 end Suppes


end Suppes

end Geometry

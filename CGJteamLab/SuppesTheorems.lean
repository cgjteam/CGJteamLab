import CGJteamLab.SuppesCore

namespace Geometry

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

axiom parallelogram_rotate3
    (A B C D : Point) :
    PrimParallelogram A B C D →
    PrimParallelogram D A B C

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

  exact parallelogram_rotate3
    (Mid A B)
    (Mid B C)
    (Mid A C)
    A
    hPar

end Suppes

end Geometry

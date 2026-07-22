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
/--
In a primitive parallelogram the fourth vertex cannot coincide
with the first one.

This is the first contradiction used in Suppes' proof of
Theorem 9.
-/

/-
Triangle formed by one vertex and the adjacent midpoints.

This is the analogue of Suppes' Theorem 8.
-/




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

end Suppes

end Geometry

import CGJteamLab.SuppesAxioms

/-
# SuppesCore

Core language for Patrick Suppes'
Quantifier-Free Axioms for Constructive Affine Plane Geometry.
-/

namespace Geometry

section Suppes

variable
  {Point : Type*}
  [SuppesGeometry Point]

local notation "Mid" =>
  SuppesGeometry.operation_midpoint

local notation "Col" =>
  SuppesGeometry.Collinear

/-- Primitive notion of triangle. -/
def PrimTriangle (A B C : Point) : Prop :=
  ¬ Col A B C

/--
Primitive notion of parallelogram (Suppes).

P(A,B,C,D) iff
  T(A,B,C) and
  Midpoint(A,C) = Midpoint(B,D).
-/
def PrimParallelogram (A B C D : Point) : Prop :=
  PrimTriangle A B C ∧
  Mid A C = Mid B D

end Suppes

end Geometry

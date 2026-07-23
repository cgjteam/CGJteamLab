import CGJteamLab.GeometryCore
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

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

/-- Primitive operations of Suppes' constructive affine geometry. -/
class SuppesGeometry (Point : Type*) where
  /-- Midpoint operation. -/
  operation_midpoint : Point → Point → Point

  /-- Doubling operation. -/
  operation_double : Point → Point → Point

  /-- Primitive collinearity relation. -/
  Collinear : Point → Point → Point → Prop

open SuppesGeometry

variable [SuppesGeometry Point]

local notation "Mid" => operation_midpoint
local notation "Dbl" => operation_double
local notation "Col" => Collinear

/-!
## Linearity axioms (L)
-/

/-- (L2) Trivial collinearity. -/
axiom L2
    (A B C : Point) :
    A = B ∨ A = C ∨ B = C →
    Col A B C

/-- (L3) Collinearity transitivity. -/
axiom L3
    (A B P Q R : Point) :
    A ≠ B →
    Col A B P →
    Col A B Q →
    Col A B R →
    Col P Q R

/-- (B1) Midpoint idempotency. -/
axiom midpoint_idempotent
    (A : Point) :
    Mid A A = A

/-- (B2) Midpoint commutativity. -/
axiom midpoint_commutative
    (A B : Point) :
    Mid A B = Mid B A

/-- (B3) Midpoint bicommutativity. -/
axiom midpoint_bicommutative
    (A B C D : Point) :
    Mid (Mid A B) (Mid C D)
      =
    Mid (Mid A C) (Mid B D)

/-- (B4) Midpoint cancellation. -/
axiom midpoint_cancellation
    (A B C : Point) :
    Mid A B = Mid A C →
    B = C

/-!
## Doubling axioms (D)
-/

/-- (D1) Doubling antisymmetry. -/
axiom doubling_antisymmetry
    (A B : Point) :
    Dbl A B = Dbl B A →
    A = B

/-- (D2) Left cancellation for doubling. -/
axiom doubling_left_cancellation
    (A B C : Point) :
    Dbl A B = Dbl A C →
    B = C

/-- (D3) Right cancellation for doubling. -/
axiom doubling_right_cancellation
    (A B C : Point) :
    Dbl A C = Dbl B C →
    A = B

/-- (BD) Midpoint-double reduction. -/
axiom midpoint_double_reduction
    (A B : Point) :
    Mid A (Dbl A B) = B

/-- (LB) Midpoint collinearity. -/
axiom midpoint_collinear
    (A B : Point) :
    Col A B (Mid A B)

/-- (LL) Midpoint lifting of collinearity. -/
axiom LL
    (A B C : Point) :
    Col
      (Mid A B)
      (Mid B C)
      (Mid A C)
    →
    Col A B C

attribute [simp] midpoint_idempotent
attribute [simp] midpoint_commutative

end Suppes

end Suppes

end Geometry

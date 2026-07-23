import CGJteamLab.GeometryBase
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

theorem tarski_midpoint_of_geometry_between
    (M A B : Geo.Point)
    (hBetween : Geo.Between A M B) :
    IsMidpoint Geo M A B →
    TarskiIsMidpoint Geo M A B := by
  intro h
  exact ⟨hBetween, h.right⟩

end Tarski

end Geometry

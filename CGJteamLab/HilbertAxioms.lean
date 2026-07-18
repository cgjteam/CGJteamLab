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

/-
class IncidenceAxioms
    (Geo : Geometry.Geo)
    [HilbertIncidence Geo] where

  line_through :
    ∀ A B : Geo.Point,
      ∃ l : Geo.Line,
        HilbertIncidence.OnLine A l ∧
        HilbertIncidence.OnLine B l


  line_unique :
    ∀ {A B : Geo.Point} {l₁ l₂ : Geo.Line},
      A ≠ B →
      HilbertIncidence.OnLine A l₁ →
      HilbertIncidence.OnLine B l₁ →
      HilbertIncidence.OnLine A l₂ →
      HilbertIncidence.OnLine B l₂ →
      l₁ = l₂

  line_has_two_points :
    ∀ l : Geo.Line,
      ∃ A B : Geo.Point,
        A ≠ B ∧
        HilbertIncidence.OnLine A l ∧
        HilbertIncidence.OnLine B l

  exists_noncollinear_points :
    ∃ A B C : Geo.Point,
      ¬ PrimCollinear Geo A B C
theorem exists_noncollinear_points
    [H : HilbertIncidence Geo]
    [I : IncidenceAxioms Geo]
    :
    ∃ A B C : Geo.Point,
      ¬ PrimCollinear Geo A B C :=
by
  exact I.exists_noncollinear_points
-/

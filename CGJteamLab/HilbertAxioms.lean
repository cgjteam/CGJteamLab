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

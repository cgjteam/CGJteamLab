import Mathlib.Data.Sym.Sym2

namespace Geometry

universe u

structure Geo where
  Point : Type u
  Line  : Type u

  OnLine :
    Point → Line → Prop

  Between :
    Point → Point → Point → Prop

  SegmentCongruent :
    Sym2 Point →
    Sym2 Point →
    Prop

  AngleCongruent :
    Point → Point → Point →
    Point → Point → Point →
    Prop

  Parallel :
    Point → Point →
    Point → Point →
    Prop

namespace Geo

/-- The unoriented segment with endpoints `A` and `B`. -/
def Segment
    (Geo : Geometry.Geo)
    (A B : Geo.Point) :
    Sym2 Geo.Point :=
  s(A, B)

/--
Congruence of the unoriented segments `AB` and `CD`.

The four-point interface is retained for compatibility with the rest of
the geometry library.
-/
def Congruent
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) : Prop :=
  Geo.SegmentCongruent (Geo.Segment A B) (Geo.Segment C D)

theorem segment_swap
    (Geo : Geometry.Geo)
    (A B : Geo.Point) :
    Geo.Segment A B = Geo.Segment B A := by
  exact Sym2.eq_swap

theorem congruent_reverse_first
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D ↔
    Geo.Congruent B A C D := by
  unfold Congruent Segment
  constructor
  · intro h
    exact (Sym2.eq_swap (a := A) (b := B)) ▸ h
  · intro h
    exact (Sym2.eq_swap (a := B) (b := A)) ▸ h

theorem congruent_reverse_second
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D ↔
    Geo.Congruent A B D C := by
  unfold Congruent Segment
  constructor
  · intro h
    exact (Sym2.eq_swap (a := C) (b := D)) ▸ h
  · intro h
    exact (Sym2.eq_swap (a := D) (b := C)) ▸ h

end Geo

end Geometry

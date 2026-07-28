import Mathlib.Data.Sym.Sym2

namespace Geometry
namespace Tarski

universe u

/--
Primitive geometric signature used by the Tarski route.
-/
structure Geo where
  Point : Type u

  Between :
    Point -> Point -> Point -> Prop

  SegmentCongruent :
    Sym2 Point ->
    Sym2 Point ->
    Prop

namespace Geo

/-- The unoriented segment with endpoints `A` and `B`. -/
def Segment
    (Geo : Tarski.Geo)
    (A B : Geo.Point) :
    Sym2 Geo.Point :=
  s(A, B)

/--
Congruence of the unoriented segments `AB` and `CD`.

The four-point interface is retained for compatibility with the rest of
the Tarski geometry library.
-/
def Congruent
    (Geo : Tarski.Geo)
    (A B C D : Geo.Point) : Prop :=
  Geo.SegmentCongruent
    (Geo.Segment A B)
    (Geo.Segment C D)

/-- Reversal of the endpoints of an unoriented segment. -/
theorem segment_swap
    (Geo : Tarski.Geo)
    (A B : Geo.Point) :
    Geo.Segment A B = Geo.Segment B A := by
  exact Sym2.eq_swap

theorem congruent_reverse_first
    (Geo : Tarski.Geo)
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D <->
    Geo.Congruent B A C D := by
  unfold Congruent Segment
  constructor
  · intro h
    exact (Sym2.eq_swap (a := A) (b := B)) ▸ h
  · intro h
    exact (Sym2.eq_swap (a := B) (b := A)) ▸ h

theorem congruent_reverse_second
    (Geo : Tarski.Geo)
    (A B C D : Geo.Point) :
    Geo.Congruent A B C D <->
    Geo.Congruent A B D C := by
  unfold Congruent Segment
  constructor
  · intro h
    exact (Sym2.eq_swap (a := C) (b := D)) ▸ h
  · intro h
    exact (Sym2.eq_swap (a := D) (b := C)) ▸ h

end Geo

end Tarski
end Geometry

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

  UnorientedAngleCongruent :
    (Point × Sym2 Point) →
    (Point × Sym2 Point) →
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

/--
The unoriented angle `ABC`, represented by its vertex `B` and the
unordered pair of points determining its two sides.
-/
def Angle
    (Geo : Geometry.Geo)
    (A B C : Geo.Point) :
    Geo.Point × Sym2 Geo.Point :=
  (B, s(A, C))

/--
Congruence of the unoriented angles `ABC` and `DEF`.

The six-point interface is retained for compatibility with the rest of
the geometry library.
-/
def AngleCongruent
    (Geo : Geometry.Geo)
    (A B C D E F : Geo.Point) : Prop :=
  Geo.UnorientedAngleCongruent
    (Geo.Angle A B C)
    (Geo.Angle D E F)

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

theorem angle_swap
    (Geo : Geometry.Geo)
    (A B C : Geo.Point) :
    Geo.Angle A B C = Geo.Angle C B A := by
  unfold Angle
  rw [Sym2.eq_swap]

theorem angle_congruent_reverse_first
    (Geo : Geometry.Geo)
    (A B C D E F : Geo.Point) :
    Geo.AngleCongruent A B C D E F ↔
    Geo.AngleCongruent C B A D E F := by
  unfold AngleCongruent
  constructor
  · intro h
    exact (Geo.angle_swap A B C) ▸ h
  · intro h
    exact (Geo.angle_swap C B A) ▸ h

theorem angle_congruent_reverse_second
    (Geo : Geometry.Geo)
    (A B C D E F : Geo.Point) :
    Geo.AngleCongruent A B C D E F ↔
    Geo.AngleCongruent A B C F E D := by
  unfold AngleCongruent
  constructor
  · intro h
    exact (Geo.angle_swap D E F) ▸ h
  · intro h
    exact (Geo.angle_swap F E D) ▸ h

end Geo

end Geometry

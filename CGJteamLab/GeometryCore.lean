import Mathlib.Data.Sym.Sym2

namespace Geometry

universe u

/--
Primitive geometric signature used by the Hilbert route.

This file contains only the carrier types and primitive relations.
No geometric axioms or derived constructions are introduced here.
-/
structure Geo where
  Point : Type u
  Line : Type u

  OnLine :
    Point -> Line -> Prop

  Between :
    Point -> Point -> Point -> Prop

  SegmentCongruent :
    Sym2 Point ->
    Sym2 Point ->
    Prop

  UnorientedAngleCongruent :
    (Point × Sym2 (Set Point)) ->
    (Point × Sym2 (Set Point)) ->
    Prop

end Geometry

namespace Geometry

universe u

structure Geo where
  Point : Type u
  Line  : Type u

  OnLine :
    Point → Line → Prop

  Between :
    Point → Point → Point → Prop

  Congruent :
    Point → Point →
    Point → Point →
    Prop

  AngleCongruent :
    Point → Point → Point →
    Point → Point → Point →
    Prop

  Parallel :
    Point → Point →
    Point → Point →
    Prop

end Geometry

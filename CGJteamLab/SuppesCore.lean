namespace Geometry

namespace Suppes

universe u

/-- Primitive operations of Suppes' constructive affine geometry. -/
class SuppesGeometry (Point : Type u) where
  /-- Midpoint operation. -/
  operation_midpoint : Point -> Point -> Point

  /-- Doubling operation. -/
  operation_double : Point -> Point -> Point

  /-- Primitive collinearity relation. -/
  Collinear : Point -> Point -> Point -> Prop

end Suppes

end Geometry

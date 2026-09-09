import CGJteamLab.Hilbert3DInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Two ambient planes are parallel in the incidence sense when they
have no common point.

This is the non-metric 3D parallel-plane notion used in the synthetic
development of Euclid Book XI.  It is intentionally independent of
the Wyler flat calculus.
-/
def HilbertSpacePlanesParallelIncidence
    [S : HilbertSpacePrimitive Geo]
    (pi rho : S.Plane) : Prop :=
  Not
    (exists X : Geo.Point,
      S.OnPlane X pi /\
      S.OnPlane X rho)

end Geometry

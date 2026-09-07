import CGJteamLab.Hilbert3DInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.3.

If two distinct planes have a common point, then their intersection is a
straight line.

The conclusion is stated extensionally: the returned line lies in both
planes, and a point belongs to both planes if and only if it lies on that
line.
-/
theorem euclid_proposition_11_3
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (hneq : Ne pi rho)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hArho : S.OnPlane A rho) :
    exists l : Geo.Line,
      H.OnLine A l /\
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo l rho /\
      forall X : Geo.Point,
        (S.OnPlane X pi /\ S.OnPlane X rho) <->
        H.OnLine X l := by

  exact
    hilbert_plane_intersection_line
      (Geo := Geo)
      pi rho hneq
      A hApi hArho

end Geometry

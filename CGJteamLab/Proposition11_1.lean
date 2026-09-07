import CGJteamLab.Hilbert3DInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.1.

If two distinct points of a straight line lie in a plane, then the whole
straight line lies in that plane.

This is the precise incidence content of Euclid's statement that a part of
a straight line cannot lie in the reference plane while another part is
"more elevated". In the present spatial Hilbert architecture this is exactly
Hilbert incidence axiom I.6, exposed through `HilbertSpaceIncidence.line_in_plane`.
-/
theorem euclid_proposition_11_1
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (l : Geo.Line)
    (A B : Geo.Point)
    (hAB : Ne A B)
    (hAl : H.OnLine A l)
    (hBl : H.OnLine B l)
    (hApi : S.OnPlane A pi)
    (hBpi : S.OnPlane B pi) :
    HilbertLineInPlane Geo l pi := by
  exact
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B hAB
      l hAl hBl
      pi hApi hBpi

end Geometry

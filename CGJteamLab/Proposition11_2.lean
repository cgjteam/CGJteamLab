import CGJteamLab.Hilbert3DInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.2, first clause.

If two distinct straight lines intersect at a point, then they lie in one
plane.

The current Hilbert 3D interface proves the stronger statement that two
distinct intersecting lines determine a unique plane. The Euclid theorem
only exposes the existence part.
-/
theorem euclid_proposition_11_2
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (P : Geo.Point)
    (hlm : Ne l m)
    (hPl : H.OnLine P l)
    (hPm : H.OnLine P m) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo m pi := by

  have h :=
    hilbert_plane_through_two_intersecting_lines
      (Geo := Geo)
      l m hlm P hPl hPm

  cases h with
  | intro pi hData =>
      exact
        Exists.intro pi
          (And.intro
            hData.1
            hData.2.1)

/--
Euclid XI.2, second clause.

Every nondegenerate triangle lies in one plane.
-/
theorem euclid_proposition_11_2_triangle
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    (A B C : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C)) :
    exists pi : S.Plane,
      S.OnPlane A pi /\
      S.OnPlane B pi /\
      S.OnPlane C pi := by

  exact
    HilbertSpaceIncidence.plane_through
      (Geo := Geo)
      A B C hABC

end Geometry

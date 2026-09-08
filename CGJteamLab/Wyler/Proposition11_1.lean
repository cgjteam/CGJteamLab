import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.1.

If two distinct points of a straight line lie in a plane, then the whole
straight line lies in that plane.

In flat language the proof is the composition

  carrier(l) subset Span{A,B} subset carrier(pi).

The two inclusions are supplied by the Wyler interface; XI.1 itself is
their geometric composition.
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

  have hLineSpan :
      Set.Subset
        (HilbertLineCarrier3D Geo l)
        (HilbertSpan3D Geo ({A, B} : Set Geo.Point)) :=
    euclid_XI1_lineCarrier_subset_pair_span
      (Geo := Geo)
      l A B
      hAB hAl hBl

  have hSpanPlane :
      Set.Subset
        (HilbertSpan3D Geo ({A, B} : Set Geo.Point))
        (HilbertPlaneCarrier3D Geo pi) :=
    euclid_XI1_pair_span_subset_plane
      (Geo := Geo)
      pi A B
      hApi hBpi

  intro X hXl

  exact
    hSpanPlane
      (hLineSpan hXl)

end Geometry

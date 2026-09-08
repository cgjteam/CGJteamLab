import CGJteamLab.Wyler.HilbertWylerInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/--
Euclid XI.2, first clause.

If two distinct straight lines intersect at a point, then they lie in one
plane.

Wyler form:

  Join(carrier(l), carrier(m)) = carrier(pi).

The Euclidean conclusion is recovered from the fact that both generators
are contained in their join.
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

  cases
      hilbertJoin3D_two_intersecting_lines_eq_planeCarrier
        (Geo := Geo)
        l m P
        hlm hPl hPm with
  | intro pi hData =>
      have hJoin :
          HilbertJoin3D Geo
              (HilbertLineCarrier3D Geo l)
              (HilbertLineCarrier3D Geo m) =
            HilbertPlaneCarrier3D Geo pi :=
        hData.2.2

      have hGenerators :=
        hilbertJoin3D_generators_subset_of_eq
          (Geo := Geo)
          (HilbertLineCarrier3D Geo l)
          (HilbertLineCarrier3D Geo m)
          (HilbertPlaneCarrier3D Geo pi)
          hJoin

      have hlpi :
          HilbertLineInPlane Geo l pi := by
        intro X hXl
        exact hGenerators.1 hXl

      have hmpi :
          HilbertLineInPlane Geo m pi := by
        intro X hXm
        exact hGenerators.2 hXm

      exact
        Exists.intro pi
          (And.intro hlpi hmpi)


/--
Euclid XI.2, second clause.

Every nondegenerate triangle lies in one plane.

Wyler form:

  Span{A,B,C} = carrier(pi).

Since A, B, and C belong to their span, they belong to pi.
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

  cases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo)
        A B C hABC with
  | intro pi hData =>
      have hApi : S.OnPlane A pi :=
        hData.1

      have hBpi : S.OnPlane B pi :=
        hData.2.1

      have hCpi : S.OnPlane C pi :=
        hData.2.2

      have hSpan :
          HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) =
            HilbertPlaneCarrier3D Geo pi :=
        hilbertSpan3D_triple_eq_planeCarrier
          (Geo := Geo)
          A B C pi
          hABC
          hApi hBpi hCpi

      have hExt :
          Set.Subset
            ({A, B, C} : Set Geo.Point)
            (HilbertSpan3D Geo ({A, B, C} : Set Geo.Point)) :=
        hilbertSpan3D_extensive
          (Geo := Geo)
          ({A, B, C} : Set Geo.Point)

      have hAspan :
          HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) A := by
        apply hExt
        simp

      have hBspan :
          HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) B := by
        apply hExt
        simp

      have hCspan :
          HilbertSpan3D Geo ({A, B, C} : Set Geo.Point) C := by
        apply hExt
        simp

      rw [hSpan] at hAspan hBspan hCspan

      exact
        Exists.intro pi
          (And.intro hAspan
            (And.intro hBspan hCspan))

end Geometry

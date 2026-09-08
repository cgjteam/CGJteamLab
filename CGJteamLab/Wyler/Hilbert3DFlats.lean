import CGJteamLab.Hilbert3DInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert 3D flats

Direct 3D development of flats over the existing Hilbert spatial
incidence structure.

This file deliberately does not use the dimension-free incidence layer.
The aim is to develop the flat calculus directly inside Hilbert 3D.
-/

/--
A Hilbert 3D flat is a set of points closed under:

1. the whole line through any two distinct points of the set;
2. the whole plane through any three noncollinear points of the set.
-/
def HilbertFlat3D
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (F : Set Geo.Point) : Prop :=
  (forall A B : Geo.Point,
      F A ->
      F B ->
      Ne A B ->
      forall l : Geo.Line,
        H.OnLine A l ->
        H.OnLine B l ->
        forall X : Geo.Point,
          H.OnLine X l ->
          F X) /\
  (forall A B C : Geo.Point,
      F A ->
      F B ->
      F C ->
      Not (PrimCollinear Geo A B C) ->
      forall pi : S.Plane,
        S.OnPlane A pi ->
        S.OnPlane B pi ->
        S.OnPlane C pi ->
        forall X : Geo.Point,
          S.OnPlane X pi ->
          F X)


/--
The 3D span of X is the intersection of all Hilbert 3D flats
containing X.
-/
def HilbertSpan3D
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X : Set Geo.Point) : Set Geo.Point :=
  fun P =>
    forall F : Set Geo.Point,
      HilbertFlat3D Geo F ->
      Set.Subset X F ->
      F P


/--
The whole space is a Hilbert 3D flat.
-/
theorem hilbertFlat3D_univ
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    HilbertFlat3D Geo (Set.univ : Set Geo.Point) := by
  constructor

  · intro A B hA hB hAB l hAl hBl X hXl
    trivial

  · intro A B C hA hB hC hABC pi hApi hBpi hCpi X hXpi
    trivial


/--
Every generator belongs to its 3D span.
-/
theorem hilbertSpan3D_extensive
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X : Set Geo.Point) :
    Set.Subset X (HilbertSpan3D Geo X) := by
  intro P hPX F hFlat hXF
  exact hXF hPX


/--
The generated span is contained in every flat containing the generators.
-/
theorem hilbertSpan3D_least
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X F : Set Geo.Point)
    (hFlat : HilbertFlat3D Geo F)
    (hXF : Set.Subset X F) :
    Set.Subset (HilbertSpan3D Geo X) F := by
  intro P hP
  exact hP F hFlat hXF


/--
The generated 3D span is itself a flat.
-/
theorem hilbertSpan3D_flat
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (X : Set Geo.Point) :
    HilbertFlat3D Geo (HilbertSpan3D Geo X) := by
  constructor

  · intro A B hA hB hAB l hAl hBl P hPl
      F hFlat hXF

    exact
      hFlat.1
        A B
        (hA F hFlat hXF)
        (hB F hFlat hXF)
        hAB
        l hAl hBl
        P hPl

  · intro A B C hA hB hC hABC
      pi hApi hBpi hCpi P hPpi
      F hFlat hXF

    exact
      hFlat.2
        A B C
        (hA F hFlat hXF)
        (hB F hFlat hXF)
        (hC F hFlat hXF)
        hABC
        pi hApi hBpi hCpi
        P hPpi


/-!
## Primitive 3D carriers
-/

/--
Carrier of an ambient Hilbert line.
-/
def HilbertLineCarrier3D
    [H : HilbertIncidence Geo]
    (l : Geo.Line) : Set Geo.Point :=
  fun P => H.OnLine P l


/--
Every ambient Hilbert line is a Hilbert 3D flat.
-/
theorem hilbertLineCarrier3D_flat
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (l : Geo.Line) :
    HilbertFlat3D Geo (HilbertLineCarrier3D Geo l) := by
  constructor

  · intro A B hAl hBl hAB
      m hAm hBm X hXm

    have hml : m = l :=
      HilbertPlaneIncidence.line_unique
        (Geo := Geo)
        A B hAB
        m l
        hAm hBm
        hAl hBl

    rw [hml] at hXm
    exact hXm

  · intro A B C hAl hBl hCl hABC
      pi hApi hBpi hCpi X hXpi

    have hABCcol : PrimCollinear Geo A B C :=
      PrimCollinear.mk
        (Geo := Geo)
        hAl hBl hCl

    exact False.elim (hABC hABCcol)


/--
Carrier of an ambient Hilbert plane.
-/
def HilbertPlaneCarrier3D
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane) : Set Geo.Point :=
  fun P => S.OnPlane P pi


/--
Every ambient Hilbert plane is a Hilbert 3D flat.
-/
theorem hilbertPlaneCarrier3D_flat
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane) :
    HilbertFlat3D Geo (HilbertPlaneCarrier3D Geo pi) := by
  constructor

  · intro A B hApi hBpi hAB
      l hAl hBl X hXl

    have hlpi : HilbertLineInPlane Geo l pi :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        A B hAB
        l hAl hBl
        pi hApi hBpi

    exact hlpi X hXl

  · intro A B C hApi hBpi hCpi hABC
      rho hArho hBrho hCrho X hXrho

    have hrhopi : rho = pi :=
      HilbertSpaceIncidence.plane_unique
        (Geo := Geo)
        A B C hABC
        rho pi
        hArho hBrho hCrho
        hApi hBpi hCpi

    rw [hrhopi] at hXrho
    exact hXrho

end Geometry

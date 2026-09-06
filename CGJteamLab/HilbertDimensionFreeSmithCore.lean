import CGJteamLab.HilbertDimensionFreeIncidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Dimension-free Smith incidence core

For the proof that Smith I5 implies exchange it is useful to separate the
incidence package into:

* the Smith I1-I3 / plane-nondegeneracy core;
* the Smith I5 statement.

This separation is purely proof-theoretic.  The production class
`HilbertDimensionFreeIncidence` still packages both parts together.

The split lets later Wyler/LP4 arguments state exactly where I5 is used
and avoids any circular use of exchange.
-/

/--
The dimension-free incidence core obtained by removing Smith I5 from
`HilbertDimensionFreeIncidence`.
-/
class SmithIncidenceCore
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop where

  two_points_on_each_line :
    forall l : Geo.Line,
      exists A B : Geo.Point,
        Ne A B /\
        H.OnLine A l /\
        H.OnLine B l

  three_noncollinear_on_plane :
    forall pi : S.Plane,
      exists A B C : Geo.Point,
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi /\
        Not (PrimCollinear Geo A B C)

  plane_through :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      exists pi : S.Plane,
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi

  plane_unique :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      forall pi rho : S.Plane,
        S.OnPlane A pi ->
        S.OnPlane B pi ->
        S.OnPlane C pi ->
        S.OnPlane A rho ->
        S.OnPlane B rho ->
        S.OnPlane C rho ->
        pi = rho

  line_in_plane :
    forall A B : Geo.Point,
      Ne A B ->
      forall l : Geo.Line,
        H.OnLine A l ->
        H.OnLine B l ->
        forall pi : S.Plane,
          S.OnPlane A pi ->
          S.OnPlane B pi ->
          HilbertLineInPlane Geo l pi


/--
Smith I5 separated from the remaining incidence core.
-/
def SmithI5Statement
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall p0 p1 q0 q1 : Geo.Point,
    HilbertCoplanar4 Geo p0 p1 q0 q1 ->
    forall p : Geo.Point,
      exists q : Geo.Point,
        Ne q p /\
        HilbertCoplanar4 Geo p p0 q0 q /\
        HilbertCoplanar4 Geo p p1 q1 q


/--
The production dimension-free incidence package yields the Smith core.
-/
theorem smithIncidenceCore_of_dimensionFree
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo] :
    SmithIncidenceCore Geo where

  two_points_on_each_line :=
    D.two_points_on_each_line

  three_noncollinear_on_plane :=
    D.three_noncollinear_on_plane

  plane_through :=
    D.plane_through

  plane_unique :=
    D.plane_unique

  line_in_plane :=
    D.line_in_plane


/--
The production dimension-free incidence package supplies Smith I5.
-/
theorem smithI5_of_dimensionFree
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo] :
    SmithI5Statement Geo := by

  exact D.smith_i5


/--
A collinear point lies on the unique line through two distinct collinear
points already known to lie on that line.
-/
theorem smithCore_on_line_of_collinear_with_two
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B C : Geo.Point)
    (hAB : Ne A B)
    (l : Geo.Line)
    (hAl : H.OnLine A l)
    (hBl : H.OnLine B l)
    (hCol : PrimCollinear Geo A B C) :
    H.OnLine C l := by

  rcases hCol with
    ⟨m, hAm, hBm, hCm⟩

  have hml : m = l :=
    HilbertPlaneIncidence.line_unique
      A B hAB
      m l
      hAm hBm
      hAl hBl

  rw [hml] at hCm
  exact hCm

end Geometry

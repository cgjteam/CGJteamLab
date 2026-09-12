import CGJteamLab.HilbertSpaceIncidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Dimension-free Hilbert incidence

This module isolates the point-line-plane incidence package used for
synthetic geometry in arbitrary finite dimension.

The point-line part remains the existing `HilbertIncidence` /
`HilbertPlaneIncidence` layer.  The new class records the genuinely
dimension-free spatial clauses:

* every ambient line has two distinct points;
* every plane has three noncollinear points;
* three noncollinear points determine a unique plane;
* a plane containing two distinct points contains their whole line;
* Smith I5 replaces Hilbert I.7.

No dimension axiom is included here.  In particular, no ambient
plane-plane intersection axiom and no noncoplanar-point axiom is assumed.

The incidence package is synthetic: it introduces no affine structure,
coordinates, metric formulas, order, congruence, parallelism,
orthogonality, reflection, or continuity.
-/

/--
Dimension-free spatial incidence extension in the point-line-plane
language.

`smith_i5` is James T. Smith's dimension-free replacement for Hilbert I.7.
-/
class HilbertDimensionFreeIncidence
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop where

  /--
  Smith I1, line nondegeneracy clause:
  every line contains two distinct points.
  -/
  two_points_on_each_line :
    forall l : Geo.Line,
      exists A B : Geo.Point,
        Ne A B /\
        H.OnLine A l /\
        H.OnLine B l

  /--
  Smith I2, plane nondegeneracy clause:
  every plane contains three noncollinear points.
  -/
  three_noncollinear_on_plane :
    forall pi : S.Plane,
      exists A B C : Geo.Point,
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi /\
        Not (PrimCollinear Geo A B C)

  /--
  Smith I2, existence clause:
  three noncollinear points lie in a plane.
  -/
  plane_through :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      exists pi : S.Plane,
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi

  /--
  Smith I2, uniqueness clause:
  three noncollinear points determine their plane uniquely.
  -/
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

  /--
  Smith I3:
  if a plane contains two distinct points of a line, it contains the
  whole line.
  -/
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
  Smith I5, the dimension-free replacement for Hilbert I.7.

  If p0,p1,q0,q1 are coplanar, then for every point p there is q != p
  such that p,p0,q0,q are coplanar and p,p1,q1,q are coplanar.
  -/
  smith_i5 :
    forall p0 p1 q0 q1 : Geo.Point,
      HilbertCoplanar4 Geo p0 p1 q0 q1 ->
      forall p : Geo.Point,
        exists q : Geo.Point,
          Ne q p /\
          HilbertCoplanar4 Geo p p0 q0 q /\
          HilbertCoplanar4 Geo p p1 q1 q


/--
Every plane contains a point.
-/
theorem hilbert_dimension_free_point_on_each_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    (pi : S.Plane) :
    exists A : Geo.Point,
      S.OnPlane A pi := by

  rcases
      HilbertDimensionFreeIncidence.three_noncollinear_on_plane
        (Geo := Geo) pi with
    ⟨A, B, C, hApi, hBpi, hCpi, hABC⟩

  exact ⟨A, hApi⟩


/--
Smith I4 (existence of a plane) is redundant in the present
decomposition.
-/
theorem hilbert_dimension_free_plane_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertDimensionFreeIncidence Geo] :
    Nonempty S.Plane := by

  rcases
      HilbertPlaneIncidence.three_noncollinear
        (Geo := Geo) with
    ⟨A, B, C, hABC⟩

  rcases
      HilbertDimensionFreeIncidence.plane_through
        (Geo := Geo)
        A B C hABC with
    ⟨pi, hApi, hBpi, hCpi⟩

  exact ⟨pi⟩


/--
Every ambient line contains two distinct points.
-/
theorem hilbert_dimension_free_two_points_on_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    (l : Geo.Line) :
    exists A B : Geo.Point,
      Ne A B /\
      H.OnLine A l /\
      H.OnLine B l := by

  exact
    HilbertDimensionFreeIncidence.two_points_on_each_line
      (Geo := Geo) l

end Geometry

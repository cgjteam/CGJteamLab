import CGJteamLab.HilbertAxioms

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert 3D axioms

This file gives a Lean representation of the spatial part of Hilbert's
original axiom system.

IMPORTANT AUDIT NOTE

This file is not intended to introduce new geometric axioms beyond
Hilbert's system.

The existing `HilbertAxioms.lean` was designed for plane geometry, where
coplanarity is implicit.  In three-dimensional geometry that convention
is no longer available.  Therefore the original Hilbert axioms must be
represented with planes and point-plane incidence made explicit.

The genuinely spatial incidence axioms are Hilbert I.4-I.8.  We also
record here the universal line clause of I.3, because the current
`HilbertPlaneIncidence.two_points_on_line` interface only asserts the
existence of one line with two distinct points, whereas Hilbert I.3 says
that every line contains at least two distinct points.

No new spatial axiom of order, congruence, parallels, or continuity is
introduced in this file.

The sufficiency of this representation for the intended development is
NOT assumed here.  It is to be tested constructively by deriving actual
three-dimensional results, in particular the required part of Euclid
Book XI, plane reflections, Coxeter A3, and later higher-dimensional
extensions.

Thus:

* mathematical axiom source: Hilbert;
* Lean representation: this file;
* adequacy test: downstream formal proofs.

-/

/-!
## Primitive spatial language

Adding the type of planes and point-plane incidence extends the
signature of the geometry.  It is not itself a geometric axiom.
-/

/--
Primitive plane data for an ambient Hilbert space.
-/
class HilbertSpacePrimitive (Geo : Geometry.Geo) where
  Plane : Type u

  OnPlane :
    Geo.Point -> Plane -> Prop


/--
The type of planes in the ambient geometry.
-/
abbrev SpacePlane
    (Geo : Geometry.Geo)
    [S : HilbertSpacePrimitive Geo] :=
  S.Plane


/--
An ambient line is contained in a plane when all of its points lie in
that plane.
-/
def HilbertLineInPlane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l : Geo.Line)
    (pi : S.Plane) : Prop :=
  forall X : Geo.Point,
    H.OnLine X l ->
    S.OnPlane X pi


/--
Four points are coplanar when one plane contains all four.
-/
def HilbertCoplanar4
    [S : HilbertSpacePrimitive Geo]
    (A B C D : Geo.Point) : Prop :=
  exists pi : S.Plane,
    S.OnPlane A pi /\
    S.OnPlane B pi /\
    S.OnPlane C pi /\
    S.OnPlane D pi


/-!
## Spatial incidence axioms

These fields represent Hilbert's original incidence axioms needed when
plane membership is no longer implicit.

Different letters in Hilbert's text denote distinct objects.  Such
distinctness conditions are written explicitly below.
-/

/--
Spatial incidence extension of the existing Hilbert incidence layer.

No order, congruence, parallel, or continuity axiom is added here.
-/
class HilbertSpaceIncidence
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop where

  /--
  I.3, line clause:
  every line contains at least two distinct points.

  This is repeated here because the present 2D Lean interface contains
  only a weaker existential formulation of this clause.
  -/
  two_points_on_each_line :
    forall l : Geo.Line,
      exists A B : Geo.Point,
        Ne A B /\
        H.OnLine A l /\
        H.OnLine B l

  /--
  I.4, first clause:
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
  I.4, second clause:
  every plane contains a point.
  -/
  point_on_each_plane :
    forall pi : S.Plane,
      exists A : Geo.Point,
        S.OnPlane A pi

  /--
  I.5:
  three noncollinear points determine at most one plane.
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
  I.6:
  if two distinct points of a line lie in a plane, then the whole line
  lies in that plane.
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
  I.7:
  if two distinct planes have a common point, they have another
  distinct common point.

  Hilbert uses the convention that differently named planes are
  distinct; the hypothesis is explicit here.
  -/
  plane_second_common_point :
    forall pi rho : S.Plane,
      Ne pi rho ->
      forall A : Geo.Point,
        S.OnPlane A pi ->
        S.OnPlane A rho ->
        exists B : Geo.Point,
          Ne B A /\
          S.OnPlane B pi /\
          S.OnPlane B rho

  /--
  I.8:
  there exist four noncoplanar points.
  -/
  four_noncoplanar :
    exists A B C D : Geo.Point,
      Not (HilbertCoplanar4 Geo A B C D)

end Geometry

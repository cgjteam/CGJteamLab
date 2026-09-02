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

/-!
## Spatial representation of Hilbert Groups II-IV

The existing `HilbertOrder` and `HilbertCongruence` classes were designed
for plane geometry.  In particular, their Pasch axiom treats every
configuration as implicitly coplanar.

That representation must not be installed globally on a spatial `Geo`.

The classes below do not add axioms beyond Hilbert's Groups II-IV.
They restate these groups in a form in which the plane-local clauses are
made explicit.

The distinction is essential:

* II.1-II.3 are line statements and remain ambient;
* II.4 (Pasch) is explicitly restricted to one plane;
* III.1-III.3 remain ambient segment-congruence statements;
* III.4 constructs an angle in a specified target plane;
* III.5 compares two triangles globally and therefore may compare
  triangles lying in different planes;
* IV is explicitly restricted to one ambient plane.

No continuity axiom is introduced here.
-/

/--
One elementary same-side step inside a specified plane.

The endpoints are required to lie in the plane and the connecting
segment must avoid the line.
-/
def HilbertSameSideStepInPlane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (P Q : Geo.Point)
    (l : Geo.Line)
    (pi : S.Plane) : Prop :=
  S.OnPlane P pi /\
  S.OnPlane Q pi /\
  Not (H.OnLine P l) /\
  Not (H.OnLine Q l) /\
  Not (HilbertSegmentMeetsLine Geo P Q l)


/--
Two points are on the same side of a line inside a specified plane.

This is the spatial replacement for using the planar
`HilbertSameSide Geo` globally.
-/
def HilbertSameSideInPlane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (P Q : Geo.Point)
    (l : Geo.Line)
    (pi : S.Plane) : Prop :=
  S.OnPlane P pi /\
  S.OnPlane Q pi /\
  Not (H.OnLine P l) /\
  Not (H.OnLine Q l) /\
  Relation.ReflTransGen
    (fun X Y =>
      HilbertSameSideStepInPlane Geo X Y l pi)
    P Q


/--
Spatial representation of Hilbert Group II.

II.1-II.3 are ambient line-order axioms.
II.4 is Pasch with the containing plane made explicit.
-/
class HilbertSpaceOrder
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo] : Prop where

  /--
  II.1:
  betweenness gives three distinct collinear points and is symmetric in
  the endpoints.
  -/
  between_incidence :
    forall A B C : Geo.Point,
      Geo.Between A B C ->
      Ne A B /\
      Ne B C /\
      Ne A C /\
      PrimCollinear Geo A B C /\
      Geo.Between C B A

  /--
  II.2:
  a segment can be extended beyond an endpoint.
  -/
  between_extension :
    forall A C : Geo.Point,
      Ne A C ->
      exists B : Geo.Point,
        Geo.Between A C B

  /--
  II.3:
  among three collinear points, no more than one lies between the other
  two.
  -/
  between_unique :
    forall A B C : Geo.Point,
      PrimCollinear Geo A B C ->
      Geo.Between A B C ->
      Not (Geo.Between B A C) /\
      Not (Geo.Between A C B)

  /--
  II.4:
  Pasch in the plane containing the triangle.

  The explicit hypotheses that the triangle vertices and the cutting
  line lie in `pi` are exactly what is implicit in the present 2D class.
  -/
  pasch_in_plane :
    forall pi : S.Plane,
      forall A B C : Geo.Point,
        S.OnPlane A pi ->
        S.OnPlane B pi ->
        S.OnPlane C pi ->
        Not (PrimCollinear Geo A B C) ->
        forall l : Geo.Line,
          HilbertLineInPlane Geo l pi ->
          Not (H.OnLine A l) ->
          Not (H.OnLine B l) ->
          Not (H.OnLine C l) ->
          HilbertSegmentMeetsLine Geo A B l ->
          HilbertSegmentMeetsLine Geo A C l \/
          HilbertSegmentMeetsLine Geo B C l


/--
Spatial representation of Hilbert Group III.

This class deliberately does not extend the planar `HilbertCongruence`
class, because that would import its globally stated Pasch axiom.

The fields below are Hilbert III.1-III.5 with III.4 made explicitly
plane-local on the target side.
-/
class HilbertSpaceCongruence
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    [HilbertSpaceOrder Geo] : Prop where

  /--
  III.1:
  a segment can be laid off on a prescribed ambient ray.
  -/
  segment_construction :
    forall A B O R : Geo.Point,
      Ne O R ->
      exists X : Geo.Point,
        HilbertSameRay Geo O R X /\
        Geo.Congruent O X A B

  /--
  III.2:
  two segments congruent to the same segment are congruent to each
  other.
  -/
  segment_congruence_common :
    forall A B A' B' A'' B'' : Geo.Point,
      Geo.Congruent A B A' B' ->
      Geo.Congruent A B A'' B'' ->
      Geo.Congruent A' B' A'' B''

  /--
  III.3:
  additivity of adjacent congruent segments.
  -/
  segment_additivity :
    forall A B C A' B' C' : Geo.Point,
      Geo.Between A B C ->
      Geo.Between A' B' C' ->
      Geo.Congruent A B A' B' ->
      Geo.Congruent B C B' C' ->
      Geo.Congruent A C A' C'

  /--
  III.4:
  an angle can be constructed uniquely on a prescribed side of a
  prescribed ray in a specified target plane.

  The source angle `ABC` may lie in another plane.  This is the
  cross-plane angle transport present in Hilbert's original axiom.
  -/
  angle_construction_in_plane :
    forall A B C A' B' T : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      Ne A' B' ->
      forall pi : S.Plane,
        forall l : Geo.Line,
          HilbertLineInPlane Geo l pi ->
          H.OnLine A' l ->
          H.OnLine B' l ->
          S.OnPlane T pi ->
          Not (H.OnLine T l) ->
          exists C' : Geo.Point,
            HilbertSameSideInPlane Geo C' T l pi /\
            Geo.AngleCongruent A B C A' B' C' /\
            forall D' : Geo.Point,
              HilbertSameSideInPlane Geo D' T l pi ->
              Geo.AngleCongruent A B C A' B' D' ->
              HilbertSameRay Geo B' C' D'

  /--
  Reflexivity clause accompanying III.4.
  -/
  angle_congruence_reflexive :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      Geo.AngleCongruent A B C A B C

  /--
  III.5:
  Hilbert SAS.

  The two nondegenerate triangles need not be in the same plane.
  -/
  sas :
    forall A B C A' B' C' : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      Not (PrimCollinear Geo A' B' C') ->
      Geo.Congruent A B A' B' ->
      Geo.Congruent A C A' C' ->
      Geo.AngleCongruent B A C B' A' C' ->
      Geo.AngleCongruent A B C A' B' C'


/--
Spatial representation of Hilbert Group IV.

The Euclidean parallel axiom is plane-local.  Inside a specified
ambient plane, through a point outside a line there is at most one line
disjoint from the given line.

This class deliberately does not install `HilbertEuclideanPlane Geo`
on the ambient space.  The latter is a planar class and would import a
globally stated planar congruence/order structure.  Instead, Group IV is
recorded with the carrier plane made explicit, exactly as Pasch is made
explicit in `HilbertSpaceOrder`.
-/
class HilbertSpaceEuclidean
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    [HilbertSpaceOrder Geo]
    [HilbertSpaceCongruence Geo] : Prop where

  /--
  IV:
  in a fixed plane, through a point outside a line there is at most one
  line in that plane disjoint from the given line.
  -/
  parallel_unique_in_plane :
    forall pi : S.Plane,
      forall l : Geo.Line,
        HilbertLineInPlane Geo l pi ->
        forall A : Geo.Point,
          S.OnPlane A pi ->
          Not (H.OnLine A l) ->
          forall b c : Geo.Line,
            HilbertLineInPlane Geo b pi ->
            HilbertLineInPlane Geo c pi ->
            H.OnLine A b ->
            HilbertLinesDisjoint Geo b l ->
            H.OnLine A c ->
            HilbertLinesDisjoint Geo c l ->
            b = c


end Geometry

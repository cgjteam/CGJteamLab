import CGJteamLab.HilbertDimension
import CGJteamLab.Hilbert3DInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 incidence production core

This module is the production consolidation of the corrected E4 incidence
checkpoint.  It deliberately removes the historical dependency on the
`AffineFlat4D_testNN` chain.

Architecture:

* `Hilbert4DPrimitive` adds hyperplanes to the existing space primitive;
* ambient line/plane/hyperplane carrier notions are dimension-safe;
* `Hilbert4DAmbientIncidence` does not inherit ambient 3D incidence;
* `Hilbert4DHyperplaneLocal3DIncidence` restores 3D incidence only inside
  a fixed hyperplane;
* `Hilbert4DHyperplaneIncidenceCore` keeps only genuinely E4 hyperplane data
  above the production dimension-free Smith/Wyler incidence layer;
* `HyperplaneGeo4` recovers the local 3D geometry of a hyperplane.

No ambient `HilbertSpaceIncidence Geo` instance is introduced here.
-/


/--
Primitive incidence language for the E4 test layer.

An E4 geometry already has ambient planes, so this class extends the
existing `HilbertSpacePrimitive`.  The only new primitive object is an
ambient 3-dimensional hyperplane.
-/
class Hilbert4DPrimitive
    (Geo : Geometry.Geo)
    extends HilbertSpacePrimitive Geo where

  Hyperplane : Type u

  OnHyperplane :
    Geo.Point -> Hyperplane -> Prop

/--
The type of ambient 3-dimensional hyperplanes.
-/
abbrev SpaceHyperplane4
    (Geo : Geometry.Geo)
    [Q : Hilbert4DPrimitive Geo] :=
  Q.Hyperplane

/--
An ambient line is contained in an E4 hyperplane when every point
of the line belongs to that hyperplane.
-/
def HilbertLineInHyperplane4
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (l : Geo.Line)
    (Sigma : Q.Hyperplane) : Prop :=
  forall X : Geo.Point,
    H.OnLine X l ->
    Q.OnHyperplane X Sigma

/--
Five points are hyperplanar when one ambient 3-dimensional hyperplane
contains all five.
-/
def HilbertHyperplanar5
    [Q : Hilbert4DPrimitive Geo]
    (A B C D E : Geo.Point) : Prop :=
  exists Sigma : Q.Hyperplane,
    Q.OnHyperplane A Sigma /\
    Q.OnHyperplane B Sigma /\
    Q.OnHyperplane C Sigma /\
    Q.OnHyperplane D Sigma /\
    Q.OnHyperplane E Sigma

/--
Points of a fixed E4 hyperplane.
-/
def HyperplanePoint4
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane) :=
  {P : Geo.Point // Q.OnHyperplane P Sigma}

/--
Ambient lines wholly contained in a fixed E4 hyperplane.
-/
def HyperplaneLine4
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane) :=
  {l : Geo.Line // HilbertLineInHyperplane4 Geo l Sigma}

/--
Incidence inside a fixed E4 hyperplane.
-/
def HyperplaneOnLine4
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    {Sigma : Q.Hyperplane}
    (P : HyperplanePoint4 Geo Sigma)
    (l : HyperplaneLine4 Geo Sigma) : Prop :=
  H.OnLine P.1 l.1

/--
The line through two distinct points of one hyperplane is unique.
-/
theorem hyperplanePoint4_line_unique
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (A B : HyperplanePoint4 Geo Sigma)
    (hAB : Ne A B)
    (l m : HyperplaneLine4 Geo Sigma)
    (hAl : HyperplaneOnLine4 Geo A l)
    (hBl : HyperplaneOnLine4 Geo B l)
    (hAm : HyperplaneOnLine4 Geo A m)
    (hBm : HyperplaneOnLine4 Geo B m) :
    l = m := by

  have hABval : Ne A.1 B.1 := by
    intro h
    apply hAB
    exact Subtype.ext h

  have hlm : l.1 = m.1 :=
    HilbertPlaneIncidence.line_unique
      A.1 B.1 hABval
      l.1 m.1
      hAl hBl hAm hBm

  exact Subtype.ext hlm

/--
An ambient plane is contained in an E4 hyperplane.
-/
def HilbertPlaneInHyperplane4
    [Q : Hilbert4DPrimitive Geo]
    (pi : Q.toHilbertSpacePrimitive.Plane)
    (Sigma : Q.Hyperplane) : Prop :=
  forall X : Geo.Point,
    Q.toHilbertSpacePrimitive.OnPlane X pi ->
    Q.OnHyperplane X Sigma

/--
Ambient planes wholly contained in a fixed E4 hyperplane.
-/
def HyperplanePlane4
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane) :=
  {pi : Q.toHilbertSpacePrimitive.Plane //
    HilbertPlaneInHyperplane4 Geo pi Sigma}

/--
Incidence of a hyperplane-slice point with a hyperplane-slice plane.
-/
def HyperplaneOnPlane4
    [Q : Hilbert4DPrimitive Geo]
    {Sigma : Q.Hyperplane}
    (P : HyperplanePoint4 Geo Sigma)
    (pi : HyperplanePlane4 Geo Sigma) : Prop :=
  Q.toHilbertSpacePrimitive.OnPlane P.1 pi.1

/--
Forget the proof that a hyperplane point lies in the fixed hyperplane,
pointwise on a set.
-/
def hyperplanePointSetToAmbient4
    [Q : Hilbert4DPrimitive Geo]
    {Sigma : Q.Hyperplane}
    (U : Set (HyperplanePoint4 Geo Sigma)) :
    Set Geo.Point :=
  Subtype.val '' U

/--
The raw geometry induced on one E4 hyperplane.

Points are ambient points lying in `Sigma`.
Lines are ambient lines wholly contained in `Sigma`.
Betweenness and segment congruence are inherited from the ambient
geometry.

For the primitive angle relation, rays are mapped back to ambient point
sets exactly as in the existing `PlaneGeo` construction.
-/
def HyperplaneGeo4
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane) :
    Geometry.Geo where

  Point :=
    HyperplanePoint4 Geo Sigma

  Line :=
    HyperplaneLine4 Geo Sigma

  OnLine :=
    fun P l =>
      HyperplaneOnLine4 Geo P l

  Between :=
    fun A B C =>
      Geo.Between A.1 B.1 C.1

  SegmentCongruent :=
    fun s t =>
      Geo.SegmentCongruent
        (mapUnorderedPair
          (fun P : HyperplanePoint4 Geo Sigma => P.1) s)
        (mapUnorderedPair
          (fun P : HyperplanePoint4 Geo Sigma => P.1) t)

  UnorientedAngleCongruent :=
    fun a b =>
      Relation.EqvGen Geo.UnorientedAngleCongruent
        ( a.1.1,
          mapUnorderedPair
            (hyperplanePointSetToAmbient4
              (Geo := Geo) (Sigma := Sigma))
            a.2 )
        ( b.1.1,
          mapUnorderedPair
            (hyperplanePointSetToAmbient4
              (Geo := Geo) (Sigma := Sigma))
            b.2 )

/--
Betweenness in the induced hyperplane geometry is literally ambient
betweenness of the underlying points.
-/
theorem hyperplaneGeo4_between
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (A B C : HyperplanePoint4 Geo Sigma) :
    (HyperplaneGeo4 Geo Sigma).Between A B C <->
      Geo.Between A.1 B.1 C.1 := by
  rfl

/--
Segment congruence in the induced hyperplane geometry is literally
ambient segment congruence of the underlying endpoints.
-/
theorem hyperplaneGeo4_congruent
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (A B C D : HyperplanePoint4 Geo Sigma) :
    (HyperplaneGeo4 Geo Sigma).Congruent A B C D <->
      Geo.Congruent A.1 B.1 C.1 D.1 := by
  rfl

/--
Point-line incidence in the induced hyperplane geometry is inherited
from ambient incidence.
-/
instance hyperplaneGeo4HilbertIncidence
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane) :
    HilbertIncidence (HyperplaneGeo4 Geo Sigma) where

  OnLine :=
    fun P l =>
      HyperplaneOnLine4 Geo P l

/--
Collinearity in the induced hyperplane geometry implies ambient
collinearity of the underlying points.
-/
theorem hyperplaneGeo4_primCollinear_to_ambient
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (A B C : HyperplanePoint4 Geo Sigma) :
    PrimCollinear (HyperplaneGeo4 Geo Sigma) A B C ->
      PrimCollinear Geo A.1 B.1 C.1 := by

  rintro ⟨l, hAl, hBl, hCl⟩
  exact ⟨l.1, hAl, hBl, hCl⟩

/--
Dimension-independent ambient incidence data needed in E4.

This deliberately does NOT extend `HilbertSpaceIncidence`.
-/
class Hilbert4DAmbientIncidence
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo] : Prop where

  /-- Every ambient line has two distinct points. -/
  two_points_on_each_line :
    forall l : Geo.Line,
      exists A B : Geo.Point,
        Ne A B /\
        H.OnLine A l /\
        H.OnLine B l

  /-- Three noncollinear points determine an ambient 2-plane. -/
  plane_through :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      exists pi : Q.toHilbertSpacePrimitive.Plane,
        Q.toHilbertSpacePrimitive.OnPlane A pi /\
        Q.toHilbertSpacePrimitive.OnPlane B pi /\
        Q.toHilbertSpacePrimitive.OnPlane C pi

  /-- Every ambient 2-plane contains a point. -/
  point_on_each_plane :
    forall pi : Q.toHilbertSpacePrimitive.Plane,
      exists A : Geo.Point,
        Q.toHilbertSpacePrimitive.OnPlane A pi

  /-- Three noncollinear points determine their 2-plane uniquely. -/
  plane_unique :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      forall pi tau : Q.toHilbertSpacePrimitive.Plane,
        Q.toHilbertSpacePrimitive.OnPlane A pi ->
        Q.toHilbertSpacePrimitive.OnPlane B pi ->
        Q.toHilbertSpacePrimitive.OnPlane C pi ->
        Q.toHilbertSpacePrimitive.OnPlane A tau ->
        Q.toHilbertSpacePrimitive.OnPlane B tau ->
        Q.toHilbertSpacePrimitive.OnPlane C tau ->
        pi = tau

  /-- A line through two points of a 2-plane lies in that 2-plane. -/
  line_in_plane :
    forall A B : Geo.Point,
      Ne A B ->
      forall l : Geo.Line,
        H.OnLine A l ->
        H.OnLine B l ->
        forall pi : Q.toHilbertSpacePrimitive.Plane,
          Q.toHilbertSpacePrimitive.OnPlane A pi ->
          Q.toHilbertSpacePrimitive.OnPlane B pi ->
          HilbertLineInPlane Geo l pi

  /-- Four noncoplanar points determine an E4 hyperplane. -/
  hyperplane_through :
    forall A B C D : Geo.Point,
      Not (HilbertCoplanar4 Geo A B C D) ->
      exists Sigma : Q.Hyperplane,
        Q.OnHyperplane A Sigma /\
        Q.OnHyperplane B Sigma /\
        Q.OnHyperplane C Sigma /\
        Q.OnHyperplane D Sigma

  /-- Every E4 hyperplane contains a point. -/
  point_on_each_hyperplane :
    forall Sigma : Q.Hyperplane,
      exists A : Geo.Point,
        Q.OnHyperplane A Sigma

  /-- Four noncoplanar points determine their hyperplane uniquely. -/
  hyperplane_unique :
    forall A B C D : Geo.Point,
      Not (HilbertCoplanar4 Geo A B C D) ->
      forall Sigma Tau : Q.Hyperplane,
        Q.OnHyperplane A Sigma ->
        Q.OnHyperplane B Sigma ->
        Q.OnHyperplane C Sigma ->
        Q.OnHyperplane D Sigma ->
        Q.OnHyperplane A Tau ->
        Q.OnHyperplane B Tau ->
        Q.OnHyperplane C Tau ->
        Q.OnHyperplane D Tau ->
        Sigma = Tau

  /-- A line through two points of a hyperplane lies in the hyperplane. -/
  line_in_hyperplane :
    forall A B : Geo.Point,
      Ne A B ->
      forall l : Geo.Line,
        H.OnLine A l ->
        H.OnLine B l ->
        forall Sigma : Q.Hyperplane,
          Q.OnHyperplane A Sigma ->
          Q.OnHyperplane B Sigma ->
          HilbertLineInHyperplane4 Geo l Sigma

  /-- Genuine four-dimensionality. -/
  five_nonhyperplanar :
    exists A B C D E : Geo.Point,
      Not (HilbertHyperplanar5 Geo A B C D E)


/--
The genuinely 3-dimensional incidence principles are required only
inside a fixed E4 hyperplane.

This class is the replacement for the accidental inheritance of ambient
`HilbertSpaceIncidence`.
-/
class Hilbert4DHyperplaneLocal3DIncidence
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo] : Prop where

  /--
  If an ambient 2-plane contains three noncollinear points of Sigma,
  then the whole 2-plane lies in Sigma.
  -/
  plane_in_hyperplane :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      forall pi : Q.toHilbertSpacePrimitive.Plane,
        Q.toHilbertSpacePrimitive.OnPlane A pi ->
        Q.toHilbertSpacePrimitive.OnPlane B pi ->
        Q.toHilbertSpacePrimitive.OnPlane C pi ->
        forall Sigma : Q.Hyperplane,
          Q.OnHyperplane A Sigma ->
          Q.OnHyperplane B Sigma ->
          Q.OnHyperplane C Sigma ->
          HilbertPlaneInHyperplane4 Geo pi Sigma

  /--
  Local 3D version of Hilbert I.7:
  two distinct 2-planes inside one hyperplane, if they share a point,
  share a second point.
  -/
  plane_second_common_point_in_hyperplane :
    forall Sigma : Q.Hyperplane,
      forall pi tau : Q.toHilbertSpacePrimitive.Plane,
        HilbertPlaneInHyperplane4 Geo pi Sigma ->
        HilbertPlaneInHyperplane4 Geo tau Sigma ->
        Ne pi tau ->
        forall P : Geo.Point,
          Q.toHilbertSpacePrimitive.OnPlane P pi ->
          Q.toHilbertSpacePrimitive.OnPlane P tau ->
          exists R : Geo.Point,
            Ne R P /\
            Q.toHilbertSpacePrimitive.OnPlane R pi /\
            Q.toHilbertSpacePrimitive.OnPlane R tau

  /--
  Every hyperplane is genuinely 3-dimensional internally.
  -/
  four_noncoplanar_on_hyperplane :
    forall Sigma : Q.Hyperplane,
      exists A B C D : Geo.Point,
        Q.OnHyperplane A Sigma /\
        Q.OnHyperplane B Sigma /\
        Q.OnHyperplane C Sigma /\
        Q.OnHyperplane D Sigma /\
        Not (HilbertCoplanar4 Geo A B C D)

/-!
# E4 refactor checkpoint 01: Smith/Wyler as the ambient incidence base

The corrected E4 test hierarchy was developed before the production
dimension-free Smith/Wyler layer was connected to it. Consequently
`Hilbert4DAmbientIncidence` duplicates several point-line-plane fields
which are already supplied by `HilbertDimensionFreeIncidence`.

This file reverses that dependency.

The new E4-specific incidence core contains only genuinely 4-dimensional
hyperplane data:

* four noncoplanar points determine a hyperplane;
* every hyperplane contains a point;
* hyperplane uniqueness;
* line closure inside a hyperplane;
* genuine 4-dimensionality.

All point-line-plane incidence is supplied by the production
`HilbertDimensionFreeIncidence` package.  The old
`Hilbert4DAmbientIncidence` is then reconstructed as a compatibility
instance, so the corrected E4 theorem chain can be reused while new
proofs also have direct access to SmithSpan, Wyler, and exchange.
-/

/--
The genuinely E4-specific ambient incidence layer, after removing the
point-line-plane clauses already provided by
`HilbertDimensionFreeIncidence`.
-/
class Hilbert4DHyperplaneIncidenceCore
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo] : Prop where

  /-- Four noncoplanar points determine an E4 hyperplane. -/
  hyperplane_through :
    forall A B C D : Geo.Point,
      Not (HilbertCoplanar4 Geo A B C D) ->
      exists Sigma : Q.Hyperplane,
        Q.OnHyperplane A Sigma /\
        Q.OnHyperplane B Sigma /\
        Q.OnHyperplane C Sigma /\
        Q.OnHyperplane D Sigma

  /-- Every E4 hyperplane contains a point. -/
  point_on_each_hyperplane :
    forall Sigma : Q.Hyperplane,
      exists A : Geo.Point,
        Q.OnHyperplane A Sigma

  /-- Four noncoplanar points determine their hyperplane uniquely. -/
  hyperplane_unique :
    forall A B C D : Geo.Point,
      Not (HilbertCoplanar4 Geo A B C D) ->
      forall Sigma Tau : Q.Hyperplane,
        Q.OnHyperplane A Sigma ->
        Q.OnHyperplane B Sigma ->
        Q.OnHyperplane C Sigma ->
        Q.OnHyperplane D Sigma ->
        Q.OnHyperplane A Tau ->
        Q.OnHyperplane B Tau ->
        Q.OnHyperplane C Tau ->
        Q.OnHyperplane D Tau ->
        Sigma = Tau

  /-- A line through two points of a hyperplane lies in the hyperplane. -/
  line_in_hyperplane :
    forall A B : Geo.Point,
      Ne A B ->
      forall l : Geo.Line,
        H.OnLine A l ->
        H.OnLine B l ->
        forall Sigma : Q.Hyperplane,
          Q.OnHyperplane A Sigma ->
          Q.OnHyperplane B Sigma ->
          HilbertLineInHyperplane4 Geo l Sigma

  /-- Genuine four-dimensionality. -/
  five_nonhyperplanar :
    exists A B C D E : Geo.Point,
      Not (HilbertHyperplanar5 Geo A B C D E)


/--
Compatibility bridge.

Under the production dimension-free incidence package, the old corrected
E4 ambient class is reconstructed automatically.  Its five
point-line-plane fields come from Smith's dimension-free incidence
package; only the hyperplane fields come from the new E4-specific core.
-/
instance hilbert4DAmbientIncidence_of_dimensionFree
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C : Hilbert4DHyperplaneIncidenceCore Geo] :
    Hilbert4DAmbientIncidence Geo where

  two_points_on_each_line :=
    D.two_points_on_each_line

  plane_through :=
    D.plane_through

  point_on_each_plane :=
    hilbert_dimension_free_point_on_each_plane
      (Geo := Geo)

  plane_unique :=
    D.plane_unique

  line_in_plane :=
    D.line_in_plane

  hyperplane_through :=
    C.hyperplane_through

  point_on_each_hyperplane :=
    C.point_on_each_hyperplane

  hyperplane_unique :=
    C.hyperplane_unique

  line_in_hyperplane :=
    C.line_in_hyperplane

  five_nonhyperplanar :=
    C.five_nonhyperplanar


/--
Sanity check 1: old corrected E4 lemmas can still ask only for
`Hilbert4DAmbientIncidence`; the bridge supplies it from the new base.
-/
theorem hilbert4D_refactor_old_ambient_api_available
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    (l : Geo.Line) :
    exists A B : Geo.Point,
      Ne A B /\
      H.OnLine A l /\
      H.OnLine B l := by

  exact
    Hilbert4DAmbientIncidence.two_points_on_each_line
      (Geo := Geo)
      l


/--
Sanity check 2: the same E4 context now has the production
Smith/Wyler/Steinitz exchange theorem available directly.
-/
theorem hilbert4D_refactor_smithSpanExchange_available
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo] :
    SmithSpanExchange Geo := by

  exact
    dimensionFreeIncidence_implies_smithSpanExchange
      (Geo := Geo)

/-!
# E4 incidence hierarchy repair: recover local 3D incidence

The corrected hierarchy separates genuine ambient E4 incidence from
the genuinely 3D incidence local to each hyperplane.

This section checks the crucial reconstruction:

  HilbertSpaceIncidence (HyperplaneGeo4 Geo Sigma)

from the corrected classes, without any ambient
`HilbertSpaceIncidence Geo` assumption.

This is the repaired production form of the old test16.
-/

/--
Dimension-independent replacement for the old spatial theorem
"plane through a line and an external point".

Only the corrected E4 ambient incidence core is used.
-/
theorem hilbert4D_plane_through_line_and_external_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [H4 : Hilbert4DAmbientIncidence Geo]
    (l : Geo.Line)
    (P : Geo.Point)
    (hPl : Not (H.OnLine P l)) :
    exists pi : Q.toHilbertSpacePrimitive.Plane,
      HilbertLineInPlane Geo l pi /\
      Q.toHilbertSpacePrimitive.OnPlane P pi := by

  rcases
      Hilbert4DAmbientIncidence.two_points_on_each_line
        (Geo := Geo) l with
    ⟨A, B, hAB, hAl, hBl⟩

  have hABP :
      Not (PrimCollinear Geo A B P) := by

    intro hCol

    have hPl' :
        H.OnLine P l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAB
        hAl hBl
        hCol

    exact hPl hPl'

  rcases
      Hilbert4DAmbientIncidence.plane_through
        (Geo := Geo)
        A B P hABP with
    ⟨pi, hApi, hBpi, hPpi⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    Hilbert4DAmbientIncidence.line_in_plane
      (Geo := Geo)
      A B hAB
      l hAl hBl
      pi hApi hBpi

  exact
    ⟨pi, hlpi, hPpi⟩

/--
Corrected line-through theorem inside one E4 hyperplane.
-/
theorem hyperplanePoint4_line_through_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (Sigma : Q.Hyperplane)
    (A B : HyperplanePoint4 Geo Sigma)
    (hAB : Ne A B) :
    exists l : HyperplaneLine4 Geo Sigma,
      HyperplaneOnLine4 Geo A l /\
      HyperplaneOnLine4 Geo B l := by

  have hABval : Ne A.1 B.1 := by
    intro h
    apply hAB
    exact Subtype.ext h

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A.1 B.1 hABval with
    ⟨l, hAl, hBl⟩

  have hlSigma :
      HilbertLineInHyperplane4 Geo l Sigma :=
    Hilbert4DAmbientIncidence.line_in_hyperplane
      (Geo := Geo)
      A.1 B.1 hABval
      l hAl hBl
      Sigma A.2 B.2

  exact
    ⟨⟨l, hlSigma⟩, hAl, hBl⟩

/--
Corrected two-points-on-each-line theorem inside one hyperplane.
-/
theorem hyperplaneLine4_two_points_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (Sigma : Q.Hyperplane)
    (l : HyperplaneLine4 Geo Sigma) :
    exists A B : HyperplanePoint4 Geo Sigma,
      Ne A B /\
      HyperplaneOnLine4 Geo A l /\
      HyperplaneOnLine4 Geo B l := by

  rcases
      Hilbert4DAmbientIncidence.two_points_on_each_line
        (Geo := Geo) l.1 with
    ⟨A, B, hAB, hAl, hBl⟩

  have hASigma :
      Q.OnHyperplane A Sigma :=
    l.2 A hAl

  have hBSigma :
      Q.OnHyperplane B Sigma :=
    l.2 B hBl

  let A' : HyperplanePoint4 Geo Sigma :=
    ⟨A, hASigma⟩

  let B' : HyperplanePoint4 Geo Sigma :=
    ⟨B, hBSigma⟩

  have hA'B' : Ne A' B' := by
    intro h
    apply hAB
    exact congrArg Subtype.val h

  exact
    ⟨A', B', hA'B', hAl, hBl⟩

/--
Ambient collinearity of hyperplane points becomes internal collinearity,
without using ambient `HilbertSpaceIncidence`.
-/
theorem hyperplaneGeo4_primCollinear_of_ambient_of_ne_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (Sigma : Q.Hyperplane)
    (A B C : HyperplanePoint4 Geo Sigma)
    (hAB : Ne A.1 B.1)
    (hCol : PrimCollinear Geo A.1 B.1 C.1) :
    PrimCollinear
      (HyperplaneGeo4 Geo Sigma) A B C := by

  rcases hCol with
    ⟨l, hAl, hBl, hCl⟩

  have hlSigma :
      HilbertLineInHyperplane4 Geo l Sigma :=
    Hilbert4DAmbientIncidence.line_in_hyperplane
      (Geo := Geo)
      A.1 B.1 hAB
      l hAl hBl
      Sigma A.2 B.2

  exact
    ⟨⟨l, hlSigma⟩, hAl, hBl, hCl⟩

/--
Every hyperplane contains three ambiently noncollinear points.

This is derived from the local four-noncoplanar clause without any
ambient 3D incidence axiom.
-/
theorem hyperplanePoint4_three_noncollinear_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane) :
    exists A B C : HyperplanePoint4 Geo Sigma,
      Not (PrimCollinear Geo A.1 B.1 C.1) := by

  rcases
      Hilbert4DHyperplaneLocal3DIncidence.four_noncoplanar_on_hyperplane
        (Geo := Geo)
        Sigma with
    ⟨A, B, C, D,
     hASigma, hBSigma, hCSigma, hDSigma,
     hNoncoplanar⟩

  let A' : HyperplanePoint4 Geo Sigma :=
    ⟨A, hASigma⟩

  let B' : HyperplanePoint4 Geo Sigma :=
    ⟨B, hBSigma⟩

  let C' : HyperplanePoint4 Geo Sigma :=
    ⟨C, hCSigma⟩

  let D' : HyperplanePoint4 Geo Sigma :=
    ⟨D, hDSigma⟩

  refine
    ⟨A', B', C', ?_⟩

  intro hABC

  rcases hABC with
    ⟨l, hAl, hBl, hCl⟩

  by_cases hDl : H.OnLine D l

  · rcases
        hilbert_point_off_line
          (Geo := Geo) l with
      ⟨P, hPl⟩

    rcases
        hilbert4D_plane_through_line_and_external_point
          (Geo := Geo)
          l P hPl with
      ⟨pi, hlpi, _hPpi⟩

    exact
      hNoncoplanar
        ⟨pi,
         hlpi A hAl,
         hlpi B hBl,
         hlpi C hCl,
         hlpi D hDl⟩

  · rcases
        hilbert4D_plane_through_line_and_external_point
          (Geo := Geo)
          l D hDl with
      ⟨pi, hlpi, hDpi⟩

    exact
      hNoncoplanar
        ⟨pi,
         hlpi A hAl,
         hlpi B hBl,
         hlpi C hCl,
         hDpi⟩

/--
The induced hyperplane geometry has three noncollinear points in its own
incidence language.
-/
theorem hyperplaneGeo4_three_noncollinear_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane) :
    exists A B C : (HyperplaneGeo4 Geo Sigma).Point,
      Not
        (PrimCollinear
          (HyperplaneGeo4 Geo Sigma)
          A B C) := by

  rcases
      hyperplanePoint4_three_noncollinear_corrected
        (Geo := Geo)
        Sigma with
    ⟨A, B, C, hABC⟩

  refine
    ⟨A, B, C, ?_⟩

  intro hCol

  exact
    hABC
      (hyperplaneGeo4_primCollinear_to_ambient
        (Geo := Geo)
        Sigma A B C hCol)

/--
Corrected `HilbertPlaneIncidence` instance on a fixed hyperplane.
-/
instance hyperplaneGeo4HilbertPlaneIncidence_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane) :
    HilbertPlaneIncidence
      (HyperplaneGeo4 Geo Sigma) where

  line_through := by
    intro A B hAB

    exact
      hyperplanePoint4_line_through_corrected
        (Geo := Geo)
        Sigma A B hAB

  line_unique := by
    intro A B hAB l m
      hAl hBl hAm hBm

    exact
      hyperplanePoint4_line_unique
        (Geo := Geo)
        Sigma A B hAB
        l m
        hAl hBl hAm hBm

  two_points_on_line := by
    rcases
        hyperplanePoint4_three_noncollinear_corrected
          (Geo := Geo)
          Sigma with
      ⟨A, B, C, hABC⟩

    have hABval : Ne A.1 B.1 :=
      hilbert_noncollinear_ne_first
        Geo A.1 B.1 C.1 hABC

    have hAB : Ne A B := by
      intro h
      apply hABval
      exact congrArg Subtype.val h

    rcases
        hyperplanePoint4_line_through_corrected
          (Geo := Geo)
          Sigma A B hAB with
      ⟨l, hAl, hBl⟩

    exact
      ⟨l, A, B, hAB, hAl, hBl⟩

  three_noncollinear := by
    exact
      hyperplaneGeo4_three_noncollinear_corrected
        (Geo := Geo)
        Sigma

/--
Internal noncollinearity implies ambient noncollinearity under the
corrected E4 incidence hierarchy.
-/
theorem hyperplaneGeo4_noncollinear_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane)
    (A B C : HyperplanePoint4 Geo Sigma)
    (hABC :
      Not
        (PrimCollinear
          (HyperplaneGeo4 Geo Sigma)
          A B C)) :
    Not (PrimCollinear Geo A.1 B.1 C.1) := by

  intro hAmbient

  have hAB : Ne A B :=
    hilbert_noncollinear_ne_first
      (HyperplaneGeo4 Geo Sigma)
      A B C hABC

  have hABval : Ne A.1 B.1 := by
    intro h
    apply hAB
    exact Subtype.ext h

  have hInternal :
      PrimCollinear
        (HyperplaneGeo4 Geo Sigma)
        A B C :=
    hyperplaneGeo4_primCollinear_of_ambient_of_ne_corrected
      (Geo := Geo)
      Sigma A B C
      hABval hAmbient

  exact hABC hInternal

/--
The primitive plane type of the hyperplane slice is unchanged.
-/
instance hyperplaneGeo4HilbertSpacePrimitive_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane) :
    HilbertSpacePrimitive
      (HyperplaneGeo4 Geo Sigma) where

  Plane :=
    HyperplanePlane4 Geo Sigma

  OnPlane :=
    fun P pi =>
      HyperplaneOnPlane4 Geo P pi

/--
Three ambiently noncollinear points of Sigma determine a local plane.
-/
theorem hyperplanePoint4_plane_through_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane)
    (A B C : HyperplanePoint4 Geo Sigma)
    (hABC :
      Not (PrimCollinear Geo A.1 B.1 C.1)) :
    exists pi : HyperplanePlane4 Geo Sigma,
      HyperplaneOnPlane4 Geo A pi /\
      HyperplaneOnPlane4 Geo B pi /\
      HyperplaneOnPlane4 Geo C pi := by

  rcases
      Hilbert4DAmbientIncidence.plane_through
        (Geo := Geo)
        A.1 B.1 C.1 hABC with
    ⟨pi, hApi, hBpi, hCpi⟩

  have hpiSigma :
      HilbertPlaneInHyperplane4
        Geo pi Sigma :=
    Hilbert4DHyperplaneLocal3DIncidence.plane_in_hyperplane
      (Geo := Geo)
      A.1 B.1 C.1 hABC
      pi hApi hBpi hCpi
      Sigma A.2 B.2 C.2

  exact
    ⟨⟨pi, hpiSigma⟩,
     hApi, hBpi, hCpi⟩

/--
The local plane through three noncollinear points is unique.
-/
theorem hyperplanePoint4_plane_unique_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (Sigma : Q.Hyperplane)
    (A B C : HyperplanePoint4 Geo Sigma)
    (hABC :
      Not (PrimCollinear Geo A.1 B.1 C.1))
    (pi rho : HyperplanePlane4 Geo Sigma)
    (hApi : HyperplaneOnPlane4 Geo A pi)
    (hBpi : HyperplaneOnPlane4 Geo B pi)
    (hCpi : HyperplaneOnPlane4 Geo C pi)
    (hArho : HyperplaneOnPlane4 Geo A rho)
    (hBrho : HyperplaneOnPlane4 Geo B rho)
    (hCrho : HyperplaneOnPlane4 Geo C rho) :
    pi = rho := by

  have hPlaneEq :
      pi.1 = rho.1 :=
    Hilbert4DAmbientIncidence.plane_unique
      (Geo := Geo)
      A.1 B.1 C.1 hABC
      pi.1 rho.1
      hApi hBpi hCpi
      hArho hBrho hCrho

  exact
    Subtype.ext hPlaneEq

/--
Every local plane contains a local point.
-/
theorem hyperplanePlane4_point_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    (Sigma : Q.Hyperplane)
    (pi : HyperplanePlane4 Geo Sigma) :
    exists A : HyperplanePoint4 Geo Sigma,
      HyperplaneOnPlane4 Geo A pi := by

  rcases
      Hilbert4DAmbientIncidence.point_on_each_plane
        (Geo := Geo)
        pi.1 with
    ⟨A, hApi⟩

  have hASigma :
      Q.OnHyperplane A Sigma :=
    pi.2 A hApi

  exact
    ⟨⟨A, hASigma⟩, hApi⟩

/--
Local I.7 inside one hyperplane.
-/
theorem hyperplanePlane4_second_common_point_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane)
    (pi rho : HyperplanePlane4 Geo Sigma)
    (hneq : Ne pi rho)
    (A : HyperplanePoint4 Geo Sigma)
    (hApi : HyperplaneOnPlane4 Geo A pi)
    (hArho : HyperplaneOnPlane4 Geo A rho) :
    exists B : HyperplanePoint4 Geo Sigma,
      Ne B A /\
      HyperplaneOnPlane4 Geo B pi /\
      HyperplaneOnPlane4 Geo B rho := by

  have hneqVal : Ne pi.1 rho.1 := by
    intro h
    apply hneq
    exact Subtype.ext h

  rcases
      Hilbert4DHyperplaneLocal3DIncidence.plane_second_common_point_in_hyperplane
        (Geo := Geo)
        Sigma
        pi.1 rho.1
        pi.2 rho.2
        hneqVal
        A.1
        hApi hArho with
    ⟨B, hBA, hBpi, hBrho⟩

  have hBSigma :
      Q.OnHyperplane B Sigma :=
    pi.2 B hBpi

  let B' : HyperplanePoint4 Geo Sigma :=
    ⟨B, hBSigma⟩

  have hB'A : Ne B' A := by
    intro h
    apply hBA
    exact congrArg Subtype.val h

  exact
    ⟨B', hB'A, hBpi, hBrho⟩

/--
Internal coplanarity implies ambient coplanarity.
-/
theorem hyperplaneGeo4_coplanar4_to_ambient_corrected
    [H : HilbertIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    (Sigma : Q.Hyperplane)
    (A B C D : (HyperplaneGeo4 Geo Sigma).Point) :
    HilbertCoplanar4
        (HyperplaneGeo4 Geo Sigma)
        A B C D ->
      HilbertCoplanar4
        Geo A.1 B.1 C.1 D.1 := by

  intro hCoplanar

  rcases hCoplanar with
    ⟨pi, hApi, hBpi, hCpi, hDpi⟩

  exact
    ⟨pi.1,
     hApi, hBpi, hCpi, hDpi⟩

/--
The repaired local 3D incidence instance.

No ambient `HilbertSpaceIncidence Geo` assumption occurs anywhere in
this declaration.
-/
instance hyperplaneGeo4HilbertSpaceIncidence_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Sigma : Q.Hyperplane) :
    HilbertSpaceIncidence
      (HyperplaneGeo4 Geo Sigma) where

  two_points_on_each_line := by
    intro l

    exact
      hyperplaneLine4_two_points_corrected
        (Geo := Geo)
        Sigma l

  plane_through := by
    intro A B C hABC

    have hAmbient :
        Not
          (PrimCollinear
            Geo A.1 B.1 C.1) :=
      hyperplaneGeo4_noncollinear_to_ambient_corrected
        (Geo := Geo)
        Sigma A B C hABC

    exact
      hyperplanePoint4_plane_through_corrected
        (Geo := Geo)
        Sigma A B C hAmbient

  point_on_each_plane := by
    intro pi

    exact
      hyperplanePlane4_point_corrected
        (Geo := Geo)
        Sigma pi

  plane_unique := by
    intro A B C hABC
      pi rho
      hApi hBpi hCpi
      hArho hBrho hCrho

    have hAmbient :
        Not
          (PrimCollinear
            Geo A.1 B.1 C.1) :=
      hyperplaneGeo4_noncollinear_to_ambient_corrected
        (Geo := Geo)
        Sigma A B C hABC

    exact
      hyperplanePoint4_plane_unique_corrected
        (Geo := Geo)
        Sigma A B C hAmbient
        pi rho
        hApi hBpi hCpi
        hArho hBrho hCrho

  line_in_plane := by
    intro A B hAB
      l hAl hBl
      pi hApi hBpi

    have hABval : Ne A.1 B.1 := by
      intro h
      apply hAB
      exact Subtype.ext h

    have hAmbient :
        HilbertLineInPlane
          Geo l.1 pi.1 :=
      Hilbert4DAmbientIncidence.line_in_plane
        (Geo := Geo)
        A.1 B.1 hABval
        l.1 hAl hBl
        pi.1 hApi hBpi

    intro X hXl

    exact hAmbient X.1 hXl

  plane_second_common_point := by
    intro pi rho hneq
      A hApi hArho

    exact
      hyperplanePlane4_second_common_point_corrected
        (Geo := Geo)
        Sigma pi rho hneq
        A hApi hArho

  four_noncoplanar := by
    rcases
        Hilbert4DHyperplaneLocal3DIncidence.four_noncoplanar_on_hyperplane
          (Geo := Geo)
          Sigma with
      ⟨A, B, C, D,
       hASigma, hBSigma, hCSigma, hDSigma,
       hAmbientNoncoplanar⟩

    let A' : HyperplanePoint4 Geo Sigma :=
      ⟨A, hASigma⟩

    let B' : HyperplanePoint4 Geo Sigma :=
      ⟨B, hBSigma⟩

    let C' : HyperplanePoint4 Geo Sigma :=
      ⟨C, hCSigma⟩

    let D' : HyperplanePoint4 Geo Sigma :=
      ⟨D, hDSigma⟩

    refine
      ⟨A', B', C', D', ?_⟩

    intro hInternalCoplanar

    exact
      hAmbientNoncoplanar
        (hyperplaneGeo4_coplanar4_to_ambient_corrected
          (Geo := Geo)
          Sigma
          A' B' C' D'
          hInternalCoplanar)



end Geometry


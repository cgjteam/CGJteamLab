import CGJteamLab.Hilbert3DAxioms
import CGJteamLab.HilbertGrundlagen
import CGJteamLab.HilbertInterface

namespace Geometry

universe u

/- Hilbert3DInterface XI.4 order bridge: single universe declaration. -/

variable (Geo : Geometry.Geo)

/-!
# Hilbert 3D interface

Derived interface for the spatial Hilbert development.

AXIOM BOUNDARY

All primitive spatial assumptions are declared in
`CGJteamLab.Hilbert3DAxioms`.

This file is intended to contain definitions, derived theorems, induced
plane geometries, and bridge instances only.  It must not introduce new
geometric axioms or classes whose fields add assumptions beyond those
declared in `Hilbert3DAxioms.lean`.

The adequacy of the chosen representation is not assumed.  It will be
tested downstream by formal derivations of Euclid Book XI, plane
reflections, Coxeter A3, and later higher-dimensional constructions.
-/

/-!
# Elementary spatial incidence consequences

The lemmas below use no axioms beyond the existing planar incidence
axioms and `HilbertSpaceIncidence`.
-/

/--
Every plane has a point outside it.

This is an immediate consequence of Hilbert I.8: if all four points
from I.8 lay in the given plane, they would be coplanar.
-/
theorem hilbert_point_off_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane) :
    exists P : Geo.Point,
      Not (S.OnPlane P pi) := by
  rcases
      HilbertSpaceIncidence.four_noncoplanar (Geo := Geo) with
    ⟨A, B, C, D, hNoncoplanar⟩
  by_cases hA : S.OnPlane A pi
  · by_cases hB : S.OnPlane B pi
    · by_cases hC : S.OnPlane C pi
      · by_cases hD : S.OnPlane D pi
        · exact False.elim
            (hNoncoplanar ⟨pi, hA, hB, hC, hD⟩)
        · exact ⟨D, hD⟩
      · exact ⟨C, hC⟩
    · exact ⟨B, hB⟩
  · exact ⟨A, hA⟩


/--
If `A` and `B` are distinct points of a line `l`, then every point
primitive-collinear with `A` and `B` lies on `l`.

This is the direct uniqueness-of-line consequence of Hilbert I.2.
-/
theorem hilbert_on_line_of_primCollinear_with_two_on_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    {A B X : Geo.Point}
    (hAB : Ne A B)
    {l : Geo.Line}
    (hAl : H.OnLine A l)
    (hBl : H.OnLine B l)
    (hCol : PrimCollinear Geo A B X) :
    H.OnLine X l := by
  rcases hCol with ⟨m, hAm, hBm, hXm⟩
  have hlm : l = m :=
    HilbertPlaneIncidence.line_unique
      A B hAB l m hAl hBl hAm hBm
  rw [hlm]
  exact hXm


/--
Two distinct planes having a common point intersect in exactly one line.

More precisely, the theorem produces a line `l` such that a point lies
in both planes if and only if it lies on `l`.
-/
theorem hilbert_plane_intersection_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi rho : S.Plane)
    (hneq : Ne pi rho)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hArho : S.OnPlane A rho) :
    exists l : Geo.Line,
      H.OnLine A l /\
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo l rho /\
      forall X : Geo.Point,
        (S.OnPlane X pi /\ S.OnPlane X rho) <->
        H.OnLine X l := by
  rcases
      HilbertSpaceIncidence.plane_second_common_point
        (Geo := Geo) pi rho hneq A hApi hArho with
    ⟨B, hBA, hBpi, hBrho⟩
  have hAB : Ne A B := hBA.symm
  rcases HilbertPlaneIncidence.line_through A B hAB with
    ⟨l, hAl, hBl⟩
  have hlpi : HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B hAB l hAl hBl pi hApi hBpi
  have hlrho : HilbertLineInPlane Geo l rho :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B hAB l hAl hBl rho hArho hBrho
  refine ⟨l, hAl, hlpi, hlrho, ?_⟩
  intro X
  constructor
  · rintro ⟨hXpi, hXrho⟩
    by_contra hXl
    have hNoncol : Not (PrimCollinear Geo A B X) := by
      intro hCol
      exact hXl
        (hilbert_on_line_of_primCollinear_with_two_on_line
          (Geo := Geo) hAB hAl hBl hCol)
    have hpirho : pi = rho :=
      HilbertSpaceIncidence.plane_unique
        (Geo := Geo)
        A B X hNoncol
        pi rho
        hApi hBpi hXpi
        hArho hBrho hXrho
    exact hneq hpirho
  · intro hXl
    exact ⟨hlpi X hXl, hlrho X hXl⟩


/--
A line together with a point outside it determines a unique plane.

This is Hilbert's first basic spatial incidence theorem.  Existence uses
the line clause of I.3, I.4 and I.6.  Uniqueness uses I.5.
-/
theorem hilbert_plane_through_line_and_external_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (l : Geo.Line)
    (P : Geo.Point)
    (hPl : Not (H.OnLine P l)) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo l pi /\
      S.OnPlane P pi /\
      forall rho : S.Plane,
        HilbertLineInPlane Geo l rho ->
        S.OnPlane P rho ->
        rho = pi := by
  rcases
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo) l with
    ⟨A, B, hAB, hAl, hBl⟩

  have hABP : Not (PrimCollinear Geo A B P) := by
    intro hCol
    have hPOnLine : H.OnLine P l :=
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo) hAB hAl hBl hCol
    exact hPl hPOnLine

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo) A B P hABP with
    ⟨pi, hApi, hBpi, hPpi⟩

  have hlpi : HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B hAB l hAl hBl pi hApi hBpi

  refine ⟨pi, hlpi, hPpi, ?_⟩
  intro rho hlrho hPrho

  have hArho : S.OnPlane A rho :=
    hlrho A hAl
  have hBrho : S.OnPlane B rho :=
    hlrho B hBl

  exact
    HilbertSpaceIncidence.plane_unique
      (Geo := Geo)
      A B P hABP
      rho pi
      hArho hBrho hPrho
      hApi hBpi hPpi


/--
Given a point on a line, there is another distinct point on that line.

This is the directly usable form of the line clause of Hilbert I.3.
-/
theorem hilbert_other_point_on_line
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (l : Geo.Line)
    (P : Geo.Point) :
    exists Q : Geo.Point,
      Ne Q P /\
      H.OnLine Q l := by
  rcases
      HilbertSpaceIncidence.two_points_on_each_line
        (Geo := Geo) l with
    ⟨A, B, hAB, hAl, hBl⟩
  by_cases hAP : A = P
  · subst A
    exact ⟨B, hAB.symm, hBl⟩
  · exact ⟨A, hAP, hAl⟩


/--
Two distinct intersecting lines determine a unique plane.

This is Hilbert's second basic spatial incidence theorem.
-/
theorem hilbert_plane_through_two_intersecting_lines
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (l m : Geo.Line)
    (hlm : Ne l m)
    (P : Geo.Point)
    (hPl : H.OnLine P l)
    (hPm : H.OnLine P m) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo l pi /\
      HilbertLineInPlane Geo m pi /\
      forall rho : S.Plane,
        HilbertLineInPlane Geo l rho ->
        HilbertLineInPlane Geo m rho ->
        rho = pi := by
  rcases hilbert_other_point_on_line
      (Geo := Geo) l P with
    ⟨A, hAP, hAl⟩
  rcases hilbert_other_point_on_line
      (Geo := Geo) m P with
    ⟨B, hBP, hBm⟩

  have hAPB : Not (PrimCollinear Geo A P B) := by
    intro hCol
    rcases hCol with ⟨n, hAn, hPn, hBn⟩
    have hln : l = n :=
      HilbertPlaneIncidence.line_unique
        A P hAP l n hAl hPl hAn hPn
    have hmn : m = n :=
      HilbertPlaneIncidence.line_unique
        B P hBP m n hBm hPm hBn hPn
    exact hlm (hln.trans hmn.symm)

  rcases
      HilbertSpaceIncidence.plane_through
        (Geo := Geo) A P B hAPB with
    ⟨pi, hApi, hPpi, hBpi⟩

  have hlpi : HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A P hAP l hAl hPl pi hApi hPpi

  have hmpi : HilbertLineInPlane Geo m pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      B P hBP m hBm hPm pi hBpi hPpi

  refine ⟨pi, hlpi, hmpi, ?_⟩
  intro rho hlrho hmrho

  have hArho : S.OnPlane A rho := hlrho A hAl
  have hPrho : S.OnPlane P rho := hlrho P hPl
  have hBrho : S.OnPlane B rho := hmrho B hBm

  exact
    HilbertSpaceIncidence.plane_unique
      (Geo := Geo)
      A P B hAPB
      rho pi
      hArho hPrho hBrho
      hApi hPpi hBpi

/--
Two ambient spatial lines are parallel when they are coplanar and
disjoint.

The coplanarity clause is essential: ambient disjointness alone would
also classify skew lines as parallel.
-/
def HilbertSpaceLinesParallel
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l m : Geo.Line) : Prop :=
  exists sigma : S.Plane,
    HilbertLineInPlane Geo l sigma /\
    HilbertLineInPlane Geo m sigma /\
    HilbertLinesDisjoint Geo l m


/-!
# Plane slice interface
-/


variable (Geo : Geometry.Geo)

/-!
# A plane as an internal incidence geometry

This file does not yet construct a full `Geometry.Geo`.
It only isolates the correct point and line carriers of one ambient plane
and proves the incidence part of Hilbert I.1-I.3 for them.
-/

/-- Points of the fixed ambient plane `pi`. -/
def PlanePoint
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane) :=
  {P : Geo.Point // S.OnPlane P pi}

/-- Ambient lines wholly contained in the fixed plane `pi`. -/
def PlaneLine
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane) :=
  {l : Geo.Line // HilbertLineInPlane Geo l pi}

/-- Incidence inside a fixed plane. -/
def PlaneOnLine
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {pi : S.Plane}
    (P : PlanePoint Geo pi)
    (l : PlaneLine Geo pi) : Prop :=
  H.OnLine P.1 l.1


/--
Two distinct points of a fixed plane determine a line contained in that
plane.
-/
theorem planePoint_line_through
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (A B : PlanePoint Geo pi)
    (hAB : Ne A B) :
    exists l : PlaneLine Geo pi,
      PlaneOnLine Geo A l /\
      PlaneOnLine Geo B l := by
  have hABval : Ne A.1 B.1 := by
    intro h
    apply hAB
    exact Subtype.ext h

  rcases HilbertPlaneIncidence.line_through
      (Geo := Geo) A.1 B.1 hABval with
    ⟨l, hAl, hBl⟩

  have hlpi : HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A.1 B.1 hABval
      l hAl hBl pi
      A.2 B.2

  exact ⟨⟨l, hlpi⟩, hAl, hBl⟩


/--
The line through two distinct points of a fixed plane is unique.
-/
theorem planePoint_line_unique
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (A B : PlanePoint Geo pi)
    (hAB : Ne A B)
    (l m : PlaneLine Geo pi)
    (hAl : PlaneOnLine Geo A l)
    (hBl : PlaneOnLine Geo B l)
    (hAm : PlaneOnLine Geo A m)
    (hBm : PlaneOnLine Geo B m) :
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
Every ambient plane contains three noncollinear points.

This is derived from Hilbert's original spatial incidence axioms.
It is deliberately not an axiom in `Hilbert3DAxioms.lean`.
-/
theorem hilbert_three_noncollinear_on_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane) :
    exists A B C : Geo.Point,
      S.OnPlane A pi /\
      S.OnPlane B pi /\
      S.OnPlane C pi /\
      Not (PrimCollinear Geo A B C) := by
  rcases
      HilbertSpaceIncidence.point_on_each_plane
        (Geo := Geo) pi with
    ⟨A, hApi⟩

  rcases hilbert_point_off_plane
      (Geo := Geo) pi with
    ⟨P, hPpi⟩

  have hAP : Ne A P := by
    intro h
    subst P
    exact hPpi hApi

  rcases HilbertPlaneIncidence.line_through
      (Geo := Geo) A P hAP with
    ⟨l, hAl, hPl⟩

  rcases hilbert_point_off_line
      (Geo := Geo) l with
    ⟨Q, hQl⟩

  rcases hilbert_plane_through_line_and_external_point
      (Geo := Geo) l Q hQl with
    ⟨beta, hlbeta, _hQbeta, _hBetaUnique⟩

  have hAbeta : S.OnPlane A beta := hlbeta A hAl
  have hPbeta : S.OnPlane P beta := hlbeta P hPl

  have hPiBeta : Ne pi beta := by
    intro h
    subst beta
    exact hPpi hPbeta

  rcases
      HilbertSpaceIncidence.plane_second_common_point
        (Geo := Geo) pi beta hPiBeta A hApi hAbeta with
    ⟨B, hBA, hBpi, hBbeta⟩

  rcases hilbert_point_off_plane
      (Geo := Geo) beta with
    ⟨R, hRbeta⟩

  have hRl : Not (H.OnLine R l) := by
    intro hRl
    exact hRbeta (hlbeta R hRl)

  rcases hilbert_plane_through_line_and_external_point
      (Geo := Geo) l R hRl with
    ⟨gamma, hlgamma, hRgamma, _hGammaUnique⟩

  have hAgamma : S.OnPlane A gamma := hlgamma A hAl
  have hPgamma : S.OnPlane P gamma := hlgamma P hPl

  have hBetaGamma : Ne beta gamma := by
    intro h
    subst gamma
    exact hRbeta hRgamma

  have hPiGamma : Ne pi gamma := by
    intro h
    subst gamma
    exact hPpi hPgamma

  rcases
      HilbertSpaceIncidence.plane_second_common_point
        (Geo := Geo) pi gamma hPiGamma A hApi hAgamma with
    ⟨C, hCA, hCpi, hCgamma⟩

  refine ⟨A, B, C, hApi, hBpi, hCpi, ?_⟩
  intro hABC

  rcases hABC with ⟨m, hAm, hBm, hCm⟩

  have hAB : Ne A B := hBA.symm

  have hmbeta : HilbertLineInPlane Geo m beta :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A B hAB
      m hAm hBm
      beta hAbeta hBbeta

  have hCbeta : S.OnPlane C beta :=
    hmbeta C hCm

  have hAPC : Not (PrimCollinear Geo A P C) := by
    intro hCol
    rcases hCol with ⟨n, hAn, hPn, hCn⟩

    have hAC : Ne A C := hCA.symm

    have hnpi : HilbertLineInPlane Geo n pi :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        A C hAC
        n hAn hCn
        pi hApi hCpi

    exact hPpi (hnpi P hPn)

  have hBetaEqGamma : beta = gamma :=
    HilbertSpaceIncidence.plane_unique
      (Geo := Geo)
      A P C hAPC
      beta gamma
      hAbeta hPbeta hCbeta
      hAgamma hPgamma hCgamma

  exact hBetaGamma hBetaEqGamma


/--
Every fixed plane contains three ambiently noncollinear plane-points.
-/
theorem planePoint_three_noncollinear
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane) :
    exists A B C : PlanePoint Geo pi,
      Not (PrimCollinear Geo A.1 B.1 C.1) := by
  rcases hilbert_three_noncollinear_on_plane
      (Geo := Geo) pi with
    ⟨A, B, C, hApi, hBpi, hCpi, hABC⟩

  exact
    ⟨⟨A, hApi⟩, ⟨B, hBpi⟩, ⟨C, hCpi⟩, hABC⟩

/-!
# Induced geometry of a plane
-/


variable (Geo : Geometry.Geo)

/-!
# The induced geometry of one ambient plane

This file constructs the raw `Geometry.Geo` carried by one plane.
No Hilbert axiom instance is asserted yet.
-/

/--
Map an unordered pair along a function.

This is the functorial map induced from the quotient representation of
`UnorderedPair`.
-/
def mapUnorderedPair
    {alpha beta : Type u}
    (f : alpha -> beta) :
    UnorderedPair alpha -> UnorderedPair beta :=
  Quotient.map
    (fun p : alpha × alpha => (f p.1, f p.2))
    (by
      intro a b hab
      cases hab with
      | direct x y =>
          exact UnorderedPairRel.direct (f x) (f y)
      | swapped x y =>
          exact UnorderedPairRel.swapped (f x) (f y))


theorem mapUnorderedPair_mk
    {alpha beta : Type u}
    (f : alpha -> beta)
    (a b : alpha) :
    mapUnorderedPair f (UnorderedPair.mk a b) =
      UnorderedPair.mk (f a) (f b) := by
  rfl


/--
Forget the proof that a plane-point lies in the plane, pointwise on a set.
-/
def planePointSetToAmbient
    [S : HilbertSpacePrimitive Geo]
    {pi : S.Plane}
    (U : Set (PlanePoint Geo pi)) :
    Set Geo.Point :=
  Subtype.val '' U


/--
The raw geometry induced on one ambient plane.

Points are ambient points lying in the plane.
Lines are ambient lines wholly contained in the plane.
Betweenness and segment congruence are inherited from the ambient geometry.

For the primitive angle relation, rays are sent to their ambient point
sets by forgetting the plane-membership proofs.
-/
def PlaneGeo
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane) :
    Geometry.Geo where

  Point :=
    PlanePoint Geo pi

  Line :=
    PlaneLine Geo pi

  OnLine :=
    fun P l => PlaneOnLine Geo P l

  Between :=
    fun A B C =>
      Geo.Between A.1 B.1 C.1

  SegmentCongruent :=
    fun s t =>
      Geo.SegmentCongruent
        (mapUnorderedPair
          (fun P : PlanePoint Geo pi => P.1) s)
        (mapUnorderedPair
          (fun P : PlanePoint Geo pi => P.1) t)

  UnorientedAngleCongruent :=
    fun a b =>
      Relation.EqvGen Geo.UnorientedAngleCongruent
        ( a.1.1,
          mapUnorderedPair
            (planePointSetToAmbient (Geo := Geo) (pi := pi))
            a.2 )
        ( b.1.1,
          mapUnorderedPair
            (planePointSetToAmbient (Geo := Geo) (pi := pi))
            b.2 )


/--
Betweenness in the induced plane geometry is literally ambient
betweenness of the underlying points.
-/
theorem planeGeo_between
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (A B C : PlanePoint Geo pi) :
    (PlaneGeo Geo pi).Between A B C <->
      Geo.Between A.1 B.1 C.1 := by
  rfl


/--
Segment congruence in the induced plane geometry is literally ambient
segment congruence of the underlying endpoints.
-/
theorem planeGeo_congruent
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (A B C D : PlanePoint Geo pi) :
    (PlaneGeo Geo pi).Congruent A B C D <->
      Geo.Congruent A.1 B.1 C.1 D.1 := by
  rfl


/-!
# Incidence instances for the induced plane geometry

The raw `PlaneGeo` is now promoted to the existing Hilbert incidence API.
No new geometric axiom is introduced here: the instances are derived
from ambient line incidence together with spatial incidence I.3-I.8.
-/

/--
Point-line incidence in `PlaneGeo pi` is the inherited ambient incidence.
-/
instance planeGeoHilbertIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane) :
    HilbertIncidence (PlaneGeo Geo pi) where
  OnLine :=
    fun P l => PlaneOnLine Geo P l


/--
Collinearity inside a plane implies ambient collinearity of the
underlying points.
-/
theorem planeGeo_primCollinear_to_ambient
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (A B C : PlanePoint Geo pi) :
    PrimCollinear (PlaneGeo Geo pi) A B C ->
      PrimCollinear Geo A.1 B.1 C.1 := by
  rintro ⟨l, hAl, hBl, hCl⟩
  exact ⟨l.1, hAl, hBl, hCl⟩


/--
Every induced plane geometry satisfies Hilbert I.1-I.3.

This is derived, not assumed:
* I.1 comes from ambient I.1 plus spatial I.6;
* I.2 comes from ambient I.2;
* the existence clauses of I.3 come from the spatial form of I.3.
-/
instance planeGeoHilbertPlaneIncidence
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane) :
    HilbertPlaneIncidence (PlaneGeo Geo pi) where

  line_through := by
    intro A B hAB
    exact planePoint_line_through
      (Geo := Geo) pi A B hAB

  line_unique := by
    intro A B hAB l m hAl hBl hAm hBm
    exact planePoint_line_unique
      (Geo := Geo) pi A B hAB
      l m hAl hBl hAm hBm

  two_points_on_line := by
    rcases planePoint_three_noncollinear
        (Geo := Geo) pi with
      ⟨A, B, C, hABC⟩

    have hABval : Ne A.1 B.1 :=
      hilbert_noncollinear_ne_first
        Geo A.1 B.1 C.1 hABC

    have hAB : Ne A B := by
      intro h
      apply hABval
      exact congrArg Subtype.val h

    rcases planePoint_line_through
        (Geo := Geo) pi A B hAB with
      ⟨l, hAl, hBl⟩

    exact ⟨l, A, B, hAB, hAl, hBl⟩

  three_noncollinear := by
    rcases planePoint_three_noncollinear
        (Geo := Geo) pi with
      ⟨A, B, C, hABC⟩

    refine ⟨A, B, C, ?_⟩
    intro hCol
    exact hABC
      (planeGeo_primCollinear_to_ambient
        (Geo := Geo) pi A B C hCol)

/-!
# Order inherited by a fixed plane

This section is the first test of the spatial Group II representation.

The ambient space is assumed only to satisfy `HilbertSpaceOrder`.
For a fixed plane `pi`, the induced geometry `PlaneGeo Geo pi` then
satisfies the existing planar `HilbertOrder` interface.

In particular, planar Pasch is not assumed globally in the ambient
space.  It is obtained by specializing `HilbertSpaceOrder.pasch_in_plane`
to `pi`.
-/

/--
An ambient collinearity of three points of `pi` becomes collinearity in
`PlaneGeo pi` as soon as two of the points are known to be distinct.

The distinct pair determines the ambient carrier line, and Hilbert I.6
puts that whole carrier into `pi`.
-/
theorem planeGeo_primCollinear_of_ambient_of_ne
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (A B C : PlanePoint Geo pi)
    (hAB : Ne A.1 B.1)
    (hCol : PrimCollinear Geo A.1 B.1 C.1) :
    PrimCollinear (PlaneGeo Geo pi) A B C := by
  rcases hCol with
    ⟨l, hAl, hBl, hCl⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      A.1 B.1 hAB
      l hAl hBl
      pi A.2 B.2

  exact
    ⟨⟨l, hlpi⟩, hAl, hBl, hCl⟩


/--
A segment of two plane-points meets a plane-line in `PlaneGeo pi` iff
the corresponding ambient segment meets the corresponding ambient line.

For the ambient-to-plane direction the intersection point belongs to
`pi` because the line itself is contained in `pi`.
-/
theorem planeGeo_segmentMeetsLine_iff_ambient
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (A B : PlanePoint Geo pi)
    (l : PlaneLine Geo pi) :
    HilbertSegmentMeetsLine
        (PlaneGeo Geo pi) A B l <->
      HilbertSegmentMeetsLine
        Geo A.1 B.1 l.1 := by
  constructor

  · rintro ⟨X, hAXB, hXl⟩
    exact
      ⟨X.1, hAXB, hXl⟩

  · rintro ⟨X, hAXB, hXl⟩

    have hXpi :
        S.OnPlane X pi :=
      l.2 X hXl

    exact
      ⟨⟨X, hXpi⟩, hAXB, hXl⟩


/--
Every fixed ambient plane inherits the existing planar Hilbert order
interface from the spatial Group II representation.

No ambient `HilbertOrder Geo` instance is used or created here.
-/
instance planeGeoHilbertOrder
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane) :
    HilbertOrder (PlaneGeo Geo pi) where

  between_incidence := by
    intro A B C hABC

    have hData :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        A.1 B.1 C.1 hABC

    rcases hData with
      ⟨hAB, hBC, hAC, hCol, hCBA⟩

    have hABplane : Ne A B := by
      intro h
      exact hAB (congrArg Subtype.val h)

    have hBCplane : Ne B C := by
      intro h
      exact hBC (congrArg Subtype.val h)

    have hACplane : Ne A C := by
      intro h
      exact hAC (congrArg Subtype.val h)

    have hColPlane :
        PrimCollinear
          (PlaneGeo Geo pi) A B C :=
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        pi A B C hAB hCol

    exact
      ⟨hABplane,
       hBCplane,
       hACplane,
       hColPlane,
       hCBA⟩

  between_extension := by
    intro A C hAC

    have hACval : Ne A.1 C.1 := by
      intro h
      apply hAC
      exact Subtype.ext h

    rcases
        HilbertSpaceOrder.between_extension
          (Geo := Geo)
          A.1 C.1 hACval with
      ⟨B, hACB⟩

    have hData :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        A.1 C.1 B hACB

    rcases hData with
      ⟨_hAC, _hCB, _hAB, hCol, _hBCA⟩

    rcases hCol with
      ⟨l, hAl, hCl, hBl⟩

    have hlpi :
        HilbertLineInPlane Geo l pi :=
      HilbertSpaceIncidence.line_in_plane
        (Geo := Geo)
        A.1 C.1 hACval
        l hAl hCl
        pi A.2 C.2

    have hBpi :
        S.OnPlane B pi :=
      hlpi B hBl

    exact
      ⟨⟨B, hBpi⟩, hACB⟩

  between_unique := by
    intro A B C hCol hABC

    have hColAmbient :
        PrimCollinear Geo A.1 B.1 C.1 :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi A B C hCol

    exact
      HilbertSpaceOrder.between_unique
        (Geo := Geo)
        A.1 B.1 C.1
        hColAmbient
        hABC

  pasch := by
    intro A B C hABC l
      hAl hBl hCl hABmeet

    have hABplane : Ne A B :=
      hilbert_noncollinear_ne_first
        (PlaneGeo Geo pi)
        A B C hABC

    have hAB : Ne A.1 B.1 := by
      intro h
      apply hABplane
      exact Subtype.ext h

    have hABCAmbient :
        Not (PrimCollinear Geo A.1 B.1 C.1) := by
      intro hCol
      exact hABC
        (planeGeo_primCollinear_of_ambient_of_ne
          (Geo := Geo)
          pi A B C hAB hCol)

    have hABmeetAmbient :
        HilbertSegmentMeetsLine
          Geo A.1 B.1 l.1 :=
      (planeGeo_segmentMeetsLine_iff_ambient
        (Geo := Geo)
        pi A B l).mp hABmeet

    have hPasch :=
      HilbertSpaceOrder.pasch_in_plane
        (Geo := Geo)
        pi
        A.1 B.1 C.1
        A.2 B.2 C.2
        hABCAmbient
        l.1 l.2
        hAl hBl hCl
        hABmeetAmbient

    rcases hPasch with hACmeet | hBCmeet

    · exact Or.inl
        ((planeGeo_segmentMeetsLine_iff_ambient
          (Geo := Geo)
          pi A C l).mpr hACmeet)

    · exact Or.inr
        ((planeGeo_segmentMeetsLine_iff_ambient
          (Geo := Geo)
          pi B C l).mpr hBCmeet)

/-!
# Ray bridge: elementary same-direction step

Before comparing whole rays, we first identify the generating relation.
Since betweenness in `PlaneGeo pi` is ambient betweenness on the
underlying points, the only work is transporting equality and
inequality through the subtype.
-/

/--
The elementary same-direction relation in a fixed plane is exactly the
ambient same-direction relation on the underlying points.
-/
theorem planeGeo_sameDirectionStep_iff_ambient
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (O P Q : PlanePoint Geo pi) :
    (PlaneGeo Geo pi).SameDirectionStep O P Q <->
      Geo.SameDirectionStep O.1 P.1 Q.1 := by

  unfold Geometry.Geo.SameDirectionStep

  constructor

  · rintro ⟨hPO, hQO, hCases⟩

    have hPOval : Ne P.1 O.1 := by
      intro h
      apply hPO
      exact Subtype.ext h

    have hQOval : Ne Q.1 O.1 := by
      intro h
      apply hQO
      exact Subtype.ext h

    rcases hCases with hPQ | hOPQ | hOQP

    · exact
        ⟨hPOval,
         hQOval,
         Or.inl (congrArg Subtype.val hPQ)⟩

    · exact
        ⟨hPOval,
         hQOval,
         Or.inr (Or.inl hOPQ)⟩

    · exact
        ⟨hPOval,
         hQOval,
         Or.inr (Or.inr hOQP)⟩

  · rintro ⟨hPO, hQO, hCases⟩

    have hPOplane : Ne P O := by
      intro h
      exact hPO (congrArg Subtype.val h)

    have hQOplane : Ne Q O := by
      intro h
      exact hQO (congrArg Subtype.val h)

    rcases hCases with hPQ | hOPQ | hOQP

    · exact
        ⟨hPOplane,
         hQOplane,
         Or.inl (Subtype.ext hPQ)⟩

    · exact
        ⟨hPOplane,
         hQOplane,
         Or.inr (Or.inl hOPQ)⟩

    · exact
        ⟨hPOplane,
         hQOplane,
         Or.inr (Or.inr hOQP)⟩

/-!
# Ray bridge: plane preservation

For the reverse direction of the ray bridge we must know that an ambient
same-direction chain beginning with a point of `pi` remains in `pi`.

This is a consequence of:
* Hilbert II.1: betweenness implies collinearity;
* Hilbert I.1: the line through two distinct points exists;
* Hilbert I.6: if two points of a line lie in a plane, the whole line
  lies in that plane.
-/

/--
If `O` and `P` are distinct points of `pi`, then every ambient point
collinear with them also belongs to `pi`.
-/
theorem hilbert_onPlane_of_primCollinear_with_two_on_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (O P Q : Geo.Point)
    (hOP : Ne O P)
    (hOpi : S.OnPlane O pi)
    (hPpi : S.OnPlane P pi)
    (hCol : PrimCollinear Geo O P Q) :
    S.OnPlane Q pi := by

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo) O P hOP with
    ⟨l, hOl, hPl⟩

  have hlpi :
      HilbertLineInPlane Geo l pi :=
    HilbertSpaceIncidence.line_in_plane
      (Geo := Geo)
      O P hOP
      l hOl hPl
      pi hOpi hPpi

  have hQl :
      H.OnLine Q l :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hOP
      hOl hPl
      hCol

  exact hlpi Q hQl


/--
An ambient elementary same-direction step from a point of `pi`, with
origin also in `pi`, stays in `pi`.
-/
theorem hilbert_sameDirectionStep_preserves_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (O P Q : Geo.Point)
    (hOpi : S.OnPlane O pi)
    (hPpi : S.OnPlane P pi)
    (hStep : Geo.SameDirectionStep O P Q) :
    S.OnPlane Q pi := by

  unfold Geometry.Geo.SameDirectionStep at hStep

  rcases hStep with
    ⟨hPO, _hQO, hCases⟩

  have hOP : Ne O P :=
    hPO.symm

  rcases hCases with hPQ | hOPQ | hOQP

  · rw [← hPQ]
    exact hPpi

  · have hCol :
        PrimCollinear Geo O P Q :=
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        O P Q hOPQ).2.2.2.1

    exact
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi O P Q
        hOP hOpi hPpi hCol

  · have hColOQP :
        PrimCollinear Geo O Q P :=
      (HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        O Q P hOQP).2.2.2.1

    have hColOPQ :
        PrimCollinear Geo O P Q :=
      PrimCollinearRotate
        Geo O Q P hColOQP

    exact
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi O P Q
        hOP hOpi hPpi hColOPQ

/-!
# Ray bridge: preservation along a reflexive-transitive chain

The previous lemma handles one `SameDirectionStep`.  We now iterate it
along `Relation.ReflTransGen`.  This is the exact closure property needed
before converting an ambient ray chain into a chain in `PlaneGeo pi`.
-/

/--
Every endpoint of an ambient reflexive-transitive same-direction chain
starting at a point of `pi` remains in `pi`.
-/
theorem hilbert_reflTransGen_sameDirection_preserves_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (O A X : Geo.Point)
    (hOpi : S.OnPlane O pi)
    (hApi : S.OnPlane A pi)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O)
        A X) :
    S.OnPlane X pi := by

  induction hChain with

  | refl =>
      exact hApi

  | tail hAB hBX ih =>
      exact
        hilbert_sameDirectionStep_preserves_plane
          (Geo := Geo)
          pi
          O _ _
          hOpi
          ih
          hBX

/-!
# Ray bridge: lifting a plane chain to the ambient geometry

A reflexive-transitive chain of same-direction steps in `PlaneGeo pi`
maps directly to the corresponding ambient chain by forgetting subtype
proofs at every vertex.
-/

/--
Every same-direction chain in `PlaneGeo pi` gives the corresponding
ambient same-direction chain on underlying points.
-/
theorem planeGeo_reflTransGen_sameDirection_to_ambient
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (O A X : PlanePoint Geo pi)
    (hChain :
      Relation.ReflTransGen
        ((PlaneGeo Geo pi).SameDirectionStep O)
        A X) :
    Relation.ReflTransGen
      (Geo.SameDirectionStep O.1)
      A.1 X.1 := by

  induction hChain with

  | refl =>
      exact Relation.ReflTransGen.refl

  | tail hAB hBX ih =>
      exact
        Relation.ReflTransGen.tail
          ih
          ((planeGeo_sameDirectionStep_iff_ambient
              (Geo := Geo)
              pi O _ _).mp hBX)

/-!
# Ray bridge: lifting an ambient chain into `PlaneGeo`

The endpoint of an ambient chain is not itself a subtype value.  Instead
of forcing a dependent endpoint during induction, we first construct a
plane-point with the same underlying ambient point and a corresponding
chain in `PlaneGeo pi`.
-/

/--
An ambient reflexive-transitive same-direction chain starting from a
plane-point can be lifted to a chain in `PlaneGeo pi`.

The returned plane-point has exactly the given ambient endpoint as its
underlying point.
-/
theorem planeGeo_exists_reflTransGen_sameDirection_of_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (O A : PlanePoint Geo pi)
    (X : Geo.Point)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X) :
    exists Xp : PlanePoint Geo pi,
      Xp.1 = X /\
      Relation.ReflTransGen
        ((PlaneGeo Geo pi).SameDirectionStep O)
        A Xp := by

  induction hChain with

  | refl =>
      exact
        ⟨A,
         rfl,
         Relation.ReflTransGen.refl⟩

  | @tail B C hAB hBC ih =>

      rcases ih with
        ⟨Bp, hBp, hPlaneAB⟩

      have hBpi :
          S.OnPlane B pi := by
        simpa [hBp] using Bp.2

      have hCpi :
          S.OnPlane C pi :=
        hilbert_sameDirectionStep_preserves_plane
          (Geo := Geo)
          pi
          O.1 B C
          O.2
          hBpi
          hBC

      let Cp : PlanePoint Geo pi :=
        ⟨C, hCpi⟩

      have hPlaneBC :
          (PlaneGeo Geo pi).SameDirectionStep O Bp Cp := by

        apply
          (planeGeo_sameDirectionStep_iff_ambient
            (Geo := Geo)
            pi O Bp Cp).mpr

        simpa [Cp, hBp] using hBC

      exact
        ⟨Cp,
         rfl,
         Relation.ReflTransGen.tail
           hPlaneAB
           hPlaneBC⟩

/-!
# Complete ray bridge

We now package the previous elementary lemmas into the full comparison
between rays in `PlaneGeo pi` and ambient rays.

The sequence is:

1. lift an ambient chain to a chain with a prescribed plane endpoint;
2. identify membership in the two ray predicates;
3. prove every ambient ray determined by two plane-points lies in the plane;
4. identify the image of a plane ray with the ambient ray;
5. identify the mapped plane angle with the ambient angle.
-/

/--
The existential ambient-to-plane chain lift can be specialized to any
already given plane-point endpoint.
-/
theorem planeGeo_reflTransGen_sameDirection_of_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (O A X : PlanePoint Geo pi)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X.1) :
    Relation.ReflTransGen
      ((PlaneGeo Geo pi).SameDirectionStep O)
      A X := by

  rcases
      planeGeo_exists_reflTransGen_sameDirection_of_ambient
        (Geo := Geo)
        pi O A X.1 hChain with
    ⟨Xp, hXpVal, hPlaneChain⟩

  have hXpX : Xp = X := by
    apply Subtype.ext
    exact hXpVal

  simpa [hXpX] using hPlaneChain


/--
Membership in a ray of `PlaneGeo pi` is exactly ambient ray membership
of the underlying point.
-/
theorem planeGeo_mem_ray_iff_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (O A X : PlanePoint Geo pi) :
    X ∈ (PlaneGeo Geo pi).ray O A <->
      X.1 ∈ Geo.ray O.1 A.1 := by

  change
    (X = O \/
      Relation.ReflTransGen
        ((PlaneGeo Geo pi).SameDirectionStep O)
        A X) <->
    (X.1 = O.1 \/
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X.1)

  constructor

  · rintro (hXO | hAX)

    · exact
        Or.inl (congrArg Subtype.val hXO)

    · exact
        Or.inr
          (planeGeo_reflTransGen_sameDirection_to_ambient
            (Geo := Geo)
            pi O A X hAX)

  · rintro (hXO | hAX)

    · exact
        Or.inl (Subtype.ext hXO)

    · exact
        Or.inr
          (planeGeo_reflTransGen_sameDirection_of_ambient
            (Geo := Geo)
            pi O A X hAX)


/--
Every ambient point of the ray determined by two points of `pi`
belongs to `pi`.
-/
theorem hilbert_onPlane_of_mem_ray
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (O A : PlanePoint Geo pi)
    (X : Geo.Point)
    (hX : X ∈ Geo.ray O.1 A.1) :
    S.OnPlane X pi := by

  change
    X = O.1 \/
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X at hX

  rcases hX with hXO | hAX

  · rw [hXO]
    exact O.2

  · exact
      hilbert_reflTransGen_sameDirection_preserves_plane
        (Geo := Geo)
        pi
        O.1 A.1 X
        O.2 A.2
        hAX


/--
Forgetting plane-membership proofs sends the ray of `PlaneGeo pi`
exactly to the corresponding ambient ray.
-/
theorem planeGeo_ray_to_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (O A : PlanePoint Geo pi) :
    planePointSetToAmbient
        (Geo := Geo)
        (pi := pi)
        ((PlaneGeo Geo pi).ray O A) =
      Geo.ray O.1 A.1 := by

  apply Set.ext
  intro X

  constructor

  · rintro ⟨Xp, hXpRay, rfl⟩

    exact
      (planeGeo_mem_ray_iff_ambient
        (Geo := Geo)
        pi O A Xp).mp hXpRay

  · intro hXRay

    have hXpi :
        S.OnPlane X pi :=
      hilbert_onPlane_of_mem_ray
        (Geo := Geo)
        pi O A X hXRay

    let Xp : PlanePoint Geo pi :=
      ⟨X, hXpi⟩

    have hXpRay :
        Xp ∈ (PlaneGeo Geo pi).ray O A := by

      apply
        (planeGeo_mem_ray_iff_ambient
          (Geo := Geo)
          pi O A Xp).mpr

      simpa [Xp] using hXRay

    exact
      ⟨Xp, hXpRay, rfl⟩


/--
The angle of three plane-points, after forgetting the subtype structure
on both rays, is exactly the corresponding ambient angle.
-/
theorem planeGeo_angle_to_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C : PlanePoint (Geo := Geo) (S := S) pi) :
    ( ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).Angle A B C).1.1,
      mapUnorderedPair
        (planePointSetToAmbient (Geo := Geo) (S := S) (pi := pi))
        ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).Angle A B C).2 ) =
      Geo.Angle A.1 B.1 C.1 := by

  change
    ( B.1,
      mapUnorderedPair
        (planePointSetToAmbient (Geo := Geo) (S := S) (pi := pi))
        (UnorderedPair.mk
          ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).ray B A)
          ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).ray B C)) ) =
    ( B.1,
      UnorderedPair.mk
        (Geo.ray B.1 A.1)
        (Geo.ray B.1 C.1) )

  have hMap :
      mapUnorderedPair
          (planePointSetToAmbient (Geo := Geo) (S := S) (pi := pi))
          (UnorderedPair.mk
            ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).ray B A)
            ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).ray B C)) =
        UnorderedPair.mk
          (planePointSetToAmbient
            (Geo := Geo) (S := S) (pi := pi)
            ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).ray B A))
          (planePointSetToAmbient
            (Geo := Geo) (S := S) (pi := pi)
            ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).ray B C)) := by
    exact
      mapUnorderedPair_mk
        (planePointSetToAmbient (Geo := Geo) (S := S) (pi := pi))
        ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).ray B A)
        ((PlaneGeo (Geo := Geo) (H := H) (S := S) pi).ray B C)

  rw [hMap]

  rw [
    planeGeo_ray_to_ambient
      (Geo := Geo)
      pi B A,
    planeGeo_ray_to_ambient
      (Geo := Geo)
      pi B C
  ]

/-!
# Group III bridges: angles, rays, and same-side relation

The ray bridge proved above is now used to compare the derived notions
appearing in Hilbert III.1, III.4, and III.5.

This section contains no new axiom.  It only proves that the notions
used by the old planar API on `PlaneGeo pi` are exactly the restrictions
of the spatial notions to the fixed plane `pi`.
-/

/--
Forget the plane-subtype structure from arbitrary angle data.
-/
def planeGeoAngleToAmbient
    [S : HilbertSpacePrimitive Geo]
    {pi : S.Plane}
    (a :
      PlanePoint Geo pi ×
        UnorderedPair (Set (PlanePoint Geo pi))) :
    Geo.Point × UnorderedPair (Set Geo.Point) :=
  ( a.1.1,
    mapUnorderedPair
      (planePointSetToAmbient (Geo := Geo) (pi := pi))
      a.2 )


/--
The primitive angle relation of `PlaneGeo pi` is, by construction,
ambient angle congruence on the forgotten angle data.
-/
theorem planeGeo_unorientedAngleCongruent_iff_ambient
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (a b :
      PlanePoint Geo pi ×
        UnorderedPair (Set (PlanePoint Geo pi))) :
    (PlaneGeo Geo pi).UnorientedAngleCongruent a b <->
      Relation.EqvGen
        Geo.UnorientedAngleCongruent
        (planeGeoAngleToAmbient
          (Geo := Geo) a)
        (planeGeoAngleToAmbient
          (Geo := Geo) b) := by
  rfl


/--
The generic forgetting map on angle data sends an actual plane angle to
the corresponding ambient angle.
-/
theorem planeGeoAngleToAmbient_angle
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C : PlanePoint Geo pi) :
    planeGeoAngleToAmbient
        (Geo := Geo)
        ((PlaneGeo Geo pi).Angle A B C) =
      Geo.Angle A.1 B.1 C.1 := by
  exact
    planeGeo_angle_to_ambient
      (Geo := Geo)
      pi A B C


/--
Angle congruence in `PlaneGeo pi` implies ambient angle congruence.
-/
theorem planeGeo_angleCongruent_to_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C D E F : PlanePoint Geo pi)
    (h :
      (PlaneGeo Geo pi).AngleCongruent
        A B C D E F) :
    Geo.AngleCongruent
      A.1 B.1 C.1 D.1 E.1 F.1 := by

  unfold Geometry.Geo.AngleCongruent at h ⊢

  have hMap :
      forall
        {x y :
          PlanePoint Geo pi ×
            UnorderedPair (Set (PlanePoint Geo pi))},
        Relation.EqvGen
          (PlaneGeo Geo pi).UnorientedAngleCongruent
          x y ->
        Relation.EqvGen
          Geo.UnorientedAngleCongruent
          (planeGeoAngleToAmbient
            (Geo := Geo) x)
          (planeGeoAngleToAmbient
            (Geo := Geo) y) := by

    intro x y hxy

    induction hxy with

    | rel x y hxy =>
        exact
          (planeGeo_unorientedAngleCongruent_iff_ambient
            (Geo := Geo)
            pi x y).mp hxy

    | refl x =>
        exact
          Relation.EqvGen.refl
            (planeGeoAngleToAmbient
              (Geo := Geo) x)

    | symm x y _hxy ih =>
        exact
          Relation.EqvGen.symm
            (planeGeoAngleToAmbient
              (Geo := Geo) x)
            (planeGeoAngleToAmbient
              (Geo := Geo) y)
            ih

    | trans x y z _hxy _hyz ihxy ihyz =>
        exact
          Relation.EqvGen.trans
            (planeGeoAngleToAmbient
              (Geo := Geo) x)
            (planeGeoAngleToAmbient
              (Geo := Geo) y)
            (planeGeoAngleToAmbient
              (Geo := Geo) z)
            ihxy ihyz

  have hAmbientMapped :=
    hMap h

  rw [
    planeGeoAngleToAmbient_angle
      (Geo := Geo) pi A B C,
    planeGeoAngleToAmbient_angle
      (Geo := Geo) pi D E F
  ] at hAmbientMapped

  exact hAmbientMapped


/--
Ambient angle congruence between two angles lying in `pi` implies angle
congruence in `PlaneGeo pi`.

This direction is short because the primitive relation of `PlaneGeo pi`
was deliberately defined to be the already closed ambient angle
congruence relation.
-/
theorem planeGeo_angleCongruent_of_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C D E F : PlanePoint Geo pi)
    (h :
      Geo.AngleCongruent
        A.1 B.1 C.1 D.1 E.1 F.1) :
    (PlaneGeo Geo pi).AngleCongruent
      A B C D E F := by

  unfold Geometry.Geo.AngleCongruent at h ⊢

  apply
    Relation.EqvGen.rel
      ((PlaneGeo Geo pi).Angle A B C)
      ((PlaneGeo Geo pi).Angle D E F)

  apply
    (planeGeo_unorientedAngleCongruent_iff_ambient
      (Geo := Geo)
      pi
      ((PlaneGeo Geo pi).Angle A B C)
      ((PlaneGeo Geo pi).Angle D E F)).mpr

  rw [
    planeGeoAngleToAmbient_angle
      (Geo := Geo) pi A B C,
    planeGeoAngleToAmbient_angle
      (Geo := Geo) pi D E F
  ]

  exact h


/--
For angles whose points all lie in `pi`, plane angle congruence and
ambient angle congruence are equivalent.
-/
theorem planeGeo_angleCongruent_iff_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A B C D E F : PlanePoint Geo pi) :
    (PlaneGeo Geo pi).AngleCongruent
        A B C D E F <->
      Geo.AngleCongruent
        A.1 B.1 C.1 D.1 E.1 F.1 := by
  constructor

  · exact
      planeGeo_angleCongruent_to_ambient
        (Geo := Geo)
        pi A B C D E F

  · exact
      planeGeo_angleCongruent_of_ambient
        (Geo := Geo)
        pi A B C D E F


/-!
## Same-ray bridge
-/

/--
The Hilbert same-ray predicate inside `PlaneGeo pi` is exactly the
ambient same-ray predicate on underlying points.
-/
theorem planeGeo_sameRay_iff_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (O P Q : PlanePoint Geo pi) :
    HilbertSameRay
        (PlaneGeo Geo pi) O P Q <->
      HilbertSameRay
        Geo O.1 P.1 Q.1 := by

  unfold HilbertSameRay

  constructor

  · rintro
      ⟨hPO, hQO, hCol, hNotBetween⟩

    have hPOval : Ne P.1 O.1 := by
      intro h
      apply hPO
      exact Subtype.ext h

    have hQOval : Ne Q.1 O.1 := by
      intro h
      apply hQO
      exact Subtype.ext h

    have hColAmbient :
        PrimCollinear Geo O.1 P.1 Q.1 :=
      planeGeo_primCollinear_to_ambient
        (Geo := Geo)
        pi O P Q hCol

    exact
      ⟨hPOval,
       hQOval,
       hColAmbient,
       hNotBetween⟩

  · rintro
      ⟨hPO, hQO, hCol, hNotBetween⟩

    have hPOplane : Ne P O := by
      intro h
      exact hPO (congrArg Subtype.val h)

    have hQOplane : Ne Q O := by
      intro h
      exact hQO (congrArg Subtype.val h)

    have hOP : Ne O.1 P.1 :=
      hPO.symm

    have hColPlane :
        PrimCollinear
          (PlaneGeo Geo pi) O P Q :=
      planeGeo_primCollinear_of_ambient_of_ne
        (Geo := Geo)
        pi O P Q
        hOP hCol

    exact
      ⟨hPOplane,
       hQOplane,
       hColPlane,
       hNotBetween⟩


/-!
## Same-side bridge
-/

/--
One same-side step in `PlaneGeo pi` is exactly one explicitly
plane-local same-side step in the ambient spatial language.
-/
theorem planeGeo_sameSideStep_iff_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (P Q : PlanePoint Geo pi)
    (l : PlaneLine Geo pi) :
    HilbertSameSideStep
        (PlaneGeo Geo pi) P Q l <->
      HilbertSameSideStepInPlane
        Geo P.1 Q.1 l.1 pi := by

  unfold HilbertSameSideStep
  unfold HilbertSameSideStepInPlane

  constructor

  · rintro
      ⟨hPl, hQl, hNoMeet⟩

    have hNoMeetAmbient :
        Not
          (HilbertSegmentMeetsLine
            Geo P.1 Q.1 l.1) := by
      intro hMeet
      apply hNoMeet
      exact
        (planeGeo_segmentMeetsLine_iff_ambient
          (Geo := Geo)
          pi P Q l).mpr hMeet

    exact
      ⟨P.2,
       Q.2,
       hPl,
       hQl,
       hNoMeetAmbient⟩

  · rintro
      ⟨_hPpi, _hQpi,
       hPl, hQl, hNoMeetAmbient⟩

    have hNoMeetPlane :
        Not
          (HilbertSegmentMeetsLine
            (PlaneGeo Geo pi) P Q l) := by
      intro hMeet
      apply hNoMeetAmbient
      exact
        (planeGeo_segmentMeetsLine_iff_ambient
          (Geo := Geo)
          pi P Q l).mp hMeet

    exact
      ⟨hPl,
       hQl,
       hNoMeetPlane⟩


/--
A reflexive-transitive same-side chain in `PlaneGeo pi` maps to the
corresponding explicitly plane-local ambient chain.
-/
theorem planeGeo_reflTransGen_sameSideStep_to_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (P Q : PlanePoint Geo pi)
    (l : PlaneLine Geo pi)
    (hChain :
      Relation.ReflTransGen
        (fun X Y =>
          HilbertSameSideStep
            (PlaneGeo Geo pi) X Y l)
        P Q) :
    Relation.ReflTransGen
      (fun X Y =>
        HilbertSameSideStepInPlane
          Geo X Y l.1 pi)
      P.1 Q.1 := by

  induction hChain with

  | refl =>
      exact
        Relation.ReflTransGen.refl

  | tail hAB hBC ih =>
      exact
        Relation.ReflTransGen.tail
          ih
          ((planeGeo_sameSideStep_iff_space
              (Geo := Geo)
              pi _ _ l).mp hBC)


/--
An explicitly plane-local ambient same-side chain starting from a
plane-point lifts to a chain in `PlaneGeo pi`.
-/
theorem planeGeo_exists_reflTransGen_sameSideStep_of_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (P : PlanePoint Geo pi)
    (X : Geo.Point)
    (l : PlaneLine Geo pi)
    (hChain :
      Relation.ReflTransGen
        (fun A B =>
          HilbertSameSideStepInPlane
            Geo A B l.1 pi)
        P.1 X) :
    exists Xp : PlanePoint Geo pi,
      Xp.1 = X /\
      Relation.ReflTransGen
        (fun A B =>
          HilbertSameSideStep
            (PlaneGeo Geo pi) A B l)
        P Xp := by

  induction hChain with

  | refl =>
      exact
        ⟨P,
         rfl,
         Relation.ReflTransGen.refl⟩

  | @tail B C hAB hBC ih =>

      rcases ih with
        ⟨Bp, hBp, hPlaneAB⟩

      have hCpi :
          S.OnPlane C pi := by
        exact hBC.2.1

      let Cp : PlanePoint Geo pi :=
        ⟨C, hCpi⟩

      have hPlaneBC :
          HilbertSameSideStep
            (PlaneGeo Geo pi) Bp Cp l := by

        apply
          (planeGeo_sameSideStep_iff_space
            (Geo := Geo)
            pi Bp Cp l).mpr

        simpa [Cp, hBp] using hBC

      exact
        ⟨Cp,
         rfl,
         Relation.ReflTransGen.tail
           hPlaneAB
           hPlaneBC⟩


/--
The ambient-to-plane same-side chain lift can be specialized to a
prescribed plane-point endpoint.
-/
theorem planeGeo_reflTransGen_sameSideStep_of_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (P Q : PlanePoint Geo pi)
    (l : PlaneLine Geo pi)
    (hChain :
      Relation.ReflTransGen
        (fun A B =>
          HilbertSameSideStepInPlane
            Geo A B l.1 pi)
        P.1 Q.1) :
    Relation.ReflTransGen
      (fun A B =>
        HilbertSameSideStep
          (PlaneGeo Geo pi) A B l)
      P Q := by

  rcases
      planeGeo_exists_reflTransGen_sameSideStep_of_space
        (Geo := Geo)
        pi P Q.1 l hChain with
    ⟨Qp, hQp, hPlaneChain⟩

  have hQpQ : Qp = Q := by
    apply Subtype.ext
    exact hQp

  simpa [hQpQ] using hPlaneChain


/--
Same-side in `PlaneGeo pi` is exactly the explicitly plane-local
same-side relation of the ambient spatial language.
-/
theorem planeGeo_sameSide_iff_space
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (P Q : PlanePoint Geo pi)
    (l : PlaneLine Geo pi) :
    HilbertSameSide
        (PlaneGeo Geo pi) P Q l <->
      HilbertSameSideInPlane
        Geo P.1 Q.1 l.1 pi := by

  unfold HilbertSameSide
  unfold HilbertSameSideInPlane

  constructor

  · rintro
      ⟨hPl, hQl, hChain⟩

    exact
      ⟨P.2,
       Q.2,
       hPl,
       hQl,
       planeGeo_reflTransGen_sameSideStep_to_space
         (Geo := Geo)
         pi P Q l hChain⟩

  · rintro
      ⟨_hPpi, _hQpi,
       hPl, hQl, hChain⟩

    exact
      ⟨hPl,
       hQl,
       planeGeo_reflTransGen_sameSideStep_of_space
         (Geo := Geo)
         pi P Q l hChain⟩

/-!
# The full Hilbert congruence instance on a fixed ambient plane

The three bridges above are now sufficient to recover the complete
existing planar `HilbertCongruence` API on every fixed ambient plane.

No global `HilbertCongruence Geo` instance is introduced.  In
particular, the ambient space does not acquire the planar Pasch axiom.
Instead, the spatial Group III representation is restricted to
`PlaneGeo pi`.
-/

/--
Noncollinearity in `PlaneGeo pi` implies ambient noncollinearity of the
underlying three points.
-/
theorem planeGeo_not_primCollinear_to_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    (pi : S.Plane)
    (A B C : PlanePoint Geo pi)
    (hABC :
      Not
        (PrimCollinear
          (PlaneGeo Geo pi) A B C)) :
    Not (PrimCollinear Geo A.1 B.1 C.1) := by

  have hABplane : Ne A B :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo pi)
      A B C hABC

  have hAB : Ne A.1 B.1 := by
    intro h
    apply hABplane
    exact Subtype.ext h

  intro hCol

  exact hABC
    (planeGeo_primCollinear_of_ambient_of_ne
      (Geo := Geo)
      pi A B C
      hAB hCol)


/--
Every fixed ambient plane inherits the complete planar Hilbert
congruence interface from the spatial Group III representation.
-/
instance planeGeoHilbertCongruence
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane) :
    HilbertCongruence (PlaneGeo Geo pi) where

  toHilbertOrder :=
    planeGeoHilbertOrder
      (Geo := Geo) pi

  segment_construction := by
    intro A B O R hOR

    have hORval : Ne O.1 R.1 := by
      intro h
      apply hOR
      exact Subtype.ext h

    rcases
        HilbertSpaceCongruence.segment_construction
          (Geo := Geo)
          A.1 B.1 O.1 R.1 hORval with
      ⟨X, hSameRayAmbient, hCongAmbient⟩

    have hXpi :
        S.OnPlane X pi :=
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi
        O.1 R.1 X
        hORval
        O.2 R.2
        hSameRayAmbient.2.2.1

    let Xp : PlanePoint Geo pi :=
      ⟨X, hXpi⟩

    have hSameRayPlane :
        HilbertSameRay
          (PlaneGeo Geo pi) O R Xp := by

      apply
        (planeGeo_sameRay_iff_ambient
          (Geo := Geo)
          pi O R Xp).mpr

      simpa [Xp] using hSameRayAmbient

    have hCongPlane :
        (PlaneGeo Geo pi).Congruent
          O Xp A B := by

      apply
        (planeGeo_congruent
          (Geo := Geo)
          pi O Xp A B).mpr

      simpa [Xp] using hCongAmbient

    exact
      ⟨Xp,
       hSameRayPlane,
       hCongPlane⟩


  segment_congruence_common := by
    intro A B A' B' A'' B''
      hCong1 hCong2

    have hCong1Ambient :
        Geo.Congruent
          A.1 B.1 A'.1 B'.1 :=
      (planeGeo_congruent
        (Geo := Geo)
        pi A B A' B').mp hCong1

    have hCong2Ambient :
        Geo.Congruent
          A.1 B.1 A''.1 B''.1 :=
      (planeGeo_congruent
        (Geo := Geo)
        pi A B A'' B'').mp hCong2

    have hResultAmbient :
        Geo.Congruent
          A'.1 B'.1 A''.1 B''.1 :=
      HilbertSpaceCongruence.segment_congruence_common
        (Geo := Geo)
        A.1 B.1
        A'.1 B'.1
        A''.1 B''.1
        hCong1Ambient
        hCong2Ambient

    exact
      (planeGeo_congruent
        (Geo := Geo)
        pi A' B' A'' B'').mpr
        hResultAmbient


  segment_additivity := by
    intro A B C A' B' C'
      hABC hA'B'C'
      hAB hBC

    have hABAmbient :
        Geo.Congruent
          A.1 B.1 A'.1 B'.1 :=
      (planeGeo_congruent
        (Geo := Geo)
        pi A B A' B').mp hAB

    have hBCAmbient :
        Geo.Congruent
          B.1 C.1 B'.1 C'.1 :=
      (planeGeo_congruent
        (Geo := Geo)
        pi B C B' C').mp hBC

    have hResultAmbient :
        Geo.Congruent
          A.1 C.1 A'.1 C'.1 :=
      HilbertSpaceCongruence.segment_additivity
        (Geo := Geo)
        A.1 B.1 C.1
        A'.1 B'.1 C'.1
        hABC hA'B'C'
        hABAmbient
        hBCAmbient

    exact
      (planeGeo_congruent
        (Geo := Geo)
        pi A C A' C').mpr
        hResultAmbient


  angle_construction := by
    intro A B C A' B' T
      hABC hA'B'
      l hA'l hB'l hTl

    have hABCAmbient :
        Not
          (PrimCollinear
            Geo A.1 B.1 C.1) :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        pi A B C hABC

    have hA'B'val :
        Ne A'.1 B'.1 := by
      intro h
      apply hA'B'
      exact Subtype.ext h

    rcases
        HilbertSpaceCongruence.angle_construction_in_plane
          (Geo := Geo)
          A.1 B.1 C.1
          A'.1 B'.1 T.1
          hABCAmbient
          hA'B'val
          pi
          l.1
          l.2
          hA'l
          hB'l
          T.2
          hTl with
      ⟨C0,
       hSameSideAmbient,
       hAngleAmbient,
       hUniqueAmbient⟩

    have hC0pi :
        S.OnPlane C0 pi :=
      hSameSideAmbient.1

    let C0p : PlanePoint Geo pi :=
      ⟨C0, hC0pi⟩

    have hSameSidePlane :
        HilbertSameSide
          (PlaneGeo Geo pi)
          C0p T l := by

      apply
        (planeGeo_sameSide_iff_space
          (Geo := Geo)
          pi C0p T l).mpr

      simpa [C0p] using hSameSideAmbient

    have hAnglePlane :
        (PlaneGeo Geo pi).AngleCongruent
          A B C A' B' C0p := by

      apply
        (planeGeo_angleCongruent_iff_ambient
          (Geo := Geo)
          pi A B C A' B' C0p).mpr

      simpa [C0p] using hAngleAmbient

    refine
      ⟨C0p,
       hSameSidePlane,
       hAnglePlane,
       ?_⟩

    intro D'
      hSameSideDPlane
      hAngleDPlane

    have hSameSideDAmbient :
        HilbertSameSideInPlane
          Geo D'.1 T.1 l.1 pi :=
      (planeGeo_sameSide_iff_space
        (Geo := Geo)
        pi D' T l).mp
        hSameSideDPlane

    have hAngleDAmbient :
        Geo.AngleCongruent
          A.1 B.1 C.1
          A'.1 B'.1 D'.1 :=
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        pi A B C A' B' D').mp
        hAngleDPlane

    have hSameRayAmbient :
        HilbertSameRay
          Geo B'.1 C0 D'.1 :=
      hUniqueAmbient
        D'.1
        hSameSideDAmbient
        hAngleDAmbient

    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        pi B' C0p D').mpr

    simpa [C0p] using hSameRayAmbient


  angle_congruence_reflexive := by
    intro A B C hABC

    have hABCAmbient :
        Not
          (PrimCollinear
            Geo A.1 B.1 C.1) :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        pi A B C hABC

    have hAmbient :
        Geo.AngleCongruent
          A.1 B.1 C.1
          A.1 B.1 C.1 :=
      HilbertSpaceCongruence.angle_congruence_reflexive
        (Geo := Geo)
        A.1 B.1 C.1
        hABCAmbient

    exact
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        pi A B C A B C).mpr
        hAmbient


  sas := by
    intro A B C A' B' C'
      hABC hA'B'C'
      hAB hAC hAngle

    have hABCAmbient :
        Not
          (PrimCollinear
            Geo A.1 B.1 C.1) :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        pi A B C hABC

    have hA'B'C'Ambient :
        Not
          (PrimCollinear
            Geo A'.1 B'.1 C'.1) :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        pi A' B' C' hA'B'C'

    have hABAmbient :
        Geo.Congruent
          A.1 B.1 A'.1 B'.1 :=
      (planeGeo_congruent
        (Geo := Geo)
        pi A B A' B').mp hAB

    have hACAmbient :
        Geo.Congruent
          A.1 C.1 A'.1 C'.1 :=
      (planeGeo_congruent
        (Geo := Geo)
        pi A C A' C').mp hAC

    have hAngleAmbient :
        Geo.AngleCongruent
          B.1 A.1 C.1
          B'.1 A'.1 C'.1 :=
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        pi B A C B' A' C').mp
        hAngle

    have hResultAmbient :
        Geo.AngleCongruent
          A.1 B.1 C.1
          A'.1 B'.1 C'.1 :=
      HilbertSpaceCongruence.sas
        (Geo := Geo)
        A.1 B.1 C.1
        A'.1 B'.1 C'.1
        hABCAmbient
        hA'B'C'Ambient
        hABAmbient
        hACAmbient
        hAngleAmbient

    exact
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        pi A B C A' B' C').mpr
        hResultAmbient

/-!
# Euclid XI.4 layer: right angles and perpendicularity in space

We now begin the first concrete adequacy test of the spatial interface.

The ambient space still has no global `HilbertCongruence Geo` instance.
Right angles are nevertheless meaningful because `HilbertRightAngle`
is a predicate built from ambient betweenness and ambient angle
congruence.  Whenever all relevant points lie in one plane, the
`PlaneGeo` instance constructed above allows the full planar Hilbert
theory to be used.

The principal bridge below says exactly that a right angle computed in
a fixed `PlaneGeo pi` is the same right angle in the ambient space.
-/

/--
A right angle between three points of a fixed plane is the same in
`PlaneGeo pi` and in the ambient geometry.
-/
theorem planeGeo_rightAngle_iff_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (A O B : PlanePoint Geo pi) :
    HilbertRightAngle
        (PlaneGeo Geo pi) A O B <->
      HilbertRightAngle
        Geo A.1 O.1 B.1 := by

  constructor

  · rintro ⟨C, hAOC, hAngle⟩

    have hAngleAmbient :
        Geo.AngleCongruent
          A.1 O.1 B.1
          B.1 O.1 C.1 :=
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        pi A O B B O C).mp
        hAngle

    exact
      ⟨C.1,
       hAOC,
       hAngleAmbient⟩

  · rintro ⟨C, hAOC, hAngleAmbient⟩

    have hData :=
      HilbertSpaceOrder.between_incidence
        (Geo := Geo)
        A.1 O.1 C hAOC

    have hAO :
        Ne A.1 O.1 :=
      hData.1

    have hCol :
        PrimCollinear Geo A.1 O.1 C :=
      hData.2.2.2.1

    have hCpi :
        S.OnPlane C pi :=
      hilbert_onPlane_of_primCollinear_with_two_on_plane
        (Geo := Geo)
        pi
        A.1 O.1 C
        hAO
        A.2 O.2
        hCol

    let Cp : PlanePoint Geo pi :=
      ⟨C, hCpi⟩

    have hAnglePlane :
        (PlaneGeo Geo pi).AngleCongruent
          A O B B O Cp := by

      apply
        (planeGeo_angleCongruent_iff_ambient
          (Geo := Geo)
          pi A O B B O Cp).mpr

      simpa [Cp] using hAngleAmbient

    exact
      ⟨Cp,
       hAOC,
       hAnglePlane⟩


/-!
## Derived ambient consequences of spatial Group III

These lemmas are genuinely spatial and proposition-independent.  They
recover the basic derived congruence API that cannot be obtained by
installing the planar `HilbertCongruence Geo` instance globally.

No new axiom is introduced here.
-/

theorem hilbert_space_congruent_reflexive
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B : Geo.Point)
    (hAB : Ne A B) :
    Geo.Congruent A B A B := by

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        A B A B hAB
    with
    ⟨X, _hRay, hAX_AB⟩

  exact
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A X
      A B
      A B
      hAX_AB hAX_AB


/--
Ambient symmetry of segment congruence, derived from spatial III.1--III.2.
-/
theorem hilbert_space_congruent_symmetry
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C D : Geo.Point)
    (hAB : Ne A B)
    (h : Geo.Congruent A B C D) :
    Geo.Congruent C D A B := by

  have hRefl :
      Geo.Congruent A B A B :=
    hilbert_space_congruent_reflexive
      (Geo := Geo) A B hAB

  exact
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A B
      C D
      A B
      h hRefl


/--
The two angle conclusions of spatial Hilbert SAS.

This is the direct spatial analogue of `hilbert_sas_remaining_angles`.
The triangles may lie in different planes.
-/
theorem hilbert_space_sas_remaining_angles
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (A B C A' B' C' : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hA'B'C' : Not (PrimCollinear Geo A' B' C'))
    (hAB : Geo.Congruent A B A' B')
    (hAC : Geo.Congruent A C A' C')
    (hAngleA : Geo.AngleCongruent B A C B' A' C') :
    Geo.AngleCongruent A B C A' B' C' /\
    Geo.AngleCongruent A C B A' C' B' := by

  constructor

  · exact
      HilbertSpaceCongruence.sas
        (Geo := Geo)
        A B C A' B' C'
        hABC hA'B'C'
        hAB hAC hAngleA

  · exact
      HilbertSpaceCongruence.sas
        (Geo := Geo)
        A C B A' C' B'
        (fun h =>
          hABC
            (PrimCollinearRotate Geo A C B h))
        (fun h =>
          hA'B'C'
            (PrimCollinearRotate Geo A' C' B' h))
        hAC hAB
        ((Geometry.Geo.angle_congruent_reverse_second
          Geo
          C A B
          B' A' C').mp
          ((Geometry.Geo.angle_congruent_reverse_first
            Geo
            B A C
            B' A' C').mp hAngleA))


/--
Spatial Hilbert Theorem 12, third-side form.

The first triangle is ambient.  The second triangle is supplied as three
points of one explicit plane `sigma`.  This is enough to run the III.4
uniqueness argument in `PlaneGeo sigma`, while III.5 itself remains the
ambient spatial SAS axiom.
-/
theorem hilbert_space_sas_third_side_and_angle
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (A B C : Geo.Point)
    (A' B' C' : PlanePoint Geo sigma)
    (hABC : Not (PrimCollinear Geo A B C))
    (hA'B'C' :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) A' B' C'))
    (hAB : Geo.Congruent A B A'.1 B'.1)
    (hAC : Geo.Congruent A C A'.1 C'.1)
    (hAngleA :
      Geo.AngleCongruent B A C B'.1 A'.1 C'.1) :
    Geo.Congruent B C B'.1 C'.1 /\
    Geo.AngleCongruent A C B A'.1 C'.1 B'.1 := by

  have hA'B'C'Ambient :
      Not (PrimCollinear Geo A'.1 B'.1 C'.1) :=
    planeGeo_not_primCollinear_to_ambient
      (Geo := Geo)
      sigma A' B' C' hA'B'C'

  have hAngles :=
    hilbert_space_sas_remaining_angles
      (Geo := Geo)
      A B C
      A'.1 B'.1 C'.1
      hABC hA'B'C'Ambient
      hAB hAC hAngleA

  have hB'C'A' :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) B' C' A') := by
    intro h
    exact
      hA'B'C'
        (PrimCollinearCycle
          (PlaneGeo Geo sigma)
          C' A' B'
          (PrimCollinearCycle
            (PlaneGeo Geo sigma)
            B' C' A' h))

  have hB'C'Plane : Ne B' C' :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo sigma)
      B' C' A' hB'C'A'

  have hB'C' : Ne B'.1 C'.1 := by
    intro h
    apply hB'C'Plane
    exact Subtype.ext h

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        B C B'.1 C'.1 hB'C'
    with
    ⟨X, hRayAmbient, hB'X_BC⟩

  have hB'X : Ne B'.1 X :=
    hRayAmbient.2.1.symm

  have hXsigma :
      S.OnPlane X sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      B'.1 C'.1 X
      hB'C'
      B'.2 C'.2
      hRayAmbient.2.2.1

  let Xp : PlanePoint Geo sigma :=
    ⟨X, hXsigma⟩

  have hRayPlane :
      HilbertSameRay
        (PlaneGeo Geo sigma) B' C' Xp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma B' C' Xp).mpr
    simpa [Xp] using hRayAmbient

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma)
        B' C' hB'C'Plane
    with
    ⟨base, hB'base, hC'base⟩

  have hXbase :
      HilbertIncidence.OnLine
        Xp base :=
    hilbert_collinear_on_line
      (PlaneGeo Geo sigma)
      B' C' Xp
      base
      hB'C'Plane
      hB'base hC'base
      hRayPlane.2.2.1

  have hA'base :
      Not (HilbertIncidence.OnLine A' base) := by
    intro h
    exact hA'B'C'
      ⟨base, h, hB'base, hC'base⟩

  have hA'B'Plane : Ne A' B' :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo sigma)
      A' B' C' hA'B'C'

  have hA'B' : Ne A'.1 B'.1 := by
    intro h
    apply hA'B'Plane
    exact Subtype.ext h

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma)
        A' B' hA'B'Plane
    with
    ⟨cross, hA'cross, hB'cross⟩

  have hSideXC' :
      HilbertSameSide
        (PlaneGeo Geo sigma) Xp C' cross :=
    hilbert_sameRay_points_sameSide
      (PlaneGeo Geo sigma)
      B' C' Xp C' A'
      base cross
      hB'base hC'base
      hB'cross hA'cross hA'base
      hRayPlane
      (hilbert_sameRay_refl
        (PlaneGeo Geo sigma)
        B' C' hB'C'Plane.symm)

  have hA'B'XPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) A' B' Xp) := by
    intro h
    exact
      (hilbert_not_collinear_of_off_line
        (PlaneGeo Geo sigma)
        B' Xp A'
        base
        (by
          intro hEq
          apply hB'X
          exact congrArg Subtype.val hEq)
        hB'base hXbase hA'base)
        (PrimCollinearCycle
          (PlaneGeo Geo sigma)
          A' B' Xp h)

  have hTargetAngleEq :
      (PlaneGeo Geo sigma).Angle A' B' C' =
      (PlaneGeo Geo sigma).Angle A' B' Xp :=
    hilbert_angle_eq_of_sameRay_second
      (PlaneGeo Geo sigma)
      B' A' C' Xp hRayPlane

  have hTargetRefl :
      (PlaneGeo Geo sigma).AngleCongruent
        A' B' C'
        A' B' C' :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := PlaneGeo Geo sigma)
      A' B' C' hA'B'C'

  have hTargetCongPlane :
      (PlaneGeo Geo sigma).AngleCongruent
        A' B' C'
        A' B' Xp := by
    unfold Geometry.Geo.AngleCongruent
      at hTargetRefl ⊢
    rw [hTargetAngleEq.symm]
    exact hTargetRefl

  have hTargetCongAmbient :
      Geo.AngleCongruent
        A'.1 B'.1 C'.1
        A'.1 B'.1 X := by
    have h :=
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        sigma
        A' B' C'
        A' B' Xp).mp
        hTargetCongPlane
    simpa [Xp] using h

  have hAngleB_X :
      Geo.AngleCongruent
        A B C
        A'.1 B'.1 X :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A B C
      A'.1 B'.1 C'.1
      A'.1 B'.1 X
      hAngles.1
      hTargetCongAmbient

  have hB'A'XPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) B' A' Xp) := by
    intro h
    exact
      hA'B'XPlane
        (PrimCollinearSwap
          (PlaneGeo Geo sigma)
          B' A' Xp h)

  have hB'A'XAmbient :
      Not (PrimCollinear Geo B'.1 A'.1 X) := by
    have h :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        sigma B' A' Xp hB'A'XPlane
    simpa [Xp] using h

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap Geo B A C h)

  have hBA_B'A' :
      Geo.Congruent B A B'.1 A'.1 :=
    (Geometry.Geo.congruent_reverse_second
      Geo
      B A A'.1 B'.1).mp
      ((Geometry.Geo.congruent_reverse_first
        Geo
        A B A'.1 B'.1).mp hAB)

  have hBC_B'X :
      Geo.Congruent B C B'.1 X :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      B'.1 X B C
      hB'X hB'X_BC

  have hAngleAX :
      Geo.AngleCongruent
        B A C
        B'.1 A'.1 X :=
    HilbertSpaceCongruence.sas
      (Geo := Geo)
      B A C
      B'.1 A'.1 X
      hBAC hB'A'XAmbient
      hBA_B'A'
      hBC_B'X
      hAngleB_X

  have hC'crossOff :
      Not (H.OnLine C'.1 cross.1) :=
    hSideXC'.2.1

  rcases
      HilbertSpaceCongruence.angle_construction_in_plane
        (Geo := Geo)
        B A C
        B'.1 A'.1 C'.1
        hBAC
        hA'B'.symm
        sigma
        cross.1
        cross.2
        hB'cross hA'cross
        C'.2
        hC'crossOff
    with
    ⟨Z, hZC'space, _hAngleZ, hUnique⟩

  have hC'C'Plane :
      HilbertSameSide
        (PlaneGeo Geo sigma) C' C' cross :=
    hilbert_sameSide_refl
      (PlaneGeo Geo sigma)
      C' cross hSideXC'.2.1

  have hC'C'space :
      HilbertSameSideInPlane
        Geo C'.1 C'.1 cross.1 sigma :=
    (planeGeo_sameSide_iff_space
      (Geo := Geo)
      sigma C' C' cross).mp
      hC'C'Plane

  have hZC'Ray :
      HilbertSameRay Geo A'.1 Z C'.1 :=
    hUnique
      C'.1
      hC'C'space
      hAngleA

  have hXC'space :
      HilbertSameSideInPlane
        Geo X C'.1 cross.1 sigma := by
    have h :=
      (planeGeo_sameSide_iff_space
        (Geo := Geo)
        sigma Xp C' cross).mp
        hSideXC'
    simpa [Xp] using h

  have hZXRay :
      HilbertSameRay Geo A'.1 Z X :=
    hUnique
      X
      hXC'space
      hAngleAX

  have hXbaseAmbient :
      H.OnLine X base.1 := by
    change PlaneOnLine Geo Xp base at hXbase
    exact hXbase

  have hC'baseAmbient :
      H.OnLine C'.1 base.1 := by
    change PlaneOnLine Geo C' base at hC'base
    exact hC'base

  have hA'baseAmbient :
      Not (H.OnLine A'.1 base.1) := by
    change Not (PlaneOnLine Geo A' base) at hA'base
    exact hA'base

  have hXC' : X = C'.1 := by
    by_contra hNe

    rcases hZXRay.2.2.1 with
      ⟨l1, hA'l1, hZl1, hXl1⟩

    rcases hZC'Ray.2.2.1 with
      ⟨l2, hA'l2, hZl2, hC'l2⟩

    have hl1l2 : l1 = l2 :=
      HilbertPlaneIncidence.line_unique
        A'.1 Z hZXRay.1.symm
        l1 l2
        hA'l1 hZl1
        hA'l2 hZl2

    subst l2

    have hBaseL1 : base.1 = l1 :=
      HilbertPlaneIncidence.line_unique
        X C'.1 hNe
        base.1 l1
        hXbaseAmbient hC'baseAmbient
        hXl1 hC'l2

    rw [hBaseL1.symm] at hA'l1
    exact hA'baseAmbient hA'l1

  subst X

  have hThird :
      Geo.Congruent B C B'.1 C'.1 :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      B'.1 C'.1 B C
      hB'C'
      hB'X_BC

  exact ⟨hThird, hAngles.2⟩


/-!
## Spatial SSS
-/

/--
Spatial SSS, angle-at-the-first-vertex form, with the target triangle
carried by one explicit ambient plane.

This is proposition-independent.  The proof reconstructs the source angle
inside the target plane using spatial III.4, lays off the second source side
on the constructed ray, uses spatial SAS for the remaining side, and closes
the target-plane comparison by the existing planar Hilbert SSS theorem.
-/
theorem hilbert_space_sss_angleA_in_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (sigma : S.Plane)
    (A B C : Geo.Point)
    (A' B' C' : PlanePoint Geo sigma)
    (hABC : Not (PrimCollinear Geo A B C))
    (hA'B'C' :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) A' B' C'))
    (hAB : Geo.Congruent A B A'.1 B'.1)
    (hBC : Geo.Congruent B C B'.1 C'.1)
    (hAC : Geo.Congruent A C A'.1 C'.1) :
    Geo.AngleCongruent B A C B'.1 A'.1 C'.1 := by

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    intro h
    exact hABC
      (PrimCollinearSwap Geo B A C h)

  have hA'B'Plane : Ne A' B' :=
    hilbert_noncollinear_ne_first
      (PlaneGeo Geo sigma)
      A' B' C' hA'B'C'

  have hA'B' : Ne A'.1 B'.1 := by
    intro h
    apply hA'B'Plane
    exact Subtype.ext h

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := PlaneGeo Geo sigma)
        A' B' hA'B'Plane
    with
    ⟨base, hA'base, hB'base⟩

  have hC'offBase :
      Not ((PlaneGeo Geo sigma).OnLine C' base) := by
    intro hC'base
    exact hA'B'C'
      ⟨base, hA'base, hB'base, hC'base⟩

  have hA'baseAmbient : H.OnLine A'.1 base.1 := by
    change PlaneOnLine Geo A' base at hA'base
    exact hA'base

  have hB'baseAmbient : H.OnLine B'.1 base.1 := by
    change PlaneOnLine Geo B' base at hB'base
    exact hB'base

  have hC'offBaseAmbient :
      Not (H.OnLine C'.1 base.1) := by
    change Not (PlaneOnLine Geo C' base) at hC'offBase
    exact hC'offBase

  rcases
      HilbertSpaceCongruence.angle_construction_in_plane
        (Geo := Geo)
        B A C
        B'.1 A'.1 C'.1
        hBAC
        hA'B'.symm
        sigma
        base.1
        base.2
        hB'baseAmbient
        hA'baseAmbient
        C'.2
        hC'offBaseAmbient
    with
    ⟨X, hXC'space, hAngleX, _hUnique⟩

  have hXsigma : S.OnPlane X sigma :=
    hXC'space.1

  have hXoffBase :
      Not (H.OnLine X base.1) :=
    hXC'space.2.2.1

  have hA'X : Ne A'.1 X := by
    intro h
    subst X
    exact hXoffBase hA'baseAmbient

  rcases
      HilbertSpaceCongruence.segment_construction
        (Geo := Geo)
        A C
        A'.1 X
        hA'X
    with
    ⟨Y, hRayXY, hA'Y_AC⟩

  have hA'Y : Ne A'.1 Y :=
    hRayXY.2.1.symm

  have hYsigma : S.OnPlane Y sigma :=
    hilbert_onPlane_of_primCollinear_with_two_on_plane
      (Geo := Geo)
      sigma
      A'.1 X Y
      hA'X
      A'.2 hXsigma
      hRayXY.2.2.1

  let Xp : PlanePoint Geo sigma :=
    ⟨X, hXsigma⟩

  let Yp : PlanePoint Geo sigma :=
    ⟨Y, hYsigma⟩

  have hRayXYPlane :
      HilbertSameRay (PlaneGeo Geo sigma) A' Xp Yp := by
    apply
      (planeGeo_sameRay_iff_ambient
        (Geo := Geo)
        sigma A' Xp Yp).mpr
    simpa [Xp, Yp] using hRayXY

  have hXoffBasePlane :
      Not ((PlaneGeo Geo sigma).OnLine Xp base) := by
    intro h
    apply hXoffBase
    change HilbertIncidence.OnLine X base.1 at h
    exact h

  have hB'A'XPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) B' A' Xp) :=
    hilbert_not_collinear_of_off_line
      (PlaneGeo Geo sigma)
      B' A' Xp
      base
      hA'B'Plane.symm
      hB'base hA'base
      hXoffBasePlane

  have hRayB'B'Plane :
      HilbertSameRay
        (PlaneGeo Geo sigma) A' B' B' :=
    hilbert_sameRay_refl
      (PlaneGeo Geo sigma)
      A' B' hA'B'Plane.symm

  have hB'A'YPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) B' A' Yp) :=
    hilbert_noncollinear_of_sameRays
      (PlaneGeo Geo sigma)
      B' A' Xp
      B' Yp
      hB'A'XPlane
      hRayB'B'Plane
      hRayXYPlane

  have hA'B'YPlane :
      Not (PrimCollinear
        (PlaneGeo Geo sigma) A' B' Yp) := by
    intro h
    exact hB'A'YPlane
      (PrimCollinearSwap
        (PlaneGeo Geo sigma) A' B' Yp h)

  have hTargetAngleXYPlane :
      (PlaneGeo Geo sigma).Angle B' A' Xp =
      (PlaneGeo Geo sigma).Angle B' A' Yp :=
    hilbert_angle_eq_of_sameRay_second
      (PlaneGeo Geo sigma)
      A' B' Xp Yp
      hRayXYPlane

  have hPlaneAngleXX :
      (PlaneGeo Geo sigma).AngleCongruent
        B' A' Xp
        B' A' Xp :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := PlaneGeo Geo sigma)
      B' A' Xp hB'A'XPlane

  have hPlaneAngleXY :
      (PlaneGeo Geo sigma).AngleCongruent
        B' A' Xp
        B' A' Yp := by
    unfold Geometry.Geo.AngleCongruent at hPlaneAngleXX ⊢
    rw [← hTargetAngleXYPlane]
    exact hPlaneAngleXX

  have hAmbientAngleXY :
      Geo.AngleCongruent
        B'.1 A'.1 X
        B'.1 A'.1 Y := by
    have h :=
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        sigma
        B' A' Xp
        B' A' Yp).mp
        hPlaneAngleXY
    simpa [Xp, Yp] using h

  have hAngleY :
      Geo.AngleCongruent
        B A C
        B'.1 A'.1 Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A C
      B'.1 A'.1 X
      B'.1 A'.1 Y
      hAngleX hAmbientAngleXY

  have hAC_A'Y :
      Geo.Congruent A C A'.1 Y :=
    hilbert_space_congruent_symmetry
      (Geo := Geo)
      A'.1 Y A C
      hA'Y
      hA'Y_AC

  have hSAS :=
    hilbert_space_sas_third_side_and_angle
      (Geo := Geo)
      sigma
      A B C
      A' B' Yp
      hABC
      hA'B'YPlane
      hAB
      hAC_A'Y
      hAngleY

  have hBC_B'Y :
      Geo.Congruent B C B'.1 Y := by
    simpa [Yp] using hSAS.1

  have hB'Y_B'C' :
      Geo.Congruent B'.1 Y B'.1 C'.1 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      B C
      B'.1 Y
      B'.1 C'.1
      hBC_B'Y hBC

  have hA'Y_A'C' :
      Geo.Congruent A'.1 Y A'.1 C'.1 :=
    HilbertSpaceCongruence.segment_congruence_common
      (Geo := Geo)
      A C
      A'.1 Y
      A'.1 C'.1
      hAC_A'Y hAC

  have hA'B'ReflAmbient :
      Geo.Congruent A'.1 B'.1 A'.1 B'.1 :=
    hilbert_space_congruent_reflexive
      (Geo := Geo)
      A'.1 B'.1 hA'B'

  have hA'B'ReflPlane :
      (PlaneGeo Geo sigma).Congruent A' B' A' B' :=
    (planeGeo_congruent
      (Geo := Geo)
      sigma A' B' A' B').mpr
      hA'B'ReflAmbient

  have hB'Y_B'C'Plane :
      (PlaneGeo Geo sigma).Congruent
        B' Yp B' C' := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        sigma B' Yp B' C').mpr
    simpa [Yp] using hB'Y_B'C'

  have hA'Y_A'C'Plane :
      (PlaneGeo Geo sigma).Congruent
        A' Yp A' C' := by
    apply
      (planeGeo_congruent
        (Geo := Geo)
        sigma A' Yp A' C').mpr
    simpa [Yp] using hA'Y_A'C'

  have hPlanarSSS :=
    HilbertSSS
      (PlaneGeo Geo sigma)
      A' B' Yp
      A' B' C'
      hA'B'YPlane
      hA'B'ReflPlane
      hB'Y_B'C'Plane
      hA'Y_A'C'Plane

  have hPlaneAngle :
      (PlaneGeo Geo sigma).AngleCongruent
        B' A' Yp
        B' A' C' :=
    hPlanarSSS.2.angleA

  have hAmbientAngle :
      Geo.AngleCongruent
        B'.1 A'.1 Y
        B'.1 A'.1 C'.1 := by
    have h :=
      (planeGeo_angleCongruent_iff_ambient
        (Geo := Geo)
        sigma
        B' A' Yp
        B' A' C').mp
        hPlaneAngle
    simpa [Yp] using h

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B A C
      B'.1 A'.1 Y
      B'.1 A'.1 C'.1
      hAngleY
      hAmbientAngle

/-!
## Perpendicular lines
-/

/--
Two incidence lines are perpendicular at `O` when they both pass
through `O` and contain non-origin points which determine a right angle
at `O`.

The definition is point-based and therefore does not assume a global
metric or an ambient planar congruence instance.
-/
def HilbertLinesPerpendicularAt
    [H : HilbertIncidence Geo]
    (l m : Geo.Line)
    (O : Geo.Point) : Prop :=
  H.OnLine O l /\
  H.OnLine O m /\
  exists A B : Geo.Point,
    Ne A O /\
    Ne B O /\
    H.OnLine A l /\
    H.OnLine B m /\
    Not (PrimCollinear Geo A O B) /\
    HilbertRightAngle Geo A O B


/--
Perpendicular incidence lines are distinct.

This is now an incidence-level consequence of the explicit
nondegeneracy witness carried by `HilbertLinesPerpendicularAt`.
-/
theorem hilbert_linesPerpendicularAt_ne
    [H : HilbertIncidence Geo]
    (l m : Geo.Line)
    (O : Geo.Point)
    (hPerp : HilbertLinesPerpendicularAt Geo l m O) :
    Ne l m := by

  intro hEq

  rcases hPerp with
    ⟨hOl, _hOm,
     A, B,
     _hAO, _hBO,
     hAl, hBm,
     hNon, _hRight⟩

  have hBl :
      H.OnLine B l := by
    rw [hEq]
    exact hBm

  exact hNon
    ⟨l, hAl, hOl, hBl⟩


/--
For two lines contained in a fixed plane, perpendicularity computed in
`PlaneGeo pi` is equivalent to ambient perpendicularity.
-/
theorem planeGeo_linesPerpendicularAt_iff_ambient
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder (Geo := Geo) (H := H) (S := S)]
    [_HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    (pi : S.Plane)
    (l m : PlaneLine Geo pi)
    (O : PlanePoint Geo pi) :
    HilbertLinesPerpendicularAt
        (PlaneGeo Geo pi) l m O <->
      HilbertLinesPerpendicularAt
        Geo l.1 m.1 O.1 := by

  unfold HilbertLinesPerpendicularAt

  constructor

  · rintro
      ⟨hOl, hOm,
       A, B,
       hAO, hBO,
       hAl, hBm,
       hNonPlane,
       hRightPlane⟩

    have hAOval :
        Ne A.1 O.1 := by
      intro h
      apply hAO
      exact Subtype.ext h

    have hBOval :
        Ne B.1 O.1 := by
      intro h
      apply hBO
      exact Subtype.ext h

    have hNonAmbient :
        Not (PrimCollinear Geo A.1 O.1 B.1) :=
      planeGeo_not_primCollinear_to_ambient
        (Geo := Geo)
        pi A O B hNonPlane

    have hRightAmbient :
        HilbertRightAngle
          Geo A.1 O.1 B.1 :=
      (planeGeo_rightAngle_iff_ambient
        (Geo := Geo)
        pi A O B).mp
        hRightPlane

    exact
      ⟨hOl,
       hOm,
       A.1, B.1,
       hAOval,
       hBOval,
       hAl,
       hBm,
       hNonAmbient,
       hRightAmbient⟩

  · rintro
      ⟨hOl, hOm,
       A, B,
       hAO, hBO,
       hAl, hBm,
       hNonAmbient,
       hRightAmbient⟩

    have hApi :
        S.OnPlane A pi :=
      l.2 A hAl

    have hBpi :
        S.OnPlane B pi :=
      m.2 B hBm

    let Ap : PlanePoint Geo pi :=
      ⟨A, hApi⟩

    let Bp : PlanePoint Geo pi :=
      ⟨B, hBpi⟩

    have hAOp :
        Ne Ap O := by
      intro h
      exact hAO (congrArg Subtype.val h)

    have hBOp :
        Ne Bp O := by
      intro h
      exact hBO (congrArg Subtype.val h)

    have hNonPlane :
        Not (PrimCollinear
          (PlaneGeo Geo pi) Ap O Bp) := by
      intro hCol
      apply hNonAmbient
      have hAmbient :=
        planeGeo_primCollinear_to_ambient
          (Geo := Geo)
          pi Ap O Bp hCol
      simpa [Ap, Bp] using hAmbient

    have hRightPlane :
        HilbertRightAngle
          (PlaneGeo Geo pi) Ap O Bp := by

      apply
        (planeGeo_rightAngle_iff_ambient
          (Geo := Geo)
          pi Ap O Bp).mpr

      simpa [Ap, Bp] using hRightAmbient

    exact
      ⟨hOl,
       hOm,
       Ap, Bp,
       hAOp,
       hBOp,
       hAl,
       hBm,
       hNonPlane,
       hRightPlane⟩


/-!
## Perpendicular line and plane
-/

/--
A line `l` is perpendicular to a plane `pi` at `O` when `O` lies on
both, and `l` is perpendicular at `O` to every line of `pi` through
`O`.

This is the synthetic Euclid XI notion needed for XI.4 and later for
plane reflection.  It quantifies only over incidence lines; no metric,
coordinates, scalar product, or normal vector is introduced.
-/
def HilbertLinePerpendicularPlaneAt
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (l : Geo.Line)
    (pi : S.Plane)
    (O : Geo.Point) : Prop :=
  H.OnLine O l /\
  S.OnPlane O pi /\
  forall m : Geo.Line,
    HilbertLineInPlane Geo m pi ->
    H.OnLine O m ->
    HilbertLinesPerpendicularAt Geo l m O


/--
Unpack the universal line condition from line-plane perpendicularity.
-/
theorem HilbertLinePerpendicularPlaneAt.perpendicular_to_line
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {l : Geo.Line}
    {pi : S.Plane}
    {O : Geo.Point}
    (hPerp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi O)
    {m : Geo.Line}
    (hmPi :
      HilbertLineInPlane Geo m pi)
    (hOm :
      H.OnLine O m) :
    HilbertLinesPerpendicularAt
      Geo l m O := by

  exact
    hPerp.2.2 m hmPi hOm


/--
The incidence part of line-plane perpendicularity.
-/
theorem HilbertLinePerpendicularPlaneAt.incidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    {l : Geo.Line}
    {pi : S.Plane}
    {O : Geo.Point}
    (hPerp :
      HilbertLinePerpendicularPlaneAt
        Geo l pi O) :
    H.OnLine O l /\
    S.OnPlane O pi := by

  exact
    ⟨hPerp.1, hPerp.2.1⟩

end Geometry

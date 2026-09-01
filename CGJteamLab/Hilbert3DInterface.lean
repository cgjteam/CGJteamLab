import CGJteamLab.Hilbert3DAxioms

namespace Geometry

universe u

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
      Geo.UnorientedAngleCongruent
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

end Geometry

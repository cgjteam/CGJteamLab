import CGJteamLab.HilbertAxioms
import CGJteamLab.HilbertAxiomsWork

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Compatibility bridge from source-faithful Hilbert axioms to the legacy plane API

`HilbertAxioms.lean` is the source-faithful foundation.
`HilbertAxiomsWork.lean` supplies only the frozen legacy API declarations used by
`HilbertPlaneTheory.lean`.

This file contains only transport/realization code.  It deliberately does not
reprove the derived plane theory.
-/

/-!
## Compatibility with the source-faithful Hilbert incidence axioms

The legacy plane API is imported from `HilbertAxiomsWork.lean`; it is not
redeclared here and it is not the foundational axiom system.

This first compatibility step identifies the legacy point-line incidence
relation with `Geo.OnLine` and derives `HilbertPlaneIncidence` from
Hilbert Group I.

No global typeclass instance is installed here.
-/

/-- Canonical legacy incidence obtained from `Geo.OnLine`. -/
@[instance_reducible]
def hilbertIncidenceOfGrundlagen :
    HilbertIncidence Geo where
  OnLine := Geo.OnLine

/--
With the canonical incidence interface, legacy `PrimCollinear` is exactly
`HilbertGrundlagenCollinear`.
-/
theorem primCollinear_ofGrundlagen_iff
    (A B C : Geo.Point) :
    @PrimCollinear Geo (hilbertIncidenceOfGrundlagen Geo) A B C <->
      HilbertGrundlagenCollinear Geo A B C := by
  rfl


/--
Under the canonical legacy incidence structure, the legacy `OnLine`
projection is definitionally the primitive `Geo.OnLine`.
-/
theorem hilbertOnLineOfGrundlagen_iff
    (P : Geo.Point) (l : Geo.Line) :
    @HilbertIncidence.OnLine Geo (hilbertIncidenceOfGrundlagen Geo) P l <->
      Geo.OnLine P l := by
  rfl

/--
Hilbert Group I implies the legacy plane-incidence interface.
-/
theorem hilbertPlaneIncidenceOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo] :
    @HilbertPlaneIncidence Geo (hilbertIncidenceOfGrundlagen Geo) := by
  refine
    @HilbertPlaneIncidence.mk
      Geo
      (hilbertIncidenceOfGrundlagen Geo)
      ?_
      ?_
      ?_
      ?_

  · intro A B hAB
    exact H1.I1_line_through A B hAB

  · intro A B hAB l m hAl hBl hAm hBm
    exact H1.I2_line_unique A B hAB l m hAl hBl hAm hBm

  · rcases H1.I3_three_noncollinear with
      ⟨A, B, C, hAB, hAC, hBC, hNoncol⟩
    rcases H1.I1_line_through A B hAB with
      ⟨l, hAl, hBl⟩
    exact ⟨l, A, B, hAB, hAl, hBl⟩

  · rcases H1.I3_three_noncollinear with
      ⟨A, B, C, hAB, hAC, hBC, hNoncol⟩
    refine ⟨A, B, C, ?_⟩
    intro hOld
    apply hNoncol
    rcases hOld with ⟨l, hAl, hBl, hCl⟩
    exact ⟨l, hAl, hBl, hCl⟩

/-!
## Compatibility with Hilbert Group II: axioms II.1-II.3

The first three order axioms pass directly to the legacy plane API.
Pasch (II.4) is deliberately not handled here yet, because the source-faithful
axiom is stated inside an explicit plane, whereas the legacy `HilbertOrder.pasch`
field suppresses that plane parameter.
-/

/-- Compatibility form of Hilbert II.1. -/
theorem hilbertBetweenIncidenceOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (A B C : Geo.Point) :
    Geo.Between A B C ->
      Ne A B /\
      Ne B C /\
      Ne A C /\
      @PrimCollinear Geo (hilbertIncidenceOfGrundlagen Geo) A B C /\
      Geo.Between C B A := by
  intro hBetween
  rcases H2.II1_between A B C hBetween with
    ⟨hAB, hBC, hAC, hCol, hReverse⟩
  refine ⟨hAB, hBC, hAC, ?_, hReverse⟩
  exact (primCollinear_ofGrundlagen_iff Geo A B C).2 hCol

/-- Compatibility form of Hilbert II.2. -/
theorem hilbertBetweenExtensionOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (A C : Geo.Point) :
    Ne A C ->
      exists B : Geo.Point,
        Geo.Between A C B := by
  intro hAC
  exact H2.II2_extension A C hAC

/-- Compatibility form of the legacy `between_unique` consequence of II.3. -/
theorem hilbertBetweenUniqueOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (A B C : Geo.Point) :
    @PrimCollinear Geo (hilbertIncidenceOfGrundlagen Geo) A B C ->
    Geo.Between A B C ->
      Not (Geo.Between B A C) /\
      Not (Geo.Between A C B) := by
  intro hCol hBetween
  have hCol' : HilbertGrundlagenCollinear Geo A B C :=
    (primCollinear_ofGrundlagen_iff Geo A B C).1 hCol
  exact (H2.II3_at_most_one_between A B C hCol').1 hBetween

/-!
## Compatibility with Hilbert II.4 (Pasch) inside an explicit plane

This is the exact point where the legacy plane API and the source-faithful
spatial formulation differ.

The theorem below proves Pasch in the form needed by the old vocabulary,
but keeps the plane `pi` and the hypothesis that `l` lies in `pi` explicit.
No attempt is made yet to collapse this to the legacy global
`HilbertOrder.pasch` field.
-/

/--
Source-faithful Pasch, rewritten in the legacy incidence/segment vocabulary,
with the containing plane kept explicit.
-/
theorem hilbertPaschInPlaneOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (A B C : Geo.Point)
    (hABC :
      Not (@PrimCollinear Geo (hilbertIncidenceOfGrundlagen Geo) A B C))
    (pi : S.Plane)
    (hA_pi : S.OnPlane A pi)
    (hB_pi : S.OnPlane B pi)
    (hC_pi : S.OnPlane C pi)
    (l : Geo.Line)
    (hl_pi : HilbertGrundlagenLineInPlane Geo l pi)
    (hAl : Not (Geo.OnLine A l))
    (hBl : Not (Geo.OnLine B l))
    (hCl : Not (Geo.OnLine C l))
    (hAB :
      @HilbertSegmentMeetsLine Geo
        (hilbertIncidenceOfGrundlagen Geo) A B l) :
    @HilbertSegmentMeetsLine Geo
        (hilbertIncidenceOfGrundlagen Geo) A C l \/
    @HilbertSegmentMeetsLine Geo
        (hilbertIncidenceOfGrundlagen Geo) B C l := by
  have hABC' : Not (HilbertGrundlagenCollinear Geo A B C) := by
    intro hCol
    apply hABC
    exact (primCollinear_ofGrundlagen_iff Geo A B C).2 hCol

  have hAB' :
      exists X : Geo.Point,
        Geo.Between A X B /\
        Geo.OnLine X l := by
    rcases hAB with ⟨X, hAXB, hXl⟩
    exact ⟨X, hAXB, (hilbertOnLineOfGrundlagen_iff Geo X l).1 hXl⟩

  have hPasch :=
    H2.II4_pasch
      A B C hABC'
      pi hA_pi hB_pi hC_pi
      l hl_pi hAl hBl hCl hAB'

  rcases hPasch with hAC | hBC

  · left
    rcases hAC with ⟨Y, hAYC, hYl⟩
    exact ⟨Y, hAYC, (hilbertOnLineOfGrundlagen_iff Geo Y l).2 hYl⟩

  · right
    rcases hBC with ⟨Z, hBZC, hZl⟩
    exact ⟨Z, hBZC, (hilbertOnLineOfGrundlagen_iff Geo Z l).2 hZl⟩

/-!
## A fixed Hilbert plane as a geometry

The legacy API is genuinely planar.  Therefore the correct bridge from
Hilbert's spatial axioms is not a global `HilbertOrder Geo` instance on the
ambient space.  Instead, for each source-faithful Hilbert plane `pi`, we form
the geometry induced on that plane.

This section only constructs the raw carrier and inherited primitive
relations.  No new geometric axiom is introduced here.
-/

/-- Points lying in the fixed Hilbert plane `pi`. -/
def HilbertPlanePoint
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane) :=
  {P : Geo.Point // S.OnPlane P pi}

/-- Ambient lines wholly contained in the fixed Hilbert plane `pi`. -/
def HilbertPlaneLine
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane) :=
  {l : Geo.Line // HilbertGrundlagenLineInPlane Geo l pi}

/-- Incidence in the fixed plane is inherited ambient incidence. -/
def HilbertPlaneOnLine
    [S : HilbertGrundlagenPrimitive Geo]
    {pi : S.Plane}
    (P : HilbertPlanePoint Geo pi)
    (l : HilbertPlaneLine Geo pi) : Prop :=
  Geo.OnLine P.1 l.1

/-- Functorial map of an unordered pair along a function. -/
def hilbertPlaneMapUnorderedPair
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

/-- Forget plane-membership proofs pointwise on a set. -/
def hilbertPlanePointSetToAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    {pi : S.Plane}
    (U : Set (HilbertPlanePoint Geo pi)) :
    Set Geo.Point :=
  Subtype.val '' U


/--
Raw same-direction step on the induced plane, defined before `HilbertPlaneGeo`
so that the primitive angle carrier can be restricted to actual point-generated
angles.
-/
def HilbertPlaneSameDirectionStepRaw
    [S : HilbertGrundlagenPrimitive Geo]
    {pi : S.Plane}
    (O P Q : HilbertPlanePoint Geo pi) : Prop :=
  Ne P O /\
  Ne Q O /\
  (P = Q \/
    Geo.Between O.1 P.1 Q.1 \/
    Geo.Between O.1 Q.1 P.1)

/-- Raw ray on the induced plane. -/
def HilbertPlaneRayRaw
    [S : HilbertGrundlagenPrimitive Geo]
    {pi : S.Plane}
    (O A : HilbertPlanePoint Geo pi) :
    Set (HilbertPlanePoint Geo pi) :=
  {X |
    X = O \/
    Relation.ReflTransGen
      (HilbertPlaneSameDirectionStepRaw
        (Geo := Geo) (pi := pi) O)
      A X}

/-- Raw angle data generated by three points of the induced plane. -/
def HilbertPlaneAngleRaw
    [S : HilbertGrundlagenPrimitive Geo]
    {pi : S.Plane}
    (A B C : HilbertPlanePoint Geo pi) :
    Prod
      (HilbertPlanePoint Geo pi)
      (UnorderedPair (Set (HilbertPlanePoint Geo pi))) :=
  ( B,
    UnorderedPair.mk
      (HilbertPlaneRayRaw (Geo := Geo) (pi := pi) B A)
      (HilbertPlaneRayRaw (Geo := Geo) (pi := pi) B C) )

/-- Forget the plane subtype from arbitrary raw angle data. -/
def hilbertPlaneAngleDataToAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    {pi : S.Plane}
    (a :
      Prod
        (HilbertPlanePoint Geo pi)
        (UnorderedPair (Set (HilbertPlanePoint Geo pi)))) :
    Prod Geo.Point (UnorderedPair (Set Geo.Point)) :=
  ( a.1.1,
    hilbertPlaneMapUnorderedPair
      (hilbertPlanePointSetToAmbient
        (Geo := Geo) (pi := pi))
      a.2 )

/-- Raw angle data is actual when it is generated by three plane-points. -/
def HilbertPlaneActualAngleData
    [S : HilbertGrundlagenPrimitive Geo]
    {pi : S.Plane}
    (a :
      Prod
        (HilbertPlanePoint Geo pi)
        (UnorderedPair (Set (HilbertPlanePoint Geo pi)))) : Prop :=
  exists A B C : HilbertPlanePoint Geo pi,
    a = HilbertPlaneAngleRaw
      (Geo := Geo) (pi := pi) A B C

/--
Primitive angle relation used by the induced plane.

Unlike the ambient raw relation, this relation only connects angle data that
actually comes from triples of plane-points.  This prevents later `EqvGen`
closure from travelling through arbitrary non-geometric angle data.
-/
def HilbertPlanePrimitiveAngleRel
    [S : HilbertGrundlagenPrimitive Geo]
    {pi : S.Plane}
    (a b :
      Prod
        (HilbertPlanePoint Geo pi)
        (UnorderedPair (Set (HilbertPlanePoint Geo pi)))) : Prop :=
  HilbertPlaneActualAngleData
      (Geo := Geo) (pi := pi) a /\
  HilbertPlaneActualAngleData
      (Geo := Geo) (pi := pi) b /\
  Geo.UnorientedAngleCongruent
    (hilbertPlaneAngleDataToAmbient
      (Geo := Geo) (pi := pi) a)
    (hilbertPlaneAngleDataToAmbient
      (Geo := Geo) (pi := pi) b)

/--
The raw `Geometry.Geo` induced on one source-faithful Hilbert plane.

Points are ambient points in `pi`; lines are ambient lines contained in `pi`.
Betweenness and segment congruence are inherited.  The primitive angle
relation is transported by forgetting the plane-membership proofs.
-/
def HilbertPlaneGeo
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane) :
    Geometry.Geo where

  Point :=
    HilbertPlanePoint Geo pi

  Line :=
    HilbertPlaneLine Geo pi

  OnLine :=
    fun P l => HilbertPlaneOnLine Geo P l

  Between :=
    fun A B C =>
      Geo.Between A.1 B.1 C.1

  SegmentCongruent :=
    fun s t =>
      Geo.SegmentCongruent
        (hilbertPlaneMapUnorderedPair
          (fun P : HilbertPlanePoint Geo pi => P.1) s)
        (hilbertPlaneMapUnorderedPair
          (fun P : HilbertPlanePoint Geo pi => P.1) t)

  UnorientedAngleCongruent :=
    fun a b =>
      HilbertPlanePrimitiveAngleRel
        (Geo := Geo) (pi := pi) a b

/-- `HilbertPlaneGeo` uses exactly the raw same-direction step above. -/
theorem hilbertPlaneGeoSameDirectionStepRaw
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (O P Q : HilbertPlanePoint Geo pi) :
    (HilbertPlaneGeo Geo pi).SameDirectionStep O P Q <->
      HilbertPlaneSameDirectionStepRaw
        (Geo := Geo) (pi := pi) O P Q := by
  rfl

/-- `HilbertPlaneGeo` uses exactly the raw ray above. -/
theorem hilbertPlaneGeoRayRaw
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (O A : HilbertPlanePoint Geo pi) :
    (HilbertPlaneGeo Geo pi).ray O A =
      HilbertPlaneRayRaw
        (Geo := Geo) (pi := pi) O A := by
  rfl

/-- Actual angle data of `HilbertPlaneGeo` is the raw point-generated angle. -/
theorem hilbertPlaneGeoAngleRaw
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (A B C : HilbertPlanePoint Geo pi) :
    (HilbertPlaneGeo Geo pi).Angle A B C =
      HilbertPlaneAngleRaw
        (Geo := Geo) (pi := pi) A B C := by
  rfl

/-- Betweenness in `HilbertPlaneGeo pi` is ambient betweenness. -/
theorem hilbertPlaneGeo_between
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (A B C : HilbertPlanePoint Geo pi) :
    (HilbertPlaneGeo Geo pi).Between A B C <->
      Geo.Between A.1 B.1 C.1 := by
  rfl

/-- Segment congruence in `HilbertPlaneGeo pi` is ambient congruence. -/
theorem hilbertPlaneGeo_congruent
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (A B C D : HilbertPlanePoint Geo pi) :
    (HilbertPlaneGeo Geo pi).Congruent A B C D <->
      Geo.Congruent A.1 B.1 C.1 D.1 := by
  rfl

/-- The legacy incidence relation on the induced plane is inherited incidence. -/
instance hilbertPlaneGeoHilbertIncidence
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane) :
    HilbertIncidence (HilbertPlaneGeo Geo pi) where
  OnLine :=
    fun P l => HilbertPlaneOnLine Geo P l

/-!
## Incidence inherited by a fixed Hilbert plane

We now derive the legacy `HilbertPlaneIncidence` interface for
`HilbertPlaneGeo Geo pi` from source-faithful Hilbert Group I.

The only nontrivial ingredient is that every Hilbert plane contains three
ambiently noncollinear points.  This is derived from I.1-I.8; it is not added
as a new axiom.
-/

/-- Every ambient Hilbert plane has a point outside it. -/
theorem hilbertGrundlagenPointOffPlane
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi : S.Plane) :
    exists P : Geo.Point,
      Not (S.OnPlane P pi) := by
  rcases H1.I8_four_noncoplanar with
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

/-- Every ambient Hilbert line has a point outside it. -/
theorem hilbertGrundlagenPointOffLine
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (l : Geo.Line) :
    exists P : Geo.Point,
      Not (Geo.OnLine P l) := by
  rcases H1.I3_three_noncollinear with
    ⟨A, B, C, hAB, hAC, hBC, hNoncollinear⟩
  by_cases hA : Geo.OnLine A l
  · by_cases hB : Geo.OnLine B l
    · by_cases hC : Geo.OnLine C l
      · exact False.elim
          (hNoncollinear ⟨l, hA, hB, hC⟩)
      · exact ⟨C, hC⟩
    · exact ⟨B, hB⟩
  · exact ⟨A, hA⟩

/--
If two distinct points of a line lie in a plane, any point collinear with
those two points lies on that line.
-/
theorem hilbertGrundlagenOnLineOfCollinearWithTwoOnLine
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    {A B X : Geo.Point}
    (hAB : Ne A B)
    {l : Geo.Line}
    (hAl : Geo.OnLine A l)
    (hBl : Geo.OnLine B l)
    (hCol : HilbertGrundlagenCollinear Geo A B X) :
    Geo.OnLine X l := by
  rcases hCol with ⟨m, hAm, hBm, hXm⟩
  have hlm : l = m :=
    H1.I2_line_unique A B hAB l m hAl hBl hAm hBm
  rw [hlm]
  exact hXm

/--
A line and a point outside it determine a unique Hilbert plane.

Existence uses I.3, I.4 and I.6.  Uniqueness uses I.5.
-/
theorem hilbertGrundlagenPlaneThroughLineAndExternalPoint
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (l : Geo.Line)
    (P : Geo.Point)
    (hPl : Not (Geo.OnLine P l)) :
    exists pi : S.Plane,
      HilbertGrundlagenLineInPlane Geo l pi /\
      S.OnPlane P pi /\
      forall rho : S.Plane,
        HilbertGrundlagenLineInPlane Geo l rho ->
        S.OnPlane P rho ->
        rho = pi := by
  rcases H1.I3_two_points_on_each_line l with
    ⟨A, B, hAB, hAl, hBl⟩

  have hABP : Not (HilbertGrundlagenCollinear Geo A B P) := by
    intro hCol
    exact hPl
      (hilbertGrundlagenOnLineOfCollinearWithTwoOnLine
        (Geo := Geo) hAB hAl hBl hCol)

  rcases H1.I4_plane_through A B P hABP with
    ⟨pi, hApi, hBpi, hPpi⟩

  have hlpi : HilbertGrundlagenLineInPlane Geo l pi := by
    intro X hXl
    exact
      H1.I6_line_in_plane
        A B hAB
        l hAl hBl
        pi hApi hBpi
        X hXl

  refine ⟨pi, hlpi, hPpi, ?_⟩
  intro rho hlrho hPrho

  have hArho : S.OnPlane A rho :=
    hlrho A hAl
  have hBrho : S.OnPlane B rho :=
    hlrho B hBl

  exact
    H1.I5_plane_unique
      A B P hABP
      rho pi
      hArho hBrho hPrho
      hApi hBpi hPpi

/--
Every source-faithful Hilbert plane contains three ambiently noncollinear
points.  We also retain two explicit inequalities used by the legacy API.
-/
theorem hilbertGrundlagenThreeNoncollinearOnPlane
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi : S.Plane) :
    exists A B C : Geo.Point,
      Ne A B /\
      Ne A C /\
      S.OnPlane A pi /\
      S.OnPlane B pi /\
      S.OnPlane C pi /\
      Not (HilbertGrundlagenCollinear Geo A B C) := by
  rcases H1.I4_point_on_each_plane pi with
    ⟨A, hApi⟩

  rcases hilbertGrundlagenPointOffPlane
      (Geo := Geo) pi with
    ⟨P, hPpi⟩

  have hAP : Ne A P := by
    intro h
    subst P
    exact hPpi hApi

  rcases H1.I1_line_through A P hAP with
    ⟨l, hAl, hPl⟩

  rcases hilbertGrundlagenPointOffLine
      (Geo := Geo) l with
    ⟨Q, hQl⟩

  rcases hilbertGrundlagenPlaneThroughLineAndExternalPoint
      (Geo := Geo) l Q hQl with
    ⟨beta, hlbeta, hQbeta, hBetaUnique⟩

  have hAbeta : S.OnPlane A beta :=
    hlbeta A hAl
  have hPbeta : S.OnPlane P beta :=
    hlbeta P hPl

  have hPiBeta : Ne pi beta := by
    intro h
    subst beta
    exact hPpi hPbeta

  rcases H1.I7_second_common_point
      pi beta hPiBeta A hApi hAbeta with
    ⟨B, hBA, hBpi, hBbeta⟩

  have hAB : Ne A B :=
    hBA.symm

  rcases hilbertGrundlagenPointOffPlane
      (Geo := Geo) beta with
    ⟨R, hRbeta⟩

  have hRl : Not (Geo.OnLine R l) := by
    intro hRl
    exact hRbeta (hlbeta R hRl)

  rcases hilbertGrundlagenPlaneThroughLineAndExternalPoint
      (Geo := Geo) l R hRl with
    ⟨gamma, hlgamma, hRgamma, hGammaUnique⟩

  have hAgamma : S.OnPlane A gamma :=
    hlgamma A hAl
  have hPgamma : S.OnPlane P gamma :=
    hlgamma P hPl

  have hBetaGamma : Ne beta gamma := by
    intro h
    subst gamma
    exact hRbeta hRgamma

  have hPiGamma : Ne pi gamma := by
    intro h
    subst gamma
    exact hPpi hPgamma

  rcases H1.I7_second_common_point
      pi gamma hPiGamma A hApi hAgamma with
    ⟨C, hCA, hCpi, hCgamma⟩

  have hAC : Ne A C :=
    hCA.symm

  refine ⟨A, B, C, hAB, hAC, hApi, hBpi, hCpi, ?_⟩
  intro hABC

  rcases hABC with
    ⟨m, hAm, hBm, hCm⟩

  have hmbeta : HilbertGrundlagenLineInPlane Geo m beta := by
    intro X hXm
    exact
      H1.I6_line_in_plane
        A B hAB
        m hAm hBm
        beta hAbeta hBbeta
        X hXm

  have hCbeta : S.OnPlane C beta :=
    hmbeta C hCm

  have hAPC : Not (HilbertGrundlagenCollinear Geo A P C) := by
    intro hCol
    rcases hCol with
      ⟨n, hAn, hPn, hCn⟩

    have hnpi : HilbertGrundlagenLineInPlane Geo n pi := by
      intro X hXn
      exact
        H1.I6_line_in_plane
          A C hAC
          n hAn hCn
          pi hApi hCpi
          X hXn

    exact hPpi (hnpi P hPn)

  have hBetaEqGamma : beta = gamma :=
    H1.I5_plane_unique
      A P C hAPC
      beta gamma
      hAbeta hPbeta hCbeta
      hAgamma hPgamma hCgamma

  exact hBetaGamma hBetaEqGamma

/--
Collinearity in the induced plane implies ambient Grundlagen collinearity
of the underlying points.
-/
theorem hilbertPlaneGeoCollinearToAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (A B C : HilbertPlanePoint Geo pi) :
    PrimCollinear (HilbertPlaneGeo Geo pi) A B C ->
      HilbertGrundlagenCollinear Geo A.1 B.1 C.1 := by
  rintro ⟨l, hAl, hBl, hCl⟩
  exact ⟨l.1, hAl, hBl, hCl⟩

/--
Every induced Hilbert plane satisfies the legacy incidence API I.1-I.3.
-/
instance hilbertPlaneGeoHilbertPlaneIncidence
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi : S.Plane) :
    HilbertPlaneIncidence (HilbertPlaneGeo Geo pi) where

  line_through := by
    intro A B hAB

    have hABval : Ne A.1 B.1 := by
      intro h
      apply hAB
      exact Subtype.ext h

    rcases H1.I1_line_through A.1 B.1 hABval with
      ⟨l, hAl, hBl⟩

    have hlpi : HilbertGrundlagenLineInPlane Geo l pi := by
      intro X hXl
      exact
        H1.I6_line_in_plane
          A.1 B.1 hABval
          l hAl hBl
          pi A.2 B.2
          X hXl

    exact ⟨⟨l, hlpi⟩, hAl, hBl⟩

  line_unique := by
    intro A B hAB l m hAl hBl hAm hBm

    have hABval : Ne A.1 B.1 := by
      intro h
      apply hAB
      exact Subtype.ext h

    have hlm : l.1 = m.1 :=
      H1.I2_line_unique
        A.1 B.1 hABval
        l.1 m.1
        hAl hBl hAm hBm

    exact Subtype.ext hlm

  two_points_on_line := by
    rcases hilbertGrundlagenThreeNoncollinearOnPlane
        (Geo := Geo) pi with
      ⟨A, B, C, hAB, hAC, hApi, hBpi, hCpi, hABC⟩

    rcases H1.I1_line_through A B hAB with
      ⟨l, hAl, hBl⟩

    have hlpi : HilbertGrundlagenLineInPlane Geo l pi := by
      intro X hXl
      exact
        H1.I6_line_in_plane
          A B hAB
          l hAl hBl
          pi hApi hBpi
          X hXl

    let A' : HilbertPlanePoint Geo pi := ⟨A, hApi⟩
    let B' : HilbertPlanePoint Geo pi := ⟨B, hBpi⟩

    have hAB' : Ne A' B' := by
      intro h
      exact hAB (congrArg Subtype.val h)

    exact ⟨⟨l, hlpi⟩, A', B', hAB', hAl, hBl⟩

  three_noncollinear := by
    rcases hilbertGrundlagenThreeNoncollinearOnPlane
        (Geo := Geo) pi with
      ⟨A, B, C, hAB, hAC, hApi, hBpi, hCpi, hABC⟩

    let A' : HilbertPlanePoint Geo pi := ⟨A, hApi⟩
    let B' : HilbertPlanePoint Geo pi := ⟨B, hBpi⟩
    let C' : HilbertPlanePoint Geo pi := ⟨C, hCpi⟩

    refine ⟨A', B', C', ?_⟩
    intro hCol
    exact hABC
      (hilbertPlaneGeoCollinearToAmbient
        (Geo := Geo) pi A' B' C' hCol)

/-!
## Two transport lemmas needed for planar Group II

Before constructing the full legacy `HilbertOrder` instance on
`HilbertPlaneGeo Geo pi`, isolate the two conversions used by Pasch and by
the order incidence clauses.
-/

/--
Ambient Grundlagen collinearity of three points of `pi` becomes legacy
collinearity in the induced plane as soon as the first two underlying points
are distinct.
-/
theorem hilbertPlaneGeoCollinearOfAmbientOfNe
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi : S.Plane)
    (A B C : HilbertPlanePoint Geo pi)
    (hAB : Ne A.1 B.1)
    (hCol : HilbertGrundlagenCollinear Geo A.1 B.1 C.1) :
    PrimCollinear (HilbertPlaneGeo Geo pi) A B C := by
  rcases hCol with
    ⟨l, hAl, hBl, hCl⟩

  have hlpi : HilbertGrundlagenLineInPlane Geo l pi := by
    intro X hXl
    exact
      H1.I6_line_in_plane
        A.1 B.1 hAB
        l hAl hBl
        pi A.2 B.2
        X hXl

  exact
    ⟨⟨l, hlpi⟩, hAl, hBl, hCl⟩

/--
A segment of two plane-points meets a plane-line iff the corresponding
ambient segment meets the underlying ambient line.
-/
theorem hilbertPlaneGeoSegmentMeetsLineIffAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (A B : HilbertPlanePoint Geo pi)
    (l : HilbertPlaneLine Geo pi) :
    HilbertSegmentMeetsLine
        (HilbertPlaneGeo Geo pi) A B l <->
      @HilbertSegmentMeetsLine Geo
        (hilbertIncidenceOfGrundlagen Geo) A.1 B.1 l.1 := by
  constructor

  · rintro ⟨X, hAXB, hXl⟩
    exact
      ⟨X.1, hAXB,
        (hilbertOnLineOfGrundlagen_iff Geo X.1 l.1).2 hXl⟩

  · rintro ⟨X, hAXB, hXl⟩

    have hXpi : S.OnPlane X pi :=
      l.2 X
        ((hilbertOnLineOfGrundlagen_iff Geo X l.1).1 hXl)

    exact
      ⟨⟨X, hXpi⟩, hAXB,
        (hilbertOnLineOfGrundlagen_iff Geo X l.1).2
          ((hilbertOnLineOfGrundlagen_iff Geo X l.1).1 hXl)⟩

/-!
## Group II on the induced plane

We can now assemble the complete legacy `HilbertOrder` interface on a fixed
source-faithful Hilbert plane.  No ambient `HilbertOrder Geo` is introduced:
Pasch is specialized to the chosen plane `pi`.
-/

/--
Every induced Hilbert plane satisfies the legacy order interface II.1-II.4.
-/
instance hilbertPlaneGeoHilbertOrder
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane) :
    HilbertOrder (HilbertPlaneGeo Geo pi) where

  toHilbertPlaneIncidence :=
    hilbertPlaneGeoHilbertPlaneIncidence (Geo := Geo) pi

  between_incidence := by
    intro A B C hABC

    rcases H2.II1_between A.1 B.1 C.1 hABC with
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
        PrimCollinear (HilbertPlaneGeo Geo pi) A B C :=
      hilbertPlaneGeoCollinearOfAmbientOfNe
        (Geo := Geo) pi A B C hAB hCol

    exact
      ⟨hABplane, hBCplane, hACplane, hColPlane, hCBA⟩

  between_extension := by
    intro A C hAC

    have hACval : Ne A.1 C.1 := by
      intro h
      apply hAC
      exact Subtype.ext h

    rcases H2.II2_extension A.1 C.1 hACval with
      ⟨B, hACB⟩

    rcases H2.II1_between A.1 C.1 B hACB with
      ⟨_hAC, _hCB, _hAB, hCol, _hBCA⟩

    rcases hCol with
      ⟨l, hAl, hCl, hBl⟩

    have hlpi : HilbertGrundlagenLineInPlane Geo l pi := by
      intro X hXl
      exact
        H1.I6_line_in_plane
          A.1 C.1 hACval
          l hAl hCl
          pi A.2 C.2
          X hXl

    have hBpi : S.OnPlane B pi :=
      hlpi B hBl

    exact
      ⟨⟨B, hBpi⟩, hACB⟩

  between_unique := by
    intro A B C hCol hABC

    have hColAmbient :
        HilbertGrundlagenCollinear Geo A.1 B.1 C.1 :=
      hilbertPlaneGeoCollinearToAmbient
        (Geo := Geo) pi A B C hCol

    exact
      (H2.II3_at_most_one_between
        A.1 B.1 C.1 hColAmbient).1 hABC

  pasch := by
    intro A B C hABC l hAl hBl hCl hABmeet

    have hABmeetAmbient :
        @HilbertSegmentMeetsLine Geo
          (hilbertIncidenceOfGrundlagen Geo)
          A.1 B.1 l.1 :=
      (hilbertPlaneGeoSegmentMeetsLineIffAmbient
        (Geo := Geo) pi A B l).mp hABmeet

    rcases hABmeetAmbient with
      ⟨X, hAXB, hXl⟩

    rcases H2.II1_between A.1 X B.1 hAXB with
      ⟨_hAX, _hXB, hAB, _hColAXB, _hBXA⟩

    have hABCAmbient :
        Not (HilbertGrundlagenCollinear Geo A.1 B.1 C.1) := by
      intro hCol
      exact hABC
        (hilbertPlaneGeoCollinearOfAmbientOfNe
          (Geo := Geo) pi A B C hAB hCol)

    have hAl' : Not (Geo.OnLine A.1 l.1) := by
      intro h
      exact hAl h

    have hBl' : Not (Geo.OnLine B.1 l.1) := by
      intro h
      exact hBl h

    have hCl' : Not (Geo.OnLine C.1 l.1) := by
      intro h
      exact hCl h

    have hABmeetSource :
        exists Y : Geo.Point,
          Geo.Between A.1 Y B.1 /\
          Geo.OnLine Y l.1 := by
      exact
        ⟨X, hAXB,
          (hilbertOnLineOfGrundlagen_iff Geo X l.1).1 hXl⟩

    have hPasch :=
      H2.II4_pasch
        A.1 B.1 C.1 hABCAmbient
        pi A.2 B.2 C.2
        l.1 l.2
        hAl' hBl' hCl'
        hABmeetSource

    rcases hPasch with hACmeet | hBCmeet

    · left

      have hACmeetAmbient :
          @HilbertSegmentMeetsLine Geo
            (hilbertIncidenceOfGrundlagen Geo)
            A.1 C.1 l.1 := by
        rcases hACmeet with
          ⟨Y, hAYC, hYl⟩
        exact
          ⟨Y, hAYC,
            (hilbertOnLineOfGrundlagen_iff Geo Y l.1).2 hYl⟩

      exact
        (hilbertPlaneGeoSegmentMeetsLineIffAmbient
          (Geo := Geo) pi A C l).mpr hACmeetAmbient

    · right

      have hBCmeetAmbient :
          @HilbertSegmentMeetsLine Geo
            (hilbertIncidenceOfGrundlagen Geo)
            B.1 C.1 l.1 := by
        rcases hBCmeet with
          ⟨Z, hBZC, hZl⟩
        exact
          ⟨Z, hBZC,
            (hilbertOnLineOfGrundlagen_iff Geo Z l.1).2 hZl⟩

      exact
        (hilbertPlaneGeoSegmentMeetsLineIffAmbient
          (Geo := Geo) pi B C l).mpr hBCmeetAmbient

/-!
## First congruence transports on the induced plane

Before assembling the full legacy `HilbertCongruence` instance, we isolate
the direct parts III.1-III.3.  The angle axioms III.4-III.5 are left for the
next step because they require explicit transport of plane-side and primitive
angle congruence.
-/

/--
A source-faithful same-ray relation between points of `pi` gives the legacy
same-ray relation in the induced plane.
-/
theorem hilbertPlaneGeoSameRayOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi : S.Plane)
    (O P Q : HilbertPlanePoint Geo pi)
    (hRay : HilbertGrundlagenSameRay Geo O.1 P.1 Q.1) :
    HilbertSameRay (HilbertPlaneGeo Geo pi) O P Q := by
  rcases hRay with
    ⟨hPO, hQO, hCol, hNotBetween⟩

  have hOP : Ne O.1 P.1 :=
    hPO.symm

  have hColPlane :
      PrimCollinear (HilbertPlaneGeo Geo pi) O P Q :=
    hilbertPlaneGeoCollinearOfAmbientOfNe
      (Geo := Geo) pi O P Q hOP hCol

  have hPOplane : Ne P O := by
    intro h
    exact hPO (congrArg Subtype.val h)

  have hQOplane : Ne Q O := by
    intro h
    exact hQO (congrArg Subtype.val h)

  exact
    ⟨hPOplane, hQOplane, hColPlane, hNotBetween⟩

/--
If an ambient point lies on the source-faithful ray `OR`, and `O,R` are
points of `pi`, then that point also lies in `pi`.
-/
theorem hilbertGrundlagenSameRayPointInPlane
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi : S.Plane)
    (O R : HilbertPlanePoint Geo pi)
    (X : Geo.Point)
    (hRay : HilbertGrundlagenSameRay Geo O.1 R.1 X) :
    S.OnPlane X pi := by
  rcases hRay with
    ⟨hRO, hXO, hCol, hNotBetween⟩

  have hOR : Ne O.1 R.1 :=
    hRO.symm

  rcases hCol with
    ⟨l, hOl, hRl, hXl⟩

  exact
    H1.I6_line_in_plane
      O.1 R.1 hOR
      l hOl hRl
      pi O.2 R.2
      X hXl

/-- Compatibility form of III.1 on a fixed induced plane. -/
theorem hilbertPlaneGeoSegmentConstructionOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    [H3 : HilbertGrundlagenGroupIII Geo]
    (pi : S.Plane)
    (A B O R : HilbertPlanePoint Geo pi)
    (hOR : Ne O R) :
    exists X : HilbertPlanePoint Geo pi,
      HilbertSameRay (HilbertPlaneGeo Geo pi) O R X /\
      (HilbertPlaneGeo Geo pi).Congruent O X A B := by
  have hORval : Ne O.1 R.1 := by
    intro h
    apply hOR
    exact Subtype.ext h

  rcases H3.III1_segment_construction
      A.1 B.1 O.1 R.1 hORval with
    ⟨X, hRay, hCong⟩

  have hXpi : S.OnPlane X pi :=
    hilbertGrundlagenSameRayPointInPlane
      (Geo := Geo) pi O R X hRay

  let X' : HilbertPlanePoint Geo pi :=
    ⟨X, hXpi⟩

  have hRayPlane :
      HilbertSameRay (HilbertPlaneGeo Geo pi) O R X' :=
    hilbertPlaneGeoSameRayOfGrundlagen
      (Geo := Geo) pi O R X' hRay

  have hCongPlane :
      (HilbertPlaneGeo Geo pi).Congruent O X' A B := by
    exact hCong

  exact
    ⟨X', hRayPlane, hCongPlane⟩

/-- Compatibility form of III.2 on a fixed induced plane. -/
theorem hilbertPlaneGeoSegmentCongruenceCommonOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    [H3 : HilbertGrundlagenGroupIII Geo]
    (pi : S.Plane)
    (A B A' B' A'' B'' : HilbertPlanePoint Geo pi)
    (h1 : (HilbertPlaneGeo Geo pi).Congruent A B A' B')
    (h2 : (HilbertPlaneGeo Geo pi).Congruent A B A'' B'') :
    (HilbertPlaneGeo Geo pi).Congruent A' B' A'' B'' := by
  exact
    H3.III2_segment_congruence_common
      A.1 B.1 A'.1 B'.1 A''.1 B''.1 h1 h2

/-- Compatibility form of III.3 on a fixed induced plane. -/
theorem hilbertPlaneGeoSegmentAdditivityOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    [H3 : HilbertGrundlagenGroupIII Geo]
    (pi : S.Plane)
    (A B C A' B' C' : HilbertPlanePoint Geo pi)
    (hABC : (HilbertPlaneGeo Geo pi).Between A B C)
    (hA'B'C' : (HilbertPlaneGeo Geo pi).Between A' B' C')
    (hAB : (HilbertPlaneGeo Geo pi).Congruent A B A' B')
    (hBC : (HilbertPlaneGeo Geo pi).Congruent B C B' C') :
    (HilbertPlaneGeo Geo pi).Congruent A C A' C' := by
  exact
    H3.III3_segment_additivity
      A.1 B.1 C.1 A'.1 B'.1 C'.1
      hABC hA'B'C' hAB hBC

/-!
## Same-side transport for III.4

The old planar API uses `HilbertSameSide`, while the source-faithful
Grundlagen formulation uses `HilbertGrundlagenSameSideInPlane`.
On a fixed induced plane these are equivalent.
-/

/-- Source and legacy open-segment/line intersection coincide ambiently. -/
theorem hilbertGrundlagenSegmentMeetsLineIffLegacy
    (A B : Geo.Point)
    (l : Geo.Line) :
    HilbertGrundlagenSegmentMeetsLine Geo A B l <->
      @HilbertSegmentMeetsLine Geo
        (hilbertIncidenceOfGrundlagen Geo) A B l := by
  constructor
  · rintro ⟨X, hAXB, hXl⟩
    exact
      ⟨X, hAXB,
        (hilbertOnLineOfGrundlagen_iff Geo X l).2 hXl⟩
  · rintro ⟨X, hAXB, hXl⟩
    exact
      ⟨X, hAXB,
        (hilbertOnLineOfGrundlagen_iff Geo X l).1 hXl⟩

/--
One legacy same-side step in the induced plane is equivalent to one
source-faithful same-side step in the ambient plane.
-/
theorem hilbertPlaneGeoSameSideStepIffGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (P Q : HilbertPlanePoint Geo pi)
    (l : HilbertPlaneLine Geo pi) :
    HilbertSameSideStep
        (HilbertPlaneGeo Geo pi) P Q l <->
      HilbertGrundlagenSameSideStep
        Geo pi l.1 P.1 Q.1 := by
  unfold HilbertSameSideStep
  unfold HilbertGrundlagenSameSideStep
  constructor

  · rintro ⟨hPl, hQl, hNoMeet⟩
    refine
      ⟨P.2, Q.2, ?_, ?_, ?_⟩

    · exact hPl
    · exact hQl
    · intro hMeet
      apply hNoMeet
      apply
        (hilbertPlaneGeoSegmentMeetsLineIffAmbient
          (Geo := Geo) pi P Q l).2
      apply
        (hilbertGrundlagenSegmentMeetsLineIffLegacy
          (Geo := Geo) P.1 Q.1 l.1).1
      exact hMeet

  · rintro ⟨hPpi, hQpi, hPl, hQl, hNoMeet⟩
    refine
      ⟨hPl, hQl, ?_⟩

    intro hMeet
    apply hNoMeet
    apply
      (hilbertGrundlagenSegmentMeetsLineIffLegacy
        (Geo := Geo) P.1 Q.1 l.1).2
    exact
      (hilbertPlaneGeoSegmentMeetsLineIffAmbient
        (Geo := Geo) pi P Q l).1 hMeet

/--
A legacy same-side chain in the induced plane gives the corresponding
source-faithful ambient chain.
-/
theorem hilbertPlaneGeoSameSideChainToGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (P Q : HilbertPlanePoint Geo pi)
    (l : HilbertPlaneLine Geo pi)
    (hChain :
      Relation.ReflTransGen
        (fun X Y =>
          HilbertSameSideStep
            (HilbertPlaneGeo Geo pi) X Y l)
        P Q) :
    Relation.ReflTransGen
      (fun X Y =>
        HilbertGrundlagenSameSideStep
          Geo pi l.1 X Y)
      P.1 Q.1 := by
  induction hChain with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hAB hBC ih =>
      exact
        Relation.ReflTransGen.tail
          ih
          ((hilbertPlaneGeoSameSideStepIffGrundlagen
            (Geo := Geo) pi _ _ l).1 hBC)

/--
A source-faithful same-side chain beginning at a plane-point can be lifted
to a chain in the induced plane.
-/
theorem hilbertPlaneGeoExistsSameSideChainOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (P : HilbertPlanePoint Geo pi)
    (X : Geo.Point)
    (l : HilbertPlaneLine Geo pi)
    (hChain :
      Relation.ReflTransGen
        (fun A B =>
          HilbertGrundlagenSameSideStep
            Geo pi l.1 A B)
        P.1 X) :
    exists Xp : HilbertPlanePoint Geo pi,
      Xp.1 = X /\
      Relation.ReflTransGen
        (fun A B =>
          HilbertSameSideStep
            (HilbertPlaneGeo Geo pi) A B l)
        P Xp := by
  induction hChain with
  | refl =>
      exact
        ⟨P, rfl, Relation.ReflTransGen.refl⟩

  | @tail B C hAB hBC ih =>
      rcases ih with
        ⟨Bp, hBp, hPlaneAB⟩

      have hCpi : S.OnPlane C pi :=
        hBC.2.1

      let Cp : HilbertPlanePoint Geo pi :=
        ⟨C, hCpi⟩

      have hPlaneBC :
          HilbertSameSideStep
            (HilbertPlaneGeo Geo pi) Bp Cp l := by
        apply
          (hilbertPlaneGeoSameSideStepIffGrundlagen
            (Geo := Geo) pi Bp Cp l).2
        simpa [Cp, hBp] using hBC

      exact
        ⟨Cp,
         rfl,
         Relation.ReflTransGen.tail
           hPlaneAB hPlaneBC⟩

/--
A source-faithful same-side chain whose endpoints are already plane-points
lifts to the corresponding induced-plane chain.
-/
theorem hilbertPlaneGeoSameSideChainOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (P Q : HilbertPlanePoint Geo pi)
    (l : HilbertPlaneLine Geo pi)
    (hChain :
      Relation.ReflTransGen
        (fun A B =>
          HilbertGrundlagenSameSideStep
            Geo pi l.1 A B)
        P.1 Q.1) :
    Relation.ReflTransGen
      (fun A B =>
        HilbertSameSideStep
          (HilbertPlaneGeo Geo pi) A B l)
      P Q := by
  rcases
      hilbertPlaneGeoExistsSameSideChainOfGrundlagen
        (Geo := Geo) pi P Q.1 l hChain with
    ⟨Qp, hQp, hPlaneChain⟩

  have hQpQ : Qp = Q := by
    apply Subtype.ext
    exact hQp

  simpa [hQpQ] using hPlaneChain

/--
Legacy same-side in `HilbertPlaneGeo pi` is exactly source-faithful
same-side in the ambient plane `pi`.
-/
theorem hilbertPlaneGeoSameSideIffGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (P Q : HilbertPlanePoint Geo pi)
    (l : HilbertPlaneLine Geo pi) :
    HilbertSameSide
        (HilbertPlaneGeo Geo pi) P Q l <->
      HilbertGrundlagenSameSideInPlane
        Geo pi l.1 P.1 Q.1 := by
  unfold HilbertSameSide
  unfold HilbertGrundlagenSameSideInPlane
  constructor

  · rintro ⟨hPl, hQl, hChain⟩
    exact
      ⟨l.2,
       P.2,
       Q.2,
       hPl,
       hQl,
       hilbertPlaneGeoSameSideChainToGrundlagen
         (Geo := Geo) pi P Q l hChain⟩

  · rintro ⟨hlpi, hPpi, hQpi, hPl, hQl, hChain⟩
    exact
      ⟨hPl,
       hQl,
       hilbertPlaneGeoSameSideChainOfGrundlagen
         (Geo := Geo) pi P Q l hChain⟩

/-!
## Ray transport for the angle bridge

The old angle representation is built from `Geo.ray`.  Before transporting
III.4 we therefore identify rays of the induced plane with the corresponding
ambient rays.
-/

/-- One same-direction step in the induced plane is exactly the ambient step. -/
theorem hilbertPlaneGeoSameDirectionStepIffAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (O P Q : HilbertPlanePoint Geo pi) :
    (HilbertPlaneGeo Geo pi).SameDirectionStep O P Q <->
      Geo.SameDirectionStep O.1 P.1 Q.1 := by
  unfold Geometry.Geo.SameDirectionStep
  constructor

  · rintro ⟨hPO, hQO, hPQ | hOPQ | hOQP⟩

    · exact
        ⟨fun h => hPO (Subtype.ext h),
         fun h => hQO (Subtype.ext h),
         Or.inl (congrArg Subtype.val hPQ)⟩

    · exact
        ⟨fun h => hPO (Subtype.ext h),
         fun h => hQO (Subtype.ext h),
         Or.inr (Or.inl hOPQ)⟩

    · exact
        ⟨fun h => hPO (Subtype.ext h),
         fun h => hQO (Subtype.ext h),
         Or.inr (Or.inr hOQP)⟩

  · rintro ⟨hPO, hQO, hPQ | hOPQ | hOQP⟩

    · exact
        ⟨fun h => hPO (congrArg Subtype.val h),
         fun h => hQO (congrArg Subtype.val h),
         Or.inl (Subtype.ext hPQ)⟩

    · exact
        ⟨fun h => hPO (congrArg Subtype.val h),
         fun h => hQO (congrArg Subtype.val h),
         Or.inr (Or.inl hOPQ)⟩

    · exact
        ⟨fun h => hPO (congrArg Subtype.val h),
         fun h => hQO (congrArg Subtype.val h),
         Or.inr (Or.inr hOQP)⟩

/--
If two distinct ambient points of `pi` are source-collinear with a third
point, then the third point also belongs to `pi`.
-/
theorem hilbertGrundlagenOnPlaneOfCollinearWithTwoOnPlane
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi : S.Plane)
    (O P Q : Geo.Point)
    (hOP : Ne O P)
    (hOpi : S.OnPlane O pi)
    (hPpi : S.OnPlane P pi)
    (hCol : HilbertGrundlagenCollinear Geo O P Q) :
    S.OnPlane Q pi := by
  rcases hCol with
    ⟨l, hOl, hPl, hQl⟩

  exact
    H1.I6_line_in_plane
      O P hOP
      l hOl hPl
      pi hOpi hPpi
      Q hQl

/--
An ambient elementary same-direction step starting from a point of `pi`,
with origin also in `pi`, stays inside `pi`.
-/
theorem hilbertGrundlagenSameDirectionStepPreservesPlane
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (O P Q : Geo.Point)
    (hOpi : S.OnPlane O pi)
    (hPpi : S.OnPlane P pi)
    (hStep : Geo.SameDirectionStep O P Q) :
    S.OnPlane Q pi := by
  unfold Geometry.Geo.SameDirectionStep at hStep
  rcases hStep with
    ⟨hPO, hQO, hPQ | hOPQ | hOQP⟩

  · rw [hPQ.symm]
    exact hPpi

  · rcases H2.II1_between O P Q hOPQ with
      ⟨_hOP, _hPQ, _hOQ, hCol, _hQPO⟩

    exact
      hilbertGrundlagenOnPlaneOfCollinearWithTwoOnPlane
        (Geo := Geo)
        pi O P Q
        hPO.symm hOpi hPpi hCol

  · rcases H2.II1_between O Q P hOQP with
      ⟨_hOQ, _hQP, _hOP, hColOQP, _hPQO⟩

    rcases hColOQP with
      ⟨l, hOl, hQl, hPl⟩

    have hColOPQ :
        HilbertGrundlagenCollinear Geo O P Q :=
      ⟨l, hOl, hPl, hQl⟩

    exact
      hilbertGrundlagenOnPlaneOfCollinearWithTwoOnPlane
        (Geo := Geo)
        pi O P Q
        hPO.symm hOpi hPpi hColOPQ

/-- Ambient same-direction chains beginning in `pi` remain in `pi`. -/
theorem hilbertGrundlagenSameDirectionChainPreservesPlane
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (O A X : Geo.Point)
    (hOpi : S.OnPlane O pi)
    (hApi : S.OnPlane A pi)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O) A X) :
    S.OnPlane X pi := by
  induction hChain with
  | refl =>
      exact hApi
  | tail hAB hBX ih =>
      exact
        hilbertGrundlagenSameDirectionStepPreservesPlane
          (Geo := Geo)
          pi O _ _
          hOpi ih hBX

/-- A same-direction chain in the induced plane forgets to the ambient chain. -/
theorem hilbertPlaneGeoSameDirectionChainToAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (O A X : HilbertPlanePoint Geo pi)
    (hChain :
      Relation.ReflTransGen
        ((HilbertPlaneGeo Geo pi).SameDirectionStep O)
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
          ((hilbertPlaneGeoSameDirectionStepIffAmbient
            (Geo := Geo) pi O _ _).1 hBX)

/--
An ambient same-direction chain from a plane-point can be lifted to the
induced plane, with the same ambient endpoint.
-/
theorem hilbertPlaneGeoExistsSameDirectionChainOfAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (O A : HilbertPlanePoint Geo pi)
    (X : Geo.Point)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X) :
    exists Xp : HilbertPlanePoint Geo pi,
      Xp.1 = X /\
      Relation.ReflTransGen
        ((HilbertPlaneGeo Geo pi).SameDirectionStep O)
        A Xp := by
  induction hChain with
  | refl =>
      exact
        ⟨A, rfl, Relation.ReflTransGen.refl⟩

  | @tail B C hAB hBC ih =>
      rcases ih with
        ⟨Bp, hBp, hPlaneAB⟩

      have hBpi : S.OnPlane B pi := by
        simpa [hBp] using Bp.2

      have hCpi : S.OnPlane C pi :=
        hilbertGrundlagenSameDirectionStepPreservesPlane
          (Geo := Geo)
          pi O.1 B C
          O.2 hBpi hBC

      let Cp : HilbertPlanePoint Geo pi :=
        ⟨C, hCpi⟩

      have hPlaneBC :
          (HilbertPlaneGeo Geo pi).SameDirectionStep O Bp Cp := by
        apply
          (hilbertPlaneGeoSameDirectionStepIffAmbient
            (Geo := Geo) pi O Bp Cp).2
        simpa [Cp, hBp] using hBC

      exact
        ⟨Cp,
         rfl,
         Relation.ReflTransGen.tail
           hPlaneAB hPlaneBC⟩

/--
An ambient same-direction chain whose endpoint is already a plane-point
lifts to the corresponding induced-plane chain.
-/
theorem hilbertPlaneGeoSameDirectionChainOfAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (O A X : HilbertPlanePoint Geo pi)
    (hChain :
      Relation.ReflTransGen
        (Geo.SameDirectionStep O.1)
        A.1 X.1) :
    Relation.ReflTransGen
      ((HilbertPlaneGeo Geo pi).SameDirectionStep O)
      A X := by
  rcases
      hilbertPlaneGeoExistsSameDirectionChainOfAmbient
        (Geo := Geo) pi O A X.1 hChain with
    ⟨Xp, hXp, hPlaneChain⟩

  have hXpX : Xp = X := by
    apply Subtype.ext
    exact hXp

  simpa [hXpX] using hPlaneChain

/-- Membership in an induced-plane ray is exactly ambient ray membership. -/
theorem hilbertPlaneGeoMemRayIffAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (O A X : HilbertPlanePoint Geo pi) :
    X ∈ (HilbertPlaneGeo Geo pi).ray O A <->
      X.1 ∈ Geo.ray O.1 A.1 := by
  change
    (X = O \/
      Relation.ReflTransGen
        ((HilbertPlaneGeo Geo pi).SameDirectionStep O)
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
          (hilbertPlaneGeoSameDirectionChainToAmbient
            (Geo := Geo) pi O A X hAX)

  · rintro (hXO | hAX)

    · exact
        Or.inl (Subtype.ext hXO)

    · exact
        Or.inr
          (hilbertPlaneGeoSameDirectionChainOfAmbient
            (Geo := Geo) pi O A X hAX)

/-- Every ambient point of a ray determined by two plane-points lies in `pi`. -/
theorem hilbertGrundlagenOnPlaneOfMemRay
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (O A : HilbertPlanePoint Geo pi)
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
      hilbertGrundlagenSameDirectionChainPreservesPlane
        (Geo := Geo)
        pi O.1 A.1 X
        O.2 A.2 hAX

/--
Forgetting plane-membership proofs sends an induced-plane ray exactly to
the corresponding ambient ray.
-/
theorem hilbertPlaneGeoRayToAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (O A : HilbertPlanePoint Geo pi) :
    hilbertPlanePointSetToAmbient
        (Geo := Geo)
        (pi := pi)
        ((HilbertPlaneGeo Geo pi).ray O A) =
      Geo.ray O.1 A.1 := by
  apply Set.ext
  intro X
  constructor

  · rintro ⟨Xp, hXpRay, rfl⟩
    exact
      (hilbertPlaneGeoMemRayIffAmbient
        (Geo := Geo) pi O A Xp).1 hXpRay

  · intro hXRay

    have hXpi : S.OnPlane X pi :=
      hilbertGrundlagenOnPlaneOfMemRay
        (Geo := Geo)
        pi O A X hXRay

    let Xp : HilbertPlanePoint Geo pi :=
      ⟨X, hXpi⟩

    have hXpRay :
        Xp ∈ (HilbertPlaneGeo Geo pi).ray O A := by
      apply
        (hilbertPlaneGeoMemRayIffAmbient
          (Geo := Geo) pi O A Xp).2
      simpa [Xp] using hXRay

    exact
      ⟨Xp, hXpRay, rfl⟩

/-!
## Primitive angle transport

The induced geometry keeps the source-faithful primitive angle relation.
We now show that an actual angle of three plane-points forgets to the
corresponding ambient angle.  This gives the forward bridge from
`HilbertGrundlagenAngleCongruent` to the legacy `Geo.AngleCongruent`.
-/

/-- Mapping an unordered pair commutes with its constructor. -/
theorem hilbertPlaneMapUnorderedPair_mk
    {alpha beta : Type u}
    (f : alpha -> beta)
    (a b : alpha) :
    hilbertPlaneMapUnorderedPair f (UnorderedPair.mk a b) =
      UnorderedPair.mk (f a) (f b) := by
  rfl

/-- Compatibility alias for forgetting the plane subtype from angle data. -/
def hilbertPlaneGeoAngleToAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    {pi : S.Plane}
    (a :
      Prod
        (HilbertPlanePoint Geo pi)
        (UnorderedPair (Set (HilbertPlanePoint Geo pi)))) :
    Prod Geo.Point (UnorderedPair (Set Geo.Point)) :=
  hilbertPlaneAngleDataToAmbient
    (Geo := Geo) (pi := pi) a

/--
The primitive induced-plane angle relation is ambient primitive congruence
restricted to actual point-generated angle data.
-/
theorem hilbertPlaneGeoUnorientedAngleCongruentIffAmbient
    [S : HilbertGrundlagenPrimitive Geo]
    (pi : S.Plane)
    (a b :
      Prod
        (HilbertPlanePoint Geo pi)
        (UnorderedPair (Set (HilbertPlanePoint Geo pi)))) :
    (HilbertPlaneGeo Geo pi).UnorientedAngleCongruent a b <->
      HilbertPlaneActualAngleData
          (Geo := Geo) (pi := pi) a /\
      HilbertPlaneActualAngleData
          (Geo := Geo) (pi := pi) b /\
      Geo.UnorientedAngleCongruent
        (hilbertPlaneGeoAngleToAmbient
          (Geo := Geo) a)
        (hilbertPlaneGeoAngleToAmbient
          (Geo := Geo) b) := by
  rfl

/--
An actual angle in the induced plane forgets to the corresponding ambient
angle.
-/
theorem hilbertPlaneGeoAngleToAmbient_angle
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (A B C : HilbertPlanePoint Geo pi) :
    hilbertPlaneGeoAngleToAmbient
        (Geo := Geo)
        ((HilbertPlaneGeo Geo pi).Angle A B C) =
      Geo.Angle A.1 B.1 C.1 := by
  change
    ( B.1,
      hilbertPlaneMapUnorderedPair
        (hilbertPlanePointSetToAmbient
          (Geo := Geo) (pi := pi))
        (UnorderedPair.mk
          ((HilbertPlaneGeo Geo pi).ray B A)
          ((HilbertPlaneGeo Geo pi).ray B C)) ) =
    ( B.1,
      UnorderedPair.mk
        (Geo.ray B.1 A.1)
        (Geo.ray B.1 C.1) )

  have hMap :
      hilbertPlaneMapUnorderedPair
          (hilbertPlanePointSetToAmbient
            (Geo := Geo) (pi := pi))
          (UnorderedPair.mk
            ((HilbertPlaneGeo Geo pi).ray B A)
            ((HilbertPlaneGeo Geo pi).ray B C)) =
        UnorderedPair.mk
          (hilbertPlanePointSetToAmbient
            (Geo := Geo) (pi := pi)
            ((HilbertPlaneGeo Geo pi).ray B A))
          (hilbertPlanePointSetToAmbient
            (Geo := Geo) (pi := pi)
            ((HilbertPlaneGeo Geo pi).ray B C)) := by
    exact
      hilbertPlaneMapUnorderedPair_mk
        (hilbertPlanePointSetToAmbient
          (Geo := Geo) (pi := pi))
        ((HilbertPlaneGeo Geo pi).ray B A)
        ((HilbertPlaneGeo Geo pi).ray B C)

  rw [hMap]

  rw [
    hilbertPlaneGeoRayToAmbient
      (Geo := Geo) pi B A,
    hilbertPlaneGeoRayToAmbient
      (Geo := Geo) pi B C
  ]

/--
Source-faithful primitive congruence of two ambient angles becomes primitive
angle congruence of the corresponding induced-plane angles.
-/
theorem hilbertPlaneGeoPrimitiveAngleCongruentOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (A B C D E F : HilbertPlanePoint Geo pi)
    (h :
      HilbertGrundlagenAngleCongruent
        Geo A.1 B.1 C.1 D.1 E.1 F.1) :
    (HilbertPlaneGeo Geo pi).UnorientedAngleCongruent
      ((HilbertPlaneGeo Geo pi).Angle A B C)
      ((HilbertPlaneGeo Geo pi).Angle D E F) := by
  apply
    (hilbertPlaneGeoUnorientedAngleCongruentIffAmbient
      (Geo := Geo)
      pi
      ((HilbertPlaneGeo Geo pi).Angle A B C)
      ((HilbertPlaneGeo Geo pi).Angle D E F)).2

  refine
    ⟨?_, ?_, ?_⟩

  · exact
      ⟨A, B, C,
       hilbertPlaneGeoAngleRaw
         (Geo := Geo) pi A B C⟩

  · exact
      ⟨D, E, F,
       hilbertPlaneGeoAngleRaw
         (Geo := Geo) pi D E F⟩

  · rw [
      hilbertPlaneGeoAngleToAmbient_angle
        (Geo := Geo) pi A B C,
      hilbertPlaneGeoAngleToAmbient_angle
        (Geo := Geo) pi D E F
    ]

    exact h

/--
Forward compatibility bridge: source-faithful primitive angle congruence
implies the legacy equivalence-closed `Geo.AngleCongruent` relation.
-/
theorem hilbertPlaneGeoAngleCongruentOfGrundlagen
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    [H2 : HilbertGrundlagenGroupII Geo]
    (pi : S.Plane)
    (A B C D E F : HilbertPlanePoint Geo pi)
    (h :
      HilbertGrundlagenAngleCongruent
        Geo A.1 B.1 C.1 D.1 E.1 F.1) :
    (HilbertPlaneGeo Geo pi).AngleCongruent
      A B C D E F := by
  unfold Geometry.Geo.AngleCongruent
  exact
    Relation.EqvGen.rel
      ((HilbertPlaneGeo Geo pi).Angle A B C)
      ((HilbertPlaneGeo Geo pi).Angle D E F)
      (hilbertPlaneGeoPrimitiveAngleCongruentOfGrundlagen
        (Geo := Geo) pi A B C D E F h)

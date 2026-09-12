import CGJteamLab.HilbertPlaneTheory

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert spatial incidence

Derived incidence theory for Hilbert's spatial geometry.

The only foundational import is `HilbertAxioms.lean`.  No separate
three-dimensional axiom system is introduced here.

All results in this file are derived directly from

* `HilbertGrundlagenPrimitive`,
* `HilbertGrundlagenGroupI`.

In particular, the spatial incidence axioms I.4-I.8 remain part of the
single source-faithful Hilbert foundation.  This module contains only
their geometric consequences.

The file is intended to replace the incidence part of the former
`Hilbert3DInterface.lean`, not to recreate `Hilbert3DAxioms.lean`.
-/
/--
Every plane has a point outside it.

This is an immediate consequence of Hilbert I.8.
-/
theorem hilbertSpace_point_off_plane
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi : S.Plane) :
    exists P : Geo.Point,
      Not (S.OnPlane P pi) := by
  cases H1.I8_four_noncoplanar with
  | intro A hArest =>
    cases hArest with
    | intro B hBrest =>
      cases hBrest with
      | intro C hCrest =>
        cases hCrest with
        | intro D hNoncoplanar =>
          by_cases hA : S.OnPlane A pi
          case neg =>
            exact Exists.intro A hA
          case pos =>
            by_cases hB : S.OnPlane B pi
            case neg =>
              exact Exists.intro B hB
            case pos =>
              by_cases hC : S.OnPlane C pi
              case neg =>
                exact Exists.intro C hC
              case pos =>
                by_cases hD : S.OnPlane D pi
                case neg =>
                  exact Exists.intro D hD
                case pos =>
                  apply False.elim
                  apply hNoncoplanar
                  exact
                    Exists.intro pi
                      (And.intro hA
                        (And.intro hB
                          (And.intro hC hD)))

/--
If `A` and `B` are distinct points of a line `l`, then every point
source-collinear with `A` and `B` lies on `l`.

This is the direct I.2 consequence needed repeatedly in spatial
incidence arguments.
-/
theorem hilbertSpace_on_line_of_collinear_with_two_on_line
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    {A B X : Geo.Point}
    (hAB : Ne A B)
    {l : Geo.Line}
    (hAl : Geo.OnLine A l)
    (hBl : Geo.OnLine B l)
    (hCol : HilbertGrundlagenCollinear Geo A B X) :
    Geo.OnLine X l := by
  cases hCol with
  | intro m hm =>
    have hAm : Geo.OnLine A m := hm.1
    have hBm : Geo.OnLine B m := hm.2.1
    have hXm : Geo.OnLine X m := hm.2.2

    have hlm : l = m :=
      H1.I2_line_unique
        A B hAB
        l m
        hAl hBl hAm hBm

    rw [hlm]
    exact hXm

/--
Two distinct planes having a common point intersect in exactly one line.

More precisely, the theorem produces a line `l` such that a point lies
in both planes iff it lies on `l`.

This is the source-faithful replacement of the first substantial
incidence theorem in the old `Hilbert3DInterface.lean`.
-/
theorem hilbertSpace_plane_intersection_line
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi rho : S.Plane)
    (hneq : Ne pi rho)
    (A : Geo.Point)
    (hApi : S.OnPlane A pi)
    (hArho : S.OnPlane A rho) :
    exists l : Geo.Line,
      Geo.OnLine A l /\
      HilbertGrundlagenLineInPlane Geo l pi /\
      HilbertGrundlagenLineInPlane Geo l rho /\
      forall X : Geo.Point,
        (S.OnPlane X pi /\ S.OnPlane X rho) <->
          Geo.OnLine X l := by
  cases
      H1.I7_second_common_point
        pi rho hneq
        A hApi hArho with
  | intro B hBdata =>
    have hBA : Ne B A := hBdata.1
    have hBpi : S.OnPlane B pi := hBdata.2.1
    have hBrho : S.OnPlane B rho := hBdata.2.2
    have hAB : Ne A B := hBA.symm

    cases H1.I1_line_through A B hAB with
    | intro l hLdata =>
      have hAl : Geo.OnLine A l := hLdata.1
      have hBl : Geo.OnLine B l := hLdata.2

      have hlpi : HilbertGrundlagenLineInPlane Geo l pi := by
        intro X hXl
        exact
          H1.I6_line_in_plane
            A B hAB
            l hAl hBl
            pi hApi hBpi
            X hXl

      have hlrho : HilbertGrundlagenLineInPlane Geo l rho := by
        intro X hXl
        exact
          H1.I6_line_in_plane
            A B hAB
            l hAl hBl
            rho hArho hBrho
            X hXl

      refine Exists.intro l ?_
      refine And.intro hAl ?_
      refine And.intro hlpi ?_
      refine And.intro hlrho ?_
      intro X
      apply Iff.intro

      case mp =>
        intro hBoth
        have hXpi : S.OnPlane X pi := hBoth.1
        have hXrho : S.OnPlane X rho := hBoth.2

        by_cases hXl : Geo.OnLine X l
        case pos =>
          exact hXl
        case neg =>
          have hNoncol :
              Not (HilbertGrundlagenCollinear Geo A B X) := by
            intro hCol
            apply hXl
            exact
              hilbertSpace_on_line_of_collinear_with_two_on_line
                (Geo := Geo)
                hAB hAl hBl hCol

          have hpirho : pi = rho :=
            H1.I5_plane_unique
              A B X hNoncol
              pi rho
              hApi hBpi hXpi
              hArho hBrho hXrho

          exact False.elim (hneq hpirho)

      case mpr =>
        intro hXl
        exact And.intro (hlpi X hXl) (hlrho X hXl)


/--
A line together with a point outside it determines a unique plane.

Existence uses I.3, I.4 and I.6. Uniqueness uses I.5.
-/
theorem hilbertSpace_plane_through_line_and_external_point
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
  cases H1.I3_two_points_on_each_line l with
  | intro A hArest =>
    cases hArest with
    | intro B hData =>
      have hAB : Ne A B := hData.1
      have hAl : Geo.OnLine A l := hData.2.1
      have hBl : Geo.OnLine B l := hData.2.2

      have hABP :
          Not (HilbertGrundlagenCollinear Geo A B P) := by
        intro hCol
        apply hPl
        exact
          hilbertSpace_on_line_of_collinear_with_two_on_line
            (Geo := Geo)
            hAB hAl hBl hCol

      cases H1.I4_plane_through A B P hABP with
      | intro pi hPiData =>
        have hApi : S.OnPlane A pi := hPiData.1
        have hBpi : S.OnPlane B pi := hPiData.2.1
        have hPpi : S.OnPlane P pi := hPiData.2.2

        have hlpi : HilbertGrundlagenLineInPlane Geo l pi := by
          intro X hXl
          exact
            H1.I6_line_in_plane
              A B hAB
              l hAl hBl
              pi hApi hBpi
              X hXl

        refine Exists.intro pi ?_
        refine And.intro hlpi ?_
        refine And.intro hPpi ?_
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
Given any point `P` and line `l`, there is a point of `l` distinct from
`P`.

Only the universal line clause of I.3 is needed.
-/
theorem hilbertSpace_other_point_on_line
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (l : Geo.Line)
    (P : Geo.Point) :
    exists Q : Geo.Point,
      Ne Q P /\
      Geo.OnLine Q l := by
  cases H1.I3_two_points_on_each_line l with
  | intro A hArest =>
    cases hArest with
    | intro B hData =>
      have hAB : Ne A B := hData.1
      have hAl : Geo.OnLine A l := hData.2.1
      have hBl : Geo.OnLine B l := hData.2.2

      by_cases hAP : A = P
      case neg =>
        exact
          Exists.intro A
            (And.intro hAP hAl)
      case pos =>
        subst A
        exact
          Exists.intro B
            (And.intro hAB.symm hBl)

/--
Two distinct intersecting lines determine a unique plane.

Existence uses I.1, I.4 and I.6. Uniqueness uses I.5.
-/
theorem hilbertSpace_plane_through_two_intersecting_lines
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (l m : Geo.Line)
    (hlm : Ne l m)
    (P : Geo.Point)
    (hPl : Geo.OnLine P l)
    (hPm : Geo.OnLine P m) :
    exists pi : S.Plane,
      HilbertGrundlagenLineInPlane Geo l pi /\
      HilbertGrundlagenLineInPlane Geo m pi /\
      forall rho : S.Plane,
        HilbertGrundlagenLineInPlane Geo l rho ->
        HilbertGrundlagenLineInPlane Geo m rho ->
        rho = pi := by
  cases
      hilbertSpace_other_point_on_line
        (Geo := Geo) l P with
  | intro A hAData =>
    have hAP : Ne A P := hAData.1
    have hAl : Geo.OnLine A l := hAData.2

    cases
        hilbertSpace_other_point_on_line
          (Geo := Geo) m P with
    | intro B hBData =>
      have hBP : Ne B P := hBData.1
      have hBm : Geo.OnLine B m := hBData.2

      have hAPB :
          Not (HilbertGrundlagenCollinear Geo A P B) := by
        intro hCol
        cases hCol with
        | intro n hNData =>
          have hAn : Geo.OnLine A n := hNData.1
          have hPn : Geo.OnLine P n := hNData.2.1
          have hBn : Geo.OnLine B n := hNData.2.2

          have hln : l = n :=
            H1.I2_line_unique
              A P hAP
              l n
              hAl hPl hAn hPn

          have hmn : m = n :=
            H1.I2_line_unique
              B P hBP
              m n
              hBm hPm hBn hPn

          exact hlm (hln.trans hmn.symm)

      cases H1.I4_plane_through A P B hAPB with
      | intro pi hPiData =>
        have hApi : S.OnPlane A pi := hPiData.1
        have hPpi : S.OnPlane P pi := hPiData.2.1
        have hBpi : S.OnPlane B pi := hPiData.2.2

        have hlpi : HilbertGrundlagenLineInPlane Geo l pi := by
          intro X hXl
          exact
            H1.I6_line_in_plane
              A P hAP
              l hAl hPl
              pi hApi hPpi
              X hXl

        have hmpi : HilbertGrundlagenLineInPlane Geo m pi := by
          intro X hXm
          exact
            H1.I6_line_in_plane
              B P hBP
              m hBm hPm
              pi hBpi hPpi
              X hXm

        refine Exists.intro pi ?_
        refine And.intro hlpi ?_
        refine And.intro hmpi ?_
        intro rho hlrho hmrho

        have hArho : S.OnPlane A rho :=
          hlrho A hAl

        have hPrho : S.OnPlane P rho :=
          hlrho P hPl

        have hBrho : S.OnPlane B rho :=
          hmrho B hBm

        exact
          H1.I5_plane_unique
            A P B hAPB
            rho pi
            hArho hPrho hBrho
            hApi hPpi hBpi


/--
Every line has a point outside it.

This is a direct consequence of Hilbert I.3:
there exist three noncollinear points, so they cannot all lie on one
given line.
-/
theorem hilbertSpace_point_off_line
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (l : Geo.Line) :
    exists P : Geo.Point,
      Not (Geo.OnLine P l) := by
  cases H1.I3_three_noncollinear with
  | intro A hArest =>
    cases hArest with
    | intro B hBrest =>
      cases hBrest with
      | intro C hData =>
        have hNoncol :
            Not (HilbertGrundlagenCollinear Geo A B C) :=
          hData.2.2.2

        by_cases hAl : Geo.OnLine A l
        case neg =>
          exact Exists.intro A hAl

        case pos =>
          by_cases hBl : Geo.OnLine B l
          case neg =>
            exact Exists.intro B hBl

          case pos =>
            by_cases hCl : Geo.OnLine C l
            case neg =>
              exact Exists.intro C hCl

            case pos =>
              apply False.elim
              apply hNoncol
              exact
                Exists.intro l
                  (And.intro hAl
                    (And.intro hBl hCl))

/--
Every Hilbert plane contains three ambiently noncollinear points.

This is a derived spatial incidence theorem, not an additional axiom.
The proof uses only Group I.
-/
theorem hilbertSpace_three_noncollinear_on_plane
    [S : HilbertGrundlagenPrimitive Geo]
    [H1 : HilbertGrundlagenGroupI Geo]
    (pi : S.Plane) :
    exists A B C : Geo.Point,
      S.OnPlane A pi /\
      S.OnPlane B pi /\
      S.OnPlane C pi /\
      Not (HilbertGrundlagenCollinear Geo A B C) := by
  cases H1.I4_point_on_each_plane pi with
  | intro A hApi =>

    cases
        hilbertSpace_point_off_plane
          (Geo := Geo) pi with
    | intro P hPpi =>

      have hAP : Ne A P := by
        intro h
        subst P
        exact hPpi hApi

      cases H1.I1_line_through A P hAP with
      | intro l hLdata =>
        have hAl : Geo.OnLine A l := hLdata.1
        have hPl : Geo.OnLine P l := hLdata.2

        cases
            hilbertSpace_point_off_line
              (Geo := Geo) l with
        | intro Q hQl =>

          cases
              hilbertSpace_plane_through_line_and_external_point
                (Geo := Geo) l Q hQl with
          | intro beta hBetaData =>
            have hlbeta :
                HilbertGrundlagenLineInPlane Geo l beta :=
              hBetaData.1
            have hQbeta : S.OnPlane Q beta :=
              hBetaData.2.1

            have hAbeta : S.OnPlane A beta :=
              hlbeta A hAl

            have hPbeta : S.OnPlane P beta :=
              hlbeta P hPl

            have hPiBeta : Ne pi beta := by
              intro h
              subst beta
              exact hPpi hPbeta

            cases
                H1.I7_second_common_point
                  pi beta hPiBeta
                  A hApi hAbeta with
            | intro B hBdata =>
              have hBA : Ne B A := hBdata.1
              have hBpi : S.OnPlane B pi := hBdata.2.1
              have hBbeta : S.OnPlane B beta := hBdata.2.2

              cases
                  hilbertSpace_point_off_plane
                    (Geo := Geo) beta with
              | intro R hRbeta =>

                have hRl : Not (Geo.OnLine R l) := by
                  intro hRl
                  exact hRbeta (hlbeta R hRl)

                cases
                    hilbertSpace_plane_through_line_and_external_point
                      (Geo := Geo) l R hRl with
                | intro gamma hGammaData =>
                  have hlgamma :
                      HilbertGrundlagenLineInPlane Geo l gamma :=
                    hGammaData.1
                  have hRgamma : S.OnPlane R gamma :=
                    hGammaData.2.1

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

                  cases
                      H1.I7_second_common_point
                        pi gamma hPiGamma
                        A hApi hAgamma with
                  | intro C hCdata =>
                    have hCA : Ne C A := hCdata.1
                    have hCpi : S.OnPlane C pi := hCdata.2.1
                    have hCgamma : S.OnPlane C gamma := hCdata.2.2

                    refine Exists.intro A ?_
                    refine Exists.intro B ?_
                    refine Exists.intro C ?_
                    refine And.intro hApi ?_
                    refine And.intro hBpi ?_
                    refine And.intro hCpi ?_
                    intro hABC

                    cases hABC with
                    | intro m hMdata =>
                      have hAm : Geo.OnLine A m := hMdata.1
                      have hBm : Geo.OnLine B m := hMdata.2.1
                      have hCm : Geo.OnLine C m := hMdata.2.2

                      have hAB : Ne A B := hBA.symm

                      have hmbeta :
                          HilbertGrundlagenLineInPlane Geo m beta := by
                        intro X hXm
                        exact
                          H1.I6_line_in_plane
                            A B hAB
                            m hAm hBm
                            beta hAbeta hBbeta
                            X hXm

                      have hCbeta : S.OnPlane C beta :=
                        hmbeta C hCm

                      have hAPC :
                          Not (HilbertGrundlagenCollinear Geo A P C) := by
                        intro hCol
                        cases hCol with
                        | intro n hNdata =>
                          have hAn : Geo.OnLine A n := hNdata.1
                          have hPn : Geo.OnLine P n := hNdata.2.1
                          have hCn : Geo.OnLine C n := hNdata.2.2

                          have hAC : Ne A C := hCA.symm

                          have hnpi :
                              HilbertGrundlagenLineInPlane Geo n pi := by
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

/-!
# Compatibility facade for the former Hilbert3DAxioms API

This section preserves the public spatial API used by the existing
downstream library.  It is a migration facade, not a second foundational
axiom file.

The plane sort itself is identified with the source-faithful plane sort
from `HilbertAxioms.lean`.  The remaining records keep the old field names
and signatures so that `Hilbert3DInterface.lean` and its downstream users
can first migrate by changing only their import.

After that import boundary is stable, the compatibility records can be
connected progressively to the source-faithful Groups I-IV without
rewriting the whole downstream library at once.
-/

/--
Compatibility primitive plane signature.

This is intentionally a real structure rather than an abbreviation.
Several downstream structures use `extends HilbertSpacePrimitive Geo`
and therefore rely on the generated projection name
`toHilbertSpacePrimitive`.

No geometric axiom is added here: the structure contains only the type
of planes and point-plane incidence.
-/
class HilbertSpacePrimitive (Geo : Geometry.Geo) where
  Plane : Type u

  OnPlane :
    Geo.Point -> Plane -> Prop

/--
Canonical passage from the compatibility primitive signature to the
source-faithful primitive signature.

The plane type and point-plane incidence are definitionally inherited;
no geometric assumption is introduced.
-/
@[instance_reducible]
def hilbertGrundlagenPrimitiveOfSpacePrimitive
    [S : HilbertSpacePrimitive Geo] :
    HilbertGrundlagenPrimitive Geo where
  Plane := S.Plane
  OnPlane := S.OnPlane

/--
The type of planes in the ambient Hilbert space.
-/
abbrev SpacePlane
    (Geo : Geometry.Geo)
    [S : HilbertSpacePrimitive Geo] :=
  S.Plane

/--
Legacy spatial line-in-plane predicate.
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
Legacy spatial coplanarity predicate for four points.
-/
def HilbertCoplanar4
    [S : HilbertSpacePrimitive Geo]
    (A B C D : Geo.Point) : Prop :=
  exists pi : S.Plane,
    S.OnPlane A pi /\
    S.OnPlane B pi /\
    S.OnPlane C pi /\
    S.OnPlane D pi

/--
Compatibility record for the spatial incidence API formerly declared in
`Hilbert3DAxioms.lean`.

This declaration is retained only so existing downstream theorem
signatures remain unchanged during the import migration.
-/
class HilbertSpaceIncidence
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop where

  two_points_on_each_line :
    forall l : Geo.Line,
      exists A B : Geo.Point,
        Ne A B /\
        H.OnLine A l /\
        H.OnLine B l

  plane_through :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      exists pi : S.Plane,
        S.OnPlane A pi /\
        S.OnPlane B pi /\
        S.OnPlane C pi

  point_on_each_plane :
    forall pi : S.Plane,
      exists A : Geo.Point,
        S.OnPlane A pi

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

  four_noncoplanar :
    exists A B C D : Geo.Point,
      Not (HilbertCoplanar4 Geo A B C D)

/--
One elementary same-side step inside a specified ambient plane.
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
Two points are on the same side of a line inside a specified ambient
plane.
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
Compatibility record for the former spatial Group II API.
-/
class HilbertSpaceOrder
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo] : Prop where

  between_incidence :
    forall A B C : Geo.Point,
      Geo.Between A B C ->
      Ne A B /\
      Ne B C /\
      Ne A C /\
      PrimCollinear Geo A B C /\
      Geo.Between C B A

  between_extension :
    forall A C : Geo.Point,
      Ne A C ->
      exists B : Geo.Point,
        Geo.Between A C B

  between_unique :
    forall A B C : Geo.Point,
      PrimCollinear Geo A B C ->
      Geo.Between A B C ->
      Not (Geo.Between B A C) /\
      Not (Geo.Between A C B)

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
Compatibility record for the former spatial Group III API.
-/
class HilbertSpaceCongruence
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    [HilbertSpaceOrder Geo] : Prop where

  segment_construction :
    forall A B O R : Geo.Point,
      Ne O R ->
      exists X : Geo.Point,
        HilbertSameRay Geo O R X /\
        Geo.Congruent O X A B

  segment_congruence_common :
    forall A B A' B' A'' B'' : Geo.Point,
      Geo.Congruent A B A' B' ->
      Geo.Congruent A B A'' B'' ->
      Geo.Congruent A' B' A'' B''

  segment_additivity :
    forall A B C A' B' C' : Geo.Point,
      Geo.Between A B C ->
      Geo.Between A' B' C' ->
      Geo.Congruent A B A' B' ->
      Geo.Congruent B C B' C' ->
      Geo.Congruent A C A' C'

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

  angle_congruence_reflexive :
    forall A B C : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      Geo.AngleCongruent A B C A B C

  sas :
    forall A B C A' B' C' : Geo.Point,
      Not (PrimCollinear Geo A B C) ->
      Not (PrimCollinear Geo A' B' C') ->
      Geo.Congruent A B A' B' ->
      Geo.Congruent A C A' C' ->
      Geo.AngleCongruent B A C B' A' C' ->
      Geo.AngleCongruent A B C A' B' C'

/--
Compatibility record for the former spatial Group IV API.
-/
class HilbertSpaceEuclidean
    (Geo : Geometry.Geo)
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertSpaceIncidence Geo]
    [HilbertSpaceOrder Geo]
    [HilbertSpaceCongruence Geo] : Prop where

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

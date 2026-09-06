import CGJteamLab.HilbertDimensionFreeProjective
import CGJteamLab.HilbertDimensionFreeExchange

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Dimension-free Wyler plane cones

This module contains the geometric core of the Smith/Wyler exchange proof.

For a Smith flat F, a point P in F, and an apex A outside F,
`WylerPlaneCone` is the union of all planes l A where l runs through the
lines through P contained in F. Using local Veblen-Young P3 and Smith I5
we prove that this cone is itself a Smith flat.

No exchange principle is assumed in this module.
-/

def WylerPlaneCone
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (F : Set Geo.Point)
    (P A : Geo.Point) : Set Geo.Point :=
  fun X =>
    exists l : Geo.Line,
      exists alpha : S.Plane,
        H.OnLine P l /\
        (forall Y : Geo.Point, H.OnLine Y l -> F Y) /\
        HilbertLineInPlane Geo l alpha /\
        S.OnPlane A alpha /\
        S.OnPlane X alpha

def WylerOnePointGenerationFormula
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall F : Set Geo.Point,
    SmithFlat Geo F ->
    forall P R : Geo.Point,
      F P ->
      F R ->
      Ne P R ->
      forall A : Geo.Point,
        Not (F A) ->
        SmithSpan Geo (SmithAdjoinPoint Geo F A) =
          WylerPlaneCone Geo F P A

theorem wylerPlaneCone_swap_apex
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (F : Set Geo.Point)
    (P A B : Geo.Point)
    (hB : WylerPlaneCone Geo F P A B) :
    WylerPlaneCone Geo F P B A := by

  rcases hB with
    ⟨l, alpha, hPl, hlF, hlalpha, hAalpha, hBalpha⟩

  exact
    ⟨l, alpha,
     hPl,
     hlF,
     hlalpha,
     hBalpha,
     hAalpha⟩

theorem smithFlat_line_through_two
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P R : Geo.Point)
    (hPF : F P)
    (hRF : F R)
    (hPR : Ne P R)
    (l : Geo.Line)
    (hPl : H.OnLine P l)
    (hRl : H.OnLine R l) :
    forall X : Geo.Point,
      H.OnLine X l ->
      F X := by

  exact
    hFlat.1
      P R
      hPF hRF hPR
      l hPl hRl

theorem wylerPlaneCone_contains_base
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P R A : Geo.Point)
    (hPF : F P)
    (hRF : F R)
    (hPR : Ne P R)
    (hAOut : Not (F A)) :
    Set.Subset F (WylerPlaneCone Geo F P A) := by

  intro X hXF

  by_cases hPX : P = X

  · subst X

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          P R hPR with
      ⟨l, hPl, hRl⟩

    have hlF :
        forall Y : Geo.Point,
          H.OnLine Y l ->
          F Y :=
      smithFlat_line_through_two
        (Geo := Geo)
        F hFlat
        P R
        hPF hRF hPR
        l hPl hRl

    have hAl : Not (H.OnLine A l) := by
      intro hAl
      exact hAOut (hlF A hAl)

    rcases
        smithCore_plane_through_line_and_external_point
          (Geo := Geo)
          l A hAl with
      ⟨alpha, hlAlpha, hAAlpha⟩

    exact
      ⟨l, alpha,
       hPl,
       hlF,
       hlAlpha,
       hAAlpha,
       hlAlpha P hPl⟩

  · have hPXne : Ne P X := hPX

    rcases
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          P X hPXne with
      ⟨l, hPl, hXl⟩

    have hlF :
        forall Y : Geo.Point,
          H.OnLine Y l ->
          F Y :=
      smithFlat_line_through_two
        (Geo := Geo)
        F hFlat
        P X
        hPF hXF hPXne
        l hPl hXl

    have hAl : Not (H.OnLine A l) := by
      intro hAl
      exact hAOut (hlF A hAl)

    rcases
        smithCore_plane_through_line_and_external_point
          (Geo := Geo)
          l A hAl with
      ⟨alpha, hlAlpha, hAAlpha⟩

    exact
      ⟨l, alpha,
       hPl,
       hlF,
       hlAlpha,
       hAAlpha,
       hlAlpha X hXl⟩

theorem wylerPlaneCone_contains_apex
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P R A : Geo.Point)
    (hPF : F P)
    (hRF : F R)
    (hPR : Ne P R)
    (hAOut : Not (F A)) :
    WylerPlaneCone Geo F P A A := by

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        P R hPR with
    ⟨l, hPl, hRl⟩

  have hlF :
      forall Y : Geo.Point,
        H.OnLine Y l ->
        F Y :=
    smithFlat_line_through_two
      (Geo := Geo)
      F hFlat
      P R
      hPF hRF hPR
      l hPl hRl

  have hAl : Not (H.OnLine A l) := by
    intro hAl
    exact hAOut (hlF A hAl)

  rcases
      smithCore_plane_through_line_and_external_point
        (Geo := Geo)
        l A hAl with
    ⟨alpha, hlAlpha, hAAlpha⟩

  exact
    ⟨l, alpha,
     hPl,
     hlF,
     hlAlpha,
     hAAlpha,
     hAAlpha⟩

theorem wylerPlaneCone_subset_span
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (P A : Geo.Point)
    (hAOut : Not (F A)) :
    Set.Subset
      (WylerPlaneCone Geo F P A)
      (SmithSpan Geo (SmithAdjoinPoint Geo F A)) := by

  intro X hX

  rcases hX with
    ⟨l, alpha, _hPl, hlF, hlAlpha, hAAlpha, hXAlpha⟩

  rcases
      C.two_points_on_each_line l with
    ⟨U, V, hUV, hUl, hVl⟩

  have hUF : F U :=
    hlF U hUl

  have hVF : F V :=
    hlF V hVl

  have hUSpan :
      SmithSpan Geo (SmithAdjoinPoint Geo F A) U :=
    smithSpan_extensive
      (Geo := Geo)
      (SmithAdjoinPoint Geo F A)
      (Or.inr hUF)

  have hVSpan :
      SmithSpan Geo (SmithAdjoinPoint Geo F A) V :=
    smithSpan_extensive
      (Geo := Geo)
      (SmithAdjoinPoint Geo F A)
      (Or.inr hVF)

  have hASpan :
      SmithSpan Geo (SmithAdjoinPoint Geo F A) A :=
    smithSpan_extensive
      (Geo := Geo)
      (SmithAdjoinPoint Geo F A)
      (Or.inl rfl)

  have hUVA :
      Not (PrimCollinear Geo U V A) := by

    intro hCol

    have hAl : H.OnLine A l :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        U V A hUV
        l hUl hVl
        hCol

    exact hAOut (hlF A hAl)

  have hSpanFlat :
      SmithFlat Geo
        (SmithSpan Geo (SmithAdjoinPoint Geo F A)) :=
    smithSpan_flat
      (Geo := Geo)
      (SmithAdjoinPoint Geo F A)

  exact
    hSpanFlat.2
      U V A
      hUSpan hVSpan hASpan
      hUVA
      alpha
      (hlAlpha U hUl)
      (hlAlpha V hVl)
      hAAlpha
      X hXAlpha

def WylerPlaneConeFlatness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall F : Set Geo.Point,
    SmithFlat Geo F ->
    forall P R : Geo.Point,
      F P ->
      F R ->
      Ne P R ->
      forall A : Geo.Point,
        Not (F A) ->
        SmithFlat Geo (WylerPlaneCone Geo F P A)

theorem wylerPlaneConeFlatness_implies_onePointGenerationFormula
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hConeFlat : WylerPlaneConeFlatness Geo) :
    WylerOnePointGenerationFormula Geo := by

  intro F hFlat P R hPF hRF hPR A hAOut

  have hConeIsFlat :
      SmithFlat Geo (WylerPlaneCone Geo F P A) :=
    hConeFlat
      F hFlat
      P R
      hPF hRF hPR
      A hAOut

  have hBaseInCone :
      Set.Subset F (WylerPlaneCone Geo F P A) :=
    wylerPlaneCone_contains_base
      (Geo := Geo)
      F hFlat
      P R A
      hPF hRF hPR
      hAOut

  have hAInCone :
      WylerPlaneCone Geo F P A A :=
    wylerPlaneCone_contains_apex
      (Geo := Geo)
      F hFlat
      P R A
      hPF hRF hPR
      hAOut

  apply Set.Subset.antisymm

  · apply
      smithSpan_least
        (Geo := Geo)
        (SmithAdjoinPoint Geo F A)
        (WylerPlaneCone Geo F P A)
        hConeIsFlat

    intro X hX

    rcases hX with hXA | hXF

    · subst X
      exact hAInCone

    · exact hBaseInCone hXF

  · exact
      wylerPlaneCone_subset_span
        (Geo := Geo)
        F P A hAOut

theorem smithFlat_plane_of_two_distinct_lines_through_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P : Geo.Point)
    (hPF : F P)
    (a b : Geo.Line)
    (hab : Ne a b)
    (hPa : H.OnLine P a)
    (hPb : H.OnLine P b)
    (haF : forall X : Geo.Point, H.OnLine X a -> F X)
    (hbF : forall X : Geo.Point, H.OnLine X b -> F X) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo a pi /\
      HilbertLineInPlane Geo b pi /\
      (forall X : Geo.Point, S.OnPlane X pi -> F X) := by

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P a hPa with
    ⟨U, hPU, hUa⟩

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P b hPb with
    ⟨V, hPV, hVb⟩

  have hUF : F U :=
    haF U hUa

  have hVF : F V :=
    hbF V hVb

  have hPUV :
      Not (PrimCollinear Geo P U V) := by

    intro hCol

    have hVa : H.OnLine V a :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        P U V hPU
        a hPa hUa
        hCol

    have hba : b = a :=
      HilbertPlaneIncidence.line_unique
        P V hPV
        b a
        hPb hVb
        hPa hVa

    exact hab hba.symm

  rcases
      C.plane_through
        P U V hPUV with
    ⟨pi, hPpi, hUpi, hVpi⟩

  have hapi : HilbertLineInPlane Geo a pi :=
    C.line_in_plane
      P U hPU
      a hPa hUa
      pi hPpi hUpi

  have hbpi : HilbertLineInPlane Geo b pi :=
    C.line_in_plane
      P V hPV
      b hPb hVb
      pi hPpi hVpi

  have hpiF :
      forall X : Geo.Point,
        S.OnPlane X pi ->
        F X := by

    intro X hXpi

    exact
      hFlat.2
        P U V
        hPF hUF hVF
        hPUV
        pi
        hPpi hUpi hVpi
        X hXpi

  exact
    ⟨pi, hapi, hbpi, hpiF⟩

theorem wylerConePlane_unique_of_base_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (P A : Geo.Point)
    (_hPF : F P)
    (hAOut : Not (F A))
    (a : Geo.Line)
    (hPa : H.OnLine P a)
    (haF : forall X : Geo.Point, H.OnLine X a -> F X)
    (alpha beta : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hAAlpha : S.OnPlane A alpha)
    (haBeta : HilbertLineInPlane Geo a beta)
    (hABeta : S.OnPlane A beta) :
    alpha = beta := by

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P a hPa with
    ⟨U, hPU, hUa⟩

  have hUAlpha : S.OnPlane U alpha :=
    haAlpha U hUa

  have hUBeta : S.OnPlane U beta :=
    haBeta U hUa

  have hPAlpha : S.OnPlane P alpha :=
    haAlpha P hPa

  have hPBeta : S.OnPlane P beta :=
    haBeta P hPa

  have hPUA :
      Not (PrimCollinear Geo P U A) := by

    intro hCol

    have hAa : H.OnLine A a :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        P U A hPU
        a hPa hUa
        hCol

    exact hAOut (haF A hAa)

  exact
    C.plane_unique
      P U A hPUA
      alpha beta
      hPAlpha hUAlpha hAAlpha
      hPBeta hUBeta hABeta

theorem wylerConePlanes_intersection_is_apex_axis
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hI7 : WylerI7IntersectionLine Geo)
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P A : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (a b : Geo.Line)
    (hab : Ne a b)
    (hPa : H.OnLine P a)
    (hPb : H.OnLine P b)
    (haF : forall X : Geo.Point, H.OnLine X a -> F X)
    (hbF : forall X : Geo.Point, H.OnLine X b -> F X)
    (alpha beta : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hAAlpha : S.OnPlane A alpha)
    (hbBeta : HilbertLineInPlane Geo b beta)
    (hABeta : S.OnPlane A beta) :
    exists k : Geo.Line,
      H.OnLine P k /\
      H.OnLine A k /\
      HilbertLineInPlane Geo k alpha /\
      HilbertLineInPlane Geo k beta /\
      forall X : Geo.Point,
        (S.OnPlane X alpha /\ S.OnPlane X beta) <->
          H.OnLine X k := by

  rcases
      smithFlat_plane_of_two_distinct_lines_through_point
        (Geo := Geo)
        F hFlat
        P hPF
        a b hab
        hPa hPb
        haF hbF with
    ⟨pi, hapi, hbpi, hpiF⟩

  have hApi : Not (S.OnPlane A pi) := by
    intro hAonPi
    exact hAOut (hpiF A hAonPi)

  have hPAlpha : S.OnPlane P alpha :=
    haAlpha P hPa

  have hPBeta : S.OnPlane P beta :=
    hbBeta P hPb

  rcases
      hI7
        pi
        a b hab
        hapi hbpi
        A hApi
        alpha beta
        haAlpha hAAlpha
        hbBeta hABeta with
    ⟨k, hAk, hkAlpha, hkBeta, hInter⟩

  have hPBoth :
      S.OnPlane P alpha /\
      S.OnPlane P beta :=
    ⟨hPAlpha, hPBeta⟩

  have hPk : H.OnLine P k :=
    (hInter P).1 hPBoth

  exact
    ⟨k,
     hPk,
     hAk,
     hkAlpha,
     hkBeta,
     hInter⟩

theorem wyler_apex_ne_base_point
    (F : Set Geo.Point)
    (P A : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A)) :
    Ne P A := by

  intro hPA
  apply hAOut
  rw [← hPA]
  exact hPF

theorem wylerConePlane_contains_axis
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (P A : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (a : Geo.Line)
    (hPa : H.OnLine P a)
    (alpha : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hAAlpha : S.OnPlane A alpha)
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k) :
    HilbertLineInPlane Geo k alpha := by

  have hPA : Ne P A :=
    wyler_apex_ne_base_point
      (Geo := Geo)
      F P A hPF hAOut

  exact
    C.line_in_plane
      P A hPA
      k hPk hAk
      alpha
      (haAlpha P hPa)
      hAAlpha

theorem wylerPlaneCone_line_closed_same_base
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (P A X Y : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (a : Geo.Line)
    (hPa : H.OnLine P a)
    (haF : forall T : Geo.Point, H.OnLine T a -> F T)
    (alpha beta : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hAAlpha : S.OnPlane A alpha)
    (hXAlpha : S.OnPlane X alpha)
    (haBeta : HilbertLineInPlane Geo a beta)
    (hABeta : S.OnPlane A beta)
    (hYBeta : S.OnPlane Y beta)
    (hXY : Ne X Y)
    (m : Geo.Line)
    (hXm : H.OnLine X m)
    (hYm : H.OnLine Y m) :
    forall Z : Geo.Point,
      H.OnLine Z m ->
      WylerPlaneCone Geo F P A Z := by

  have hAlphaBeta : alpha = beta :=
    wylerConePlane_unique_of_base_line
      (Geo := Geo)
      F P A
      hPF hAOut
      a hPa haF
      alpha beta
      haAlpha hAAlpha
      haBeta hABeta

  rw [hAlphaBeta] at hXAlpha

  have hmBeta : HilbertLineInPlane Geo m beta :=
    C.line_in_plane
      X Y hXY
      m hXm hYm
      beta hXAlpha hYBeta

  intro Z hZm

  exact
    ⟨a, beta,
     hPa,
     haF,
     haBeta,
     hABeta,
     hmBeta Z hZm⟩

theorem wylerPlaneCone_line_closed_axis_left
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (P A X Y : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (hXk : H.OnLine X k)
    (hY : WylerPlaneCone Geo F P A Y)
    (hXY : Ne X Y)
    (m : Geo.Line)
    (hXm : H.OnLine X m)
    (hYm : H.OnLine Y m) :
    forall Z : Geo.Point,
      H.OnLine Z m ->
      WylerPlaneCone Geo F P A Z := by

  rcases hY with
    ⟨b, beta, hPb, hbF, hbBeta, hABeta, hYBeta⟩

  have hkBeta : HilbertLineInPlane Geo k beta :=
    wylerConePlane_contains_axis
      (Geo := Geo)
      F P A
      hPF hAOut
      b hPb
      beta hbBeta hABeta
      k hPk hAk

  have hXBeta : S.OnPlane X beta :=
    hkBeta X hXk

  have hmBeta : HilbertLineInPlane Geo m beta :=
    C.line_in_plane
      X Y hXY
      m hXm hYm
      beta hXBeta hYBeta

  intro Z hZm

  exact
    ⟨b, beta,
     hPb,
     hbF,
     hbBeta,
     hABeta,
     hmBeta Z hZm⟩

theorem wylerPlaneCone_line_closed_axis_right
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (P A X Y : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (hX : WylerPlaneCone Geo F P A X)
    (hYk : H.OnLine Y k)
    (hXY : Ne X Y)
    (m : Geo.Line)
    (hXm : H.OnLine X m)
    (hYm : H.OnLine Y m) :
    forall Z : Geo.Point,
      H.OnLine Z m ->
      WylerPlaneCone Geo F P A Z := by

  have hYX : Ne Y X :=
    Ne.symm hXY

  have hClosure :
      forall Z : Geo.Point,
        H.OnLine Z m ->
        WylerPlaneCone Geo F P A Z :=
    wylerPlaneCone_line_closed_axis_left
      (Geo := Geo)
      F P A Y X
      hPF hAOut
      k hPk hAk
      hYk hX
      hYX
      m hYm hXm

  exact hClosure

def WylerConeDistinctOffAxisLineClosure
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall F : Set Geo.Point,
    SmithFlat Geo F ->
    forall P R A : Geo.Point,
      F P ->
      F R ->
      Ne P R ->
      Not (F A) ->
      forall k : Geo.Line,
        H.OnLine P k ->
        H.OnLine A k ->
        forall X Y : Geo.Point,
          Not (H.OnLine X k) ->
          Not (H.OnLine Y k) ->
          forall a b : Geo.Line,
            Ne a b ->
            forall alpha beta : S.Plane,
              H.OnLine P a ->
              H.OnLine P b ->
              (forall T : Geo.Point, H.OnLine T a -> F T) ->
              (forall T : Geo.Point, H.OnLine T b -> F T) ->
              HilbertLineInPlane Geo a alpha ->
              S.OnPlane A alpha ->
              S.OnPlane X alpha ->
              HilbertLineInPlane Geo b beta ->
              S.OnPlane A beta ->
              S.OnPlane Y beta ->
              forall m : Geo.Line,
                Ne X Y ->
                H.OnLine X m ->
                H.OnLine Y m ->
                forall Z : Geo.Point,
                  H.OnLine Z m ->
                  WylerPlaneCone Geo F P A Z

theorem wylerConeDistinctOffAxis_implies_full_line_closure
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hHard : WylerConeDistinctOffAxisLineClosure Geo)
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P R A : Geo.Point)
    (hPF : F P)
    (hRF : F R)
    (hPR : Ne P R)
    (hAOut : Not (F A))
    (X Y : Geo.Point)
    (hX : WylerPlaneCone Geo F P A X)
    (hY : WylerPlaneCone Geo F P A Y)
    (hXY : Ne X Y)
    (m : Geo.Line)
    (hXm : H.OnLine X m)
    (hYm : H.OnLine Y m) :
    forall Z : Geo.Point,
      H.OnLine Z m ->
      WylerPlaneCone Geo F P A Z := by

  have hPA : Ne P A :=
    wyler_apex_ne_base_point
      (Geo := Geo)
      F P A hPF hAOut

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        P A hPA with
    ⟨k, hPk, hAk⟩

  by_cases hXk : H.OnLine X k

  · exact
      wylerPlaneCone_line_closed_axis_left
        (Geo := Geo)
        F P A X Y
        hPF hAOut
        k hPk hAk
        hXk hY
        hXY
        m hXm hYm

  · by_cases hYk : H.OnLine Y k

    · exact
        wylerPlaneCone_line_closed_axis_right
          (Geo := Geo)
          F P A X Y
          hPF hAOut
          k hPk hAk
          hX hYk
          hXY
          m hXm hYm

    · rcases hX with
        ⟨a, alpha, hPa, haF, haAlpha, hAAlpha, hXAlpha⟩

      rcases hY with
        ⟨b, beta, hPb, hbF, hbBeta, hABeta, hYBeta⟩

      by_cases hab : a = b

      · subst b

        exact
          wylerPlaneCone_line_closed_same_base
            (Geo := Geo)
            F P A X Y
            hPF hAOut
            a hPa haF
            alpha beta
            haAlpha hAAlpha hXAlpha
            hbBeta hABeta hYBeta
            hXY
            m hXm hYm

      · exact
          hHard
            F hFlat
            P R A
            hPF hRF hPR
            hAOut
            k hPk hAk
            X Y
            hXk hYk
            a b hab
            alpha beta
            hPa hPb
            haF hbF
            haAlpha hAAlpha hXAlpha
            hbBeta hABeta hYBeta
            m hXY hXm hYm

theorem wyler_axis_off_point_noncollinear
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (P A Z : Geo.Point)
    (hPA : Ne P A)
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (hZk : Not (H.OnLine Z k)) :
    Not (PrimCollinear Geo P A Z) := by

  intro hCol

  have hZonK : H.OnLine Z k :=
    smithCore_on_line_of_collinear_with_two
      (Geo := Geo)
      P A Z hPA
      k hPk hAk
      hCol

  exact hZk hZonK

theorem wylerPlaneCone_off_axis_has_base_line_in_canonical_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (P A Z : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (hZk : Not (H.OnLine Z k))
    (gamma : S.Plane)
    (hPgamma : S.OnPlane P gamma)
    (hAgamma : S.OnPlane A gamma)
    (hZgamma : S.OnPlane Z gamma)
    (hZCone : WylerPlaneCone Geo F P A Z) :
    exists c : Geo.Line,
      H.OnLine P c /\
      (forall T : Geo.Point, H.OnLine T c -> F T) /\
      HilbertLineInPlane Geo c gamma := by

  have hPA : Ne P A :=
    wyler_apex_ne_base_point
      (Geo := Geo)
      F P A hPF hAOut

  have hPAZ :
      Not (PrimCollinear Geo P A Z) :=
    wyler_axis_off_point_noncollinear
      (Geo := Geo)
      P A Z
      hPA
      k hPk hAk
      hZk

  rcases hZCone with
    ⟨c, delta, hPc, hcF, hcDelta, hADelta, hZDelta⟩

  have hPDelta : S.OnPlane P delta :=
    hcDelta P hPc

  have hDeltaGamma : delta = gamma :=
    C.plane_unique
      P A Z hPAZ
      delta gamma
      hPDelta hADelta hZDelta
      hPgamma hAgamma hZgamma

  rw [hDeltaGamma] at hcDelta

  exact
    ⟨c, hPc, hcF, hcDelta⟩

theorem wylerPlaneCone_of_base_line_in_plane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (F : Set Geo.Point)
    (P A Z : Geo.Point)
    (gamma : S.Plane)
    (c : Geo.Line)
    (hPc : H.OnLine P c)
    (hcF : forall T : Geo.Point, H.OnLine T c -> F T)
    (hcGamma : HilbertLineInPlane Geo c gamma)
    (hAGamma : S.OnPlane A gamma)
    (hZGamma : S.OnPlane Z gamma) :
    WylerPlaneCone Geo F P A Z := by

  exact
    ⟨c, gamma,
     hPc,
     hcF,
     hcGamma,
     hAGamma,
     hZGamma⟩

theorem wylerPlaneCone_off_axis_iff_canonical_base_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (P A Z : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (hZk : Not (H.OnLine Z k))
    (gamma : S.Plane)
    (hPgamma : S.OnPlane P gamma)
    (hAgamma : S.OnPlane A gamma)
    (hZgamma : S.OnPlane Z gamma) :
    WylerPlaneCone Geo F P A Z <->
      exists c : Geo.Line,
        H.OnLine P c /\
        (forall T : Geo.Point, H.OnLine T c -> F T) /\
        HilbertLineInPlane Geo c gamma := by

  constructor

  · intro hCone

    exact
      wylerPlaneCone_off_axis_has_base_line_in_canonical_plane
        (Geo := Geo)
        F P A Z
        hPF hAOut
        k hPk hAk hZk
        gamma
        hPgamma hAgamma hZgamma
        hCone

  · intro hBase

    rcases hBase with
      ⟨c, hPc, hcF, hcGamma⟩

    exact
      wylerPlaneCone_of_base_line_in_plane
        (Geo := Geo)
        F P A Z
        gamma c
        hPc hcF hcGamma
        hAgamma hZgamma

def WylerCanonicalSectionLine
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall F : Set Geo.Point,
    SmithFlat Geo F ->
    forall P R A : Geo.Point,
      F P ->
      F R ->
      Ne P R ->
      Not (F A) ->
      forall k : Geo.Line,
        H.OnLine P k ->
        H.OnLine A k ->
        forall X Y : Geo.Point,
          Not (H.OnLine X k) ->
          Not (H.OnLine Y k) ->
          forall a b : Geo.Line,
            Ne a b ->
            forall alpha beta : S.Plane,
              H.OnLine P a ->
              H.OnLine P b ->
              (forall T : Geo.Point, H.OnLine T a -> F T) ->
              (forall T : Geo.Point, H.OnLine T b -> F T) ->
              HilbertLineInPlane Geo a alpha ->
              S.OnPlane A alpha ->
              S.OnPlane X alpha ->
              HilbertLineInPlane Geo b beta ->
              S.OnPlane A beta ->
              S.OnPlane Y beta ->
              forall m : Geo.Line,
                Ne X Y ->
                H.OnLine X m ->
                H.OnLine Y m ->
                forall Z : Geo.Point,
                  H.OnLine Z m ->
                  Not (H.OnLine Z k) ->
                  forall gamma : S.Plane,
                    S.OnPlane P gamma ->
                    S.OnPlane A gamma ->
                    S.OnPlane Z gamma ->
                    exists c : Geo.Line,
                      H.OnLine P c /\
                      (forall T : Geo.Point, H.OnLine T c -> F T) /\
                      HilbertLineInPlane Geo c gamma

theorem wylerCanonicalSectionLine_implies_distinctOffAxisLineClosure
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hSection : WylerCanonicalSectionLine Geo) :
    WylerConeDistinctOffAxisLineClosure Geo := by

  intro F hFlat P R A hPF hRF hPR hAOut k hPk hAk X Y hXk hYk a b hab alpha beta hPa hPb haF hbF haAlpha hAAlpha hXAlpha hbBeta hABeta hYBeta m hXY hXm hYm Z hZm

  by_cases hZk : H.OnLine Z k

  · have hkAlpha : HilbertLineInPlane Geo k alpha :=
      wylerConePlane_contains_axis
        (Geo := Geo)
        F P A
        hPF hAOut
        a hPa
        alpha haAlpha hAAlpha
        k hPk hAk

    exact
      ⟨a, alpha,
       hPa,
       haF,
       haAlpha,
       hAAlpha,
       hkAlpha Z hZk⟩

  · have hPA : Ne P A :=
      wyler_apex_ne_base_point
        (Geo := Geo)
        F P A hPF hAOut

    have hPAZ :
        Not (PrimCollinear Geo P A Z) :=
      wyler_axis_off_point_noncollinear
        (Geo := Geo)
        P A Z
        hPA
        k hPk hAk
        hZk

    rcases
        C.plane_through
          P A Z hPAZ with
      ⟨gamma, hPgamma, hAgamma, hZgamma⟩

    rcases
        hSection
          F hFlat
          P R A
          hPF hRF hPR
          hAOut
          k hPk hAk
          X Y hXk hYk
          a b hab
          alpha beta
          hPa hPb
          haF hbF
          haAlpha hAAlpha hXAlpha
          hbBeta hABeta hYBeta
          m hXY hXm hYm
          Z hZm hZk
          gamma
          hPgamma hAgamma hZgamma with
      ⟨c, hPc, hcF, hcGamma⟩

    exact
      wylerPlaneCone_of_base_line_in_plane
        (Geo := Geo)
        F P A Z
        gamma c
        hPc hcF hcGamma
        hAgamma hZgamma

theorem wyler_distinct_cone_planes_intersection_axis
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hI7 : WylerI7IntersectionLine Geo)
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P A : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (a b : Geo.Line)
    (hab : Ne a b)
    (hPa : H.OnLine P a)
    (hPb : H.OnLine P b)
    (haF : forall T : Geo.Point, H.OnLine T a -> F T)
    (hbF : forall T : Geo.Point, H.OnLine T b -> F T)
    (alpha beta : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hAAlpha : S.OnPlane A alpha)
    (hbBeta : HilbertLineInPlane Geo b beta)
    (hABeta : S.OnPlane A beta) :
    forall T : Geo.Point,
      (S.OnPlane T alpha /\ S.OnPlane T beta) <->
        H.OnLine T k := by

  rcases
      wylerConePlanes_intersection_is_apex_axis
        (Geo := Geo)
        hI7
        F hFlat
        P A
        hPF hAOut
        a b hab
        hPa hPb
        haF hbF
        alpha beta
        haAlpha hAAlpha
        hbBeta hABeta with
    ⟨j, hPj, hAj, hjAlpha, hjBeta, hInter⟩

  have hPA : Ne P A :=
    wyler_apex_ne_base_point
      (Geo := Geo)
      F P A hPF hAOut

  have hjk : j = k :=
    HilbertPlaneIncidence.line_unique
      P A hPA
      j k
      hPj hAj
      hPk hAk

  rw [hjk] at hInter

  exact hInter

theorem wyler_hard_case_P_not_on_joining_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hI7 : WylerI7IntersectionLine Geo)
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P A X Y : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (hXk : Not (H.OnLine X k))
    (hYk : Not (H.OnLine Y k))
    (a b : Geo.Line)
    (hab : Ne a b)
    (hPa : H.OnLine P a)
    (hPb : H.OnLine P b)
    (haF : forall T : Geo.Point, H.OnLine T a -> F T)
    (hbF : forall T : Geo.Point, H.OnLine T b -> F T)
    (alpha beta : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hAAlpha : S.OnPlane A alpha)
    (hXAlpha : S.OnPlane X alpha)
    (hbBeta : HilbertLineInPlane Geo b beta)
    (hABeta : S.OnPlane A beta)
    (hYBeta : S.OnPlane Y beta)
    (hXY : Ne X Y)
    (m : Geo.Line)
    (hXm : H.OnLine X m)
    (hYm : H.OnLine Y m) :
    Not (H.OnLine P m) := by

  intro hPm

  have hXP : Ne X P := by
    intro hXP
    subst X
    exact hXk hPk

  have hYP : Ne Y P := by
    intro hYP
    subst Y
    exact hYk hPk

  have hPAlpha : S.OnPlane P alpha :=
    haAlpha P hPa

  have hPBeta : S.OnPlane P beta :=
    hbBeta P hPb

  have hmAlpha : HilbertLineInPlane Geo m alpha :=
    C.line_in_plane
      X P hXP
      m hXm hPm
      alpha hXAlpha hPAlpha

  have hmBeta : HilbertLineInPlane Geo m beta :=
    C.line_in_plane
      Y P hYP
      m hYm hPm
      beta hYBeta hPBeta

  have hXBeta : S.OnPlane X beta :=
    hmBeta X hXm

  have hXBoth :
      S.OnPlane X alpha /\
      S.OnPlane X beta :=
    ⟨hXAlpha, hXBeta⟩

  have hAxis :=
    wyler_distinct_cone_planes_intersection_axis
      (Geo := Geo)
      hI7
      F hFlat
      P A
      hPF hAOut
      k hPk hAk
      a b hab
      hPa hPb
      haF hbF
      alpha beta
      haAlpha hAAlpha
      hbBeta hABeta

  exact hXk ((hAxis X).1 hXBoth)

theorem lines_from_external_point_to_two_line_points_ne
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (P X Y : Geo.Point)
    (hXY : Ne X Y)
    (m : Geo.Line)
    (hXm : H.OnLine X m)
    (hYm : H.OnLine Y m)
    (hPm : Not (H.OnLine P m))
    (x y : Geo.Line)
    (hPx : H.OnLine P x)
    (hXx : H.OnLine X x)
    (hPy : H.OnLine P y)
    (hYy : H.OnLine Y y) :
    Ne x y := by

  intro hxy
  subst y

  have hmX : m = x :=
    HilbertPlaneIncidence.line_unique
      X Y hXY
      m x
      hXm hYm
      hXx hYy

  apply hPm
  rw [hmX]
  exact hPx

theorem three_distinct_rays_from_external_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (P X Y Z : Geo.Point)
    (hXY : Ne X Y)
    (hXZ : Ne X Z)
    (hYZ : Ne Y Z)
    (m : Geo.Line)
    (hXm : H.OnLine X m)
    (hYm : H.OnLine Y m)
    (hZm : H.OnLine Z m)
    (hPm : Not (H.OnLine P m))
    (x y z : Geo.Line)
    (hPx : H.OnLine P x)
    (hXx : H.OnLine X x)
    (hPy : H.OnLine P y)
    (hYy : H.OnLine Y y)
    (hPz : H.OnLine P z)
    (hZz : H.OnLine Z z) :
    Ne x y /\ Ne x z /\ Ne y z := by

  have hxy :
      Ne x y :=
    lines_from_external_point_to_two_line_points_ne
      (Geo := Geo)
      P X Y hXY
      m hXm hYm hPm
      x y
      hPx hXx
      hPy hYy

  have hxz :
      Ne x z :=
    lines_from_external_point_to_two_line_points_ne
      (Geo := Geo)
      P X Z hXZ
      m hXm hZm hPm
      x z
      hPx hXx
      hPz hZz

  have hyz :
      Ne y z :=
    lines_from_external_point_to_two_line_points_ne
      (Geo := Geo)
      P Y Z hYZ
      m hYm hZm hPm
      y z
      hPy hYy
      hPz hZz

  exact ⟨hxy, hxz, hyz⟩

theorem three_rays_from_external_point_are_coplanar
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (P X Y Z : Geo.Point)
    (hXY : Ne X Y)
    (m : Geo.Line)
    (hXm : H.OnLine X m)
    (hYm : H.OnLine Y m)
    (hZm : H.OnLine Z m)
    (hPm : Not (H.OnLine P m))
    (x y z : Geo.Line)
    (hPx : H.OnLine P x)
    (hXx : H.OnLine X x)
    (hPy : H.OnLine P y)
    (hYy : H.OnLine Y y)
    (hPz : H.OnLine P z)
    (hZz : H.OnLine Z z) :
    exists epsilon : S.Plane,
      HilbertLineInPlane Geo x epsilon /\
      HilbertLineInPlane Geo y epsilon /\
      HilbertLineInPlane Geo z epsilon := by

  have hPXY :
      Not (PrimCollinear Geo P X Y) := by

    intro hCol

    have hPm' : H.OnLine P m :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        X Y P hXY
        m hXm hYm
        (PrimCollinearCycle
          (Geo := Geo)
          P X Y hCol)

    exact hPm hPm'

  rcases
      C.plane_through
        P X Y hPXY with
    ⟨epsilon, hPe, hXe, hYe⟩

  have hmEpsilon : HilbertLineInPlane Geo m epsilon :=
    C.line_in_plane
      X Y hXY
      m hXm hYm
      epsilon hXe hYe

  have hZe : S.OnPlane Z epsilon :=
    hmEpsilon Z hZm

  have hPX : Ne P X := by
    intro hPX
    subst X
    exact hPm hXm

  have hPY : Ne P Y := by
    intro hPY
    subst Y
    exact hPm hYm

  have hPZ : Ne P Z := by
    intro hPZ
    subst Z
    exact hPm hZm

  have hxEpsilon : HilbertLineInPlane Geo x epsilon :=
    C.line_in_plane
      P X hPX
      x hPx hXx
      epsilon hPe hXe

  have hyEpsilon : HilbertLineInPlane Geo y epsilon :=
    C.line_in_plane
      P Y hPY
      y hPy hYy
      epsilon hPe hYe

  have hzEpsilon : HilbertLineInPlane Geo z epsilon :=
    C.line_in_plane
      P Z hPZ
      z hPz hZz
      epsilon hPe hZe

  exact
    ⟨epsilon,
     hxEpsilon,
     hyEpsilon,
     hzEpsilon⟩

theorem wyler_hard_side_planes_ne
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P A : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (a b : Geo.Line)
    (hab : Ne a b)
    (hPa : H.OnLine P a)
    (hPb : H.OnLine P b)
    (haF : forall T : Geo.Point, H.OnLine T a -> F T)
    (hbF : forall T : Geo.Point, H.OnLine T b -> F T)
    (alpha beta : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hAAlpha : S.OnPlane A alpha)
    (hbBeta : HilbertLineInPlane Geo b beta)
    (hABeta : S.OnPlane A beta) :
    Ne alpha beta := by

  rcases
      smithFlat_plane_of_two_distinct_lines_through_point
        (Geo := Geo)
        F hFlat
        P hPF
        a b hab
        hPa hPb
        haF hbF with
    ⟨pi, hapi, hbpi, hpiF⟩

  have hApi : Not (S.OnPlane A pi) := by
    intro hAonPi
    exact hAOut (hpiF A hAonPi)

  exact
    wyler_side_planes_ne
      (Geo := Geo)
      pi a b hab
      hapi hbpi
      A hApi
      alpha beta
      haAlpha hAAlpha
      hbBeta hABeta

theorem wyler_axis_in_two_cone_planes
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (P A : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (k a b : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (hPa : H.OnLine P a)
    (hPb : H.OnLine P b)
    (alpha beta : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hAAlpha : S.OnPlane A alpha)
    (hbBeta : HilbertLineInPlane Geo b beta)
    (hABeta : S.OnPlane A beta) :
    HilbertLineInPlane Geo k alpha /\
    HilbertLineInPlane Geo k beta := by

  constructor

  · exact
      wylerConePlane_contains_axis
        (Geo := Geo)
        F P A
        hPF hAOut
        a hPa
        alpha haAlpha hAAlpha
        k hPk hAk

  · exact
      wylerConePlane_contains_axis
        (Geo := Geo)
        F P A
        hPF hAOut
        b hPb
        beta hbBeta hABeta
        k hPk hAk

def WylerPlaneConeLineClosure
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall F : Set Geo.Point,
    SmithFlat Geo F ->
    forall P R : Geo.Point,
      F P ->
      F R ->
      Ne P R ->
      forall A : Geo.Point,
        Not (F A) ->
        forall X Y : Geo.Point,
          WylerPlaneCone Geo F P A X ->
          WylerPlaneCone Geo F P A Y ->
          Ne X Y ->
          forall m : Geo.Line,
            H.OnLine X m ->
            H.OnLine Y m ->
            forall Z : Geo.Point,
              H.OnLine Z m ->
              WylerPlaneCone Geo F P A Z

theorem plane_unique_of_two_distinct_lines_through_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (P : Geo.Point)
    (a b : Geo.Line)
    (hab : Ne a b)
    (hPa : H.OnLine P a)
    (hPb : H.OnLine P b)
    (alpha beta : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hbAlpha : HilbertLineInPlane Geo b alpha)
    (haBeta : HilbertLineInPlane Geo a beta)
    (hbBeta : HilbertLineInPlane Geo b beta) :
    alpha = beta := by

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P a hPa with
    ⟨A, hPA, hAa⟩

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P b hPb with
    ⟨B, hPB, hBb⟩

  have hPAB :
      Not (PrimCollinear Geo P A B) := by

    intro hCol

    have hBa : H.OnLine B a :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        P A B hPA
        a hPa hAa
        hCol

    have hba : b = a :=
      HilbertPlaneIncidence.line_unique
        P B hPB
        b a
        hPb hBb
        hPa hBa

    exact hab hba.symm

  exact
    C.plane_unique
      P A B hPAB
      alpha beta
      (haAlpha P hPa)
      (haAlpha A hAa)
      (hbAlpha B hBb)
      (haBeta P hPa)
      (haBeta A hAa)
      (hbBeta B hBb)

theorem wyler_base_axis_local_triangle
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P A : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (a b : Geo.Line)
    (hab : Ne a b)
    (hPa : H.OnLine P a)
    (hPb : H.OnLine P b)
    (haF : forall T : Geo.Point, H.OnLine T a -> F T)
    (hbF : forall T : Geo.Point, H.OnLine T b -> F T) :
    WylerLocalTriangleAtPoint Geo P a b k := by

  have hak : Ne a k := by
    intro hak
    apply hAOut
    apply haF A
    rw [hak]
    exact hAk

  have hbk : Ne b k := by
    intro hbk
    apply hAOut
    apply hbF A
    rw [hbk]
    exact hAk

  refine
    ⟨hPa, hPb, hPk, hab, hbk, Ne.symm hak, ?_⟩

  intro hCoplanar
  rcases hCoplanar with
    ⟨delta, haDelta, hbDelta, hkDelta⟩

  rcases
      smithFlat_plane_of_two_distinct_lines_through_point
        (Geo := Geo)
        F hFlat
        P hPF
        a b hab
        hPa hPb
        haF hbF with
    ⟨pi, hapi, hbpi, hpiF⟩

  have hDeltaPi : delta = pi :=
    plane_unique_of_two_distinct_lines_through_point
      (Geo := Geo)
      P a b hab
      hPa hPb
      delta pi
      haDelta hbDelta
      hapi hbpi

  have hApi : S.OnPlane A pi := by
    rw [← hDeltaPi]
    exact hkDelta A hAk

  exact hAOut (hpiF A hApi)

theorem wyler_ray_ne_axis_of_point_off_axis
    [H : HilbertIncidence Geo]
    (X : Geo.Point)
    (k x : Geo.Line)
    (hXk : Not (H.OnLine X k))
    (hXx : H.OnLine X x) :
    Ne x k := by

  intro hxk
  apply hXk
  rw [← hxk]
  exact hXx

theorem wylerLocalP3_first_cross_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P A X Y : Geo.Point)
    (hPF : F P)
    (hAOut : Not (F A))
    (k : Geo.Line)
    (hPk : H.OnLine P k)
    (hAk : H.OnLine A k)
    (hXk : Not (H.OnLine X k))
    (hYk : Not (H.OnLine Y k))
    (a b : Geo.Line)
    (hab : Ne a b)
    (hPa : H.OnLine P a)
    (hPb : H.OnLine P b)
    (haF : forall T : Geo.Point, H.OnLine T a -> F T)
    (hbF : forall T : Geo.Point, H.OnLine T b -> F T)
    (alpha beta pi epsilon : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hkAlpha : HilbertLineInPlane Geo k alpha)
    (hbBeta : HilbertLineInPlane Geo b beta)
    (hkBeta : HilbertLineInPlane Geo k beta)
    (haPi : HilbertLineInPlane Geo a pi)
    (hbPi : HilbertLineInPlane Geo b pi)
    (x y : Geo.Line)
    (hPx : H.OnLine P x)
    (hXx : H.OnLine X x)
    (hPy : H.OnLine P y)
    (hYy : H.OnLine Y y)
    (hxAlpha : HilbertLineInPlane Geo x alpha)
    (hxEpsilon : HilbertLineInPlane Geo x epsilon)
    (hyBeta : HilbertLineInPlane Geo y beta)
    (hyEpsilon : HilbertLineInPlane Geo y epsilon) :
    exists d : Geo.Line,
      H.OnLine P d /\
      HilbertLineInPlane Geo d pi /\
      HilbertLineInPlane Geo d epsilon := by

  have hTriangle :
      WylerLocalTriangleAtPoint Geo P a b k :=
    wyler_base_axis_local_triangle
      (Geo := Geo)
      F hFlat
      P A
      hPF hAOut
      k hPk hAk
      a b hab
      hPa hPb
      haF hbF

  have hxk : Ne x k :=
    wyler_ray_ne_axis_of_point_off_axis
      (Geo := Geo)
      X
      k x
      hXk hXx

  have hyk : Ne y k :=
    wyler_ray_ne_axis_of_point_off_axis
      (Geo := Geo)
      Y
      k y
      hYk hYy

  exact
    hP3
      P
      a b k
      hTriangle
      alpha beta pi
      haAlpha hkAlpha
      hbBeta hkBeta
      haPi hbPi
      epsilon
      x y
      hPx hPy
      hxAlpha hxEpsilon
      hyBeta hyEpsilon
      hxk hyk

theorem wylerLocalP3_second_cross_line
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (P : Geo.Point)
    (a d x k z : Geo.Line)
    (hTriangle : WylerLocalTriangleAtPoint Geo P a d x)
    (alpha epsilon pi gamma : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hxAlpha : HilbertLineInPlane Geo x alpha)
    (hdEpsilon : HilbertLineInPlane Geo d epsilon)
    (hxEpsilon : HilbertLineInPlane Geo x epsilon)
    (haPi : HilbertLineInPlane Geo a pi)
    (hdPi : HilbertLineInPlane Geo d pi)
    (hPk : H.OnLine P k)
    (hPz : H.OnLine P z)
    (hkAlpha : HilbertLineInPlane Geo k alpha)
    (hkGamma : HilbertLineInPlane Geo k gamma)
    (hzEpsilon : HilbertLineInPlane Geo z epsilon)
    (hzGamma : HilbertLineInPlane Geo z gamma)
    (hkx : Ne k x)
    (hzx : Ne z x) :
    exists c : Geo.Line,
      H.OnLine P c /\
      HilbertLineInPlane Geo c pi /\
      HilbertLineInPlane Geo c gamma := by

  exact
    hP3
      P
      a d x
      hTriangle
      alpha epsilon pi
      haAlpha hxAlpha
      hdEpsilon hxEpsilon
      haPi hdPi
      gamma
      k z
      hPk hPz
      hkAlpha hkGamma
      hzEpsilon hzGamma
      hkx hzx

theorem wylerLocalP3_finish_from_first_cross
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (P : Geo.Point)
    (a d x k z : Geo.Line)
    (hTriangle : WylerLocalTriangleAtPoint Geo P a d x)
    (alpha epsilon pi gamma : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hxAlpha : HilbertLineInPlane Geo x alpha)
    (hdEpsilon : HilbertLineInPlane Geo d epsilon)
    (hxEpsilon : HilbertLineInPlane Geo x epsilon)
    (haPi : HilbertLineInPlane Geo a pi)
    (hdPi : HilbertLineInPlane Geo d pi)
    (hPk : H.OnLine P k)
    (hPz : H.OnLine P z)
    (hkAlpha : HilbertLineInPlane Geo k alpha)
    (hkGamma : HilbertLineInPlane Geo k gamma)
    (hzEpsilon : HilbertLineInPlane Geo z epsilon)
    (hzGamma : HilbertLineInPlane Geo z gamma)
    (hkx : Ne k x)
    (hzx : Ne z x) :
    exists c : Geo.Line,
      H.OnLine P c /\
      HilbertLineInPlane Geo c pi /\
      HilbertLineInPlane Geo c gamma := by

  exact
    wylerLocalP3_second_cross_line
      (Geo := Geo)
      hP3
      P
      a d x k z
      hTriangle
      alpha epsilon pi gamma
      haAlpha hxAlpha
      hdEpsilon hxEpsilon
      haPi hdPi
      hPk hPz
      hkAlpha hkGamma
      hzEpsilon hzGamma
      hkx hzx

theorem localTriangle_side_plane_ne_opposite
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [_C : SmithIncidenceCore Geo]
    (P : Geo.Point)
    (a b k : Geo.Line)
    (hTriangle : WylerLocalTriangleAtPoint Geo P a b k)
    (alpha pi : S.Plane)
    (_haAlpha : HilbertLineInPlane Geo a alpha)
    (hkAlpha : HilbertLineInPlane Geo k alpha)
    (haPi : HilbertLineInPlane Geo a pi)
    (hbPi : HilbertLineInPlane Geo b pi) :
    Ne alpha pi := by

  intro hEq
  apply hTriangle.2.2.2.2.2.2

  refine
    ⟨pi,
     haPi,
     hbPi,
     ?_⟩

  rw [← hEq]
  exact hkAlpha

theorem localTriangle_of_three_side_planes
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (P : Geo.Point)
    (a d x : Geo.Line)
    (hPa : H.OnLine P a)
    (hPd : H.OnLine P d)
    (hPx : H.OnLine P x)
    (alpha epsilon pi : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hxAlpha : HilbertLineInPlane Geo x alpha)
    (hdEpsilon : HilbertLineInPlane Geo d epsilon)
    (_hxEpsilon : HilbertLineInPlane Geo x epsilon)
    (haPi : HilbertLineInPlane Geo a pi)
    (hdPi : HilbertLineInPlane Geo d pi)
    (hAlphaPi : Ne alpha pi)
    (had : Ne a d)
    (hax : Ne a x) :
    WylerLocalTriangleAtPoint Geo P a d x := by

  have hdx : Ne d x := by
    intro hdxEq
    subst d

    have hEq : alpha = pi :=
      plane_unique_of_two_distinct_lines_through_point
        (Geo := Geo)
        P a x hax
        hPa hPx
        alpha pi
        haAlpha hxAlpha
        haPi hdPi

    exact hAlphaPi hEq

  refine
    ⟨hPa,
     hPd,
     hPx,
     had,
     hdx,
     Ne.symm hax,
     ?_⟩

  intro hCoplanar
  rcases hCoplanar with
    ⟨delta, haDelta, hdDelta, hxDelta⟩

  have hDeltaAlpha : delta = alpha :=
    plane_unique_of_two_distinct_lines_through_point
      (Geo := Geo)
      P a x hax
      hPa hPx
      delta alpha
      haDelta hxDelta
      haAlpha hxAlpha

  have hDeltaPi : delta = pi :=
    plane_unique_of_two_distinct_lines_through_point
      (Geo := Geo)
      P a d had
      hPa hPd
      delta pi
      haDelta hdDelta
      haPi hdPi

  apply hAlphaPi
  rw [← hDeltaAlpha, ← hDeltaPi]

theorem wyler_second_P3_triangle_dichotomy
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (P : Geo.Point)
    (a b k x y d : Geo.Line)
    (hTriangle : WylerLocalTriangleAtPoint Geo P a b k)
    (alpha beta pi epsilon : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hkAlpha : HilbertLineInPlane Geo k alpha)
    (hbBeta : HilbertLineInPlane Geo b beta)
    (hkBeta : HilbertLineInPlane Geo k beta)
    (haPi : HilbertLineInPlane Geo a pi)
    (hbPi : HilbertLineInPlane Geo b pi)
    (hxAlpha : HilbertLineInPlane Geo x alpha)
    (hyBeta : HilbertLineInPlane Geo y beta)
    (hxEpsilon : HilbertLineInPlane Geo x epsilon)
    (hyEpsilon : HilbertLineInPlane Geo y epsilon)
    (hdPi : HilbertLineInPlane Geo d pi)
    (hdEpsilon : HilbertLineInPlane Geo d epsilon)
    (hPx : H.OnLine P x)
    (hPy : H.OnLine P y)
    (hPd : H.OnLine P d) :
    epsilon = pi \/
      WylerLocalTriangleAtPoint Geo P a d x \/
      WylerLocalTriangleAtPoint Geo P b d y := by

  rcases hTriangle with
    ⟨hPa, hPb, hPk, hab, hbk, hka, hNoncoplanar⟩

  have hAlphaPi : Ne alpha pi := by
    apply
      localTriangle_side_plane_ne_opposite
        (Geo := Geo)
        P a b k
        ⟨hPa, hPb, hPk, hab, hbk, hka, hNoncoplanar⟩
        alpha pi
        haAlpha hkAlpha
        haPi hbPi

  have hBetaPi : Ne beta pi := by
    intro hEq
    apply hNoncoplanar

    refine
      ⟨pi,
       haPi,
       hbPi,
       ?_⟩

    rw [← hEq]
    exact hkBeta

  by_cases hEpsilonPi : epsilon = pi

  · exact Or.inl hEpsilonPi

  · by_cases hax : a = x

    · by_cases hbd : b = d

      · have hEpsilonPi' : epsilon = pi := by
          have hxb : Ne x b := by
            intro hxbEq
            exact hab (hax.trans hxbEq)

          apply
            plane_unique_of_two_distinct_lines_through_point
              (Geo := Geo)
              P x b hxb
              hPx hPb
              epsilon pi
              hxEpsilon
              (by
                rw [hbd]
                exact hdEpsilon)
              (by
                rw [← hax]
                exact haPi)
              hbPi

        exact False.elim (hEpsilonPi hEpsilonPi')

      · have hby : Ne b y := by
          intro hbyEq

          have hEpsilonPi' : epsilon = pi := by
            apply
              plane_unique_of_two_distinct_lines_through_point
                (Geo := Geo)
                P d b
                (Ne.symm hbd)
                hPd hPb
                epsilon pi
                hdEpsilon
                (by
                  rw [hbyEq]
                  exact hyEpsilon)
                hdPi hbPi

          exact hEpsilonPi hEpsilonPi'

        have hTriangle2 :
            WylerLocalTriangleAtPoint Geo P b d y :=
          localTriangle_of_three_side_planes
            (Geo := Geo)
            P b d y
            hPb hPd hPy
            beta epsilon pi
            hbBeta hyBeta
            hdEpsilon hyEpsilon
            hbPi hdPi
            hBetaPi
            hbd
            hby

        exact Or.inr (Or.inr hTriangle2)

    · by_cases had : a = d

      · by_cases hby : b = y

        · have hEpsilonPi' : epsilon = pi := by
            apply
              plane_unique_of_two_distinct_lines_through_point
                (Geo := Geo)
                P a b hab
                hPa hPb
                epsilon pi
                (by
                  rw [had]
                  exact hdEpsilon)
                (by
                  rw [hby]
                  exact hyEpsilon)
                haPi hbPi

          exact False.elim (hEpsilonPi hEpsilonPi')

        · have hbd : Ne b d := by
            intro hbdEq
            apply hab
            rw [had, hbdEq]

          have hTriangle2 :
              WylerLocalTriangleAtPoint Geo P b d y :=
            localTriangle_of_three_side_planes
              (Geo := Geo)
              P b d y
              hPb hPd hPy
              beta epsilon pi
              hbBeta hyBeta
              hdEpsilon hyEpsilon
              hbPi hdPi
              hBetaPi
              hbd
              hby

          exact Or.inr (Or.inr hTriangle2)

      · have hTriangle1 :
            WylerLocalTriangleAtPoint Geo P a d x :=
          localTriangle_of_three_side_planes
            (Geo := Geo)
            P a d x
            hPa hPd hPx
            alpha epsilon pi
            haAlpha hxAlpha
            hdEpsilon hxEpsilon
            haPi hdPi
            hAlphaPi
            had
            hax

        exact Or.inr (Or.inl hTriangle1)

theorem wylerLocalP3_implies_canonicalSectionLine
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo) :
    WylerCanonicalSectionLine Geo := by

  intro F hFlat P R A hPF hRF hPR hAOut k hPk hAk X Y hXk hYk a b hab alpha beta hPa hPb haF hbF haAlpha hAAlpha hXAlpha hbBeta hABeta hYBeta m hXY hXm hYm Z hZm hZk gamma hPgamma hAgamma hZgamma

  have hPA : Ne P A :=
    wyler_apex_ne_base_point
      (Geo := Geo)
      F P A hPF hAOut

  have hAlphaBeta : Ne alpha beta :=
    wyler_hard_side_planes_ne
      (Geo := Geo)
      F hFlat
      P A
      hPF hAOut
      a b hab
      hPa hPb
      haF hbF
      alpha beta
      haAlpha hAAlpha
      hbBeta hABeta

  have hkBoth :
      HilbertLineInPlane Geo k alpha /\
      HilbertLineInPlane Geo k beta :=
    wyler_axis_in_two_cone_planes
      (Geo := Geo)
      F P A
      hPF hAOut
      k a b
      hPk hAk
      hPa hPb
      alpha beta
      haAlpha hAAlpha
      hbBeta hABeta

  rcases
      smithFlat_plane_of_two_distinct_lines_through_point
        (Geo := Geo)
        F hFlat
        P hPF
        a b hab
        hPa hPb
        haF hbF with
    ⟨pi, haPi, hbPi, hpiF⟩

  by_cases hZX : Z = X

  · subst Z

    have hPAX :
        Not (PrimCollinear Geo P A X) :=
      wyler_axis_off_point_noncollinear
        (Geo := Geo)
        P A X
        hPA
        k hPk hAk
        hXk

    have hAlphaGamma : alpha = gamma :=
      C.plane_unique
        P A X hPAX
        alpha gamma
        (haAlpha P hPa)
        hAAlpha
        hXAlpha
        hPgamma
        hAgamma
        hZgamma

    have haGamma : HilbertLineInPlane Geo a gamma := by
      rw [← hAlphaGamma]
      exact haAlpha

    exact
      ⟨a,
       hPa,
       haF,
       haGamma⟩

  · by_cases hZY : Z = Y

    · subst Z

      have hPAY :
          Not (PrimCollinear Geo P A Y) :=
        wyler_axis_off_point_noncollinear
          (Geo := Geo)
          P A Y
          hPA
          k hPk hAk
          hYk

      have hBetaGamma : beta = gamma :=
        C.plane_unique
          P A Y hPAY
          beta gamma
          (hbBeta P hPb)
          hABeta
          hYBeta
          hPgamma
          hAgamma
          hZgamma

      have hbGamma : HilbertLineInPlane Geo b gamma := by
        rw [← hBetaGamma]
        exact hbBeta

      exact
        ⟨b,
         hPb,
         hbF,
         hbGamma⟩

    · have hPX : Ne P X := by
        intro hPXeq
        subst X
        exact hXk hPk

      have hPY : Ne P Y := by
        intro hPYeq
        subst Y
        exact hYk hPk

      have hPZ : Ne P Z := by
        intro hPZeq
        subst Z
        exact hZk hPk

      rcases
          HilbertPlaneIncidence.line_through
            (Geo := Geo)
            P X hPX with
        ⟨x, hPx, hXx⟩

      rcases
          HilbertPlaneIncidence.line_through
            (Geo := Geo)
            P Y hPY with
        ⟨y, hPy, hYy⟩

      rcases
          HilbertPlaneIncidence.line_through
            (Geo := Geo)
            P Z hPZ with
        ⟨z, hPz, hZz⟩

      have hxAlpha : HilbertLineInPlane Geo x alpha :=
        C.line_in_plane
          P X hPX
          x hPx hXx
          alpha
          (haAlpha P hPa)
          hXAlpha

      have hyBeta : HilbertLineInPlane Geo y beta :=
        C.line_in_plane
          P Y hPY
          y hPy hYy
          beta
          (hbBeta P hPb)
          hYBeta

      have hPm : Not (H.OnLine P m) := by
        intro hPm

        have hmAlpha : HilbertLineInPlane Geo m alpha :=
          C.line_in_plane
            P X hPX
            m hPm hXm
            alpha
            (haAlpha P hPa)
            hXAlpha

        have hmBeta : HilbertLineInPlane Geo m beta :=
          C.line_in_plane
            P Y hPY
            m hPm hYm
            beta
            (hbBeta P hPb)
            hYBeta

        have hPAX :
            Not (PrimCollinear Geo P A X) :=
          wyler_axis_off_point_noncollinear
            (Geo := Geo)
            P A X
            hPA
            k hPk hAk
            hXk

        have hEq : alpha = beta :=
          C.plane_unique
            P A X hPAX
            alpha beta
            (haAlpha P hPa)
            hAAlpha
            hXAlpha
            (hbBeta P hPb)
            hABeta
            (hmBeta X hXm)

        exact hAlphaBeta hEq

      have hPXY :
          Not (PrimCollinear Geo P X Y) := by

        intro hCol

        have hPonM : H.OnLine P m :=
          smithCore_on_line_of_collinear_with_two
            (Geo := Geo)
            X Y P hXY
            m hXm hYm
            (PrimCollinearCycle
              (Geo := Geo)
              P X Y hCol)

        exact hPm hPonM

      rcases
          C.plane_through
            P X Y hPXY with
        ⟨epsilon, hPepsilon, hXepsilon, hYepsilon⟩

      have hmEpsilon : HilbertLineInPlane Geo m epsilon :=
        C.line_in_plane
          X Y hXY
          m hXm hYm
          epsilon hXepsilon hYepsilon

      have hZepsilon : S.OnPlane Z epsilon :=
        hmEpsilon Z hZm

      have hxEpsilon : HilbertLineInPlane Geo x epsilon :=
        C.line_in_plane
          P X hPX
          x hPx hXx
          epsilon hPepsilon hXepsilon

      have hyEpsilon : HilbertLineInPlane Geo y epsilon :=
        C.line_in_plane
          P Y hPY
          y hPy hYy
          epsilon hPepsilon hYepsilon

      have hzEpsilon : HilbertLineInPlane Geo z epsilon :=
        C.line_in_plane
          P Z hPZ
          z hPz hZz
          epsilon hPepsilon hZepsilon

      have hkGamma : HilbertLineInPlane Geo k gamma :=
        C.line_in_plane
          P A hPA
          k hPk hAk
          gamma hPgamma hAgamma

      have hzGamma : HilbertLineInPlane Geo z gamma :=
        C.line_in_plane
          P Z hPZ
          z hPz hZz
          gamma hPgamma hZgamma

      rcases
          wylerLocalP3_first_cross_line
            (Geo := Geo)
            hP3
            F hFlat
            P A X Y
            hPF hAOut
            k hPk hAk
            hXk hYk
            a b hab
            hPa hPb
            haF hbF
            alpha beta pi epsilon
            haAlpha hkBoth.1
            hbBeta hkBoth.2
            haPi hbPi
            x y
            hPx hXx
            hPy hYy
            hxAlpha hxEpsilon
            hyBeta hyEpsilon with
        ⟨d, hPd, hdPi, hdEpsilon⟩

      have hTriangle0 :
          WylerLocalTriangleAtPoint Geo P a b k :=
        wyler_base_axis_local_triangle
          (Geo := Geo)
          F hFlat
          P A
          hPF hAOut
          k hPk hAk
          a b hab
          hPa hPb
          haF hbF

      rcases
          wyler_second_P3_triangle_dichotomy
            (Geo := Geo)
            P
            a b k x y d
            hTriangle0
            alpha beta pi epsilon
            haAlpha hkBoth.1
            hbBeta hkBoth.2
            haPi hbPi
            hxAlpha hyBeta
            hxEpsilon hyEpsilon
            hdPi hdEpsilon
            hPx hPy hPd with
        hEpsilonPi | hTriangle1 | hTriangle2

      · have hzPi : HilbertLineInPlane Geo z pi := by
          rw [← hEpsilonPi]
          exact hzEpsilon

        exact
          ⟨z,
           hPz,
           (fun T hTz => hpiF T (hzPi T hTz)),
           hzGamma⟩

      · have hkx : Ne k x := by
          exact
            Ne.symm
              (wyler_ray_ne_axis_of_point_off_axis
                (Geo := Geo)
                X
                k x
                hXk hXx)

        have hzx : Ne z x :=
          lines_from_external_point_to_two_line_points_ne
            (Geo := Geo)
            P Z X
            (by
              intro hZXeq
              exact hZX hZXeq)
            m hZm hXm hPm
            z x
            hPz hZz
            hPx hXx

        rcases
            wylerLocalP3_second_cross_line
              (Geo := Geo)
              hP3
              P
              a d x k z
              hTriangle1
              alpha epsilon pi gamma
              haAlpha hxAlpha
              hdEpsilon hxEpsilon
              haPi hdPi
              hPk hPz
              hkBoth.1 hkGamma
              hzEpsilon hzGamma
              hkx hzx with
          ⟨c, hPc, hcPi, hcGamma⟩

        exact
          ⟨c,
           hPc,
           (fun T hTc => hpiF T (hcPi T hTc)),
           hcGamma⟩

      · have hky : Ne k y := by
          exact
            Ne.symm
              (wyler_ray_ne_axis_of_point_off_axis
                (Geo := Geo)
                Y
                k y
                hYk hYy)

        have hzy : Ne z y :=
          lines_from_external_point_to_two_line_points_ne
            (Geo := Geo)
            P Z Y
            (by
              intro hZYeq
              exact hZY hZYeq)
            m hZm hYm hPm
            z y
            hPz hZz
            hPy hYy

        rcases
            wylerLocalP3_second_cross_line
              (Geo := Geo)
              hP3
              P
              b d y k z
              hTriangle2
              beta epsilon pi gamma
              hbBeta hyBeta
              hdEpsilon hyEpsilon
              hbPi hdPi
              hPk hPz
              hkBoth.2 hkGamma
              hzEpsilon hzGamma
              hky hzy with
          ⟨c, hPc, hcPi, hcGamma⟩

        exact
          ⟨c,
           hPc,
           (fun T hTc => hpiF T (hcPi T hTc)),
           hcGamma⟩

theorem wylerLocalP3_implies_distinctOffAxisLineClosure
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo) :
    WylerConeDistinctOffAxisLineClosure Geo := by

  have hSection :
      WylerCanonicalSectionLine Geo :=
    wylerLocalP3_implies_canonicalSectionLine
      (Geo := Geo)
      hP3

  exact
    wylerCanonicalSectionLine_implies_distinctOffAxisLineClosure
      (Geo := Geo)
      hSection

theorem wylerLocalP3_implies_planeConeLineClosure
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo) :
    WylerPlaneConeLineClosure Geo := by

  have hHard :
      WylerConeDistinctOffAxisLineClosure Geo :=
    wylerLocalP3_implies_distinctOffAxisLineClosure
      (Geo := Geo)
      hP3

  intro F hFlat P R hPF hRF hPR A hAOut X Y hX hY hXY m hXm hYm Z hZm

  exact
    wylerConeDistinctOffAxis_implies_full_line_closure
      (Geo := Geo)
      hHard
      F hFlat
      P R A
      hPF hRF hPR
      hAOut
      X Y
      hX hY hXY
      m hXm hYm
      Z hZm

def WylerPlaneConePlaneClosure
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall F : Set Geo.Point,
    SmithFlat Geo F ->
    forall P R : Geo.Point,
      F P ->
      F R ->
      Ne P R ->
      forall A : Geo.Point,
        Not (F A) ->
        forall U V W : Geo.Point,
          WylerPlaneCone Geo F P A U ->
          WylerPlaneCone Geo F P A V ->
          WylerPlaneCone Geo F P A W ->
          Not (PrimCollinear Geo U V W) ->
          forall pi : S.Plane,
            S.OnPlane U pi ->
            S.OnPlane V pi ->
            S.OnPlane W pi ->
            forall X : Geo.Point,
              S.OnPlane X pi ->
              WylerPlaneCone Geo F P A X

theorem wylerConeLineAndPlaneClosure_implies_flatness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (hLine : WylerPlaneConeLineClosure Geo)
    (hPlane : WylerPlaneConePlaneClosure Geo) :
    WylerPlaneConeFlatness Geo := by

  intro F hFlat P R hPF hRF hPR A hAOut

  constructor

  · intro U V hU hV hUV l hUl hVl X hXl

    exact
      hLine
        F hFlat
        P R hPF hRF hPR
        A hAOut
        U V hU hV hUV
        l hUl hVl
        X hXl

  · intro U V W hU hV hW hUVW pi hUpi hVpi hWpi X hXpi

    exact
      hPlane
        F hFlat
        P R hPF hRF hPR
        A hAOut
        U V W
        hU hV hW
        hUVW
        pi
        hUpi hVpi hWpi
        X hXpi

theorem wylerLocalP3_and_planeClosure_implies_coneFlatness
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (hPlane : WylerPlaneConePlaneClosure Geo) :
    WylerPlaneConeFlatness Geo := by

  have hLine :
      WylerPlaneConeLineClosure Geo :=
    wylerLocalP3_implies_planeConeLineClosure
      (Geo := Geo)
      hP3

  exact
    wylerConeLineAndPlaneClosure_implies_flatness
      (Geo := Geo)
      hLine hPlane

theorem wylerLocalP3_and_planeClosure_implies_onePointGenerationFormula
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (hPlane : WylerPlaneConePlaneClosure Geo) :
    WylerOnePointGenerationFormula Geo := by

  have hConeFlat :
      WylerPlaneConeFlatness Geo :=
    wylerLocalP3_and_planeClosure_implies_coneFlatness
      (Geo := Geo)
      hP3 hPlane

  exact
    wylerPlaneConeFlatness_implies_onePointGenerationFormula
      (Geo := Geo)
      hConeFlat

theorem smithCore_plane_through_two_distinct_lines_at_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (P : Geo.Point)
    (r s : Geo.Line)
    (hrs : Ne r s)
    (hPr : H.OnLine P r)
    (hPs : H.OnLine P s) :
    exists gamma : S.Plane,
      HilbertLineInPlane Geo r gamma /\
      HilbertLineInPlane Geo s gamma := by

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P r hPr with
    ⟨R, hPR, hRr⟩

  rcases
      smithCore_other_point_on_line
        (Geo := Geo)
        P s hPs with
    ⟨T, hPT, hTs⟩

  have hPRT :
      Not (PrimCollinear Geo P R T) := by

    intro hCol

    have hTr : H.OnLine T r :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        P R T hPR
        r hPr hRr
        hCol

    have hsr : s = r :=
      HilbertPlaneIncidence.line_unique
        P T hPT
        s r
        hPs hTs
        hPr hTr

    exact hrs hsr.symm

  rcases
      C.plane_through
        P R T hPRT with
    ⟨gamma, hPgamma, hRgamma, hTgamma⟩

  have hrGamma : HilbertLineInPlane Geo r gamma :=
    C.line_in_plane
      P R hPR
      r hPr hRr
      gamma
      hPgamma hRgamma

  have hsGamma : HilbertLineInPlane Geo s gamma :=
    C.line_in_plane
      P T hPT
      s hPs hTs
      gamma
      hPgamma hTgamma

  exact
    ⟨gamma,
     hrGamma,
     hsGamma⟩

def WylerLocalJoinWitness
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (P : Geo.Point)
    (k x : Geo.Line)
    (pi : S.Plane) : Prop :=
  exists c : Geo.Line,
    exists gamma : S.Plane,
      H.OnLine P c /\
      HilbertLineInPlane Geo c pi /\
      HilbertLineInPlane Geo c gamma /\
      HilbertLineInPlane Geo k gamma /\
      HilbertLineInPlane Geo x gamma

theorem wylerLocalP3_local_join_line_closure
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (P : Geo.Point)
    (a b k u v x : Geo.Line)
    (hTriangle : WylerLocalTriangleAtPoint Geo P a b k)
    (alpha beta pi epsilon : S.Plane)
    (haAlpha : HilbertLineInPlane Geo a alpha)
    (hkAlpha : HilbertLineInPlane Geo k alpha)
    (hbBeta : HilbertLineInPlane Geo b beta)
    (hkBeta : HilbertLineInPlane Geo k beta)
    (haPi : HilbertLineInPlane Geo a pi)
    (hbPi : HilbertLineInPlane Geo b pi)
    (hPu : H.OnLine P u)
    (hPv : H.OnLine P v)
    (hPx : H.OnLine P x)
    (huAlpha : HilbertLineInPlane Geo u alpha)
    (huEpsilon : HilbertLineInPlane Geo u epsilon)
    (hvBeta : HilbertLineInPlane Geo v beta)
    (hvEpsilon : HilbertLineInPlane Geo v epsilon)
    (hxEpsilon : HilbertLineInPlane Geo x epsilon)
    (huk : Ne u k)
    (hvk : Ne v k) :
    WylerLocalJoinWitness Geo P k x pi := by

  rcases hTriangle with
    ⟨hPa, hPb, hPk, hab, hbk, hka, hNoncoplanar⟩

  by_cases hxk : x = k

  · subst x

    exact
      ⟨a,
       alpha,
       hPa,
       haPi,
       haAlpha,
       hkAlpha,
       hkAlpha⟩

  · by_cases hxu : x = u

    · subst x

      exact
        ⟨a,
         alpha,
         hPa,
         haPi,
         haAlpha,
         hkAlpha,
         huAlpha⟩

    · by_cases hxv : x = v

      · subst x

        exact
          ⟨b,
           beta,
           hPb,
           hbPi,
           hbBeta,
           hkBeta,
           hvBeta⟩

      · rcases
            smithCore_plane_through_two_distinct_lines_at_point
              (Geo := Geo)
              P
              k x
              (Ne.symm hxk)
              hPk hPx with
          ⟨gamma, hkGamma, hxGamma⟩

        rcases
            hP3
              P
              a b k
              ⟨hPa, hPb, hPk, hab, hbk, hka, hNoncoplanar⟩
              alpha beta pi
              haAlpha hkAlpha
              hbBeta hkBeta
              haPi hbPi
              epsilon
              u v
              hPu hPv
              huAlpha huEpsilon
              hvBeta hvEpsilon
              huk hvk with
          ⟨d, hPd, hdPi, hdEpsilon⟩

        rcases
            wyler_second_P3_triangle_dichotomy
              (Geo := Geo)
              P
              a b k u v d
              ⟨hPa, hPb, hPk, hab, hbk, hka, hNoncoplanar⟩
              alpha beta pi epsilon
              haAlpha hkAlpha
              hbBeta hkBeta
              haPi hbPi
              huAlpha hvBeta
              huEpsilon hvEpsilon
              hdPi hdEpsilon
              hPu hPv hPd with
          hEpsilonPi | hTriangle1 | hTriangle2

        · have hxPi : HilbertLineInPlane Geo x pi := by
            rw [← hEpsilonPi]
            exact hxEpsilon

          exact
            ⟨x,
             gamma,
             hPx,
             hxPi,
             hxGamma,
             hkGamma,
             hxGamma⟩

        · have hku : Ne k u :=
            Ne.symm huk

          have hxu' : Ne x u :=
            hxu

          rcases
              wylerLocalP3_second_cross_line
                (Geo := Geo)
                hP3
                P
                a d u k x
                hTriangle1
                alpha epsilon pi gamma
                haAlpha huAlpha
                hdEpsilon huEpsilon
                haPi hdPi
                hPk hPx
                hkAlpha hkGamma
                hxEpsilon hxGamma
                hku hxu' with
            ⟨c, hPc, hcPi, hcGamma⟩

          exact
            ⟨c,
             gamma,
             hPc,
             hcPi,
             hcGamma,
             hkGamma,
             hxGamma⟩

        · have hkv : Ne k v :=
            Ne.symm hvk

          have hxv' : Ne x v :=
            hxv

          rcases
              wylerLocalP3_second_cross_line
                (Geo := Geo)
                hP3
                P
                b d v k x
                hTriangle2
                beta epsilon pi gamma
                hbBeta hvBeta
                hdEpsilon hvEpsilon
                hbPi hdPi
                hPk hPx
                hkBeta hkGamma
                hxEpsilon hxGamma
                hkv hxv' with
            ⟨c, hPc, hcPi, hcGamma⟩

          exact
            ⟨c,
             gamma,
             hPc,
             hcPi,
             hcGamma,
             hkGamma,
             hxGamma⟩

theorem wylerLocalP3_cone_plane_through_base_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P R A : Geo.Point)
    (hPF : F P)
    (hRF : F R)
    (hPR : Ne P R)
    (hAOut : Not (F A))
    (U V : Geo.Point)
    (hU : WylerPlaneCone Geo F P A U)
    (hV : WylerPlaneCone Geo F P A V)
    (hPUV : Not (PrimCollinear Geo P U V))
    (epsilon : S.Plane)
    (hPepsilon : S.OnPlane P epsilon)
    (hUepsilon : S.OnPlane U epsilon)
    (hVepsilon : S.OnPlane V epsilon) :
    forall X : Geo.Point,
      S.OnPlane X epsilon ->
      WylerPlaneCone Geo F P A X := by

  rcases hU with
    ⟨a, alpha, hPa, haF, haAlpha, hAAlpha, hUAlpha⟩

  rcases hV with
    ⟨b, beta, hPb, hbF, hbBeta, hABeta, hVBeta⟩

  have hPA : Ne P A :=
    wyler_apex_ne_base_point
      (Geo := Geo)
      F P A hPF hAOut

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        P A hPA with
    ⟨k, hPk, hAk⟩

  intro X hXepsilon

  by_cases hab : a = b

  · subst b

    have hAlphaBeta : alpha = beta :=
      wylerConePlane_unique_of_base_line
        (Geo := Geo)
        F P A
        hPF hAOut
        a hPa haF
        alpha beta
        haAlpha hAAlpha
        hbBeta hABeta

    have hVAlpha : S.OnPlane V alpha := by
      rw [hAlphaBeta]
      exact hVBeta

    have hEpsilonAlpha : epsilon = alpha :=
      C.plane_unique
        P U V hPUV
        epsilon alpha
        hPepsilon hUepsilon hVepsilon
        (haAlpha P hPa)
        hUAlpha
        hVAlpha

    have hXAlpha : S.OnPlane X alpha := by
      rw [← hEpsilonAlpha]
      exact hXepsilon

    exact
      ⟨a, alpha,
       hPa,
       haF,
       haAlpha,
       hAAlpha,
       hXAlpha⟩

  · have hTriangle :
        WylerLocalTriangleAtPoint Geo P a b k :=
      wyler_base_axis_local_triangle
        (Geo := Geo)
        F hFlat
        P A
        hPF hAOut
        k hPk hAk
        a b hab
        hPa hPb
        haF hbF

    have hkAlpha : HilbertLineInPlane Geo k alpha :=
      wylerConePlane_contains_axis
        (Geo := Geo)
        F P A
        hPF hAOut
        a hPa
        alpha haAlpha hAAlpha
        k hPk hAk

    have hkBeta : HilbertLineInPlane Geo k beta :=
      wylerConePlane_contains_axis
        (Geo := Geo)
        F P A
        hPF hAOut
        b hPb
        beta hbBeta hABeta
        k hPk hAk

    by_cases hUk : H.OnLine U k

    · have hVk : Not (H.OnLine V k) := by
        intro hVk
        exact
          hPUV
            ⟨k, hPk, hUk, hVk⟩

      have hPV : Ne P V := by
        intro hPV
        subst V
        exact hVk hPk

      have hPU : Ne P U := by
        intro hPU
        subst U

        rcases
            HilbertPlaneIncidence.line_through
              (Geo := Geo)
              P V hPV with
          ⟨m, hPm, hVm⟩

        exact
          hPUV
            ⟨m, hPm, hPm, hVm⟩

      have hkEpsilon : HilbertLineInPlane Geo k epsilon :=
        C.line_in_plane
          P U hPU
          k hPk hUk
          epsilon
          hPepsilon hUepsilon

      have hAepsilon : S.OnPlane A epsilon :=
        hkEpsilon A hAk

      have hPAV :
          Not (PrimCollinear Geo P A V) :=
        wyler_axis_off_point_noncollinear
          (Geo := Geo)
          P A V
          hPA
          k hPk hAk
          hVk

      have hEpsilonBeta : epsilon = beta :=
        C.plane_unique
          P A V hPAV
          epsilon beta
          hPepsilon
          hAepsilon
          hVepsilon
          (hbBeta P hPb)
          hABeta
          hVBeta

      have hXBeta : S.OnPlane X beta := by
        rw [← hEpsilonBeta]
        exact hXepsilon

      exact
        ⟨b, beta,
         hPb,
         hbF,
         hbBeta,
         hABeta,
         hXBeta⟩

    · by_cases hVk : H.OnLine V k

      · have hPU : Ne P U := by
          intro hPU
          subst U
          exact hUk hPk

        have hPV : Ne P V := by
          intro hPV
          subst V

          rcases
              HilbertPlaneIncidence.line_through
                (Geo := Geo)
                P U hPU with
            ⟨m, hPm, hUm⟩

          exact
            hPUV
              ⟨m, hPm, hUm, hPm⟩

        have hkEpsilon : HilbertLineInPlane Geo k epsilon :=
          C.line_in_plane
            P V hPV
            k hPk hVk
            epsilon
            hPepsilon hVepsilon

        have hAepsilon : S.OnPlane A epsilon :=
          hkEpsilon A hAk

        have hPAU :
            Not (PrimCollinear Geo P A U) :=
          wyler_axis_off_point_noncollinear
            (Geo := Geo)
            P A U
            hPA
            k hPk hAk
            hUk

        have hEpsilonAlpha : epsilon = alpha :=
          C.plane_unique
            P A U hPAU
            epsilon alpha
            hPepsilon
            hAepsilon
            hUepsilon
            (haAlpha P hPa)
            hAAlpha
            hUAlpha

        have hXAlpha : S.OnPlane X alpha := by
          rw [← hEpsilonAlpha]
          exact hXepsilon

        exact
          ⟨a, alpha,
           hPa,
           haF,
           haAlpha,
           hAAlpha,
           hXAlpha⟩

      · have hPU : Ne P U := by
          intro hPU
          subst U
          exact hUk hPk

        have hPV : Ne P V := by
          intro hPV
          subst V
          exact hVk hPk

        rcases
            HilbertPlaneIncidence.line_through
              (Geo := Geo)
              P U hPU with
          ⟨u, hPu, hUu⟩

        rcases
            HilbertPlaneIncidence.line_through
              (Geo := Geo)
              P V hPV with
          ⟨v, hPv, hVv⟩

        have huAlpha : HilbertLineInPlane Geo u alpha :=
          C.line_in_plane
            P U hPU
            u hPu hUu
            alpha
            (haAlpha P hPa)
            hUAlpha

        have hvBeta : HilbertLineInPlane Geo v beta :=
          C.line_in_plane
            P V hPV
            v hPv hVv
            beta
            (hbBeta P hPb)
            hVBeta

        have huEpsilon : HilbertLineInPlane Geo u epsilon :=
          C.line_in_plane
            P U hPU
            u hPu hUu
            epsilon
            hPepsilon hUepsilon

        have hvEpsilon : HilbertLineInPlane Geo v epsilon :=
          C.line_in_plane
            P V hPV
            v hPv hVv
            epsilon
            hPepsilon hVepsilon

        have huk : Ne u k :=
          wyler_ray_ne_axis_of_point_off_axis
            (Geo := Geo)
            U
            k u
            hUk hUu

        have hvk : Ne v k :=
          wyler_ray_ne_axis_of_point_off_axis
            (Geo := Geo)
            V
            k v
            hVk hVv

        rcases
            smithFlat_plane_of_two_distinct_lines_through_point
              (Geo := Geo)
              F hFlat
              P hPF
              a b hab
              hPa hPb
              haF hbF with
          ⟨pi, haPi, hbPi, hpiF⟩

        by_cases hPX : P = X

        · subst X

          exact
            wylerPlaneCone_contains_base
              (Geo := Geo)
              F hFlat
              P R A
              hPF hRF hPR
              hAOut
              hPF

        · have hPX' : Ne P X :=
            hPX

          rcases
              HilbertPlaneIncidence.line_through
                (Geo := Geo)
                P X hPX' with
            ⟨x, hPx, hXx⟩

          have hxEpsilon : HilbertLineInPlane Geo x epsilon :=
            C.line_in_plane
              P X hPX'
              x hPx hXx
              epsilon
              hPepsilon hXepsilon

          rcases
              wylerLocalP3_local_join_line_closure
                (Geo := Geo)
                hP3
                P
                a b k u v x
                hTriangle
                alpha beta pi epsilon
                haAlpha hkAlpha
                hbBeta hkBeta
                haPi hbPi
                hPu hPv hPx
                huAlpha huEpsilon
                hvBeta hvEpsilon
                hxEpsilon
                huk hvk with
            ⟨c, gamma, hPc, hcPi, hcGamma, hkGamma, hxGamma⟩

          have hcF :
              forall T : Geo.Point,
                H.OnLine T c ->
                F T := by

            intro T hTc
            exact
              hpiF T (hcPi T hTc)

          have hAGamma : S.OnPlane A gamma :=
            hkGamma A hAk

          have hXGamma : S.OnPlane X gamma :=
            hxGamma X hXx

          exact
            ⟨c, gamma,
             hPc,
             hcF,
             hcGamma,
             hAGamma,
             hXGamma⟩

theorem noncollinear_pair_with_plane_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (P U V W : Geo.Point)
    (hUVW : Not (PrimCollinear Geo U V W)) :
    Not (PrimCollinear Geo P U V) \/
    Not (PrimCollinear Geo P U W) \/
    Not (PrimCollinear Geo P V W) := by

  by_cases hPU : P = U

  · subst U
    exact Or.inr (Or.inr hUVW)

  · by_cases hPV : P = V

    · subst V

      have hUPW :
          Not (PrimCollinear Geo P U W) := by
        intro hCol

        apply hUVW

        exact
          PrimCollinearSwap
            (Geo := Geo)
            P U W
            hCol

      exact Or.inr (Or.inl hUPW)

    · by_cases hPW : P = W

      · subst W

        have hPUV' :
            Not (PrimCollinear Geo P U V) := by
          intro hCol

          apply hUVW

          have hUVP :
              PrimCollinear Geo U V P :=
            PrimCollinearCycle
              (Geo := Geo)
              P U V
              hCol

          exact hUVP

        exact Or.inl hPUV'

      · by_cases hPUV : PrimCollinear Geo P U V

        · by_cases hPUW : PrimCollinear Geo P U W

          · rcases hPUV with
              ⟨l, hPl, hUl, hVl⟩

            rcases hPUW with
              ⟨m, hPm, hUm, hWm⟩

            have hlm : l = m :=
              HilbertPlaneIncidence.line_unique
                P U hPU
                l m
                hPl hUl
                hPm hUm

            subst m

            exact
              False.elim
                (hUVW
                  ⟨l,
                   hUl,
                   hVl,
                   hWm⟩)

          · exact Or.inr (Or.inl hPUW)

        · exact Or.inl hPUV

theorem wylerLocalP3_cone_plane_closure_when_base_point_on_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P R A : Geo.Point)
    (hPF : F P)
    (hRF : F R)
    (hPR : Ne P R)
    (hAOut : Not (F A))
    (U V W : Geo.Point)
    (hU : WylerPlaneCone Geo F P A U)
    (hV : WylerPlaneCone Geo F P A V)
    (hW : WylerPlaneCone Geo F P A W)
    (hUVW : Not (PrimCollinear Geo U V W))
    (pi : S.Plane)
    (hPpi : S.OnPlane P pi)
    (hUpi : S.OnPlane U pi)
    (hVpi : S.OnPlane V pi)
    (hWpi : S.OnPlane W pi) :
    forall X : Geo.Point,
      S.OnPlane X pi ->
      WylerPlaneCone Geo F P A X := by

  rcases
      noncollinear_pair_with_plane_point
        (Geo := Geo)
        P U V W
        hUVW with
    hPUV | hPUW | hPVW

  · exact
      wylerLocalP3_cone_plane_through_base_point
        (Geo := Geo)
        hP3
        F hFlat
        P R A
        hPF hRF hPR
        hAOut
        U V
        hU hV
        hPUV
        pi
        hPpi hUpi hVpi

  · exact
      wylerLocalP3_cone_plane_through_base_point
        (Geo := Geo)
        hP3
        F hFlat
        P R A
        hPF hRF hPR
        hAOut
        U W
        hU hW
        hPUW
        pi
        hPpi hUpi hWpi

  · exact
      wylerLocalP3_cone_plane_through_base_point
        (Geo := Geo)
        hP3
        F hFlat
        P R A
        hPF hRF hPR
        hAOut
        V W
        hV hW
        hPVW
        pi
        hPpi hVpi hWpi

theorem wylerLocalP3_and_SmithI5_cone_plane_closure_when_base_point_off_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (hI5 : SmithI5Statement Geo)
    (F : Set Geo.Point)
    (hFlat : SmithFlat Geo F)
    (P R A : Geo.Point)
    (hPF : F P)
    (hRF : F R)
    (hPR : Ne P R)
    (hAOut : Not (F A))
    (U V W : Geo.Point)
    (hU : WylerPlaneCone Geo F P A U)
    (hV : WylerPlaneCone Geo F P A V)
    (hW : WylerPlaneCone Geo F P A W)
    (hUVW : Not (PrimCollinear Geo U V W))
    (pi : S.Plane)
    (hPOut : Not (S.OnPlane P pi))
    (hUpi : S.OnPlane U pi)
    (hVpi : S.OnPlane V pi)
    (hWpi : S.OnPlane W pi) :
    forall X : Geo.Point,
      S.OnPlane X pi ->
      WylerPlaneCone Geo F P A X := by

  have hVW : Ne V W := by
    intro hEq
    apply hUVW

    have hVWU :
        PrimCollinear Geo V W U :=
      primCollinear_of_eq_first_second
        (Geo := Geo)
        V W U hEq

    have hWUV :
        PrimCollinear Geo W U V :=
      PrimCollinearCycle
        (Geo := Geo)
        V W U hVWU

    exact
      PrimCollinearCycle
        (Geo := Geo)
        W U V hWUV

  have hPVW :
      Not (PrimCollinear Geo P V W) := by

    intro hCol
    rcases hCol with
      ⟨l, hPl, hVl, hWl⟩

    have hlPi : HilbertLineInPlane Geo l pi :=
      C.line_in_plane
        V W hVW
        l hVl hWl
        pi hVpi hWpi

    exact hPOut (hlPi P hPl)

  intro X hXpi

  have hUVXW :
      HilbertCoplanar4 Geo U V X W :=
    ⟨pi,
     hUpi,
     hVpi,
     hXpi,
     hWpi⟩

  rcases
      hI5
        U V X W
        hUVXW
        P with
    ⟨Q, hQP, hPUXQ, hPVWQ⟩

  rcases hPVWQ with
    ⟨beta,
     hPbeta,
     hVbeta,
     hWbeta,
     hQbeta⟩

  have hBetaCone :
      forall T : Geo.Point,
        S.OnPlane T beta ->
        WylerPlaneCone Geo F P A T :=
    wylerLocalP3_cone_plane_through_base_point
      (Geo := Geo)
      hP3
      F hFlat
      P R A
      hPF hRF hPR
      hAOut
      V W
      hV hW
      hPVW
      beta
      hPbeta hVbeta hWbeta

  have hQ :
      WylerPlaneCone Geo F P A Q :=
    hBetaCone Q hQbeta

  have hPUQ :
      Not (PrimCollinear Geo P U Q) := by

    intro hCol
    rcases hCol with
      ⟨l, hPl, hUl, hQl⟩

    have hlBeta : HilbertLineInPlane Geo l beta :=
      C.line_in_plane
        P Q
        (Ne.symm hQP)
        l hPl hQl
        beta hPbeta hQbeta

    have hUbeta : S.OnPlane U beta :=
      hlBeta U hUl

    have hBetaPi : beta = pi :=
      C.plane_unique
        U V W hUVW
        beta pi
        hUbeta hVbeta hWbeta
        hUpi hVpi hWpi

    have hPpi : S.OnPlane P pi := by
      rw [← hBetaPi]
      exact hPbeta

    exact hPOut hPpi

  rcases hPUXQ with
    ⟨delta,
     hPdelta,
     hUdelta,
     hXdelta,
     hQdelta⟩

  have hDeltaCone :
      forall T : Geo.Point,
        S.OnPlane T delta ->
        WylerPlaneCone Geo F P A T :=
    wylerLocalP3_cone_plane_through_base_point
      (Geo := Geo)
      hP3
      F hFlat
      P R A
      hPF hRF hPR
      hAOut
      U Q
      hU hQ
      hPUQ
      delta
      hPdelta hUdelta hQdelta

  exact hDeltaCone X hXdelta

theorem wylerLocalP3_and_SmithI5_implies_planeConePlaneClosure
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (hI5 : SmithI5Statement Geo) :
    WylerPlaneConePlaneClosure Geo := by

  intro F hFlat P R hPF hRF hPR A hAOut U V W hU hV hW hUVW pi hUpi hVpi hWpi X hXpi

  by_cases hPpi : S.OnPlane P pi

  · exact
      wylerLocalP3_cone_plane_closure_when_base_point_on_plane
        (Geo := Geo)
        hP3
        F hFlat
        P R A
        hPF hRF hPR
        hAOut
        U V W
        hU hV hW
        hUVW
        pi
        hPpi hUpi hVpi hWpi
        X hXpi

  · exact
      wylerLocalP3_and_SmithI5_cone_plane_closure_when_base_point_off_plane
        (Geo := Geo)
        hP3 hI5
        F hFlat
        P R A
        hPF hRF hPR
        hAOut
        U V W
        hU hV hW
        hUVW
        pi
        hPpi hUpi hVpi hWpi
        X hXpi

theorem wylerLocalP3_and_SmithI5_implies_coneFlatness
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (hI5 : SmithI5Statement Geo) :
    WylerPlaneConeFlatness Geo := by

  have hPlane :
      WylerPlaneConePlaneClosure Geo :=
    wylerLocalP3_and_SmithI5_implies_planeConePlaneClosure
      (Geo := Geo)
      hP3 hI5

  exact
    wylerLocalP3_and_planeClosure_implies_coneFlatness
      (Geo := Geo)
      hP3 hPlane

theorem wylerLocalP3_and_SmithI5_implies_onePointGenerationFormula
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo]
    (hP3 : WylerLocalP3AtPoint Geo)
    (hI5 : SmithI5Statement Geo) :
    WylerOnePointGenerationFormula Geo := by

  have hConeFlat :
      WylerPlaneConeFlatness Geo :=
    wylerLocalP3_and_SmithI5_implies_coneFlatness
      (Geo := Geo)
      hP3 hI5

  exact
    wylerPlaneConeFlatness_implies_onePointGenerationFormula
      (Geo := Geo)
      hConeFlat

end Geometry

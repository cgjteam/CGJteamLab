import CGJteamLab.HilbertDimensionFreeSmithCore

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Dimension-free Wyler / LP4 incidence

This module packages the dimension-free replacement for Hilbert I.7 in
the form used by Wyler and in modern locally-projective formulations.

Over `SmithIncidenceCore` we prove the exact equivalence:

    Smith I5
      <-> Wyler second-common-point form
      <-> Wyler I.7 / LP4 intersection-line form.

No exchange principle is used here.
-/

/--
Every line has an ambient point outside it.
-/
theorem smithCore_point_off_line
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (l : Geo.Line) :
    exists P : Geo.Point,
      Not (H.OnLine P l) := by

  rcases
      HilbertPlaneIncidence.three_noncollinear
        (Geo := Geo) with
    ⟨A, B, C, hABC⟩

  by_cases hAl : H.OnLine A l

  · by_cases hBl : H.OnLine B l

    · by_cases hCl : H.OnLine C l

      · exact False.elim (hABC ⟨l, hAl, hBl, hCl⟩)

      · exact ⟨C, hCl⟩

    · exact ⟨B, hBl⟩

  · exact ⟨A, hAl⟩


/--
Dimension-free line-plus-external-point plane theorem.
-/
theorem smithCore_plane_through_line_and_external_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (l : Geo.Line)
    (P : Geo.Point)
    (hPl : Not (H.OnLine P l)) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo l pi /\
      S.OnPlane P pi := by

  rcases
      C.two_points_on_each_line l with
    ⟨A, B, hAB, hAl, hBl⟩

  have hABP : Not (PrimCollinear Geo A B P) := by
    intro hCol
    exact
      hPl
        (smithCore_on_line_of_collinear_with_two
          (Geo := Geo)
          A B P hAB
          l hAl hBl hCol)

  rcases
      C.plane_through
        A B P hABP with
    ⟨pi, hApi, hBpi, hPpi⟩

  have hlpi : HilbertLineInPlane Geo l pi :=
    C.line_in_plane
      A B hAB
      l hAl hBl
      pi hApi hBpi

  exact ⟨pi, hlpi, hPpi⟩


/--
Any three points are coplanar, without Smith I5.
-/
theorem smithCore_three_points_coplanar
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (A B D : Geo.Point) :
    exists pi : S.Plane,
      S.OnPlane A pi /\
      S.OnPlane B pi /\
      S.OnPlane D pi := by

  by_cases hABD : PrimCollinear Geo A B D

  · rcases hABD with
      ⟨l, hAl, hBl, hDl⟩

    rcases
        smithCore_point_off_line
          (Geo := Geo) l with
      ⟨P, hPl⟩

    rcases
        smithCore_plane_through_line_and_external_point
          (Geo := Geo)
          l P hPl with
      ⟨pi, hlpi, _hPpi⟩

    exact
      ⟨pi,
       hlpi A hAl,
       hlpi B hBl,
       hlpi D hDl⟩

  · exact
      C.plane_through
        A B D hABD


/--
There is always a point distinct from a prescribed point.
-/
theorem smithCore_exists_point_ne
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (P : Geo.Point) :
    exists Q : Geo.Point,
      Ne Q P := by

  rcases
      HilbertPlaneIncidence.two_points_on_line
        (Geo := Geo) with
    ⟨l, A, B, hAB, _hAl, _hBl⟩

  by_cases hAP : A = P

  · have hBP : Ne B P := by
      intro hBP
      apply hAB
      exact hAP.trans hBP.symm

    exact ⟨B, hBP⟩

  · exact ⟨A, hAP⟩


/--
Point-level content of Wyler's dimension-free I.7.
-/
def WylerI7SecondCommonPoint
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall pi : S.Plane,
    forall a b : Geo.Line,
      Ne a b ->
      HilbertLineInPlane Geo a pi ->
      HilbertLineInPlane Geo b pi ->
      forall P : Geo.Point,
        Not (S.OnPlane P pi) ->
        forall alpha beta : S.Plane,
          HilbertLineInPlane Geo a alpha ->
          S.OnPlane P alpha ->
          HilbertLineInPlane Geo b beta ->
          S.OnPlane P beta ->
          exists Q : Geo.Point,
            Ne Q P /\
            S.OnPlane Q alpha /\
            S.OnPlane Q beta


/--
Three repetitions of one point are collinear.
-/
theorem primCollinear_refl3
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A : Geo.Point) :
    PrimCollinear Geo A A A := by

  rcases
      smithCore_exists_point_ne
        (Geo := Geo) A with
    ⟨B, hBA⟩

  have hAB : Ne A B :=
    Ne.symm hBA

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        A B hAB with
    ⟨l, hAl, _hBl⟩

  exact ⟨l, hAl, hAl, hAl⟩


/--
If the first two points coincide, the triple is collinear.
-/
theorem primCollinear_of_eq_first_second
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    (A B C : Geo.Point)
    (hAB : A = B) :
    PrimCollinear Geo A B C := by

  subst B

  by_cases hAC : A = C

  · subst C
    exact
      primCollinear_refl3
        (Geo := Geo) A

  · rcases
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          A C hAC with
      ⟨l, hAl, hCl⟩

    exact ⟨l, hAl, hAl, hCl⟩


/--
Every primitive plane contains a point different from any prescribed point.
-/
theorem smithCore_plane_has_point_ne
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (pi : S.Plane)
    (P : Geo.Point) :
    exists Q : Geo.Point,
      Ne Q P /\
      S.OnPlane Q pi := by

  rcases
      C.three_noncollinear_on_plane pi with
    ⟨A, B, D, hApi, hBpi, _hDpi, hABD⟩

  by_cases hAP : A = P

  · have hBP : Ne B P := by
      intro hBP

      have hAB : A = B :=
        hAP.trans hBP.symm

      exact
        hABD
          (primCollinear_of_eq_first_second
            (Geo := Geo)
            A B D hAB)

    exact ⟨B, hBP, hBpi⟩

  · exact ⟨A, hAP, hApi⟩


/--
If A,B lie on a line contained in pi and P is outside pi, then A,B,P are
noncollinear.
-/
theorem external_point_noncollinear_with_line_pair
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (pi : S.Plane)
    (l : Geo.Line)
    (A B P : Geo.Point)
    (hAB : Ne A B)
    (hAl : H.OnLine A l)
    (hBl : H.OnLine B l)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hPpi : Not (S.OnPlane P pi)) :
    Not (PrimCollinear Geo A B P) := by

  intro hCol

  have hPl : H.OnLine P l :=
    smithCore_on_line_of_collinear_with_two
      (Geo := Geo)
      A B P hAB
      l hAl hBl hCol

  exact hPpi (hlpi P hPl)


/--
Smith I5 implies Wyler's dimension-free I.7 second-common-point form.
-/
theorem smithI5_implies_wylerI7SecondCommonPoint
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hSmith : SmithI5Statement Geo) :
    WylerI7SecondCommonPoint Geo := by

  intro pi a b _hab hapi hbpi P hPpi alpha beta haalpha hPalpha hbbeta hPbeta

  rcases
      C.two_points_on_each_line a with
    ⟨A, B, hAB, hAa, hBa⟩

  rcases
      C.two_points_on_each_line b with
    ⟨D, E, hDE, hDb, hEb⟩

  have hBase :
      HilbertCoplanar4 Geo A D B E :=
    ⟨pi,
     hapi A hAa,
     hbpi D hDb,
     hapi B hBa,
     hbpi E hEb⟩

  rcases
      hSmith
        A D B E
        hBase
        P with
    ⟨Q, hQP, hFirst, hSecond⟩

  rcases hFirst with
    ⟨rho, hPrho, hArho, hBrho, hQrho⟩

  rcases hSecond with
    ⟨sigma, hPsigma, hDsigma, hEsigma, hQsigma⟩

  have hABP :
      Not (PrimCollinear Geo A B P) :=
    external_point_noncollinear_with_line_pair
      (Geo := Geo)
      pi a A B P
      hAB hAa hBa hapi hPpi

  have hDEP :
      Not (PrimCollinear Geo D E P) :=
    external_point_noncollinear_with_line_pair
      (Geo := Geo)
      pi b D E P
      hDE hDb hEb hbpi hPpi

  have hrhoAlpha : rho = alpha :=
    C.plane_unique
      A B P hABP
      rho alpha
      hArho hBrho hPrho
      (haalpha A hAa)
      (haalpha B hBa)
      hPalpha

  have hsigmaBeta : sigma = beta :=
    C.plane_unique
      D E P hDEP
      sigma beta
      hDsigma hEsigma hPsigma
      (hbbeta D hDb)
      (hbbeta E hEb)
      hPbeta

  rw [hrhoAlpha] at hQrho
  rw [hsigmaBeta] at hQsigma

  exact ⟨Q, hQP, hQrho, hQsigma⟩


/--
Wyler's I.7 second-common-point form implies Smith I5.
-/
theorem wylerI7SecondCommonPoint_implies_smithI5
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hWyler : WylerI7SecondCommonPoint Geo) :
    SmithI5Statement Geo := by

  intro p0 p1 q0 q1 hBase P

  rcases hBase with
    ⟨pi, hp0pi, hp1pi, hq0pi, hq1pi⟩

  by_cases hPpi : S.OnPlane P pi

  · rcases
        smithCore_plane_has_point_ne
          (Geo := Geo)
          pi P with
      ⟨Q, hQP, hQpi⟩

    exact
      ⟨Q, hQP,
       ⟨pi, hPpi, hp0pi, hq0pi, hQpi⟩,
       ⟨pi, hPpi, hp1pi, hq1pi, hQpi⟩⟩

  · have hp0P : Ne p0 P := by
      intro h
      apply hPpi
      rw [← h]
      exact hp0pi

    have hp1P : Ne p1 P := by
      intro h
      apply hPpi
      rw [← h]
      exact hp1pi

    by_cases hp0q0 : p0 = q0

    · subst q0

      rcases
          smithCore_three_points_coplanar
            (Geo := Geo)
            P p0 p1 with
        ⟨alpha, hPalpha, hp0alpha, hp1alpha⟩

      rcases
          smithCore_three_points_coplanar
            (Geo := Geo)
            P p1 q1 with
        ⟨beta, hPbeta, hp1beta, hq1beta⟩

      exact
        ⟨p1, hp1P,
         ⟨alpha,
          hPalpha, hp0alpha, hp0alpha, hp1alpha⟩,
         ⟨beta,
          hPbeta, hp1beta, hq1beta, hp1beta⟩⟩

    · by_cases hp1q1 : p1 = q1

      · subst q1

        rcases
            smithCore_three_points_coplanar
              (Geo := Geo)
              P p0 q0 with
          ⟨alpha, hPalpha, hp0alpha, hq0alpha⟩

        rcases
            smithCore_three_points_coplanar
              (Geo := Geo)
              P p1 p0 with
          ⟨beta, hPbeta, hp1beta, hp0beta⟩

        exact
          ⟨p0, hp0P,
           ⟨alpha,
            hPalpha, hp0alpha, hq0alpha, hp0alpha⟩,
           ⟨beta,
            hPbeta, hp1beta, hp1beta, hp0beta⟩⟩

      · rcases
            HilbertPlaneIncidence.line_through
              (Geo := Geo)
              p0 q0 hp0q0 with
          ⟨a, hp0a, hq0a⟩

        rcases
            HilbertPlaneIncidence.line_through
              (Geo := Geo)
              p1 q1 hp1q1 with
          ⟨b, hp1b, hq1b⟩

        have hapi : HilbertLineInPlane Geo a pi :=
          C.line_in_plane
            p0 q0 hp0q0
            a hp0a hq0a
            pi hp0pi hq0pi

        have hbpi : HilbertLineInPlane Geo b pi :=
          C.line_in_plane
            p1 q1 hp1q1
            b hp1b hq1b
            pi hp1pi hq1pi

        by_cases hab : a = b

        · subst b

          rcases
              smithCore_plane_through_line_and_external_point
                (Geo := Geo)
                a P
                (by
                  intro hPa
                  exact hPpi (hapi P hPa)) with
            ⟨alpha, haalpha, hPalpha⟩

          exact
            ⟨p0, hp0P,
             ⟨alpha,
              hPalpha,
              haalpha p0 hp0a,
              haalpha q0 hq0a,
              haalpha p0 hp0a⟩,
             ⟨alpha,
              hPalpha,
              haalpha p1 hp1b,
              haalpha q1 hq1b,
              haalpha p0 hp0a⟩⟩

        · rcases
              smithCore_plane_through_line_and_external_point
                (Geo := Geo)
                a P
                (by
                  intro hPa
                  exact hPpi (hapi P hPa)) with
            ⟨alpha, haalpha, hPalpha⟩

          rcases
              smithCore_plane_through_line_and_external_point
                (Geo := Geo)
                b P
                (by
                  intro hPb
                  exact hPpi (hbpi P hPb)) with
            ⟨beta, hbbeta, hPbeta⟩

          rcases
              hWyler
                pi a b hab
                hapi hbpi
                P hPpi
                alpha beta
                haalpha hPalpha
                hbbeta hPbeta with
            ⟨Q, hQP, hQalpha, hQbeta⟩

          exact
            ⟨Q, hQP,
             ⟨alpha,
              hPalpha,
              haalpha p0 hp0a,
              haalpha q0 hq0a,
              hQalpha⟩,
             ⟨beta,
              hPbeta,
              hbbeta p1 hp1b,
              hbbeta q1 hq1b,
              hQbeta⟩⟩


/--
Exact equivalence of Smith I5 and Wyler's point-level I.7.
-/
theorem wylerI7SecondCommonPoint_iff_smithI5
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo] :
    WylerI7SecondCommonPoint Geo <->
      SmithI5Statement Geo := by

  constructor

  · exact
      wylerI7SecondCommonPoint_implies_smithI5
        (Geo := Geo)

  · exact
      smithI5_implies_wylerI7SecondCommonPoint
        (Geo := Geo)


/--
The exact intersection-line form of Wyler I.7 / LP4.
-/
def WylerI7IntersectionLine
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] : Prop :=
  forall pi : S.Plane,
    forall a b : Geo.Line,
      Ne a b ->
      HilbertLineInPlane Geo a pi ->
      HilbertLineInPlane Geo b pi ->
      forall P : Geo.Point,
        Not (S.OnPlane P pi) ->
        forall alpha beta : S.Plane,
          HilbertLineInPlane Geo a alpha ->
          S.OnPlane P alpha ->
          HilbertLineInPlane Geo b beta ->
          S.OnPlane P beta ->
          exists k : Geo.Line,
            H.OnLine P k /\
            HilbertLineInPlane Geo k alpha /\
            HilbertLineInPlane Geo k beta /\
            forall X : Geo.Point,
              (S.OnPlane X alpha /\ S.OnPlane X beta) <->
                H.OnLine X k


/--
For two distinct lines a,b, there is a point of b which is not on a.
-/
theorem point_on_second_line_off_first
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (a b : Geo.Line)
    (hab : Ne a b) :
    exists B : Geo.Point,
      H.OnLine B b /\
      Not (H.OnLine B a) := by

  rcases
      C.two_points_on_each_line b with
    ⟨B, D, hBD, hBb, hDb⟩

  by_cases hBa : H.OnLine B a

  · by_cases hDa : H.OnLine D a

    · have hba : b = a :=
        HilbertPlaneIncidence.line_unique
          B D hBD
          b a
          hBb hDb
          hBa hDa

      exact False.elim (hab hba.symm)

    · exact ⟨D, hDb, hDa⟩

  · exact ⟨B, hBb, hBa⟩


/--
Two distinct base lines and an external point produce distinct side planes.
-/
theorem wyler_side_planes_ne
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (pi : S.Plane)
    (a b : Geo.Line)
    (hab : Ne a b)
    (hapi : HilbertLineInPlane Geo a pi)
    (hbpi : HilbertLineInPlane Geo b pi)
    (P : Geo.Point)
    (hPpi : Not (S.OnPlane P pi))
    (alpha beta : S.Plane)
    (haalpha : HilbertLineInPlane Geo a alpha)
    (hPalpha : S.OnPlane P alpha)
    (hbbeta : HilbertLineInPlane Geo b beta)
    (_hPbeta : S.OnPlane P beta) :
    Ne alpha beta := by

  intro hAlphaBeta

  rcases
      C.two_points_on_each_line a with
    ⟨A, D, hAD, hAa, hDa⟩

  rcases
      point_on_second_line_off_first
        (Geo := Geo)
        a b hab with
    ⟨B, hBb, hBa⟩

  have hADB :
      Not (PrimCollinear Geo A D B) := by

    intro hCol

    have hBonA : H.OnLine B a :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        A D B hAD
        a hAa hDa
        hCol

    exact hBa hBonA

  have hApi : S.OnPlane A pi :=
    hapi A hAa

  have hDpi : S.OnPlane D pi :=
    hapi D hDa

  have hBpi : S.OnPlane B pi :=
    hbpi B hBb

  have hAalpha : S.OnPlane A alpha :=
    haalpha A hAa

  have hDalpha : S.OnPlane D alpha :=
    haalpha D hDa

  have hBalpha : S.OnPlane B alpha := by
    rw [hAlphaBeta]
    exact hbbeta B hBb

  have hPiAlpha : pi = alpha :=
    C.plane_unique
      A D B hADB
      pi alpha
      hApi hDpi hBpi
      hAalpha hDalpha hBalpha

  apply hPpi

  rw [hPiAlpha]

  exact hPalpha


/--
The point-level form implies the exact intersection-line form.
-/
theorem wylerI7SecondCommonPoint_implies_intersectionLine
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hWyler : WylerI7SecondCommonPoint Geo) :
    WylerI7IntersectionLine Geo := by

  intro pi a b hab hapi hbpi P hPpi alpha beta haalpha hPalpha hbbeta hPbeta

  have hAlphaBeta : Ne alpha beta :=
    wyler_side_planes_ne
      (Geo := Geo)
      pi a b hab
      hapi hbpi
      P hPpi
      alpha beta
      haalpha hPalpha
      hbbeta hPbeta

  rcases
      hWyler
        pi a b hab
        hapi hbpi
        P hPpi
        alpha beta
        haalpha hPalpha
        hbbeta hPbeta with
    ⟨Q, hQP, hQalpha, hQbeta⟩

  have hPQ : Ne P Q :=
    Ne.symm hQP

  rcases
      HilbertPlaneIncidence.line_through
        (Geo := Geo)
        P Q hPQ with
    ⟨k, hPk, hQk⟩

  have hkAlpha : HilbertLineInPlane Geo k alpha :=
    C.line_in_plane
      P Q hPQ
      k hPk hQk
      alpha hPalpha hQalpha

  have hkBeta : HilbertLineInPlane Geo k beta :=
    C.line_in_plane
      P Q hPQ
      k hPk hQk
      beta hPbeta hQbeta

  refine
    ⟨k, hPk, hkAlpha, hkBeta, ?_⟩

  intro X
  constructor

  · intro hX

    rcases hX with
      ⟨hXalpha, hXbeta⟩

    by_contra hXk

    have hPQX :
        Not (PrimCollinear Geo P Q X) := by

      intro hCol

      have hXonK : H.OnLine X k :=
        smithCore_on_line_of_collinear_with_two
          (Geo := Geo)
          P Q X hPQ
          k hPk hQk
          hCol

      exact hXk hXonK

    have hEq : alpha = beta :=
      C.plane_unique
        P Q X hPQX
        alpha beta
        hPalpha hQalpha hXalpha
        hPbeta hQbeta hXbeta

    exact hAlphaBeta hEq

  · intro hXk

    exact
      ⟨hkAlpha X hXk,
       hkBeta X hXk⟩


/--
The exact intersection-line form implies the point-level form.
-/
theorem wylerI7IntersectionLine_implies_secondCommonPoint
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (hWyler : WylerI7IntersectionLine Geo) :
    WylerI7SecondCommonPoint Geo := by

  intro pi a b hab hapi hbpi P hPpi alpha beta haalpha hPalpha hbbeta hPbeta

  rcases
      hWyler
        pi a b hab
        hapi hbpi
        P hPpi
        alpha beta
        haalpha hPalpha
        hbbeta hPbeta with
    ⟨k, hPk, _hkAlpha, _hkBeta, hInter⟩

  rcases
      C.two_points_on_each_line k with
    ⟨U, V, hUV, hUk, hVk⟩

  by_cases hUP : U = P

  · have hVP : Ne V P := by
      intro hVP
      apply hUV
      exact hUP.trans hVP.symm

    have hVBoth :
        S.OnPlane V alpha /\
        S.OnPlane V beta :=
      (hInter V).2 hVk

    exact
      ⟨V, hVP, hVBoth.1, hVBoth.2⟩

  · have hUBoth :
        S.OnPlane U alpha /\
        S.OnPlane U beta :=
      (hInter U).2 hUk

    exact
      ⟨U, hUP, hUBoth.1, hUBoth.2⟩


/--
The two Wyler I.7 formulations are exactly equivalent.
-/
theorem wylerI7IntersectionLine_iff_secondCommonPoint
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo] :
    WylerI7IntersectionLine Geo <->
      WylerI7SecondCommonPoint Geo := by

  constructor

  · exact
      wylerI7IntersectionLine_implies_secondCommonPoint
        (Geo := Geo)

  · exact
      wylerI7SecondCommonPoint_implies_intersectionLine
        (Geo := Geo)


/--
The exact Wyler I.7 / LP4 form is equivalent to Smith I5.
-/
theorem wylerI7IntersectionLine_iff_smithI5
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SmithIncidenceCore Geo] :
    WylerI7IntersectionLine Geo <->
      SmithI5Statement Geo := by

  rw [wylerI7IntersectionLine_iff_secondCommonPoint (Geo := Geo)]

  exact
    wylerI7SecondCommonPoint_iff_smithI5
      (Geo := Geo)

end Geometry

import CGJteamLab.HilbertWylerE4Compatibility
import CGJteamLab.HilbertDimensionFreeSmithExchange

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Local 3D incidence inside derived E4 hyperplanes

This file proves directly, for the derived closure-theoretic E4 hyperplane,
the two nontrivial local 3D facts needed by the historical E4 API:

* two distinct ambient planes contained in one E4 hyperplane and sharing
  a point have a second common point;
* every derived E4 hyperplane contains four ambiently noncoplanar points.

The first proof uses Wyler's one-point generation formula, derived from
Wyler I.7 through Smith I5.

No new axiom is introduced here.
-/

/--
A plane contains another point distinct from any prescribed point of it.
-/
theorem hilbertWyler_plane_other_point
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
    (pi : S.Plane)
    (P : Geo.Point)
    (_hPpi : S.OnPlane P pi) :
    exists R : Geo.Point,
      Ne R P /\
      S.OnPlane R pi := by

  rcases A.three_noncollinear_on_plane pi with
    ⟨U, V, W, hUpi, hVpi, hWpi, hUVW⟩

  have hUV : Ne U V := by
    intro hUV
    exact
      hUVW
        (primCollinear_of_eq_first_second
          (Geo := Geo)
          U V W
          hUV)

  by_cases hPU : P = U

  · refine ⟨V, ?_, hVpi⟩
    intro hVP
    apply hUV
    exact hPU.symm.trans hVP.symm

  · exact
      ⟨U,
       Ne.symm hPU,
       hUpi⟩


/--
Every ambient plane contains a point off any prescribed ambient line.
-/
theorem hilbertWyler_plane_point_off_line
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
    (pi : S.Plane)
    (l : Geo.Line) :
    exists Y : Geo.Point,
      S.OnPlane Y pi /\
      Not (H.OnLine Y l) := by

  rcases A.three_noncollinear_on_plane pi with
    ⟨U, V, W, hUpi, hVpi, hWpi, hUVW⟩

  by_cases hUl : H.OnLine U l

  · by_cases hVl : H.OnLine V l

    · by_cases hWl : H.OnLine W l

      · exact
          False.elim
            (hUVW
              ⟨l, hUl, hVl, hWl⟩)

      · exact ⟨W, hWpi, hWl⟩

    · exact ⟨V, hVpi, hVl⟩

  · exact ⟨U, hUpi, hUl⟩


/--
For two distinct ambient planes, the second plane contains a point outside
the first one.
-/
theorem hilbertWyler_distinct_planes_point_outside_first
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
    (pi tau : S.Plane)
    (hPiTau : Ne pi tau) :
    exists X : Geo.Point,
      S.OnPlane X tau /\
      Not (S.OnPlane X pi) := by

  rcases A.three_noncollinear_on_plane tau with
    ⟨U, V, W, hUtau, hVtau, hWtau, hUVW⟩

  by_cases hUpi : S.OnPlane U pi

  · by_cases hVpi : S.OnPlane V pi

    · by_cases hWpi : S.OnPlane W pi

      · have hPiEqTau : pi = tau :=
          A.plane_unique
            U V W hUVW
            pi tau
            hUpi hVpi hWpi
            hUtau hVtau hWtau

        exact False.elim (hPiTau hPiEqTau)

      · exact ⟨W, hWtau, hWpi⟩

    · exact ⟨V, hVtau, hVpi⟩

  · exact ⟨U, hUtau, hUpi⟩


/--
Three noncollinear points of a plane together with a point outside the
plane are noncoplanar.
-/
theorem hilbertWyler_plane_external_point_noncoplanar4
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
    (pi : S.Plane)
    (U V W X : Geo.Point)
    (hUpi : S.OnPlane U pi)
    (hVpi : S.OnPlane V pi)
    (hWpi : S.OnPlane W pi)
    (hUVW : Not (PrimCollinear Geo U V W))
    (hXout : Not (S.OnPlane X pi)) :
    Not (HilbertCoplanar4 Geo U V W X) := by

  intro hCop

  rcases hCop with
    ⟨rho, hUrho, hVrho, hWrho, hXrho⟩

  have hRhoPi : rho = pi :=
    A.plane_unique
      U V W hUVW
      rho pi
      hUrho hVrho hWrho
      hUpi hVpi hWpi

  rw [hRhoPi] at hXrho
  exact hXout hXrho


/--
If pi is contained in Sigma and X is another point of Sigma outside pi,
then pi together with X generates the whole derived E4 hyperplane Sigma.
-/
theorem hilbertWyler_e4_plane_adjoin_external_eq_hyperplane
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
    [D4 : E4Dimension Geo]
    (Sigma : E4Hyperplane Geo)
    (pi : S.Plane)
    (hPiSigma :
      forall Z : Geo.Point,
        S.OnPlane Z pi ->
        E4OnHyperplane Geo Z Sigma)
    (X : Geo.Point)
    (hXSigma : E4OnHyperplane Geo X Sigma)
    (hXout : Not (S.OnPlane X pi)) :
    SmithSpan Geo
        (SmithAdjoinPoint Geo
          (SmithPlaneCarrier Geo pi) X) =
      Sigma.carrier := by

  rcases A.three_noncollinear_on_plane pi with
    ⟨U, V, W, hUpi, hVpi, hWpi, hUVW⟩

  have hTripleSpan :
      SmithSpan Geo (SmithPointTriple Geo U V W) =
        SmithPlaneCarrier Geo pi :=
    @smithSpan_three_noncollinear_eq_plane
      Geo
      H
      HP
      S
      (hilbertDimensionFreeIncidence_of_hilbertWyler
        (Geo := Geo))
      U V W
      hUVW
      pi
      hUpi hVpi hWpi

  have hNormalize :
      SmithSpan Geo
          (SmithAdjoinPoint Geo
            (SmithPlaneCarrier Geo pi) X) =
        SmithSpan Geo
          (SmithAdjoinPoint Geo
            (SmithPointTriple Geo U V W) X) := by

    rw [<- hTripleSpan]

    exact
      e4_span_adjoin_span_eq_adjoin
        (Geo := Geo)
        (SmithPointTriple Geo U V W)
        X

  have hNoncoplanar :
      Not (HilbertCoplanar4 Geo U V W X) :=
    hilbertWyler_plane_external_point_noncoplanar4
      (Geo := Geo)
      pi
      U V W X
      hUpi hVpi hWpi
      hUVW
      hXout

  have hUSigma : E4OnHyperplane Geo U Sigma :=
    hPiSigma U hUpi

  have hVSigma : E4OnHyperplane Geo V Sigma :=
    hPiSigma V hVpi

  have hWSigma : E4OnHyperplane Geo W Sigma :=
    hPiSigma W hWpi

  have hCarrier :
      Sigma.carrier =
        SmithSpan Geo
          (SmithAdjoinPoint Geo
            (SmithPointTriple Geo U V W) X) :=
    hilbertWyler_e4_hyperplane_carrier_eq_quad_span
      (Geo := Geo)
      U V W X
      hNoncoplanar
      Sigma
      hUSigma hVSigma hWSigma hXSigma

  exact hNormalize.trans hCarrier.symm


/--
Direct local Hilbert-I.7 conclusion inside a derived E4 hyperplane.

Two distinct ambient planes contained in Sigma, if they share P, share a
second point R != P.
-/
theorem hilbertWyler_e4_plane_second_common_point_in_hyperplane
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
    [D4 : E4Dimension Geo]
    (Sigma : E4Hyperplane Geo)
    (pi tau : S.Plane)
    (hPiSigma :
      forall Z : Geo.Point,
        S.OnPlane Z pi ->
        E4OnHyperplane Geo Z Sigma)
    (hTauSigma :
      forall Z : Geo.Point,
        S.OnPlane Z tau ->
        E4OnHyperplane Geo Z Sigma)
    (hPiTau : Ne pi tau)
    (P : Geo.Point)
    (hPpi : S.OnPlane P pi)
    (hPtau : S.OnPlane P tau) :
    exists R : Geo.Point,
      Ne R P /\
      S.OnPlane R pi /\
      S.OnPlane R tau := by

  rcases
      hilbertWyler_distinct_planes_point_outside_first
        (Geo := Geo)
        pi tau hPiTau with
    ⟨X, hXtau, hXout⟩

  have hPX : Ne P X := by
    intro hPX
    subst X
    exact hXout hPpi

  rcases
      HP.line_through
        P X hPX with
    ⟨k, hPk, hXk⟩

  rcases
      hilbertWyler_plane_point_off_line
        (Geo := Geo)
        tau k with
    ⟨Y, hYtau, hYk⟩

  have hPXY :
      Not (PrimCollinear Geo P X Y) := by
    intro hCol

    have hYOnK :
        H.OnLine Y k :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        P X Y
        hPX
        k
        hPk hXk
        hCol

    exact hYk hYOnK

  have hXSigma :
      E4OnHyperplane Geo X Sigma :=
    hTauSigma X hXtau

  have hYSigma :
      E4OnHyperplane Geo Y Sigma :=
    hTauSigma Y hYtau

  have hSpanSigma :
      SmithSpan Geo
          (SmithAdjoinPoint Geo
            (SmithPlaneCarrier Geo pi) X) =
        Sigma.carrier :=
    hilbertWyler_e4_plane_adjoin_external_eq_hyperplane
      (Geo := Geo)
      Sigma
      pi
      hPiSigma
      X
      hXSigma
      hXout

  have hYSpan :
      SmithSpan Geo
        (SmithAdjoinPoint Geo
          (SmithPlaneCarrier Geo pi) X) Y := by

    rw [hSpanSigma]

    exact hYSigma

  rcases
      hilbertWyler_plane_other_point
        (Geo := Geo)
        pi P hPpi with
    ⟨R0, hR0P, hR0pi⟩

  have hOnePoint :
      WylerOnePointGenerationFormula Geo :=
    @smithI5_implies_wylerOnePointGenerationFormula
      Geo
      H
      HP
      S
      (hilbertWyler_smithIncidenceCore
        (Geo := Geo))
      (hilbertWyler_implies_smithI5
        (Geo := Geo))

  have hPlaneFlat :
      SmithFlat Geo (SmithPlaneCarrier Geo pi) :=
    @smithPlaneCarrier_flat
      Geo
      H
      HP
      S
      (hilbertDimensionFreeIncidence_of_hilbertWyler
        (Geo := Geo))
      pi

  have hFormula :
      SmithSpan Geo
          (SmithAdjoinPoint Geo
            (SmithPlaneCarrier Geo pi) X) =
        WylerPlaneCone Geo
          (SmithPlaneCarrier Geo pi)
          P X :=
    hOnePoint
      (SmithPlaneCarrier Geo pi)
      hPlaneFlat
      P R0
      hPpi hR0pi
      hR0P.symm
      X
      hXout

  rw [hFormula] at hYSpan

  rcases hYSpan with
    ⟨l, alpha,
     hPl,
     hlPi,
     hlAlpha,
     hXalpha,
     hYalpha⟩

  have hPalpha : S.OnPlane P alpha :=
    hlAlpha P hPl

  have hAlphaTau : alpha = tau :=
    A.plane_unique
      P X Y hPXY
      alpha tau
      hPalpha hXalpha hYalpha
      hPtau hXtau hYtau

  rcases A.two_points_on_each_line l with
    ⟨U, V, hUV, hUl, hVl⟩

  by_cases hPU : P = U

  · have hVP : Ne V P := by
      intro hVP
      apply hUV
      exact hPU.symm.trans hVP.symm

    have hVpi : S.OnPlane V pi :=
      hlPi V hVl

    have hValpha : S.OnPlane V alpha :=
      hlAlpha V hVl

    have hVtau : S.OnPlane V tau := by
      rw [<- hAlphaTau]
      exact hValpha

    exact
      ⟨V, hVP, hVpi, hVtau⟩

  · have hUP : Ne U P :=
      Ne.symm hPU

    have hUpi : S.OnPlane U pi :=
      hlPi U hUl

    have hUalpha : S.OnPlane U alpha :=
      hlAlpha U hUl

    have hUtau : S.OnPlane U tau := by
      rw [<- hAlphaTau]
      exact hUalpha

    exact
      ⟨U, hUP, hUpi, hUtau⟩


/--
Every derived E4 hyperplane contains four ambiently noncoplanar points.
-/
theorem hilbertWyler_e4_four_noncoplanar_on_hyperplane
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
    (Sigma : E4Hyperplane Geo) :
    exists A0 B C D : Geo.Point,
      E4OnHyperplane Geo A0 Sigma /\
      E4OnHyperplane Geo B Sigma /\
      E4OnHyperplane Geo C Sigma /\
      E4OnHyperplane Geo D Sigma /\
      Not (HilbertCoplanar4 Geo A0 B C D) := by

  rcases Sigma.generated3Flat with
    ⟨A0, B, C, D,
     hABC,
     hDout,
     hCarrier⟩

  have hNoncoplanar :
      Not (HilbertCoplanar4 Geo A0 B C D) := by

    intro hCop

    rcases hCop with
      ⟨pi, hApi, hBpi, hCpi, hDpi⟩

    have hTripleSpan :
        SmithSpan Geo (SmithPointTriple Geo A0 B C) =
          SmithPlaneCarrier Geo pi :=
      @smithSpan_three_noncollinear_eq_plane
        Geo
        H
        HP
        S
        (hilbertDimensionFreeIncidence_of_hilbertWyler
          (Geo := Geo))
        A0 B C
        hABC
        pi
        hApi hBpi hCpi

    apply hDout

    rw [hTripleSpan]

    exact hDpi

  have hAon :
      E4OnHyperplane Geo A0 Sigma := by
    dsimp [E4OnHyperplane]
    rw [hCarrier]

    apply
      smithSpan_extensive
        (Geo := Geo)
        (SmithAdjoinPoint Geo
          (SmithPointTriple Geo A0 B C) D)

    exact Or.inr (Or.inl rfl)

  have hBon :
      E4OnHyperplane Geo B Sigma := by
    dsimp [E4OnHyperplane]
    rw [hCarrier]

    apply
      smithSpan_extensive
        (Geo := Geo)
        (SmithAdjoinPoint Geo
          (SmithPointTriple Geo A0 B C) D)

    exact Or.inr (Or.inr (Or.inl rfl))

  have hCon :
      E4OnHyperplane Geo C Sigma := by
    dsimp [E4OnHyperplane]
    rw [hCarrier]

    apply
      smithSpan_extensive
        (Geo := Geo)
        (SmithAdjoinPoint Geo
          (SmithPointTriple Geo A0 B C) D)

    exact Or.inr (Or.inr (Or.inr rfl))

  have hDon :
      E4OnHyperplane Geo D Sigma := by
    dsimp [E4OnHyperplane]
    rw [hCarrier]

    apply
      smithSpan_extensive
        (Geo := Geo)
        (SmithAdjoinPoint Geo
          (SmithPointTriple Geo A0 B C) D)

    exact Or.inl rfl

  exact
    ⟨A0, B, C, D,
     hAon, hBon, hCon, hDon,
     hNoncoplanar⟩

end Geometry

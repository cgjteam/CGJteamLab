import CGJteamLab.SalasE4Local3D
import CGJteamLab.SalasE4PlaneIncidence
import CGJteamLab.Coxeter.E4NormalCore

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Plane-hyperplane incidence from Salas + dimension four

The historical E4 development isolated

    Hilbert4DPlaneHyperplaneIncidence

as a temporary incidence boundary.  It is not needed as a new axiom.

In dimension four, if an ambient 2-plane and a derived 3-hyperplane
share a point, then they share a second distinct point.

The proof uses only:

* Sancho de Salas LP1-LP4;
* the dimension-four assumption;
* the Smith/Wyler one-point generation theorem already derived from LP4.

No new axiom is introduced here.
-/

/--
A derived E4 hyperplane contains two distinct points, one of which may be
chosen different from any prescribed point.
-/
theorem salas_e4_hyperplane_other_point
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point) :
    exists R : Geo.Point,
      Ne R P /\
      E4OnHyperplane Geo R Sigma := by

  rcases
      salas_e4_four_noncoplanar_on_hyperplane
        (Geo := Geo)
        Sigma with
    ⟨A, B, C, D,
     hASigma, hBSigma, _hCSigma, _hDSigma,
     hNoncoplanar⟩

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    salas_noncoplanar4_first_three_noncollinear
      (Geo := Geo)
      A B C D
      hNoncoplanar

  have hAB : Ne A B :=
    e4_noncollinear_first_ne_second
      (Geo := Geo)
      A B C
      hABC

  by_cases hPA : P = A

  · refine ⟨B, ?_, hBSigma⟩
    intro hBP
    apply hAB
    exact hPA.symm.trans hBP.symm

  · exact
      ⟨A,
       Ne.symm hPA,
       hASigma⟩


/--
A 2-plane and a derived E4 hyperplane sharing a point share a second
distinct point.
-/
theorem salas_e4_plane_hyperplane_second_common_point
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : SalasIncidence Geo]
    [D4 : E4Dimension Geo]
    (pi : S.Plane)
    (Sigma : E4Hyperplane Geo)
    (P : Geo.Point)
    (hPpi : S.OnPlane P pi)
    (hPSigma : E4OnHyperplane Geo P Sigma) :
    exists R : Geo.Point,
      Ne R P /\
      S.OnPlane R pi /\
      E4OnHyperplane Geo R Sigma := by

  by_cases hPiSigma :
      forall Z : Geo.Point,
        S.OnPlane Z pi ->
        E4OnHyperplane Geo Z Sigma

  · rcases
        salas_plane_other_point
          (Geo := Geo)
          pi P hPpi with
      ⟨R, hRP, hRpi⟩

    exact
      ⟨R,
       hRP,
       hRpi,
       hPiSigma R hRpi⟩

  · push Not at hPiSigma

    rcases hPiSigma with
      ⟨X, hXpi, hXoutSigma⟩

    have hPX : Ne P X := by
      intro hPX
      subst X
      exact hXoutSigma hPSigma

    rcases
        HP.line_through
          P X hPX with
      ⟨k, hPk, hXk⟩

    rcases
        salas_plane_point_off_line
          (Geo := Geo)
          pi k with
      ⟨Y, hYpi, hYk⟩

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

    have hAmbientSpan :
        SmithSpan Geo
            (SmithAdjoinPoint Geo Sigma.carrier X) =
          (Set.univ : Set Geo.Point) :=
      e4Hyperplane_adjoin_external_span_eq_univ
        (Geo := Geo)
        Sigma X
        hXoutSigma

    have hYSpan :
        SmithSpan Geo
          (SmithAdjoinPoint Geo Sigma.carrier X) Y := by
      rw [hAmbientSpan]
      trivial

    rcases
        salas_e4_hyperplane_other_point
          (Geo := Geo)
          Sigma P with
      ⟨R0, hR0P, hR0Sigma⟩

    have hOnePoint :
        WylerOnePointGenerationFormula Geo :=
      @smithI5_implies_wylerOnePointGenerationFormula
        Geo
        H
        HP
        S
        (salas_to_smithIncidenceCore
          (Geo := Geo))
        (salas_implies_smithI5
          (Geo := Geo))

    have hFormula :
        SmithSpan Geo
            (SmithAdjoinPoint Geo Sigma.carrier X) =
          WylerPlaneCone Geo Sigma.carrier P X :=
      hOnePoint
        Sigma.carrier
        (e4Hyperplane_flat
          (Geo := Geo)
          Sigma)
        P R0
        hPSigma
        hR0Sigma
        hR0P.symm
        X
        hXoutSigma

    rw [hFormula] at hYSpan

    rcases hYSpan with
      ⟨l, alpha,
       hPl,
       hlSigma,
       hlAlpha,
       hXalpha,
       hYalpha⟩

    have hPalpha :
        S.OnPlane P alpha :=
      hlAlpha P hPl

    rcases
        A.plane_through_unique
          P X Y hPXY with
      ⟨rho,
       _hPrho, _hXrho, _hYrho,
       hUnique⟩

    have hAlphaRho : alpha = rho :=
      hUnique
        alpha
        hPalpha
        hXalpha
        hYalpha

    have hPiRho : pi = rho :=
      hUnique
        pi
        hPpi
        hXpi
        hYpi

    have hAlphaPi : alpha = pi :=
      hAlphaRho.trans hPiRho.symm

    rcases A.two_points_on_each_line l with
      ⟨U, V, hUV, hUl, hVl⟩

    by_cases hPU : P = U

    · have hVP : Ne V P := by
        intro hVP
        apply hUV
        exact hPU.symm.trans hVP.symm

      have hVpi : S.OnPlane V pi := by
        rw [<- hAlphaPi]
        exact hlAlpha V hVl

      have hVSigma :
          E4OnHyperplane Geo V Sigma :=
        hlSigma V hVl

      exact
        ⟨V,
         hVP,
         hVpi,
         hVSigma⟩

    · have hUP : Ne U P :=
        Ne.symm hPU

      have hUpi : S.OnPlane U pi := by
        rw [<- hAlphaPi]
        exact hlAlpha U hUl

      have hUSigma :
          E4OnHyperplane Geo U Sigma :=
        hlSigma U hUl

      exact
        ⟨U,
         hUP,
         hUpi,
         hUSigma⟩


/-!
## Compatibility with the historical E4 API
-/

@[instance_reducible]
local instance salasE4Primitive_planeHyperplane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo] :
    Hilbert4DPrimitive Geo :=
  salasE4Primitive (Geo := Geo)


local instance salasE4PlaneIncidence_planeHyperplane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertPlaneIncidence Geo :=
  salas_e4_implies_hilbertPlaneIncidence
    (Geo := Geo)


local instance salasDimensionFree_planeHyperplane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    HilbertDimensionFreeIncidence Geo :=
  salas_implies_dimensionFreeIncidence
    (Geo := Geo)


local instance salasOldHyperplaneCore_planeHyperplane
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DHyperplaneIncidenceCore Geo :=
  salas_e4_implies_oldHyperplaneIncidenceCore
    (Geo := Geo)


/--
The historical temporary class `Hilbert4DPlaneHyperplaneIncidence` is a
theorem of the new incidence foundation.
-/
theorem salas_e4_implies_oldPlaneHyperplaneIncidence
    [H : HilbertIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    [E4Dimension Geo] :
    Hilbert4DPlaneHyperplaneIncidence Geo where

  plane_hyperplane_second_common_point := by
    intro pi Sigma P hPpi hPSigma

    exact
      salas_e4_plane_hyperplane_second_common_point
        (Geo := Geo)
        pi Sigma P
        hPpi hPSigma

end Geometry

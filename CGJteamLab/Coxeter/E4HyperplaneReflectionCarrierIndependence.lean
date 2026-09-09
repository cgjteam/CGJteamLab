import CGJteamLab.Coxeter.E4HyperplaneReflectionPlaneTransport
import CGJteamLab.Coxeter.E4HyperplaneReflectionCarrierCandidate

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 reflection carrier: independence of the chosen point

Let Sigma and Tau contain the same plane Delta, and let X be a point of
Tau outside Delta.  The first carrier candidate was defined as

    span(Delta, r_Sigma(X)).

This file proves that this hyperplane contains the reflected image of
every point of Tau.  Consequently the carrier does not depend on the
chosen external point X.

The proof is synthetic.

For Y in Tau:

* if Y is in Delta, it is fixed because Delta is contained in Sigma;
* otherwise, choose the plane rho through XY and a suitable point
  A of Delta outside XY;
* rho and Delta are distinct planes inside Tau sharing A;
* local Hilbert I.7 supplies a second common point R;
* hence A,R lie in rho cap Delta and A,R,X are noncollinear;
* exact plane transport sends rho to rho';
* r(A), r(R) lie in Delta and r(X) lies in the candidate hyperplane;
* therefore rho' lies in the candidate hyperplane;
* hence r(Y) lies there.

No coordinates or vector geometry are used.
-/

/--
A plane contained in the reflecting hyperplane is fixed pointwise.
-/
theorem hyperplaneReflect4_corrected_fixed_on_contained_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma :
      HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (P : Geo.Point)
    (hPDelta :
      Q.toHilbertSpacePrimitive.OnPlane P Delta) :
    hyperplaneReflect4_corrected Geo Sigma P = P := by

  exact
    hyperplaneReflect4_corrected_of_on_hyperplane
      (Geo := Geo)
      Sigma P
      (hDeltaSigma P hPDelta)


/--
Among three noncollinear points of Delta, at least one is outside a
prescribed ambient line.
-/
theorem hilbert_dimension_free_plane_point_off_line_from_marked_triple
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    (Delta : S.Plane)
    (k : Geo.Line) :
    exists A : Geo.Point,
      S.OnPlane A Delta /\
      Not (H.OnLine A k) := by

  have hABCExists :=
    D.three_noncollinear_on_plane Delta

  let A : Geo.Point :=
    Classical.choose hABCExists

  have hBCExists :=
    Classical.choose_spec hABCExists

  let B : Geo.Point :=
    Classical.choose hBCExists

  have hCExists :=
    Classical.choose_spec hBCExists

  let C : Geo.Point :=
    Classical.choose hCExists

  have hData :=
    Classical.choose_spec hCExists

  have hADelta :
      S.OnPlane A Delta :=
    hData.1

  have hBDelta :
      S.OnPlane B Delta :=
    hData.2.1

  have hCDelta :
      S.OnPlane C Delta :=
    hData.2.2.1

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hData.2.2.2

  by_cases hAk :
      H.OnLine A k

  case neg =>
    exact
      Exists.intro A
        (And.intro hADelta hAk)

  case pos =>
    by_cases hBk :
        H.OnLine B k

    case neg =>
      exact
        Exists.intro B
          (And.intro hBDelta hBk)

    case pos =>
      by_cases hCk :
          H.OnLine C k

      case neg =>
        exact
          Exists.intro C
            (And.intro hCDelta hCk)

      case pos =>
        exact
          False.elim
            (hABC
              (Exists.intro k
                (And.intro hAk
                  (And.intro hBk hCk))))


/--
If A and R are distinct points of Delta and X is outside Delta, then
A,R,X are noncollinear.
-/
theorem hilbert_dimension_free_noncollinear_of_two_plane_points_and_external
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    (Delta : S.Plane)
    (A R X : Geo.Point)
    (hAR : Ne A R)
    (hADelta : S.OnPlane A Delta)
    (hRDelta : S.OnPlane R Delta)
    (hXoff : Not (S.OnPlane X Delta)) :
    Not (PrimCollinear Geo A R X) := by

  intro hCol

  have hLineExists :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo)
      A R hAR

  let k : Geo.Line :=
    Classical.choose hLineExists

  have hkData :=
    Classical.choose_spec hLineExists

  have hAk :
      H.OnLine A k :=
    hkData.1

  have hRk :
      H.OnLine R k :=
    hkData.2

  have hXk :
      H.OnLine X k :=
    hilbert_on_line_of_primCollinear_with_two_on_line
      (Geo := Geo)
      hAR
      hAk hRk
      hCol

  have hkDelta :
      HilbertLineInPlane Geo k Delta :=
    D.line_in_plane
      A R hAR
      k hAk hRk
      Delta hADelta hRDelta

  exact
    hXoff
      (hkDelta X hXk)


/--
Main containment theorem.

If Lambda contains Delta and the reflected image of one external point
X of Tau, then Lambda contains the reflected image of every point of
Tau.
-/
theorem hyperplaneReflect4_corrected_image_point_mem_of_span
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau Lambda : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma :
      HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau)
    (hDeltaLambda :
      HilbertPlaneInHyperplane4 Geo Delta Lambda)
    (X : Geo.Point)
    (hXTau :
      Q.OnHyperplane X Tau)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta))
    (hXPrimeLambda :
      Q.OnHyperplane
        (hyperplaneReflect4_corrected Geo Sigma X)
        Lambda)
    (Y : Geo.Point)
    (hYTau :
      Q.OnHyperplane Y Tau) :
    Q.OnHyperplane
      (hyperplaneReflect4_corrected Geo Sigma Y)
      Lambda := by

  by_cases hYDelta :
      Q.toHilbertSpacePrimitive.OnPlane Y Delta

  case pos =>
    have hFixY :
        hyperplaneReflect4_corrected Geo Sigma Y = Y :=
      hyperplaneReflect4_corrected_fixed_on_contained_plane
        (Geo := Geo)
        Sigma Delta hDeltaSigma
        Y hYDelta

    rw [hFixY]

    exact
      hDeltaLambda Y hYDelta

  case neg =>
    by_cases hYX :
        Y = X

    case pos =>
      subst Y
      exact hXPrimeLambda

    case neg =>
      have hXY :
          Ne X Y := by
        intro hEq
        exact hYX hEq.symm

      have hkExists :=
        HilbertPlaneIncidence.line_through
          (Geo := Geo)
          X Y hXY

      let k : Geo.Line :=
        Classical.choose hkExists

      have hkData :=
        Classical.choose_spec hkExists

      have hXk :
          H.OnLine X k :=
        hkData.1

      have hYk :
          H.OnLine Y k :=
        hkData.2

      have hAExists :=
        hilbert_dimension_free_plane_point_off_line_from_marked_triple
          (Geo := Geo)
          Delta k

      let A : Geo.Point :=
        Classical.choose hAExists

      have hAData :=
        Classical.choose_spec hAExists

      have hADelta :
          Q.toHilbertSpacePrimitive.OnPlane A Delta :=
        hAData.1

      have hAk :
          Not (H.OnLine A k) :=
        hAData.2

      have hATau :
          Q.OnHyperplane A Tau :=
        hDeltaTau A hADelta

      let C : SmithIncidenceCore Geo :=
        smithIncidenceCore_of_dimensionFree
          (Geo := Geo)

      have hRhoExists :=
        smithCore_plane_through_line_and_external_point
          (Geo := Geo)
          (C := C)
          k A hAk

      let rho : Q.toHilbertSpacePrimitive.Plane :=
        Classical.choose hRhoExists

      have hRhoData :=
        Classical.choose_spec hRhoExists

      have hkRho :
          HilbertLineInPlane Geo k rho :=
        hRhoData.1

      have hARho :
          Q.toHilbertSpacePrimitive.OnPlane A rho :=
        hRhoData.2

      have hXRho :
          Q.toHilbertSpacePrimitive.OnPlane X rho :=
        hkRho X hXk

      have hYRho :
          Q.toHilbertSpacePrimitive.OnPlane Y rho :=
        hkRho Y hYk

      have hXYA :
          Not (PrimCollinear Geo X Y A) := by

        intro hCol

        have hAonK :
            H.OnLine A k :=
          hilbert_on_line_of_primCollinear_with_two_on_line
            (Geo := Geo)
            hXY
            hXk hYk
            hCol

        exact hAk hAonK

      have hRhoTau :
          HilbertPlaneInHyperplane4 Geo rho Tau :=
        H4L.plane_in_hyperplane
          X Y A
          hXYA
          rho
          hXRho hYRho hARho
          Tau
          hXTau hYTau hATau

      have hRhoDelta :
          Ne rho Delta := by

        intro hEq

        apply hXoff

        rw [<- hEq]

        exact hXRho

      have hSecondExists :=
        H4L.plane_second_common_point_in_hyperplane
          Tau
          rho Delta
          hRhoTau hDeltaTau
          hRhoDelta
          A
          hARho hADelta

      let R : Geo.Point :=
        Classical.choose hSecondExists

      have hRData :=
        Classical.choose_spec hSecondExists

      have hRA :
          Ne R A :=
        hRData.1

      have hRRho :
          Q.toHilbertSpacePrimitive.OnPlane R rho :=
        hRData.2.1

      have hRDelta :
          Q.toHilbertSpacePrimitive.OnPlane R Delta :=
        hRData.2.2

      have hAR :
          Ne A R :=
        hRA.symm

      have hARX :
          Not (PrimCollinear Geo A R X) :=
        hilbert_dimension_free_noncollinear_of_two_plane_points_and_external
          (Geo := Geo)
          Delta
          A R X
          hAR
          hADelta hRDelta
          hXoff

      let rhoPrime : Q.toHilbertSpacePrimitive.Plane :=
        hyperplaneReflectionPlaneCarrier4_corrected
          (Geo := Geo)
          Sigma rho

      have hMapRho :
          HyperplaneReflectionMapsPlane4_corrected
            Geo Sigma rho rhoPrime := by

        exact
          hyperplaneReflectionPlaneCarrier4_corrected_spec
            (Geo := Geo)
            Sigma rho

      have hAPrimeRho :
          Q.toHilbertSpacePrimitive.OnPlane
            (hyperplaneReflect4_corrected Geo Sigma A)
            rhoPrime :=
        (hMapRho A).mp hARho

      have hRPrimeRho :
          Q.toHilbertSpacePrimitive.OnPlane
            (hyperplaneReflect4_corrected Geo Sigma R)
            rhoPrime :=
        (hMapRho R).mp hRRho

      have hXPrimeRho :
          Q.toHilbertSpacePrimitive.OnPlane
            (hyperplaneReflect4_corrected Geo Sigma X)
            rhoPrime :=
        (hMapRho X).mp hXRho

      have hYPrimeRho :
          Q.toHilbertSpacePrimitive.OnPlane
            (hyperplaneReflect4_corrected Geo Sigma Y)
            rhoPrime :=
        (hMapRho Y).mp hYRho

      have hAPrimeLambda :
          Q.OnHyperplane
            (hyperplaneReflect4_corrected Geo Sigma A)
            Lambda := by

        have hFixA :
            hyperplaneReflect4_corrected Geo Sigma A = A :=
          hyperplaneReflect4_corrected_fixed_on_contained_plane
            (Geo := Geo)
            Sigma Delta hDeltaSigma
            A hADelta

        rw [hFixA]

        exact
          hDeltaLambda A hADelta

      have hRPrimeLambda :
          Q.OnHyperplane
            (hyperplaneReflect4_corrected Geo Sigma R)
            Lambda := by

        have hFixR :
            hyperplaneReflect4_corrected Geo Sigma R = R :=
          hyperplaneReflect4_corrected_fixed_on_contained_plane
            (Geo := Geo)
            Sigma Delta hDeltaSigma
            R hRDelta

        rw [hFixR]

        exact
          hDeltaLambda R hRDelta

      have hImageNoncol :
          Not
            (PrimCollinear
              Geo
              (hyperplaneReflect4_corrected Geo Sigma A)
              (hyperplaneReflect4_corrected Geo Sigma R)
              (hyperplaneReflect4_corrected Geo Sigma X)) :=
        hyperplaneReflect4_corrected_preserves_noncollinear
          (Geo := Geo)
          Sigma
          A R X
          hARX

      have hRhoPrimeLambda :
          HilbertPlaneInHyperplane4
            Geo rhoPrime Lambda :=
        H4L.plane_in_hyperplane
          (hyperplaneReflect4_corrected Geo Sigma A)
          (hyperplaneReflect4_corrected Geo Sigma R)
          (hyperplaneReflect4_corrected Geo Sigma X)
          hImageNoncol
          rhoPrime
          hAPrimeRho
          hRPrimeRho
          hXPrimeRho
          Lambda
          hAPrimeLambda
          hRPrimeLambda
          hXPrimeLambda

      exact
        hRhoPrimeLambda
          (hyperplaneReflect4_corrected Geo Sigma Y)
          hYPrimeRho


/--
The point-defined carrier contains the reflected image of every point
of Tau.
-/
theorem hyperplaneReflectionCarrierFromPoint4_corrected_contains
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma :
      HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau)
    (X : Geo.Point)
    (hXTau :
      Q.OnHyperplane X Tau)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta))
    (Y : Geo.Point)
    (hYTau :
      Q.OnHyperplane Y Tau) :
    Q.OnHyperplane
      (hyperplaneReflect4_corrected Geo Sigma Y)
      (hyperplaneReflectionCarrierFromPoint4_corrected
        (Geo := Geo)
        Sigma Delta hDeltaSigma
        X hXoff) := by

  have hSpec :=
    hyperplaneReflectionCarrierFromPoint4_corrected_spec
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      X hXoff

  exact
    hyperplaneReflect4_corrected_image_point_mem_of_span
      (Geo := Geo)
      Sigma Tau
      (hyperplaneReflectionCarrierFromPoint4_corrected
        (Geo := Geo)
        Sigma Delta hDeltaSigma
        X hXoff)
      Delta
      hDeltaSigma
      hDeltaTau
      hSpec.1
      X hXTau hXoff
      hSpec.2
      Y hYTau


/--
The point-defined carrier is independent of the chosen external point
of Tau.
-/
theorem hyperplaneReflectionCarrierFromPoint4_corrected_independent
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma :
      HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau)
    (X Y : Geo.Point)
    (hXTau :
      Q.OnHyperplane X Tau)
    (hYTau :
      Q.OnHyperplane Y Tau)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta))
    (hYoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane Y Delta)) :
    hyperplaneReflectionCarrierFromPoint4_corrected
        (Geo := Geo)
        Sigma Delta hDeltaSigma
        X hXoff =
      hyperplaneReflectionCarrierFromPoint4_corrected
        (Geo := Geo)
        Sigma Delta hDeltaSigma
        Y hYoff := by

  let LambdaX :=
    hyperplaneReflectionCarrierFromPoint4_corrected
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      X hXoff

  let LambdaY :=
    hyperplaneReflectionCarrierFromPoint4_corrected
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      Y hYoff

  have hSpecX :=
    hyperplaneReflectionCarrierFromPoint4_corrected_spec
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      X hXoff

  have hSpecY :=
    hyperplaneReflectionCarrierFromPoint4_corrected_spec
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      Y hYoff

  have hYPrimeOff :
      Not
        (Q.toHilbertSpacePrimitive.OnPlane
          (hyperplaneReflect4_corrected Geo Sigma Y)
          Delta) :=
    hyperplaneReflect4_corrected_preserves_off_fixed_plane
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      Y hYoff

  have hYPrimeLambdaX :
      Q.OnHyperplane
        (hyperplaneReflect4_corrected Geo Sigma Y)
        LambdaX :=
    hyperplaneReflectionCarrierFromPoint4_corrected_contains
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau
      X hXTau hXoff
      Y hYTau

  have hEq :
      LambdaX = LambdaY :=
    hilbert4D_hyperplane_unique_of_plane_and_external_point_corrected
      (Geo := Geo)
      Delta
      (hyperplaneReflect4_corrected Geo Sigma Y)
      hYPrimeOff
      LambdaX LambdaY
      hSpecX.1
      hYPrimeLambdaX
      hSpecY.1
      hSpecY.2

  exact hEq


/--
The canonical selected carrier contains the reflected image of every
point of Tau.
-/
theorem hyperplaneReflectionCarrier4_corrected_contains
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DAmbientEuclidean Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma :
      HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau)
    (Y : Geo.Point)
    (hYTau :
      Q.OnHyperplane Y Tau) :
    Q.OnHyperplane
      (hyperplaneReflect4_corrected Geo Sigma Y)
      (hyperplaneReflectionCarrier4_corrected
        (Geo := Geo)
        Sigma Tau Delta
        hDeltaSigma hDeltaTau) := by

  let X :=
    hilbert4DHyperplanePointOffPlane_corrected
      (Geo := Geo)
      Tau Delta hDeltaTau

  have hXData :=
    hilbert4DHyperplanePointOffPlane_corrected_spec
      (Geo := Geo)
      Tau Delta hDeltaTau

  exact
    hyperplaneReflectionCarrierFromPoint4_corrected_contains
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau
      X hXData.1 hXData.2
      Y hYTau

end Geometry

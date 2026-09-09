import CGJteamLab.Coxeter.E4Incidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 hyperplane carriers

This module isolates the basic incidence fact needed by the Coxeter
hyperplane-transport layer:

    a plane Delta and a point X outside Delta determine exactly one
    E4 hyperplane.

The proof is dimension-safe and purely incidence-theoretic.

* Smith I2 supplies three noncollinear points A,B,C on Delta.
* Since X is outside Delta, A,B,C,X are noncoplanar.
* The corrected E4 hyperplane core gives the hyperplane through those
  four points.
* Local hyperplane closure absorbs the whole plane Delta.
* The same four-point uniqueness proves uniqueness.

No order, congruence, perpendicularity, parallelism, reflection,
Euclidean axiom, or continuity is used.
-/

/--
If A,B,C are noncollinear points of Delta and X is outside Delta, then
A,B,C,X are not coplanar.
-/
theorem hilbert4D_noncoplanar_of_plane_external_point_dimensionFree
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (A B C X : Geo.Point)
    (hADelta :
      Q.toHilbertSpacePrimitive.OnPlane A Delta)
    (hBDelta :
      Q.toHilbertSpacePrimitive.OnPlane B Delta)
    (hCDelta :
      Q.toHilbertSpacePrimitive.OnPlane C Delta)
    (hABC :
      Not (PrimCollinear Geo A B C))
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta)) :
    Not (HilbertCoplanar4 Geo A B C X) := by

  intro hCop

  let pi : Q.toHilbertSpacePrimitive.Plane :=
    Classical.choose hCop

  have hPiData :=
    Classical.choose_spec hCop

  have hApi :
      Q.toHilbertSpacePrimitive.OnPlane A pi :=
    hPiData.1

  have hBpi :
      Q.toHilbertSpacePrimitive.OnPlane B pi :=
    hPiData.2.1

  have hCpi :
      Q.toHilbertSpacePrimitive.OnPlane C pi :=
    hPiData.2.2.1

  have hXpi :
      Q.toHilbertSpacePrimitive.OnPlane X pi :=
    hPiData.2.2.2

  have hPiDelta :
      pi = Delta :=
    D.plane_unique
      A B C
      hABC
      pi Delta
      hApi hBpi hCpi
      hADelta hBDelta hCDelta

  apply hXoff

  simpa [hPiDelta] using hXpi


/--
A plane Delta and a point X outside Delta lie in a common corrected E4
hyperplane.
-/
theorem hilbert4D_hyperplane_through_plane_and_external_point_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (X : Geo.Point)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta)) :
    exists Lambda : Q.Hyperplane,
      HilbertPlaneInHyperplane4 Geo Delta Lambda /\
      Q.OnHyperplane X Lambda := by

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

  have hABCData :=
    Classical.choose_spec hCExists

  have hADelta :
      Q.toHilbertSpacePrimitive.OnPlane A Delta :=
    hABCData.1

  have hBDelta :
      Q.toHilbertSpacePrimitive.OnPlane B Delta :=
    hABCData.2.1

  have hCDelta :
      Q.toHilbertSpacePrimitive.OnPlane C Delta :=
    hABCData.2.2.1

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hABCData.2.2.2

  have hABCX :
      Not (HilbertCoplanar4 Geo A B C X) :=
    hilbert4D_noncoplanar_of_plane_external_point_dimensionFree
      (Geo := Geo)
      Delta
      A B C X
      hADelta hBDelta hCDelta
      hABC hXoff

  have hLambdaExists :=
    C4.hyperplane_through
      A B C X
      hABCX

  let Lambda : Q.Hyperplane :=
    Classical.choose hLambdaExists

  have hLambdaData :=
    Classical.choose_spec hLambdaExists

  have hALambda :
      Q.OnHyperplane A Lambda :=
    hLambdaData.1

  have hBLambda :
      Q.OnHyperplane B Lambda :=
    hLambdaData.2.1

  have hCLambda :
      Q.OnHyperplane C Lambda :=
    hLambdaData.2.2.1

  have hXLambda :
      Q.OnHyperplane X Lambda :=
    hLambdaData.2.2.2

  have hDeltaLambda :
      HilbertPlaneInHyperplane4 Geo Delta Lambda :=
    H4L.plane_in_hyperplane
      A B C
      hABC
      Delta
      hADelta hBDelta hCDelta
      Lambda
      hALambda hBLambda hCLambda

  exact
    Exists.intro Lambda
      (And.intro hDeltaLambda hXLambda)


/--
Uniqueness of the corrected E4 hyperplane containing Delta and an
external point X.
-/
theorem hilbert4D_hyperplane_unique_of_plane_and_external_point_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [C4 : Hilbert4DHyperplaneIncidenceCore Geo]
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (X : Geo.Point)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta))
    (Lambda Rho : Q.Hyperplane)
    (hDeltaLambda :
      HilbertPlaneInHyperplane4 Geo Delta Lambda)
    (hXLambda :
      Q.OnHyperplane X Lambda)
    (hDeltaRho :
      HilbertPlaneInHyperplane4 Geo Delta Rho)
    (hXRho :
      Q.OnHyperplane X Rho) :
    Lambda = Rho := by

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

  have hABCData :=
    Classical.choose_spec hCExists

  have hADelta :
      Q.toHilbertSpacePrimitive.OnPlane A Delta :=
    hABCData.1

  have hBDelta :
      Q.toHilbertSpacePrimitive.OnPlane B Delta :=
    hABCData.2.1

  have hCDelta :
      Q.toHilbertSpacePrimitive.OnPlane C Delta :=
    hABCData.2.2.1

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hABCData.2.2.2

  have hABCX :
      Not (HilbertCoplanar4 Geo A B C X) :=
    hilbert4D_noncoplanar_of_plane_external_point_dimensionFree
      (Geo := Geo)
      Delta
      A B C X
      hADelta hBDelta hCDelta
      hABC hXoff

  exact
    C4.hyperplane_unique
      A B C X
      hABCX
      Lambda Rho
      (hDeltaLambda A hADelta)
      (hDeltaLambda B hBDelta)
      (hDeltaLambda C hCDelta)
      hXLambda
      (hDeltaRho A hADelta)
      (hDeltaRho B hBDelta)
      (hDeltaRho C hCDelta)
      hXRho


/--
Existence and uniqueness in one package.
-/
theorem hilbert4D_hyperplane_through_plane_and_external_point_existsUnique_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (X : Geo.Point)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta)) :
    ExistsUnique
      (fun Lambda : Q.Hyperplane =>
        HilbertPlaneInHyperplane4 Geo Delta Lambda /\
        Q.OnHyperplane X Lambda) := by

  have hExists :=
    hilbert4D_hyperplane_through_plane_and_external_point_corrected
      (Geo := Geo)
      Delta X hXoff

  let Lambda : Q.Hyperplane :=
    Classical.choose hExists

  have hLambda :
      HilbertPlaneInHyperplane4 Geo Delta Lambda /\
      Q.OnHyperplane X Lambda :=
    Classical.choose_spec hExists

  refine
    Exists.intro Lambda
      (And.intro hLambda ?_)

  intro Rho hRho

  exact
    hilbert4D_hyperplane_unique_of_plane_and_external_point_corrected
      (Geo := Geo)
      Delta X hXoff
      Rho Lambda
      hRho.1 hRho.2
      hLambda.1 hLambda.2


/--
Canonical corrected E4 hyperplane generated by Delta and an external
point X.
-/
noncomputable def hilbert4DHyperplaneSpanPlanePoint_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (X : Geo.Point)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta)) :
    Q.Hyperplane :=

  Classical.choose
    (hilbert4D_hyperplane_through_plane_and_external_point_corrected
      (Geo := Geo)
      Delta X hXoff)


/--
Specification of the canonical plane-plus-point hyperplane.
-/
theorem hilbert4DHyperplaneSpanPlanePoint_corrected_spec
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (X : Geo.Point)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta)) :
    HilbertPlaneInHyperplane4
        Geo Delta
        (hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta X hXoff) /\
    Q.OnHyperplane
        X
        (hilbert4DHyperplaneSpanPlanePoint_corrected
          (Geo := Geo)
          Delta X hXoff) :=

  Classical.choose_spec
    (hilbert4D_hyperplane_through_plane_and_external_point_corrected
      (Geo := Geo)
      Delta X hXoff)


/--
Any hyperplane containing Delta and X is the canonical span.
-/
theorem hilbert4DHyperplaneSpanPlanePoint_corrected_eq
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (X : Geo.Point)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta))
    (Tau : Q.Hyperplane)
    (hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau)
    (hXTau :
      Q.OnHyperplane X Tau) :
    hilbert4DHyperplaneSpanPlanePoint_corrected
        (Geo := Geo)
        Delta X hXoff =
      Tau := by

  have hSpec :=
    hilbert4DHyperplaneSpanPlanePoint_corrected_spec
      (Geo := Geo)
      Delta X hXoff

  exact
    hilbert4D_hyperplane_unique_of_plane_and_external_point_corrected
      (Geo := Geo)
      Delta X hXoff
      (hilbert4DHyperplaneSpanPlanePoint_corrected
        (Geo := Geo)
        Delta X hXoff)
      Tau
      hSpec.1 hSpec.2
      hDeltaTau hXTau

end Geometry

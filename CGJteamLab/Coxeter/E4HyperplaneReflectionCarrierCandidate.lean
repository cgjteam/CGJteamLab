import CGJteamLab.HilbertIsometry
import CGJteamLab.Hilbert4DHyperplaneCarriers

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 reflection carrier candidate

This module performs only the first carrier-transport step needed by the
Coxeter layer.

Given two hyperplanes Sigma and Tau containing a common plane Delta:

1. choose a point X of Tau outside Delta;
2. reflect X in Sigma;
3. prove that the reflected point is still outside Delta, because Sigma
   fixes Delta pointwise and the reflection equivalence is injective;
4. define the candidate reflected hyperplane as

       span(Delta, r_Sigma(X)).

At this stage no claim is made yet that the result is independent of the
chosen point X.  That independence theorem is deliberately the next
checkpoint.
-/

/--
A corrected E4 hyperplane containing Delta has a point outside Delta.

The proof uses only the genuine internal 3-dimensionality of the
hyperplane: four noncoplanar hyperplane points cannot all lie in the
single plane Delta.
-/
theorem hilbert4D_hyperplane_has_point_off_plane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [H4L : Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (_hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau) :
    exists X : Geo.Point,
      Q.OnHyperplane X Tau /\
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta) := by

  have hABCDExists :=
    H4L.four_noncoplanar_on_hyperplane Tau

  let A : Geo.Point :=
    Classical.choose hABCDExists

  have hBCDExists :=
    Classical.choose_spec hABCDExists

  let B : Geo.Point :=
    Classical.choose hBCDExists

  have hCDExists :=
    Classical.choose_spec hBCDExists

  let C : Geo.Point :=
    Classical.choose hCDExists

  have hDExists :=
    Classical.choose_spec hCDExists

  let D : Geo.Point :=
    Classical.choose hDExists

  have hData :=
    Classical.choose_spec hDExists

  have hATau :
      Q.OnHyperplane A Tau :=
    hData.1

  have hBTau :
      Q.OnHyperplane B Tau :=
    hData.2.1

  have hCTau :
      Q.OnHyperplane C Tau :=
    hData.2.2.1

  have hDTau :
      Q.OnHyperplane D Tau :=
    hData.2.2.2.1

  have hNonCop :
      Not (HilbertCoplanar4 Geo A B C D) :=
    hData.2.2.2.2

  by_cases hADelta :
      Q.toHilbertSpacePrimitive.OnPlane A Delta

  case neg =>
    exact
      Exists.intro A
        (And.intro hATau hADelta)

  case pos =>
    by_cases hBDelta :
        Q.toHilbertSpacePrimitive.OnPlane B Delta

    case neg =>
      exact
        Exists.intro B
          (And.intro hBTau hBDelta)

    case pos =>
      by_cases hCDelta :
          Q.toHilbertSpacePrimitive.OnPlane C Delta

      case neg =>
        exact
          Exists.intro C
            (And.intro hCTau hCDelta)

      case pos =>
        by_cases hDDelta :
            Q.toHilbertSpacePrimitive.OnPlane D Delta

        case neg =>
          exact
            Exists.intro D
              (And.intro hDTau hDDelta)

        case pos =>
          exact
            False.elim
              (hNonCop
                (Exists.intro Delta
                  (And.intro hADelta
                    (And.intro hBDelta
                      (And.intro hCDelta hDDelta)))))


/--
Canonical selected point of Tau outside Delta.
-/
noncomputable def hilbert4DHyperplanePointOffPlane_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau) :
    Geo.Point :=

  Classical.choose
    (hilbert4D_hyperplane_has_point_off_plane_corrected
      (Geo := Geo)
      Tau Delta hDeltaTau)


/--
Specification of the selected point outside Delta.
-/
theorem hilbert4DHyperplanePointOffPlane_corrected_spec
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    (Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau) :
    Q.OnHyperplane
        (hilbert4DHyperplanePointOffPlane_corrected
          (Geo := Geo)
          Tau Delta hDeltaTau)
        Tau /\
    Not
      (Q.toHilbertSpacePrimitive.OnPlane
        (hilbert4DHyperplanePointOffPlane_corrected
          (Geo := Geo)
          Tau Delta hDeltaTau)
        Delta) :=

  Classical.choose_spec
    (hilbert4D_hyperplane_has_point_off_plane_corrected
      (Geo := Geo)
      Tau Delta hDeltaTau)


/--
If Delta is contained in the mirror Sigma, reflection in Sigma sends a
point outside Delta to another point outside Delta.

This uses only:

* Delta subset Sigma;
* Sigma is fixed pointwise;
* the corrected hyperplane reflection is an equivalence.
-/
theorem hyperplaneReflect4_corrected_preserves_off_fixed_plane
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
    (X : Geo.Point)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta)) :
    Not
      (Q.toHilbertSpacePrimitive.OnPlane
        (hyperplaneReflect4_corrected Geo Sigma X)
        Delta) := by

  intro hXPrimeDelta

  have hXPrimeSigma :
      Q.OnHyperplane
        (hyperplaneReflect4_corrected Geo Sigma X)
        Sigma :=
    hDeltaSigma
      (hyperplaneReflect4_corrected Geo Sigma X)
      hXPrimeDelta

  have hFixXPrime :
      hyperplaneReflect4_corrected
          Geo Sigma
          (hyperplaneReflect4_corrected Geo Sigma X) =
        hyperplaneReflect4_corrected Geo Sigma X :=
    hyperplaneReflect4_corrected_of_on_hyperplane
      (Geo := Geo)
      Sigma
      (hyperplaneReflect4_corrected Geo Sigma X)
      hXPrimeSigma

  have hXXPrime :
      X =
        hyperplaneReflect4_corrected Geo Sigma X := by

    apply
      (hyperplaneReflectionEquiv4_corrected
        Geo Sigma).injective

    change
      hyperplaneReflect4_corrected Geo Sigma X =
        hyperplaneReflect4_corrected
          Geo Sigma
          (hyperplaneReflect4_corrected Geo Sigma X)

    exact hFixXPrime.symm

  apply hXoff

  rw [hXXPrime]

  exact hXPrimeDelta


/--
Candidate reflected hyperplane generated by Delta and the reflection of
one prescribed point X outside Delta.
-/
noncomputable def hyperplaneReflectionCarrierFromPoint4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma :
      HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (X : Geo.Point)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta)) :
    Q.Hyperplane :=

  hilbert4DHyperplaneSpanPlanePoint_corrected
    (Geo := Geo)
    Delta
    (hyperplaneReflect4_corrected Geo Sigma X)
    (hyperplaneReflect4_corrected_preserves_off_fixed_plane
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      X hXoff)


/--
The candidate carrier contains Delta and the reflected point.
-/
theorem hyperplaneReflectionCarrierFromPoint4_corrected_spec
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma :
      HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (X : Geo.Point)
    (hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta)) :
    HilbertPlaneInHyperplane4
        Geo Delta
        (hyperplaneReflectionCarrierFromPoint4_corrected
          (Geo := Geo)
          Sigma Delta hDeltaSigma X hXoff) /\
    Q.OnHyperplane
        (hyperplaneReflect4_corrected Geo Sigma X)
        (hyperplaneReflectionCarrierFromPoint4_corrected
          (Geo := Geo)
          Sigma Delta hDeltaSigma X hXoff) := by

  exact
    hilbert4DHyperplaneSpanPlanePoint_corrected_spec
      (Geo := Geo)
      Delta
      (hyperplaneReflect4_corrected Geo Sigma X)
      (hyperplaneReflect4_corrected_preserves_off_fixed_plane
        (Geo := Geo)
        Sigma Delta hDeltaSigma
        X hXoff)


/--
Canonical first candidate for the image of Tau under reflection in
Sigma, relative to a common contained plane Delta.

The definition uses the selected point of Tau outside Delta.
Independence of that selected point is intentionally not asserted here.
-/
noncomputable def hyperplaneReflectionCarrier4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma :
      HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau) :
    Q.Hyperplane :=

  hyperplaneReflectionCarrierFromPoint4_corrected
    (Geo := Geo)
    Sigma Delta hDeltaSigma
    (hilbert4DHyperplanePointOffPlane_corrected
      (Geo := Geo)
      Tau Delta hDeltaTau)
    (hilbert4DHyperplanePointOffPlane_corrected_spec
      (Geo := Geo)
      Tau Delta hDeltaTau).2


/--
Specification of the canonical first carrier candidate.
-/
theorem hyperplaneReflectionCarrier4_corrected_spec
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma Tau : Q.Hyperplane)
    (Delta : Q.toHilbertSpacePrimitive.Plane)
    (hDeltaSigma :
      HilbertPlaneInHyperplane4 Geo Delta Sigma)
    (hDeltaTau :
      HilbertPlaneInHyperplane4 Geo Delta Tau) :
    HilbertPlaneInHyperplane4
        Geo Delta
        (hyperplaneReflectionCarrier4_corrected
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau) /\
    Q.OnHyperplane
        (hyperplaneReflect4_corrected
          Geo Sigma
          (hilbert4DHyperplanePointOffPlane_corrected
            (Geo := Geo)
            Tau Delta hDeltaTau))
        (hyperplaneReflectionCarrier4_corrected
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau) := by

  exact
    hyperplaneReflectionCarrierFromPoint4_corrected_spec
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      (hilbert4DHyperplanePointOffPlane_corrected
        (Geo := Geo)
        Tau Delta hDeltaTau)
      (hilbert4DHyperplanePointOffPlane_corrected_spec
        (Geo := Geo)
        Tau Delta hDeltaTau).2

end Geometry

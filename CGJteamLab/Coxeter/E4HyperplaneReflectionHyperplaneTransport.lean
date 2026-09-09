import CGJteamLab.Coxeter.E4HyperplaneReflectionCarrierIndependence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 hyperplane reflection: exact hyperplane transport

The carrier construction is now independent of the chosen point.
This module upgrades one-way containment to exact setwise transport:

    P in Tau
      iff
    r_Sigma(P) in hyperplaneReflectionCarrier4_corrected Sigma Tau Delta.

The reverse implication uses the same span theorem a second time.

Choose X in Tau outside Delta.  Then r(X) lies in the carrier and is
still outside Delta.  Regard the carrier as the new source hyperplane,
Tau as the target hyperplane, and r(X) as the new external base point.
Its reflected image is X by involutivity.  Therefore every point of the
carrier reflects back into Tau.

This avoids any separate four-point hyperplane-collineation theorem.
-/

/--
Exact setwise transport of one corrected E4 hyperplane by reflection.
-/
def HyperplaneReflectionMapsHyperplane4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma source target : Q.Hyperplane) : Prop :=

  forall P : Geo.Point,
    Q.OnHyperplane P source <->
      Q.OnHyperplane
        (hyperplaneReflect4_corrected Geo Sigma P)
        target


/--
The canonical carrier agrees with the point-defined carrier built from
any external point of Tau.
-/
theorem hyperplaneReflectionCarrier4_corrected_eq_from_point
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
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta)) :
    hyperplaneReflectionCarrier4_corrected
        (Geo := Geo)
        Sigma Tau Delta
        hDeltaSigma hDeltaTau =
      hyperplaneReflectionCarrierFromPoint4_corrected
        (Geo := Geo)
        Sigma Delta hDeltaSigma
        X hXoff := by

  let Z : Geo.Point :=
    hilbert4DHyperplanePointOffPlane_corrected
      (Geo := Geo)
      Tau Delta hDeltaTau

  have hZData :=
    hilbert4DHyperplanePointOffPlane_corrected_spec
      (Geo := Geo)
      Tau Delta hDeltaTau

  have hInd :=
    hyperplaneReflectionCarrierFromPoint4_corrected_independent
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau
      Z X
      hZData.1 hXTau
      hZData.2 hXoff

  exact hInd


/--
The canonical carrier gives exact hyperplane transport.
-/
theorem hyperplaneReflectionCarrier4_corrected_maps
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
      HilbertPlaneInHyperplane4 Geo Delta Tau) :
    HyperplaneReflectionMapsHyperplane4_corrected
      Geo Sigma Tau
      (hyperplaneReflectionCarrier4_corrected
        (Geo := Geo)
        Sigma Tau Delta
        hDeltaSigma hDeltaTau) := by

  let Lambda : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau

  have hLambdaSpec :=
    hyperplaneReflectionCarrier4_corrected_spec
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau

  have hDeltaLambda :
      HilbertPlaneInHyperplane4 Geo Delta Lambda :=
    hLambdaSpec.1

  let X : Geo.Point :=
    hilbert4DHyperplanePointOffPlane_corrected
      (Geo := Geo)
      Tau Delta hDeltaTau

  have hXData :=
    hilbert4DHyperplanePointOffPlane_corrected_spec
      (Geo := Geo)
      Tau Delta hDeltaTau

  have hXTau :
      Q.OnHyperplane X Tau :=
    hXData.1

  have hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta) :=
    hXData.2

  have hXPrimeLambda :
      Q.OnHyperplane
        (hyperplaneReflect4_corrected Geo Sigma X)
        Lambda :=
    hyperplaneReflectionCarrier4_corrected_contains
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau
      X hXTau

  have hXPrimeOff :
      Not
        (Q.toHilbertSpacePrimitive.OnPlane
          (hyperplaneReflect4_corrected Geo Sigma X)
          Delta) :=
    hyperplaneReflect4_corrected_preserves_off_fixed_plane
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      X hXoff

  have hXBackTau :
      Q.OnHyperplane
        (hyperplaneReflect4_corrected Geo Sigma
          (hyperplaneReflect4_corrected Geo Sigma X))
        Tau := by

    simpa only [
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo) Sigma X
    ] using hXTau

  intro P
  constructor

  case mp =>
    intro hPTau

    exact
      hyperplaneReflectionCarrier4_corrected_contains
        (Geo := Geo)
        Sigma Tau Delta
        hDeltaSigma hDeltaTau
        P hPTau

  case mpr =>
    intro hPPrimeLambda

    have hBack :
        Q.OnHyperplane
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma P))
          Tau :=
      hyperplaneReflect4_corrected_image_point_mem_of_span
        (Geo := Geo)
        Sigma Lambda Tau
        Delta
        hDeltaSigma
        hDeltaLambda
        hDeltaTau
        (hyperplaneReflect4_corrected Geo Sigma X)
        hXPrimeLambda
        hXPrimeOff
        hXBackTau
        (hyperplaneReflect4_corrected Geo Sigma P)
        hPPrimeLambda

    simpa only [
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo) Sigma P
    ] using hBack


/--
Pointwise membership characterization of the canonical reflected
hyperplane.
-/
theorem hyperplaneReflectionCarrier4_corrected_iff
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
    (P : Geo.Point) :
    Q.OnHyperplane P Tau <->
      Q.OnHyperplane
        (hyperplaneReflect4_corrected Geo Sigma P)
        (hyperplaneReflectionCarrier4_corrected
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau) :=

  hyperplaneReflectionCarrier4_corrected_maps
    (Geo := Geo)
    Sigma Tau Delta
    hDeltaSigma hDeltaTau
    P


/--
Exact hyperplane transport reverses under the same involutive
reflection.
-/
theorem hyperplaneReflectionMapsHyperplane4_corrected_symm
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma source target : Q.Hyperplane)
    (hMap :
      HyperplaneReflectionMapsHyperplane4_corrected
        Geo Sigma source target) :
    HyperplaneReflectionMapsHyperplane4_corrected
      Geo Sigma target source := by

  intro P
  constructor

  case mp =>
    intro hPt

    have hDoubleTarget :
        Q.OnHyperplane
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma P))
          target := by

      simpa only [
        hyperplaneReflect4_corrected_involutive
          (Geo := Geo) Sigma P
      ] using hPt

    exact
      (hMap
        (hyperplaneReflect4_corrected Geo Sigma P)).mpr
        hDoubleTarget

  case mpr =>
    intro hPs

    have hDoubleTarget :
        Q.OnHyperplane
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma P))
          target :=
      (hMap
        (hyperplaneReflect4_corrected Geo Sigma P)).mp
        hPs

    simpa only [
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo) Sigma P
    ] using hDoubleTarget


/--
The canonical carrier contains Delta.
-/
theorem hyperplaneReflectionCarrier4_corrected_contains_common_plane
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
        hDeltaSigma hDeltaTau) :=

  (hyperplaneReflectionCarrier4_corrected_spec
    (Geo := Geo)
    Sigma Tau Delta
    hDeltaSigma hDeltaTau).1


/--
Applying the canonical carrier construction twice returns the original
hyperplane.
-/
theorem hyperplaneReflectionCarrier4_corrected_involutive
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
      HilbertPlaneInHyperplane4 Geo Delta Tau) :
    hyperplaneReflectionCarrier4_corrected
        (Geo := Geo)
        Sigma
        (hyperplaneReflectionCarrier4_corrected
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau)
        Delta
        hDeltaSigma
        (hyperplaneReflectionCarrier4_corrected_contains_common_plane
          (Geo := Geo)
          Sigma Tau Delta
          hDeltaSigma hDeltaTau) =
      Tau := by

  let Lambda : Q.Hyperplane :=
    hyperplaneReflectionCarrier4_corrected
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau

  have hDeltaLambda :
      HilbertPlaneInHyperplane4 Geo Delta Lambda :=
    hyperplaneReflectionCarrier4_corrected_contains_common_plane
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau

  let X : Geo.Point :=
    hilbert4DHyperplanePointOffPlane_corrected
      (Geo := Geo)
      Tau Delta hDeltaTau

  have hXData :=
    hilbert4DHyperplanePointOffPlane_corrected_spec
      (Geo := Geo)
      Tau Delta hDeltaTau

  have hXTau :
      Q.OnHyperplane X Tau :=
    hXData.1

  have hXoff :
      Not (Q.toHilbertSpacePrimitive.OnPlane X Delta) :=
    hXData.2

  let Xp : Geo.Point :=
    hyperplaneReflect4_corrected Geo Sigma X

  have hXpLambda :
      Q.OnHyperplane Xp Lambda :=
    hyperplaneReflectionCarrier4_corrected_contains
      (Geo := Geo)
      Sigma Tau Delta
      hDeltaSigma hDeltaTau
      X hXTau

  have hXpOff :
      Not (Q.toHilbertSpacePrimitive.OnPlane Xp Delta) :=
    hyperplaneReflect4_corrected_preserves_off_fixed_plane
      (Geo := Geo)
      Sigma Delta hDeltaSigma
      X hXoff

  have hCarrierEqPoint :
      hyperplaneReflectionCarrier4_corrected
          (Geo := Geo)
          Sigma Lambda Delta
          hDeltaSigma hDeltaLambda =
        hyperplaneReflectionCarrierFromPoint4_corrected
          (Geo := Geo)
          Sigma Delta hDeltaSigma
          Xp hXpOff :=
    hyperplaneReflectionCarrier4_corrected_eq_from_point
      (Geo := Geo)
      Sigma Lambda Delta
      hDeltaSigma hDeltaLambda
      Xp hXpLambda hXpOff

  have hPointCarrierTau :
      hyperplaneReflectionCarrierFromPoint4_corrected
          (Geo := Geo)
          Sigma Delta hDeltaSigma
          Xp hXpOff =
        Tau := by

    unfold hyperplaneReflectionCarrierFromPoint4_corrected

    simpa only [
      Xp,
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo) Sigma X
    ] using
      (hilbert4DHyperplaneSpanPlanePoint_corrected_eq
        (Geo := Geo)
        Delta X hXoff
        Tau hDeltaTau hXTau)

  exact
    hCarrierEqPoint.trans hPointCarrierTau

end Geometry

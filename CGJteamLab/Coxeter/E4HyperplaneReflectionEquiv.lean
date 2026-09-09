import CGJteamLab.Coxeter.E4HyperplaneReflectionCore

/-!
# Corrected E4 hyperplane reflection equivalence

Production `Equiv` packaging of the corrected E4 hyperplane reflection,
together with the canonical fixed-point characterization.
-/

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 hyperplane reflection as an equivalence

Test66 constructed the corrected hyperplane reflection as a function and
proved that it is involutive, under the single XI.11-type existence class

  Hilbert4DNormalFromExternalPointExistence_corrected.

This file packages that involution as an actual equivalence of the ambient
point type and identifies its fixed-point set exactly with the reflecting
hyperplane.

This is the representation needed later for Coxeter compositions:
hyperplane reflections are now genuine invertible transformations.
-/

/--
A point is fixed by the corrected hyperplane-reflection function exactly
when it lies on the reflecting hyperplane.
-/
theorem hyperplaneReflect4_corrected_fixed_iff
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [H4O : Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    hyperplaneReflect4_corrected Geo Sigma P = P <->
      Q.OnHyperplane P Sigma := by

  constructor

  · intro hFix

    have hSpec :
        IsHyperplaneReflection4_corrected
          Geo Sigma P
          (hyperplaneReflect4_corrected Geo Sigma P) :=
      hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Sigma P

    rw [hFix] at hSpec

    rcases hSpec with hFixed | hOff

    · exact hFixed.1

    · rcases hOff with
        ⟨_hPoff, F, _hPerp, hMid⟩

      have hPP : Ne P P :=
        (H4O.between_incidence
          P F P hMid.1).2.2.1

      exact False.elim (hPP rfl)

  · intro hPSigma

    have hSpec :
        IsHyperplaneReflection4_corrected
          Geo Sigma P
          (hyperplaneReflect4_corrected Geo Sigma P) :=
      hyperplaneReflect4_corrected_spec
        (Geo := Geo)
        Sigma P

    have hSelf :
        IsHyperplaneReflection4_corrected
          Geo Sigma P P :=
      Or.inl
        ⟨hPSigma, rfl⟩

    exact
      hyperplaneReflection4_unique_corrected
        (Geo := Geo)
        Sigma
        P
        (hyperplaneReflect4_corrected Geo Sigma P)
        P
        hSpec
        hSelf

/--
The corrected E4 reflection in a hyperplane, packaged as an equivalence
of the ambient point type.
-/
noncomputable def hyperplaneReflectionEquiv4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane) :
    Equiv Geo.Point Geo.Point where

  toFun :=
    hyperplaneReflect4_corrected Geo Sigma

  invFun :=
    hyperplaneReflect4_corrected Geo Sigma

  left_inv := by
    intro P
    exact
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo)
        Sigma P

  right_inv := by
    intro P
    exact
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo)
        Sigma P

/--
The equivalence really realizes the relational corrected reflection.
-/
theorem hyperplaneReflectionEquiv4_corrected_spec
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    IsHyperplaneReflection4_corrected
      Geo Sigma P
      (hyperplaneReflectionEquiv4_corrected
        Geo Sigma P) := by

  exact
    hyperplaneReflect4_corrected_spec
      (Geo := Geo)
      Sigma P

/--
The equivalence is its own inverse pointwise.
-/
theorem hyperplaneReflectionEquiv4_corrected_apply_apply
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    hyperplaneReflectionEquiv4_corrected Geo Sigma
      (hyperplaneReflectionEquiv4_corrected Geo Sigma P) = P := by

  change
    hyperplaneReflect4_corrected Geo Sigma
      (hyperplaneReflect4_corrected Geo Sigma P) = P

  exact
    hyperplaneReflect4_corrected_involutive
      (Geo := Geo)
      Sigma P

/--
The fixed points of the equivalence are exactly the points of Sigma.
-/
theorem hyperplaneReflectionEquiv4_corrected_fixed_iff
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [Hilbert4DAmbientIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (P : Geo.Point) :
    hyperplaneReflectionEquiv4_corrected Geo Sigma P = P <->
      Q.OnHyperplane P Sigma := by

  change
    hyperplaneReflect4_corrected Geo Sigma P = P <->
      Q.OnHyperplane P Sigma

  exact
    hyperplaneReflect4_corrected_fixed_iff
      (Geo := Geo)
      Sigma P

end Geometry

import CGJteamLab.Coxeter.E4HyperplaneReflectionIncidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Corrected E4 hyperplane reflection: line transport

This module upgrades collinearity preservation to exact setwise
transport of ambient lines.

The central predicate

  HyperplaneReflectionMapsLine4_corrected

means

  P in source <-> r_Sigma(P) in target.

The proof uses only line existence/uniqueness, two points on a line,
collinearity preservation, and involutivity of the reflection.
-/

/--
Exact setwise transport of one ambient line by corrected E4 hyperplane
reflection.
-/
def HyperplaneReflectionMapsLine4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target : Geo.Line) : Prop :=
  forall P : Geo.Point,
    H.OnLine P source <->
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma P)
        target


/--
Two reflected images of distinct source points determine the exact
image line.
-/
theorem hyperplaneReflectionMapsLine4_corrected_of_two_points
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target : Geo.Line)
    (A B : Geo.Point)
    (hAB : Ne A B)
    (hAs : H.OnLine A source)
    (hBs : H.OnLine B source)
    (hA't :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma A)
        target)
    (hB't :
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma B)
        target) :
    HyperplaneReflectionMapsLine4_corrected
      Geo Sigma source target := by

  have hImageAB :
      Ne
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma B) := by

    intro hEq
    apply hAB

    exact
      (hyperplaneReflectionEquiv4_corrected
        Geo Sigma).injective hEq

  intro P
  constructor

  case mp =>
    intro hPs

    have hABP :
        PrimCollinear Geo A B P :=
      Exists.intro source
        (And.intro hAs
          (And.intro hBs hPs))

    have hImageCol :
        PrimCollinear
          Geo
          (hyperplaneReflect4_corrected Geo Sigma A)
          (hyperplaneReflect4_corrected Geo Sigma B)
          (hyperplaneReflect4_corrected Geo Sigma P) :=
      hyperplaneReflect4_corrected_preserves_collinear
        (Geo := Geo)
        Sigma
        A B P
        hABP

    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hImageAB
        hA't hB't
        hImageCol

  case mpr =>
    intro hP't

    have hImageCol :
        PrimCollinear
          Geo
          (hyperplaneReflect4_corrected Geo Sigma A)
          (hyperplaneReflect4_corrected Geo Sigma B)
          (hyperplaneReflect4_corrected Geo Sigma P) :=
      Exists.intro target
        (And.intro hA't
          (And.intro hB't hP't))

    have hBackCol :
        PrimCollinear
          Geo
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma A))
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma B))
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma P)) :=
      hyperplaneReflect4_corrected_preserves_collinear
        (Geo := Geo)
        Sigma
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma B)
        (hyperplaneReflect4_corrected Geo Sigma P)
        hImageCol

    have hABP :
        PrimCollinear Geo A B P := by

      simpa only [
        hyperplaneReflect4_corrected_involutive
          (Geo := Geo) Sigma A,
        hyperplaneReflect4_corrected_involutive
          (Geo := Geo) Sigma B,
        hyperplaneReflect4_corrected_involutive
          (Geo := Geo) Sigma P
      ] using hBackCol

    exact
      hilbert_on_line_of_primCollinear_with_two_on_line
        (Geo := Geo)
        hAB
        hAs hBs
        hABP


/--
Every ambient line has an exact image line.
-/
theorem hyperplaneReflectionMapsLine4_corrected_exists
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source : Geo.Line) :
    exists target : Geo.Line,
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma source target := by

  have hABExists :=
    D.two_points_on_each_line source

  let A : Geo.Point :=
    Classical.choose hABExists

  have hBExists :=
    Classical.choose_spec hABExists

  let B : Geo.Point :=
    Classical.choose hBExists

  have hABData :=
    Classical.choose_spec hBExists

  have hAB :
      Ne A B :=
    hABData.1

  have hAs :
      H.OnLine A source :=
    hABData.2.1

  have hBs :
      H.OnLine B source :=
    hABData.2.2

  have hImageAB :
      Ne
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma B) := by

    intro hEq
    apply hAB

    exact
      (hyperplaneReflectionEquiv4_corrected
        Geo Sigma).injective hEq

  have hTargetExists :=
    HilbertPlaneIncidence.line_through
      (Geo := Geo)
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      hImageAB

  let target : Geo.Line :=
    Classical.choose hTargetExists

  have hTargetData :=
    Classical.choose_spec hTargetExists

  exact
    Exists.intro target
      (hyperplaneReflectionMapsLine4_corrected_of_two_points
        (Geo := Geo)
        Sigma
        source target
        A B
        hAB
        hAs hBs
        hTargetData.1 hTargetData.2)


/--
The exact image line is unique.
-/
theorem hyperplaneReflectionMapsLine4_corrected_unique
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target1 target2 : Geo.Line)
    (hMap1 :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma source target1)
    (hMap2 :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma source target2) :
    target1 = target2 := by

  have hABExists :=
    D.two_points_on_each_line source

  let A : Geo.Point :=
    Classical.choose hABExists

  have hBExists :=
    Classical.choose_spec hABExists

  let B : Geo.Point :=
    Classical.choose hBExists

  have hABData :=
    Classical.choose_spec hBExists

  have hAB :
      Ne A B :=
    hABData.1

  have hAs :
      H.OnLine A source :=
    hABData.2.1

  have hBs :
      H.OnLine B source :=
    hABData.2.2

  have hImageAB :
      Ne
        (hyperplaneReflect4_corrected Geo Sigma A)
        (hyperplaneReflect4_corrected Geo Sigma B) := by

    intro hEq
    apply hAB

    exact
      (hyperplaneReflectionEquiv4_corrected
        Geo Sigma).injective hEq

  exact
    HilbertPlaneIncidence.line_unique
      (Geo := Geo)
      (hyperplaneReflect4_corrected Geo Sigma A)
      (hyperplaneReflect4_corrected Geo Sigma B)
      hImageAB
      target1 target2
      ((hMap1 A).mp hAs)
      ((hMap1 B).mp hBs)
      ((hMap2 A).mp hAs)
      ((hMap2 B).mp hBs)


/--
Canonical image line.
-/
noncomputable def hyperplaneReflectionLineCarrier4_corrected
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source : Geo.Line) :
    Geo.Line :=

  Classical.choose
    (hyperplaneReflectionMapsLine4_corrected_exists
      (Geo := Geo)
      Sigma source)


/--
Specification of the canonical image line.
-/
theorem hyperplaneReflectionLineCarrier4_corrected_spec
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source : Geo.Line) :
    HyperplaneReflectionMapsLine4_corrected
      Geo Sigma source
      (hyperplaneReflectionLineCarrier4_corrected
        (Geo := Geo)
        Sigma source) :=

  Classical.choose_spec
    (hyperplaneReflectionMapsLine4_corrected_exists
      (Geo := Geo)
      Sigma source)


/--
Pointwise membership characterization of the canonical image line.
-/
theorem hyperplaneReflectionLineCarrier4_corrected_iff
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source : Geo.Line)
    (P : Geo.Point) :
    H.OnLine P source <->
      H.OnLine
        (hyperplaneReflect4_corrected Geo Sigma P)
        (hyperplaneReflectionLineCarrier4_corrected
          (Geo := Geo)
          Sigma source) :=

  hyperplaneReflectionLineCarrier4_corrected_spec
    (Geo := Geo)
    Sigma source P


/--
Any exact target is the canonical image line.
-/
theorem hyperplaneReflectionLineCarrier4_corrected_eq
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target : Geo.Line)
    (hMap :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma source target) :
    hyperplaneReflectionLineCarrier4_corrected
        (Geo := Geo)
        Sigma source =
      target := by

  exact
    hyperplaneReflectionMapsLine4_corrected_unique
      (Geo := Geo)
      Sigma
      source
      (hyperplaneReflectionLineCarrier4_corrected
        (Geo := Geo)
        Sigma source)
      target
      (hyperplaneReflectionLineCarrier4_corrected_spec
        (Geo := Geo)
        Sigma source)
      hMap


/--
Exact line transport reverses under the same involutive reflection.
-/
theorem hyperplaneReflectionMapsLine4_corrected_symm
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source target : Geo.Line)
    (hMap :
      HyperplaneReflectionMapsLine4_corrected
        Geo Sigma source target) :
    HyperplaneReflectionMapsLine4_corrected
      Geo Sigma target source := by

  intro P
  constructor

  case mp =>
    intro hPt

    have hPtBack :
        H.OnLine
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
        hPtBack

  case mpr =>
    intro hPrs

    have h :
        H.OnLine
          (hyperplaneReflect4_corrected Geo Sigma
            (hyperplaneReflect4_corrected Geo Sigma P))
          target :=
      (hMap
        (hyperplaneReflect4_corrected Geo Sigma P)).mp
        hPrs

    simpa only [
      hyperplaneReflect4_corrected_involutive
        (Geo := Geo) Sigma P
    ] using h


/--
Canonical line transport is involutive.
-/
theorem hyperplaneReflectionLineCarrier4_corrected_involutive
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [Q : Hilbert4DPrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo]
    [Hilbert4DHyperplaneIncidenceCore Geo]
    [Hilbert4DHyperplaneLocal3DIncidence Geo]
    [Hilbert4DPlaneHyperplaneIncidence Geo]
    [Hilbert4DAmbientOrder Geo]
    [Hilbert4DAmbientCongruence Geo]
    [Hilbert4DNormalFromExternalPointExistence_corrected Geo]
    (Sigma : Q.Hyperplane)
    (source : Geo.Line) :
    hyperplaneReflectionLineCarrier4_corrected
        (Geo := Geo)
        Sigma
        (hyperplaneReflectionLineCarrier4_corrected
          (Geo := Geo)
          Sigma source) =
      source := by

  have hForward :=
    hyperplaneReflectionLineCarrier4_corrected_spec
      (Geo := Geo)
      Sigma source

  have hBackward :=
    hyperplaneReflectionMapsLine4_corrected_symm
      (Geo := Geo)
      Sigma
      source
      (hyperplaneReflectionLineCarrier4_corrected
        (Geo := Geo)
        Sigma source)
      hForward

  exact
    hyperplaneReflectionLineCarrier4_corrected_eq
      (Geo := Geo)
      Sigma
      (hyperplaneReflectionLineCarrier4_corrected
        (Geo := Geo)
        Sigma source)
      source
      hBackward

end Geometry

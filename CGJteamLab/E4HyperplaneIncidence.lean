import CGJteamLab.E4Hyperplane
import CGJteamLab.SalasCompatibility

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Incidence lemmas for derived E4 hyperplanes

This file promotes the first dimension-free lemmas needed to construct
derived E4 hyperplanes from arbitrary noncoplanar quadruples.

No new axiom is introduced here.

The assumptions are:

* the existing Hilbert point-line base;
* Sancho de Salas LP1-LP4 incidence;
* the existing primitive plane signature.

The Salas axioms are converted locally to the old Smith compatibility
interfaces only when an existing production theorem requires them.
-/

/--
Under Salas incidence, a line together with a point outside it lies in
an ambient plane.
-/
theorem salas_plane_through_line_and_external_point
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : SalasIncidence Geo]
    (l : Geo.Line)
    (P : Geo.Point)
    (hPl : Not (H.OnLine P l)) :
    exists pi : S.Plane,
      HilbertLineInPlane Geo l pi /\
      S.OnPlane P pi := by

  exact
    smithCore_plane_through_line_and_external_point
      (Geo := Geo)
      (C :=
        salas_to_smithIncidenceCore
          (Geo := Geo))
      l P hPl


/--
If four points are noncoplanar, then the first three are noncollinear.

This is derived from Salas incidence; it is not a dimension-four axiom.
-/
theorem salas_noncoplanar4_first_three_noncollinear
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : SalasIncidence Geo]
    (A0 B C D : Geo.Point)
    (hNoncoplanar : Not (HilbertCoplanar4 Geo A0 B C D)) :
    Not (PrimCollinear Geo A0 B C) := by

  intro hABC
  rcases hABC with
    ⟨l, hAl, hBl, hCl⟩

  by_cases hDl : H.OnLine D l

  · rcases
        hilbert_point_off_line
          (Geo := Geo) l with
      ⟨P, hPl⟩

    rcases
        salas_plane_through_line_and_external_point
          (Geo := Geo)
          l P hPl with
      ⟨pi, hlpi, _hPpi⟩

    exact
      hNoncoplanar
        ⟨pi,
         hlpi A0 hAl,
         hlpi B hBl,
         hlpi C hCl,
         hlpi D hDl⟩

  · rcases
        salas_plane_through_line_and_external_point
          (Geo := Geo)
          l D hDl with
      ⟨pi, hlpi, hDpi⟩

    exact
      hNoncoplanar
        ⟨pi,
         hlpi A0 hAl,
         hlpi B hBl,
         hlpi C hCl,
         hDpi⟩


/--
For four noncoplanar points, the fourth point lies outside the Smith span
of the first three.

This is the closure-theoretic form of noncoplanarity needed to construct
a generated 3-flat.
-/
theorem salas_noncoplanar4_fourth_outside_triple_span
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : SalasIncidence Geo]
    (A0 B C D : Geo.Point)
    (hNoncoplanar : Not (HilbertCoplanar4 Geo A0 B C D)) :
    Not (SmithSpan Geo (SmithPointTriple Geo A0 B C) D) := by

  have hABC :
      Not (PrimCollinear Geo A0 B C) :=
    salas_noncoplanar4_first_three_noncollinear
      (Geo := Geo)
      A0 B C D
      hNoncoplanar

  rcases
      A.plane_through_unique
        A0 B C hABC with
    ⟨pi, hApi, hBpi, hCpi, _hUnique⟩

  have hTripleSpan :
      SmithSpan Geo (SmithPointTriple Geo A0 B C) =
        SmithPlaneCarrier Geo pi :=
    @smithSpan_three_noncollinear_eq_plane
      Geo
      H
      HP
      S
      (salas_implies_dimensionFreeIncidence
        (Geo := Geo))
      A0 B C hABC
      pi hApi hBpi hCpi

  intro hDspan

  have hDpi : S.OnPlane D pi := by
    change SmithPlaneCarrier Geo pi D
    rw [<- hTripleSpan]
    exact hDspan

  exact
    hNoncoplanar
      ⟨pi,
       hApi,
       hBpi,
       hCpi,
       hDpi⟩


/--
Any four noncoplanar points generate an `E4Generated3Flat`.

No dimension-four upper bound is used here.
-/
theorem salas_noncoplanar4_generates_3flat
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo]
    (A B C D : Geo.Point)
    (hNoncoplanar : Not (HilbertCoplanar4 Geo A B C D)) :
    E4Generated3Flat Geo
      (SmithSpan Geo
        (SmithAdjoinPoint Geo (SmithPointTriple Geo A B C) D)) := by

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    salas_noncoplanar4_first_three_noncollinear
      (Geo := Geo)
      A B C D
      hNoncoplanar

  have hDout :
      Not (SmithSpan Geo (SmithPointTriple Geo A B C) D) :=
    salas_noncoplanar4_fourth_outside_triple_span
      (Geo := Geo)
      A B C D
      hNoncoplanar

  exact
    ⟨A, B, C, D,
     hABC,
     hDout,
     rfl⟩

end Geometry

import CGJteamLab.E4Hyperplane
import CGJteamLab.HilbertWylerCompatibility

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
* `HilbertWylerAxioms`;
* the existing primitive plane signature.

The Hilbert-Wyler axioms are converted locally to the older Smith
compatibility interfaces only where an existing production theorem
still requires them.
-/

/--
Under Hilbert-Wyler incidence, a line together with a point outside it
lies in an ambient plane.
-/
theorem hilbertWyler_plane_through_line_and_external_point
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
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
        hilbertWyler_smithIncidenceCore
          (Geo := Geo))
      l P hPl


/--
If four points are noncoplanar, then the first three are noncollinear.

This is derived from Hilbert-Wyler incidence; it is not a
dimension-four axiom.
-/
theorem hilbertWyler_noncoplanar4_first_three_noncollinear
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
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
        hilbertWyler_plane_through_line_and_external_point
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
        hilbertWyler_plane_through_line_and_external_point
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


set_option linter.style.haveILetI false

/--
For four noncoplanar points, the fourth point lies outside the Smith span
of the first three.

This is the closure-theoretic form of noncoplanarity needed to construct
a generated 3-flat.
-/
theorem hilbertWyler_noncoplanar4_fourth_outside_triple_span
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo]
    (A0 B C D : Geo.Point)
    (hNoncoplanar : Not (HilbertCoplanar4 Geo A0 B C D)) :
    Not (SmithSpan Geo (SmithPointTriple Geo A0 B C) D) := by

  have hABC :
      Not (PrimCollinear Geo A0 B C) :=
    hilbertWyler_noncoplanar4_first_three_noncollinear
      (Geo := Geo)
      A0 B C D
      hNoncoplanar

  rcases
      A.plane_through
        A0 B C hABC with
    ⟨pi, hApi, hBpi, hCpi⟩

  have hTripleSpan :
      SmithSpan Geo (SmithPointTriple Geo A0 B C) =
        SmithPlaneCarrier Geo pi := by
    letI : HilbertDimensionFreeIncidence Geo :=
      hilbertDimensionFreeIncidence_of_hilbertWyler
        (Geo := Geo)

    exact
      smithSpan_three_noncollinear_eq_plane
        (Geo := Geo)
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


set_option linter.style.haveILetI true

/--
Any four noncoplanar points generate an `E4Generated3Flat`.

No dimension-four upper bound is used here.
-/
theorem hilbertWyler_noncoplanar4_generates_3flat
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertWylerAxioms Geo]
    (A B C D : Geo.Point)
    (hNoncoplanar : Not (HilbertCoplanar4 Geo A B C D)) :
    E4Generated3Flat Geo
      (SmithSpan Geo
        (SmithAdjoinPoint Geo (SmithPointTriple Geo A B C) D)) := by

  have hABC :
      Not (PrimCollinear Geo A B C) :=
    hilbertWyler_noncoplanar4_first_three_noncollinear
      (Geo := Geo)
      A B C D
      hNoncoplanar

  have hDout :
      Not (SmithSpan Geo (SmithPointTriple Geo A B C) D) :=
    hilbertWyler_noncoplanar4_fourth_outside_triple_span
      (Geo := Geo)
      A B C D
      hNoncoplanar

  exact
    ⟨A, B, C, D,
     hABC,
     hDout,
     rfl⟩

end Geometry

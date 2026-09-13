import CGJteamLab.HilbertWylerAxioms
import CGJteamLab.HilbertDimensionFreeWyler
import CGJteamLab.HilbertDimensionFreeSmithExchange

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Hilbert-Wyler derived incidence theory

This module contains consequences of `HilbertWylerAxioms`.

The intended dependency chain is

    Hilbert-Wyler common incidence core
      + Wyler I.7
        -> Smith I.5
        -> Wyler generated-flat theory
        -> Mac Lane-Steinitz exchange.

Thus neither Smith I.5 nor exchange is an axiom of the Hilbert-Wyler
foundation.

The imports of the existing `HilbertDimensionFree*` modules are temporary
reuse of already proved production theorems.  They can be renamed or
reorganized after the new axiom boundary is stable.
-/

/--
The common part of `HilbertWylerAxioms` supplies the existing
`SmithIncidenceCore` interface.
-/
theorem hilbertWyler_smithIncidenceCore
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo] :
    SmithIncidenceCore Geo where

  two_points_on_each_line :=
    A.two_points_on_each_line

  three_noncollinear_on_plane :=
    A.three_noncollinear_on_plane

  plane_through :=
    A.plane_through

  plane_unique :=
    A.plane_unique

  line_in_plane :=
    A.line_in_plane


/--
The axiom field is exactly the existing production formulation
`WylerI7IntersectionLine`.
-/
theorem hilbertWyler_wylerI7IntersectionLine
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo] :
    WylerI7IntersectionLine Geo := by

  intro pi a b hab hapi hbpi P hPpi
    alpha beta
    haalpha hPalpha
    hbbeta hPbeta

  cases
      A.wyler_i7_intersection_line
        pi a b hab
        hapi hbpi
        P hPpi
        alpha beta
        haalpha hPalpha
        hbbeta hPbeta with
  | intro k hk =>
      exact
        Exists.intro k
          (And.intro
            ((hk P).mpr
              (And.intro hPalpha hPbeta))
            (And.intro
              (by
                intro X hXk
                exact ((hk X).mp hXk).1)
              (And.intro
                (by
                  intro X hXk
                  exact ((hk X).mp hXk).2)
                (by
                  intro X
                  constructor
                  case mp =>
                    intro hXboth
                    exact (hk X).mpr hXboth
                  case mpr =>
                    intro hXk
                    exact (hk X).mp hXk))))


set_option linter.style.haveILetI false

/--
Wyler I.7 implies Smith I.5.

This is a theorem of the Hilbert-Wyler theory, not an axiom.
-/
theorem hilbertWyler_implies_smithI5
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo] :
    SmithI5Statement Geo := by

  letI : SmithIncidenceCore Geo :=
    hilbertWyler_smithIncidenceCore
      (Geo := Geo)

  have hWyler : WylerI7IntersectionLine Geo :=
    hilbertWyler_wylerI7IntersectionLine
      (Geo := Geo)

  exact
    (wylerI7IntersectionLine_iff_smithI5
      (Geo := Geo)).mp hWyler


/--
Hilbert-Wyler incidence implies the full Steinitz exchange law for
`SmithSpan`.

Again, exchange is derived theory.
-/
theorem hilbertWyler_implies_smithSpanExchange
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo] :
    SmithSpanExchange Geo := by

  letI : SmithIncidenceCore Geo :=
    hilbertWyler_smithIncidenceCore
      (Geo := Geo)

  have hI5 : SmithI5Statement Geo :=
    hilbertWyler_implies_smithI5
      (Geo := Geo)

  exact
    smithI5_implies_smithSpanExchange
      (Geo := Geo)
      hI5

set_option linter.style.haveILetI true

end Geometry

import CGJteamLab.HilbertWylerTheory
import CGJteamLab.HilbertDimensionFreeIncidence

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Compatibility between the old dimension-free incidence package
# and the Hilbert-Wyler axiom/theory split

This module is migration-only infrastructure.

It provides explicit translations in both directions between

    HilbertDimensionFreeIncidence

and

    HilbertWylerAxioms.

No global instances are declared here.  In particular, the two
translations are not registered simultaneously with typeclass search,
which avoids an instance cycle during the E4 refactor.
-/

set_option linter.style.haveILetI false

/--
The old production dimension-free incidence package implies the new
Hilbert-Wyler axiom package.

The common incidence fields are copied directly.  The old Smith I5 field
is converted to the full Wyler I.7 intersection-line theorem and then
restricted to the minimal extensional intersection statement used as the
new primitive axiom.
-/
theorem hilbertWylerAxioms_of_dimensionFree
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [D : HilbertDimensionFreeIncidence Geo] :
    HilbertWylerAxioms Geo := by

  let C : SmithIncidenceCore Geo :=
    smithIncidenceCore_of_dimensionFree
      (Geo := Geo)

  have hI5 : SmithI5Statement Geo :=
    smithI5_of_dimensionFree
      (Geo := Geo)

  have hWyler : WylerI7IntersectionLine Geo := by
    letI : SmithIncidenceCore Geo := C
    exact
      (wylerI7IntersectionLine_iff_smithI5
        (Geo := Geo)).mpr hI5

  constructor

  case two_points_on_each_line =>
    exact D.two_points_on_each_line

  case three_noncollinear_on_plane =>
    exact D.three_noncollinear_on_plane

  case plane_through =>
    exact D.plane_through

  case plane_unique =>
    exact D.plane_unique

  case line_in_plane =>
    exact D.line_in_plane

  case wyler_i7_intersection_line =>
    intro pi a b hab hapi hbpi P hPpi
      alpha beta
      haalpha hPalpha
      hbbeta hPbeta

    cases
        hWyler
          pi a b hab
          hapi hbpi
          P hPpi
          alpha beta
          haalpha hPalpha
          hbbeta hPbeta with
    | intro k hk =>
        exact
          Exists.intro k
            (fun X =>
              Iff.symm
                (hk.2.2.2 X))


set_option linter.style.haveILetI true

/--
The new Hilbert-Wyler axiom package implies the old production
dimension-free incidence package.

This direction is the one used to keep old downstream E4 modules
compiling while their assumptions are migrated.  Smith I5 is supplied
by `HilbertWylerTheory`, not by a new axiom.
-/
theorem hilbertDimensionFreeIncidence_of_hilbertWyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : HilbertWylerAxioms Geo] :
    HilbertDimensionFreeIncidence Geo where

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

  smith_i5 :=
    hilbertWyler_implies_smithI5
      (Geo := Geo)

end Geometry

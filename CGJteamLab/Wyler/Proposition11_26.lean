import CGJteamLab.Proposition11_26
import CGJteamLab.HilbertWyler3DCompatibility

namespace Geometry

universe u

variable (Geo : Geometry.Geo.{u})

/-!
# Euclid XI.26 - Hilbert-Wyler route

The audited direct XI.26 proof is already parametric in
`HilbertSpaceIncidence`.

Its proposition-level incidence is routed through `HilbertWylerAxioms`
without duplicating the metric/order proof.

The hybrid incidence package uses the common Hilbert-Wyler incidence
fields for:

* two points on every ambient line;
* a point on every plane (derived from Wyler plane nondegeneracy);
* plane through three noncollinear points;
* uniqueness of that plane;
* line-in-plane closure.

The two specifically three-dimensional Hilbert fields not contained in
the dimension-free Wyler package are retained from the ambient Hilbert
3D instance:

* the second common point of two intersecting planes (Hilbert I.7);
* existence of four noncoplanar points (Hilbert I.8).

This does not claim an arbitrary-dimensional XI.26 theorem.  It shows
that the 3D XI.26 construction factors through the common Hilbert-Wyler
incidence front end while retaining its established spatial metric core.
-/


/--
Replace the common incidence part of a Hilbert three-space by the
corresponding Hilbert-Wyler fields, retaining only the genuinely 3D
Hilbert I.7/I.8 fields from the original spatial incidence package.
-/
theorem hilbertSpaceIncidence_routed_through_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    (HSI : HilbertSpaceIncidence Geo)
    (W : HilbertWylerAxioms Geo) :
    HilbertSpaceIncidence Geo where

  two_points_on_each_line :=
    W.two_points_on_each_line

  plane_through :=
    W.plane_through

  point_on_each_plane := by
    intro pi
    cases W.three_noncollinear_on_plane pi with
    | intro A hA =>
        cases hA with
        | intro B hB =>
            cases hB with
            | intro C hData =>
                exact Exists.intro A hData.1

  plane_unique :=
    W.plane_unique

  line_in_plane :=
    W.line_in_plane

  plane_second_common_point :=
    HSI.plane_second_common_point

  four_noncoplanar :=
    HSI.four_noncoplanar


/--
XI.26 with the common spatial incidence fields explicitly routed through
the Hilbert-Wyler package.

The metric and order layers are the already established Hilbert 3D ones.
-/
theorem euclid_proposition_11_26_wyler_core
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    [W : HilbertWylerAxioms Geo]
    (D E C F A B : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B) :
    exists L H0 : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H0 E D C C D F F D E := by

  let HSIw : HilbertSpaceIncidence Geo :=
    hilbertSpaceIncidence_routed_through_wyler
      (Geo := Geo) HSI W

  exact
    euclid_proposition_11_26
      (Geo := Geo)
      (HSI := HSIw)
      (HSO := HSO)
      (HSC := HSC)
      D E C F A B
      hTri hAB


/--
Hilbert 3D public corollary.

The Hilbert-Wyler incidence package is derived from the existing Hilbert
three-space by `hilbertWylerAxioms_of_hilbert3D`, so no additional public
geometric axiom is assumed.
-/
theorem euclid_proposition_11_26_wyler
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (D E C F A B : Geo.Point)
    (hTri : HilbertTrihedralConfiguration Geo D E C F)
    (hAB : Ne A B) :
    exists L H0 : Geo.Point,
      HilbertTrihedralRealizesThreeAngles
        Geo A B L H0 E D C C D F F D E := by

  let W : HilbertWylerAxioms Geo :=
    hilbertWylerAxioms_of_hilbert3D
      (Geo := Geo)

  exact
    euclid_proposition_11_26_wyler_core
      (Geo := Geo)
      (W := W)
      D E C F A B
      hTri hAB

end Geometry

import CGJteamLab.HilbertDimensionFreeWyler

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Dimension-free affine carrier helpers

The production Smith/Wyler layer already proves existence of a plane
through a line and a point outside that line:

  `smithCore_plane_through_line_and_external_point`.

For downstream E4 work we also need the corresponding uniqueness fact
and one immediate carrier-absorption corollary.

These statements are entirely dimension-free and incidence-theoretic.
They contain no order, congruence, perpendicularity, parallel axiom,
metric structure, reflection, or dimension assumption.
-/

/--
A primitive plane containing a line `l` and a point `P` outside `l` is
unique.

This is the uniqueness companion to
`smithCore_plane_through_line_and_external_point`.
-/
theorem smithCore_plane_unique_of_line_and_external_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [C : SmithIncidenceCore Geo]
    (l : Geo.Line)
    (P : Geo.Point)
    (hPl : Not (H.OnLine P l))
    (pi rho : S.Plane)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hPpi : S.OnPlane P pi)
    (hlrho : HilbertLineInPlane Geo l rho)
    (hPrho : S.OnPlane P rho) :
    pi = rho := by

  have hABExists :=
    C.two_points_on_each_line l

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

  have hAl :
      H.OnLine A l :=
    hABData.2.1

  have hBl :
      H.OnLine B l :=
    hABData.2.2

  have hABP :
      Not (PrimCollinear Geo A B P) := by

    intro hCol

    have hPonL :
        H.OnLine P l :=
      smithCore_on_line_of_collinear_with_two
        (Geo := Geo)
        A B P
        hAB
        l
        hAl hBl
        hCol

    exact hPl hPonL

  exact
    C.plane_unique
      A B P
      hABP
      pi rho
      (hlpi A hAl)
      (hlpi B hBl)
      hPpi
      (hlrho A hAl)
      (hlrho B hBl)
      hPrho


/--
Production-wrapper form of line-plus-external-point plane uniqueness.

The Smith core is reconstructed from
`HilbertDimensionFreeIncidence`; no additional assumption is introduced.
-/
theorem hilbert_dimension_free_plane_unique_of_line_and_external_point
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    (l : Geo.Line)
    (P : Geo.Point)
    (hPl : Not (H.OnLine P l))
    (pi rho : S.Plane)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hPpi : S.OnPlane P pi)
    (hlrho : HilbertLineInPlane Geo l rho)
    (hPrho : S.OnPlane P rho) :
    pi = rho := by

  let C : SmithIncidenceCore Geo :=
    smithIncidenceCore_of_dimensionFree
      (Geo := Geo)

  exact
    smithCore_plane_unique_of_line_and_external_point
      (Geo := Geo)
      (C := C)
      l P hPl
      pi rho
      hlpi hPpi
      hlrho hPrho


/--
Carrier absorption for a disjoint coplanar line.

Suppose `r` lies in a plane `N`, while `l` and `r` lie together in a
plane `pi`.  If `l` passes through a point `P` of `N` and `l` is
disjoint from `r`, then the entire line `l` lies in `N`.

Geometrically, disjointness gives `P` outside `r`; therefore both `pi`
and `N` are the unique plane through `r` and the external point `P`.
-/
theorem hilbert_dimension_free_disjoint_coplanar_line_absorbed_by_plane
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HilbertDimensionFreeIncidence Geo]
    (N pi : S.Plane)
    (r l : Geo.Line)
    (P : Geo.Point)
    (hrN : HilbertLineInPlane Geo r N)
    (hrpi : HilbertLineInPlane Geo r pi)
    (hlpi : HilbertLineInPlane Geo l pi)
    (hPl : H.OnLine P l)
    (hPN : S.OnPlane P N)
    (hDisjoint : HilbertLinesDisjoint Geo l r) :
    HilbertLineInPlane Geo l N := by

  have hPnotr :
      Not (H.OnLine P r) := by

    intro hPr

    exact
      hDisjoint
        (Exists.intro P
          (And.intro hPl hPr))

  have hPpi :
      S.OnPlane P pi :=
    hlpi P hPl

  have hPiEqN :
      pi = N :=
    hilbert_dimension_free_plane_unique_of_line_and_external_point
      (Geo := Geo)
      r P hPnotr
      pi N
      hrpi hPpi
      hrN hPN

  rw [hPiEqN] at hlpi

  exact hlpi

end Geometry

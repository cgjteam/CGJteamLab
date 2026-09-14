import CGJteamLab.Wyler.HilbertWylerPerpendicularParallel
import CGJteamLab.Wyler.Proposition11_8

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Euclid XI.18 in Wyler form

If a straight line is perpendicular to a plane, then every plane through
that straight line is perpendicular to the given plane.

The conclusion uses `HilbertSpacePlanesPerpendicular`, the directed
synthetic rendering of Euclid XI.Def.4.

The proof follows Euclid's geometry:

1. the given normal `l` and the second plane `rho` determine a common
   point `O` of `rho` and `pi`;
2. XI.3 gives the exact section line `s = rho cap pi`;
3. since `l` is perpendicular to `pi`, it is perpendicular to `s`;
4. for an arbitrary line `g` in `rho` perpendicular to `s`, the neutral
   coplanar helper gives `g = l` or `g || l`;
5. in the parallel case XI.8 transports perpendicularity to `pi`;
6. uniqueness of the foot identifies the transported foot with the
   original point on the common section.

Thus XI.18 is not made true by definition: it proves that the plane
containing a normal satisfies the universal common-section condition of
Euclid XI.Def.4.
-/

/--
Euclid XI.18, Wyler reconstruction.

If `l` is perpendicular to `pi` at `O` and the plane `rho` contains `l`,
then `rho` is perpendicular to `pi` in the sense of XI.Def.4.
-/
theorem euclid_proposition_11_18_wyler
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [HSI : HilbertSpaceIncidence Geo]
    [_HSO : HilbertSpaceOrder
      (Geo := Geo) (H := H) (S := S)]
    [HSC : HilbertSpaceCongruence
      (Geo := Geo) (H := H) (S := S)]
    [HSE : HilbertSpaceEuclidean Geo]
    (pi rho : S.Plane)
    (l : Geo.Line)
    (O : Geo.Point)
    (hPerp :
      HilbertLinePerpendicularPlaneAt Geo l pi O)
    (hlrho :
      HilbertLineInPlane Geo l rho) :
    HilbertSpacePlanesPerpendicular Geo rho pi := by

  ----------------------------------------------------------------------
  -- Incidence of the given normal foot.
  ----------------------------------------------------------------------

  have hInc :=
    HilbertLinePerpendicularPlaneAt.incidence
      (Geo := Geo) hPerp

  have hOl : H.OnLine O l :=
    hInc.1

  have hOpi : S.OnPlane O pi :=
    hInc.2

  have hOrho : S.OnPlane O rho :=
    hlrho O hOl

  ----------------------------------------------------------------------
  -- rho and pi are distinct: otherwise the normal l would lie in pi.
  ----------------------------------------------------------------------

  have hRhoPi : Ne rho pi := by
    intro hEq

    have hlpi : HilbertLineInPlane Geo l pi := by
      intro X hXl

      have hXrho : S.OnPlane X rho :=
        hlrho X hXl

      rw [hEq] at hXrho
      exact hXrho

    exact
      (hilbertLinePerpendicularPlaneAt_not_in_plane_wyler
        (Geo := Geo)
        l pi O hPerp)
        hlpi

  ----------------------------------------------------------------------
  -- XI.3 / flat meet: the two planes have an exact common section s.
  ----------------------------------------------------------------------

  rcases
      hilbert_plane_intersection_line
        (Geo := Geo)
        rho pi hRhoPi
        O hOrho hOpi
    with
    ⟨s, hOs, hsrho, hspi, hSection⟩

  refine
    ⟨hRhoPi,
     s,
     ?_⟩

  refine
    ⟨hsrho,
     hspi,
     hSection,
     ?_⟩

  ----------------------------------------------------------------------
  -- The given normal l is perpendicular to the common section s.
  ----------------------------------------------------------------------

  have hPerpLS :
      HilbertLinesPerpendicularAt Geo l s O :=
    HilbertLinePerpendicularPlaneAt.perpendicular_to_line
      (Geo := Geo)
      hPerp
      hspi
      hOs

  ----------------------------------------------------------------------
  -- Euclid XI.Def.4: every line g in rho perpendicular to the common
  -- section s is perpendicular to pi.
  ----------------------------------------------------------------------

  intro g F hgrho hPerpGS

  have hEqOrParallel :
      l = g \/
      HilbertSpaceLinesParallel Geo l g :=
    hilbert_coplanar_perpendiculars_to_same_line_eq_or_parallel_wyler
      (Geo := Geo)
      rho
      s l g
      O F
      hsrho
      hlrho
      hgrho
      hPerpLS
      hPerpGS

  rcases hEqOrParallel with hlg | hParallel

  ----------------------------------------------------------------------
  -- Degenerate branch: g is the original normal.
  ----------------------------------------------------------------------

  · subst g

    have hFl : H.OnLine F l :=
      hPerpGS.1

    have hFs : H.OnLine F s :=
      hPerpGS.2.1

    have hFpi : S.OnPlane F pi :=
      hspi F hFs

    have hFO : F = O :=
      hilbertLinePerpendicularPlaneAt_foot_unique_wyler
        (Geo := Geo)
        pi l O F
        hPerp
        hFl
        hFpi

    subst F
    exact hPerp

  ----------------------------------------------------------------------
  -- Proper Euclidean branch: XI.8 transports normality along the
  -- parallel line g.
  ----------------------------------------------------------------------

  · rcases
        euclid_proposition_11_8
          (Geo := Geo)
          l g pi O
          hParallel
          hPerp
      with
      ⟨D, hPerpG⟩

    have hFg : H.OnLine F g :=
      hPerpGS.1

    have hFs : H.OnLine F s :=
      hPerpGS.2.1

    have hFpi : S.OnPlane F pi :=
      hspi F hFs

    have hFD : F = D :=
      hilbertLinePerpendicularPlaneAt_foot_unique_wyler
        (Geo := Geo)
        pi g D F
        hPerpG
        hFg
        hFpi

    simpa [hFD] using hPerpG

end Geometry

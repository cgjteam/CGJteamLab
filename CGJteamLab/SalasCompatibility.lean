import CGJteamLab.SalasToSmith

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Compatibility bridge from Sancho de Salas incidence

The existing dimension-free Smith/Wyler development is packaged in the
historical project class `HilbertDimensionFreeIncidence`.

After introducing the source-based `SalasIncidence` interface, that old
package no longer needs to be assumed independently: LP1-LP3 provide its
incidence core, while LP4 implies Smith I5 through `SalasToSmith`.

This file introduces no new axiom.  It exists only so that the current
production Smith/Wyler and E4 code can be reused without rewriting it
while the foundations are migrated to the Salas interface.
-/

/--
Sancho de Salas LP1-LP4 supply the complete existing
`HilbertDimensionFreeIncidence` compatibility package.
-/
theorem salas_implies_dimensionFreeIncidence
    [H : HilbertIncidence Geo]
    [HP : HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : SalasIncidence Geo] :
    HilbertDimensionFreeIncidence Geo where

  two_points_on_each_line :=
    A.two_points_on_each_line

  three_noncollinear_on_plane :=
    A.three_noncollinear_on_each_plane

  plane_through := by
    intro P Q R hPQR

    rcases
        A.plane_through_unique
          P Q R hPQR with
      ⟨pi, hPpi, hQpi, hRpi, _hUnique⟩

    exact ⟨pi, hPpi, hQpi, hRpi⟩

  plane_unique := by
    intro P Q R hPQR pi rho
      hPpi hQpi hRpi
      hPrho hQrho hRrho

    rcases
        A.plane_through_unique
          P Q R hPQR with
      ⟨tau, _hPtau, _hQtau, _hRtau, hUnique⟩

    have hPiTau : pi = tau :=
      hUnique pi hPpi hQpi hRpi

    have hRhoTau : rho = tau :=
      hUnique rho hPrho hQrho hRrho

    exact hPiTau.trans hRhoTau.symm

  line_in_plane :=
    A.line_in_plane

  smith_i5 :=
    salas_implies_smithI5
      (Geo := Geo)

end Geometry

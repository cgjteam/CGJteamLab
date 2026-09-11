import CGJteamLab.SalasAxioms
import CGJteamLab.HilbertDimensionFreeWyler

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

/-!
# Bridge from Sancho de Salas incidence to the Smith incidence interface

This file connects the source-based LP1-LP4 incidence axioms recorded in
`SalasAxioms.lean` with the existing dimension-free Smith/Wyler proof
machinery.

No new geometric axiom is introduced here.

The bridge has two parts:

1. LP1-LP3 supply the fields of `SmithIncidenceCore`.
2. LP4 gives `WylerI7SecondCommonPoint`; the already proved equivalence
   then yields `SmithI5Statement`.

The ambient project still assumes the existing Hilbert point-line
incidence layer.  In particular, `HilbertPlaneIncidence` is retained as
the Hilbert base over which the Salas extension is being added.
-/

/--
LP1-LP3 of Sancho de Salas supply the existing Smith incidence core.
-/
theorem salas_to_smithIncidenceCore
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : SalasIncidence Geo] :
    SmithIncidenceCore Geo where

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


/--
Salas LP4 implies the point-level Wyler I.7 second-common-point form.

LP4 gives the exact intersection line of the two constructed planes.
Every line contains two distinct points by LP1, hence at least one point
of that intersection line is different from the prescribed point `P`.
-/
theorem salas_lp4_implies_wylerI7SecondCommonPoint
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [A : SalasIncidence Geo] :
    WylerI7SecondCommonPoint Geo := by

  intro pi a b hab hapi hbpi P hPpi
    alpha beta
    haalpha hPalpha
    hbbeta hPbeta

  rcases
      A.lp4
        pi
        a b hab
        hapi hbpi
        P hPpi
        alpha beta
        haalpha hPalpha
        hbbeta hPbeta with
    ⟨m, hm⟩

  rcases
      A.two_points_on_each_line m with
    ⟨U, V, hUV, hUm, hVm⟩

  by_cases hUP : U = P

  · have hVP : Ne V P := by
      intro hVP
      apply hUV
      exact hUP.trans hVP.symm

    have hVab :
        S.OnPlane V alpha /\
        S.OnPlane V beta :=
      (hm V).mp hVm

    exact
      ⟨V, hVP, hVab.1, hVab.2⟩

  · have hUab :
        S.OnPlane U alpha /\
        S.OnPlane U beta :=
      (hm U).mp hUm

    exact
      ⟨U, hUP, hUab.1, hUab.2⟩


/--
Sancho de Salas LP1-LP4 imply Smith I5 over the existing Hilbert base.

The proof uses the already established production equivalence between
the Wyler second-common-point formulation and Smith I5.
-/
theorem salas_implies_smithI5
    [H : HilbertIncidence Geo]
    [HilbertPlaneIncidence Geo]
    [S : HilbertSpacePrimitive Geo]
    [SalasIncidence Geo] :
    SmithI5Statement Geo := by

  have hWyler :
      WylerI7SecondCommonPoint Geo :=
    salas_lp4_implies_wylerI7SecondCommonPoint
      (Geo := Geo)

  exact
    wylerI7SecondCommonPoint_implies_smithI5
      (Geo := Geo)
      (C :=
        salas_to_smithIncidenceCore
          (Geo := Geo))
      hWyler

end Geometry

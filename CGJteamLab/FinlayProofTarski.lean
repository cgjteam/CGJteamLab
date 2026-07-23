import CGJteamLab.MidsegmentParallelTarski

/-!
# Finlay's proof via Tarski

This module states the midpoint and collinearity assumptions in
Tarski's primitive language. The explicit bridge from `TarskiBase`
is used only when a result from the shared `GeometryBase` language
is needed.
-/

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Geo)
variable [HilbertIncidence Geo]
variable [HilbertCongruence Geo]
variable [TarskiGeometryBaseBridge Geo]

/-- Finlay's proof using the Tarski-based midsegment theorem. -/
theorem FinlayTarski
    (A B C E F G P D : Geo.Point)
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hGP : G ≠ P)
    (hAPne : A ≠ P)
    (hBE : TarskiCollinear Geo B G E)
    (hCF : TarskiCollinear Geo C G F)
    (hAP : TarskiCollinear Geo A D P)
    (hBC : TarskiCollinear Geo B D C) :
    IsMedian Geo A D B C ∧
    TarskiCollinear Geo A G D := by
  have hBEGeometry : Collinear Geo B G E :=
    collinear_of_tarski Geo B G E hBE
  have hCFGeometry : Collinear Geo C G F :=
    collinear_of_tarski Geo C G F hCF
  have hAPGeometry : Collinear Geo A D P :=
    collinear_of_tarski Geo A D P hAP
  have hBCGeometry : Collinear Geo B D C :=
    collinear_of_tarski Geo B D C hBC

  have hCFG : Collinear Geo C F G :=
    CollinearRotate Geo C G F hCFGeometry
  have hBEG : Collinear Geo B E G :=
    CollinearRotate Geo B G E hBEGeometry

  have hFG : Geo.Parallel F G B P :=
    MidsegmentTheoremTarski Geo A B P F G hF hG
  have hCG : Geo.Parallel C G B P :=
    ParallelCollinearLeft Geo F G C B P hFG hCFG
  have hEG : Geo.Parallel E G C P :=
    MidsegmentTheoremTarski Geo A C P E G hE hG
  have hBG : Geo.Parallel B G C P :=
    ParallelCollinearLeft Geo E G B C P hEG hBEG

  have h₁ : Geo.Parallel B P C G :=
    ParallelSymmetry Geo C G B P hCG
  have h₂ : Geo.Parallel B G P C :=
    ParallelSwapSecondLine Geo B G C P hBG
  have hPar : IsParallelogram Geo B P C G :=
    ParallelogramOfParallel Geo B P C G h₁ h₂

  have hAGP : Collinear Geo A G P :=
    collinear_of_tarski Geo A G P
      (tarski_midpoint_collinear Geo G A P hG)
  have hIntAP : IsIntersection Geo A P B C D :=
    And.intro hAPGeometry hBCGeometry
  have hIntPG : IsIntersection Geo P G B C D :=
    IntersectionOnSameLine Geo A G P B C D hAPne hAGP hIntAP

  have hMid : IsMidpoint Geo D B C :=
    ParallelogramDiagonals
      Geo B P C G D hPar hIntPG.right hIntPG.left
  have hMedian : IsMedian Geo A D B C :=
    MidpointMedian Geo A B C D hMid
  have hPG : Collinear Geo P D G := hIntPG.left
  have hAGD : Collinear Geo A G D :=
    CollinearTrans Geo A G P D hGP hAGP hPG
  have hAGDTarski : TarskiCollinear Geo A G D :=
    tarski_collinear_of_geometry Geo A G D hAGD

  exact And.intro hMedian hAGDTarski

end Tarski

end Geometry

import CGJteamLab.MidsegmentParallelSuppes
import CGJteamLab.FinlayCommon

/-!
# Finlay's proof via Suppes

This module is the Suppes adapter for the single proof in
`FinlayCommon`.  Its only mathematical task is to obtain the two
midsegment parallelisms from `MidsegmentTheoremSuppes`.
-/

namespace Geometry

universe u

variable (Geo : Geo)
variable [HilbertIncidence Geo]
variable [HilbertOrder Geo]
variable [Suppes.SuppesGeometry Geo.Point]
variable [SuppesMidsegmentBridge Geo]

/-- Finlay's proof using the Suppes-based Midsegment Theorem. -/
theorem FinlaySuppes
    (A B C E F G P D : Geo.Point)
    (hE : IsMidpoint Geo E A C)
    (hF : IsMidpoint Geo F A B)
    (hG : IsMidpoint Geo G A P)
    (hGP : G ≠ P)
    (hAPne : A ≠ P)
    (hCGne : C ≠ G)
    (hBGne : B ≠ G)
    (hBE : Collinear Geo B G E)
    (hCF : Collinear Geo C G F)
    (hAP : Collinear Geo A D P)
    (hBC : Collinear Geo B D C) :
    IsMedian Geo A D B C ∧
    Collinear Geo A G D := by
  have hFG : Geo.Parallel F G B P :=
    MidsegmentTheoremSuppes Geo A B P F G hF hG
  have hEG : Geo.Parallel E G C P :=
    MidsegmentTheoremSuppes Geo A C P E G hE hG
  have hAGP : Collinear Geo A G P :=
    midpoint_collinear Geo A P G hG

  exact
    FinlayFromMidsegmentParallels
      Geo A B C E F G P D
      hFG hEG hAGP
      hGP hAPne hCGne hBGne
      hBE hCF hAP hBC

end Geometry

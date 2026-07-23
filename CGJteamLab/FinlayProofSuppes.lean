import CGJteamLab.MidsegmentParallelSuppes

namespace Geometry

universe u

variable (Geo : Geo)
variable [HilbertIncidence Geo]
variable [HilbertOrder Geo]
variable [Suppes.SuppesGeometry Geo.Point]
variable [SuppesMidsegmentBridge Geo]

/-- Finlay's proof using the Suppes-based midsegment theorem. -/
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
  IsMedian Geo A D B C ∧ Collinear Geo A G D := by
  have hCFG : Collinear Geo C F G := CollinearRotate Geo C G F hCF
  have hBEG : Collinear Geo B E G := CollinearRotate Geo B G E hBE

  have hFG : Geo.Parallel F G B P :=
    MidsegmentTheoremSuppes Geo A B P F G hF hG
  have hCG : Geo.Parallel C G B P :=
    ParallelCollinearLeft Geo F G C B P hCGne hFG hCFG
  have hEG : Geo.Parallel E G C P :=
    MidsegmentTheoremSuppes Geo A C P E G hE hG
  have hBG : Geo.Parallel B G C P :=
    ParallelCollinearLeft Geo E G B C P hBGne hEG hBEG

  have h1 : Geo.Parallel B P C G :=
    ParallelSymmetry Geo C G B P hCG
  have h2 : Geo.Parallel B G P C :=
    ParallelSwapSecondLine Geo B G C P hBG
  have hPar : IsParallelogram Geo B P C G :=
    ParallelogramOfParallel Geo B P C G h1 h2

  have hAGP : Collinear Geo A G P :=
    midpoint_collinear Geo A P G hG
  have hIntAP : IsIntersection Geo A P B C D := And.intro hAP hBC
  have hIntPG : IsIntersection Geo P G B C D :=
    IntersectionOnSameLine Geo A G P B C D hAPne hAGP hIntAP

  have hMid : IsMidpoint Geo D B C :=
    ParallelogramDiagonals Geo B P C G D hPar hIntPG.right hIntPG.left
  have hMedian : IsMedian Geo A D B C :=
    MidpointMedian Geo A B C D hMid
  have hPG : Collinear Geo P D G := hIntPG.left
  have hAGD : Collinear Geo A G D :=
    CollinearTrans Geo A G P D hGP hAGP hPG
  exact And.intro hMedian hAGD

end Geometry

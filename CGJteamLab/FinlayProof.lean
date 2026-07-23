import CGJteamLab.MidsegmentParallel
import CGJteamLab.FinlayCommon

/-!
# Finlay's proof via Hilbert

This module is the Hilbert adapter for the single proof in
`FinlayCommon`.  Its only mathematical task is to obtain the two
midsegment parallelisms from `MidsegmentTheorem`.
-/

namespace Geometry

universe u

variable (Geo : Geo)
variable [HilbertIncidence Geo]
variable [HilbertCongruence Geo]

/-- Finlay's proof using the Hilbert-based Midsegment Theorem. -/
theorem Finlay
    (A B C E F G P D : Geo.Point)
    (hE : HilbertIsMidpoint Geo E A C)
    (hF : HilbertIsMidpoint Geo F A B)
    (hG : HilbertIsMidpoint Geo G A P)
    (hGFA : ¬ Collinear Geo G F A)
    (hGEA : ¬ Collinear Geo G E A)
    (hGP : G ≠ P)
    (hBE : Collinear Geo B G E)
    (hCF : Collinear Geo C G F)
    (hAP : Collinear Geo A D P)
    (hBC : Collinear Geo B D C) :
    IsMedian Geo A D B C ∧
    Collinear Geo A G D := by
  have hCGne : C ≠ G := by
    intro hCG
    subst C
    exact
      hGEA
        (PrimCollinearSymm Geo A E G
          (HilbertOrder.between_incidence
            A E G hE.left).2.2.2.1)
  have hBGne : B ≠ G := by
    intro hBG
    subst B
    exact
      hGFA
        (PrimCollinearSymm Geo A F G
          (HilbertOrder.between_incidence
            A F G hF.left).2.2.2.1)
  have hFG : Geo.Parallel F G B P :=
    MidsegmentTheorem Geo A B P F G hF hG hGFA
  have hEG : Geo.Parallel E G C P :=
    MidsegmentTheorem Geo A C P E G hE hG hGEA
  have hAGP : Collinear Geo A G P :=
    midpoint_collinear Geo A P G
      (midpoint_of_hilbert Geo G A P hG)
  have hAPne : A ≠ P :=
    (HilbertOrder.between_incidence A G P hG.left).2.2.1

  exact
    FinlayFromMidsegmentParallels
      Geo A B C E F G P D
      hFG hEG hAGP
      hGP hAPne hCGne hBGne
      hBE hCF hAP hBC

end Geometry

import CGJteamLab.MidsegmentParallelTarski
import CGJteamLab.FinlayCommon

/-!
# Finlay's proof via Tarski

This module is the Tarski adapter for the single proof in
`FinlayCommon`.  It obtains the two parallelisms from
`MidsegmentTheoremTarski` and performs only the explicit conversions
between Tarski's primitive language and `GeometryBase`.
-/

namespace Geometry

namespace Tarski

universe u

variable (Geo : Geometry.Geo)
variable [HilbertIncidence Geo]
variable [HilbertCongruence Geo]
variable [TarskiGeometryBaseBridge Geo]

/-- Finlay's proof using the Tarski-based Midsegment Theorem. -/
theorem FinlayTarski
    (A B C E F G P D : Geo.Point)
    (hE : TarskiIsMidpoint Geo E A C)
    (hF : TarskiIsMidpoint Geo F A B)
    (hG : TarskiIsMidpoint Geo G A P)
    (hGFA : ¬ TarskiCollinear Geo G F A)
    (hGEA : ¬ TarskiCollinear Geo G E A)
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
  have hGFAGeometry : ¬ Collinear Geo G F A :=
    fun h => hGFA (tarski_collinear_of_geometry Geo G F A h)
  have hGEAGeometry : ¬ Collinear Geo G E A :=
    fun h => hGEA (tarski_collinear_of_geometry Geo G E A h)

  have hCGne : C ≠ G := by
    intro hCG
    subst C
    exact
      hGEAGeometry
        (PrimCollinearSymm Geo A E G
          (HilbertOrder.between_incidence
            A E G hE.left).2.2.2.1)
  have hBGne : B ≠ G := by
    intro hBG
    subst B
    exact
      hGFAGeometry
        (PrimCollinearSymm Geo A F G
          (HilbertOrder.between_incidence
            A F G hF.left).2.2.2.1)
  have hFG : Geo.Parallel F G B P :=
    MidsegmentTheoremTarski Geo A B P F G hF hG hGFAGeometry
  have hEG : Geo.Parallel E G C P :=
    MidsegmentTheoremTarski Geo A C P E G hE hG hGEAGeometry
  have hAGP : Collinear Geo A G P :=
    collinear_of_tarski Geo A G P
      (tarski_midpoint_collinear Geo G A P hG)

  have hResult :=
    FinlayFromMidsegmentParallels
      Geo A B C E F G P D
      hFG hEG hAGP
      hGP hAPne hCGne hBGne
      hBEGeometry hCFGeometry hAPGeometry hBCGeometry

  exact
    ⟨hResult.1,
      tarski_collinear_of_geometry Geo A G D hResult.2⟩

end Tarski

end Geometry

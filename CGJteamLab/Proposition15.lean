import CGJteamLab.HilbertBookZero

namespace Geometry

variable (Geo : Geometry.Geo)

theorem euclid_proposition_15
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E : Geo.Point)
    (hAEB : Geo.Between A E B)
    (hCED : Geo.Between C E D)
    (hAEC : ¬ PrimCollinear Geo A E C) :
    Geo.AngleCongruent A E C B E D ∧
    Geo.AngleCongruent C E B D E A := by

  have hFirst :
      Geo.AngleCongruent A E C B E D :=
    hilbert_vertical_angles
      Geo A E C B D
      hAEB
      hCED
      hAEC

  have hBEC : Geo.Between B E A :=
    (HilbertOrder.between_incidence
      A E B hAEB).2.2.2.2

  have hCEB :
      ¬ PrimCollinear Geo C E B := by
    intro h

    have hEBC :
        PrimCollinear Geo E B C :=
      PrimCollinearCycle Geo C E B h

    have hAEBcol :
        PrimCollinear Geo A E B :=
      (HilbertOrder.between_incidence
        A E B hAEB).2.2.2.1

    have hEB : E ≠ B :=
      (HilbertOrder.between_incidence
        A E B hAEB).2.1

    have hAECcol :
        PrimCollinear Geo A E C :=
      hilbert_primCollinear_trans
        Geo A E B C
        hEB
        hAEBcol
        hEBC

    exact hAEC hAECcol

  have hSecond :
      Geo.AngleCongruent C E B D E A :=
    hilbert_vertical_angles
      Geo C E B D A
      hCED
      hBEC
      hCEB

  exact ⟨hFirst, hSecond⟩
end Geometry

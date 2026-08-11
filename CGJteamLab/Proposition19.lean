import CGJteamLab.Proposition18

namespace Geometry

variable (Geo : Geometry.Geo)

theorem euclid_proposition_19
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hAngle :
      HilbertAngleLess Geo A C B A B C) :
    HilbertSegmentLess Geo A B A C := by

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (by
        intro h
        exact hABC
          (PrimCollinearRotate Geo A C B h))

  rcases
      hilbert_segment_trichotomy
        Geo
        A B
        A C
        hAC with
    hEq | hABltAC | hACltAB

  ·
    have hIso :
        Geo.AngleCongruent A B C A C B :=
      hilbert_isosceles_base_angles
        Geo
        A B C
        hABC
        hEq

    have hACB :
        ¬ PrimCollinear Geo A C B := by
      intro h
      exact hABC
        (PrimCollinearRotate Geo A C B h)

    have hSame :
        HilbertAngleLess Geo A C B A C B :=
      hilbert_angleLess_transport_right
        Geo
        A C B
        A B C
        A C B
        hAngle
        hACB
        hIso

    exact
      False.elim
        ((hilbert_angleLess_irrefl
            Geo A C B)
          hSame)

  ·
    exact hABltAC

  ·
    have hACB :
        ¬ PrimCollinear Geo A C B := by
      intro h
      exact hABC
        (PrimCollinearRotate Geo A C B h)

    have hOpp :
        HilbertAngleLess Geo A B C A C B :=
      euclid_proposition_18
        Geo
        A C B
        hACB
        hACltAB

    have hCycle :
        HilbertAngleLess Geo A C B A C B :=
      hilbert_angleLess_trans
        Geo
        A C B
        A B C
        A C B
        hAngle
        hOpp

    exact
      False.elim
        ((hilbert_angleLess_irrefl
            Geo A C B)
          hCycle)


end Geometry

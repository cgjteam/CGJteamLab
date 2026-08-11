import CGJteamLab.Proposition16

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Synthetic Hilbert representation of the statement that two angles
are together less than two right angles.

The witness E extends the second angle to its supplementary angle.
The first angle is then required to be strictly smaller than that
supplement.
-/
def HilbertAnglesLessThanTwoRightAngles
    [HilbertIncidence Geo]
    (A O B C P D : Geo.Point) : Prop :=
  ∃ E : Geo.Point,
    Geo.Between D P E ∧
    HilbertAngleLess Geo A O B C P E


theorem euclid_proposition_17_BAC_ACB
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C) :
    HilbertAnglesLessThanTwoRightAngles
      Geo B A C A C B := by

  have hBCA :
      ¬ PrimCollinear Geo B C A := by
    intro h

    have hACB :
        PrimCollinear Geo A C B :=
      PrimCollinearSymm Geo B C A h

    have hABC' :
        PrimCollinear Geo A B C :=
      PrimCollinearRotate Geo A C B hACB

    exact hABC hABC'

  have hBC : B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C A hBCA

  rcases
      HilbertOrder.between_extension
        B C hBC with
    ⟨D, hBCD⟩

  refine ⟨D, hBCD, ?_⟩

  exact
    euclid_proposition_16_first
      Geo A B C D hABC hBCD

theorem euclid_proposition_17_ABC_ACB
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C) :
    HilbertAnglesLessThanTwoRightAngles
      Geo A B C A C B := by

  have hBCA :
      ¬ PrimCollinear Geo B C A := by
    intro h

    have hACB :
        PrimCollinear Geo A C B :=
      PrimCollinearSymm Geo B C A h

    have hABC' :
        PrimCollinear Geo A B C :=
      PrimCollinearRotate Geo A C B hACB

    exact hABC hABC'

  have hBC : B ≠ C :=
    hilbert_noncollinear_ne_first
      Geo B C A hBCA

  rcases
      HilbertOrder.between_extension
        B C hBC with
    ⟨D, hBCD⟩

  refine ⟨D, hBCD, ?_⟩

  exact
    euclid_proposition_16_second
      Geo A B C D hABC hBCD

theorem euclid_proposition_17_BAC_ABC
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C) :
    HilbertAnglesLessThanTwoRightAngles
      Geo B A C A B C := by

  have hCBA :
      ¬ PrimCollinear Geo C B A := by
    intro h

    have hABC' :
        PrimCollinear Geo A B C :=
      PrimCollinearSymm Geo C B A h

    exact hABC hABC'

  have hCB : C ≠ B :=
    hilbert_noncollinear_ne_first
      Geo C B A hCBA

  rcases
      HilbertOrder.between_extension
        C B hCB with
    ⟨E, hCBE⟩

  refine ⟨E, hCBE, ?_⟩

  have hACB :
      ¬ PrimCollinear Geo A C B := by
    intro h

    have hABC' :
        PrimCollinear Geo A B C :=
      PrimCollinearRotate Geo A C B h

    exact hABC hABC'

  have hLessCAB :
      HilbertAngleLess Geo C A B A B E :=
    euclid_proposition_16_first
      Geo A C B E hACB hCBE

  rcases hLessCAB with
    ⟨hCABnc, hABEnc, X, hMeet, hAngle⟩

  have hBACnc :
      ¬ PrimCollinear Geo B A C := by
    intro h
    exact hABC
      (PrimCollinearSwap Geo B A C h)

  have hAngle' :
      Geo.AngleCongruent B A C A B X :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo C A B A B X).mp hAngle

  exact
    ⟨hBACnc,
      hABEnc,
      X,
      hMeet,
      hAngle'⟩

theorem euclid_proposition_17
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C) :
    HilbertAnglesLessThanTwoRightAngles Geo B A C A B C ∧
    HilbertAnglesLessThanTwoRightAngles Geo B A C A C B ∧
    HilbertAnglesLessThanTwoRightAngles Geo A B C A C B := by

  have h1 :
      HilbertAnglesLessThanTwoRightAngles
        Geo B A C A B C :=
    euclid_proposition_17_BAC_ABC
      Geo A B C hABC

  have h2 :
      HilbertAnglesLessThanTwoRightAngles
        Geo B A C A C B :=
    euclid_proposition_17_BAC_ACB
      Geo A B C hABC

  have h3 :
      HilbertAnglesLessThanTwoRightAngles
        Geo A B C A C B :=
    euclid_proposition_17_ABC_ACB
      Geo A B C hABC

  exact ⟨h1, h2, h3⟩

end Geometry

import CGJteamLab.HilbertAngleComparison

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Euclid, Book I, Proposition 16, first opposite interior angle.

If `ABC` is a nondegenerate triangle and `BC` is extended through `C`
to `D`, then the exterior angle `ACD` is greater than the opposite
interior angle `BAC`.
-/
theorem euclid_proposition_16_first
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hBCD : Geo.Between B C D) :
    HilbertAngleLess Geo B A C A C D := by

  rcases
      hilbert_exterior_angle_aux
        Geo A B C hABC with
    ⟨M, E,
      hAMC,
      hAMMC,
      hBME,
      hBMME,
      hAngle⟩

  have hParallel :
      Geo.Parallel A B C E :=
    hilbert_exterior_angle_aux_parallel
      Geo A B C M E
      hABC
      hAMC
      hBME
      hAngle

  exact
    hilbert_exterior_angle_less
      Geo A B C D M E
      hABC
      hAMC
      hBME
      hBCD
      hAngle
      hParallel

/--
Euclid, Book I, Proposition 16, second opposite interior angle.

If `ABC` is a nondegenerate triangle and `BC` is extended through `C`
to `D`, then the exterior angle `ACD` is greater than the other
opposite interior angle `ABC`.
-/
theorem euclid_proposition_16_second
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hBCD : Geo.Between B C D) :
    HilbertAngleLess Geo A B C A C D := by

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B
      (fun h =>
        hABC
          (PrimCollinearRotate Geo A C B h))

  rcases HilbertOrder.between_extension A C hAC with
    ⟨F, hACF⟩

  have hBACnc :
      ¬ PrimCollinear Geo B A C := by
    intro h
    exact hABC
      (PrimCollinearSwap Geo B A C h)

  have hLessBCF :
      HilbertAngleLess Geo A B C B C F :=
    euclid_proposition_16_first
      Geo
      B A C F
      hBACnc
      hACF

  have hBCDdata :=
    HilbertOrder.between_incidence B C D hBCD

  have hDCA :
      Geo.Between D C B :=
    hBCDdata.2.2.2.2

  have hACDnc :
      ¬ PrimCollinear Geo A C D := by
    intro hACD

    have hBCDcol :
        PrimCollinear Geo B C D :=
      hBCDdata.2.2.2.1

    have hCD : C ≠ D :=
      hBCDdata.2.1

    have hCDB :
        PrimCollinear Geo C D B :=
      PrimCollinearCycle
        Geo B C D hBCDcol

    have hACB :
        PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo A C D B
        hCD
        hACD
        hCDB

    exact hABC
      (PrimCollinearRotate Geo A C B hACB)

  have hVerticalRaw :
      Geo.AngleCongruent A C D F C B :=
    VerticalAngles
      Geo
      A C D F B
      hACF
      hDCA
      hACDnc

  have hVerticalSymm :
      Geo.AngleCongruent F C B A C D :=
    Geo.angle_congruent_symmetry
      A C D
      F C B
      hVerticalRaw

  have hVertical :
      Geo.AngleCongruent B C F A C D :=
    (Geo.angle_congruent_reverse_first
      F C B A C D).mp
      hVerticalSymm

  exact
    hilbert_angleLess_transport_right
      Geo
      A B C
      B C F
      A C D
      hLessBCF
      hACDnc
      hVertical

/--
Euclid, Book I, Proposition 16.

If one side of a triangle is produced, the exterior angle is greater
than either of the two interior opposite angles.
-/
theorem euclid_proposition_16
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hBCD : Geo.Between B C D) :
    HilbertAngleLess Geo B A C A C D ∧
    HilbertAngleLess Geo A B C A C D := by

  have hFirst :
      HilbertAngleLess Geo B A C A C D :=
    euclid_proposition_16_first
      Geo A B C D
      hABC
      hBCD

  have hSecond :
      HilbertAngleLess Geo A B C A C D :=
    euclid_proposition_16_second
      Geo A B C D
      hABC
      hBCD

  exact ⟨hFirst, hSecond⟩

end Geometry

import CGJteamLab.Proposition16

namespace Geometry

variable (Geo : Geometry.Geo)

theorem euclid_proposition_18
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C : Geo.Point)
    (hABC : ¬ PrimCollinear Geo A B C)
    (hABltAC : HilbertSegmentLess Geo A B A C) :
    HilbertAngleLess Geo A C B A B C := by

  rcases hABltAC with
    ⟨D, hADC, hAB_AD⟩

  have hABD :
      ¬ Collinear Geo A B D := by
    intro hCol

    have hADCcol :
        PrimCollinear Geo A D C :=
      (HilbertOrder.between_incidence
        A D C hADC).2.2.2.1

    rcases hCol with
      ⟨l, hAl, hBl, hDl⟩

    have hAD : A ≠ D :=
      (HilbertOrder.between_incidence
        A D C hADC).1

    have hCl :
        HilbertIncidence.OnLine C l :=
      hilbert_collinear_on_line
        Geo
        A D C
        l
        hAD
        hAl
        hDl
        hADCcol

    exact hABC
      ⟨l, hAl, hBl, hCl⟩

  have hIso :
      Geo.AngleCongruent A B D A D B :=
    hilbert_isosceles_base_angles
      Geo
      A B D
      hABD
      hAB_AD

  have hBCD :
      ¬ PrimCollinear Geo B C D := by
    intro h

    have hADCcol :
        PrimCollinear Geo A D C :=
      (HilbertOrder.between_incidence
        A D C hADC).2.2.2.1

    have hDC : D ≠ C :=
      (HilbertOrder.between_incidence
        A D C hADC).2.1

    rcases h with
      ⟨l, hBl, hCl, hDl⟩

    have hDCA :
        PrimCollinear Geo D C A :=
      PrimCollinearCycle Geo A D C hADCcol

    have hAl :
        HilbertIncidence.OnLine A l :=
      hilbert_collinear_on_line
        Geo
        D C A
        l
        hDC
        hDl
        hCl
        hDCA

    exact hABC
      ⟨l, hAl, hBl, hCl⟩

  have hCDA :
      Geo.Between C D A :=
    (HilbertOrder.between_incidence
      A D C hADC).2.2.2.2

  have hBCD_BDA :
      HilbertAngleLess Geo B C D B D A :=
    euclid_proposition_16_second
      Geo B C D A hBCD hCDA

  have hRayCDA :
      HilbertSameRay Geo C D A :=
    hilbert_sameRay_of_between
      Geo C D A hCDA

  rcases hBCD_BDA with
    ⟨hBCDnc, hBDAnc, X, hInside, hAngle⟩

  have hAngleBCD_BCA :
      Geo.Angle B C D =
      Geo.Angle B C A :=
    hilbert_angle_eq_of_sameRay_second
      Geo C B D A hRayCDA

  have hAngle' :
      Geo.AngleCongruent B C A B D X := by
    unfold Geometry.Geo.AngleCongruent at hAngle ⊢
    rw [← hAngleBCD_BCA]
    exact hAngle

  have hBCA :
      ¬ PrimCollinear Geo B C A := by
    intro hBCAcol

    have hCAB :
        PrimCollinear Geo C A B :=
      PrimCollinearCycle Geo B C A hBCAcol

    have hABC' :
        PrimCollinear Geo A B C :=
      PrimCollinearCycle Geo C A B hCAB

    exact hABC hABC'

  have hBCA_BDA :
      HilbertAngleLess Geo B C A B D A := by
    exact
      ⟨hBCA,
        hBDAnc,
        ⟨X,
          hInside,
          hAngle'⟩⟩

  have hBDA_ABD :
      Geo.AngleCongruent B D A A B D :=
    (Geo.angle_congruent_reverse_first
      A D B
      A B D).mp
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        A B D
        A D B
        hIso)

  have hBCA_ABD :
      HilbertAngleLess Geo B C A A B D :=
    hilbert_angleLess_transport_right
      Geo
      B C A
      B D A
      A B D
      hBCA_BDA
      (by
        intro h
        exact hABD h)
      hBDA_ABD

  have hBDA_nc :
      ¬ PrimCollinear Geo B D A := by
    intro h

    have hDAB :
        PrimCollinear Geo D A B :=
      PrimCollinearCycle Geo B D A h

    have hABD' :
        PrimCollinear Geo A B D :=
      PrimCollinearCycle Geo D A B hDAB

    exact hABD hABD'

  have hBD : B ≠ D :=
    hilbert_noncollinear_ne_first
      Geo B D A hBDA_nc

  have hRayBDD :
      HilbertSameRay Geo B D D :=
    hilbert_sameRay_refl
      Geo B D hBD.symm

  have hInsideBD :
      HilbertRayMeetsSegment Geo B D A C :=
    ⟨D, hADC, hRayBDD⟩

  have hABD_ABC :
      HilbertAngleLess Geo A B D A B C :=
    hilbert_interior_angle_less
      Geo
      B D A C
      hABC
      hInsideBD
  have hInsideBD :
      HilbertRayMeetsSegment Geo B D A C :=
    ⟨D, hADC, hRayBDD⟩

  have hABD_ABC :
      HilbertAngleLess Geo A B D A B C :=
    hilbert_interior_angle_less
      Geo
      B D A C
      hABC
      hInsideBD

  have hFinal :
      HilbertAngleLess Geo B C A A B C :=
    hilbert_angleLess_trans
      Geo
      B C A
      A B D
      A B C
      hBCA_ABD
      hABD_ABC

  rcases hFinal with
    ⟨hBCAnc, hABCnc, X, hInsideFinal, hAngleFinal⟩

  have hACBnc :
      ¬ PrimCollinear Geo A C B := by
    intro h

    have hABC' :
        PrimCollinear Geo A B C :=
      PrimCollinearRotate Geo A C B h

    exact hABC hABC'

  have hAngleFinal' :
      Geo.AngleCongruent A C B A B X :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo B C A A B X).mp hAngleFinal

  exact
    ⟨hACBnc,
      hABCnc,
      X,
      hInsideFinal,
      hAngleFinal'⟩


end Geometry

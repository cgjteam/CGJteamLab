import CGJteamLab.HilbertBookZero

namespace Geometry

variable (Geo : Geometry.Geo)

/--
Hilbert form of the perpendicular construction needed for Euclid I.12.

Given distinct points A and B on a line base and a point P outside
base, there exist a point H on base and a point R on base such that
RH forms a right angle with HP.
-/
theorem hilbert_perpendicular_from_point_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B P : Geo.Point)
    (base : Geo.Line)
    (hAB : A ≠ B)
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hPbase : ¬ HilbertIncidence.OnLine P base) :
    ∃ H R : Geo.Point,
      HilbertIncidence.OnLine H base ∧
      HilbertIncidence.OnLine R base ∧
      HilbertRightAngle Geo R H P := by

  ----------------------------------------------------------------------
  -- P is not collinear with A and B.
  ----------------------------------------------------------------------

  have hABP :
      ¬ Collinear Geo A B P :=
    hilbert_not_collinear_of_off_line
      Geo A B P base
      hAB
      hAbase
      hBbase
      hPbase

  have hPAB :
      ¬ PrimCollinear Geo P A B := by
    intro h

    have hABP' :
        PrimCollinear Geo A B P :=
      PrimCollinearCycle
        Geo P A B h

    exact hABP hABP'

  have hPA : P ≠ A := by
    intro h
    subst P
    exact hPbase hAbase

  have hBA : B ≠ A :=
    hAB.symm

  ----------------------------------------------------------------------
  -- Choose S on the extension of PA through A.
  -- Then P and S lie on opposite sides of base.
  ----------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        P A hPA with
    ⟨S, hPAS⟩

  have hPASData :=
    HilbertOrder.between_incidence
      P A S hPAS

  have hSA : S ≠ A :=
    hPASData.2.1.symm

  have hSbase :
      ¬ HilbertIncidence.OnLine S base := by

    intro hSbase

    have hSAP :
        Collinear Geo S A P :=
      PrimCollinearSymm
        Geo P A S
        hPASData.2.2.2.1

    have hPbase' :
        HilbertIncidence.OnLine P base :=
      hilbert_collinear_on_line
        Geo S A P base
        hSA
        hSbase
        hAbase
        hSAP

    exact hPbase hPbase'

  have hOppositePS :
      HilbertOppositeSide Geo P S base :=
    ⟨hPbase,
     hSbase,
     ⟨A, hPAS, hAbase⟩⟩

  ----------------------------------------------------------------------
  -- Reflect the direction AP across base at A.
  ----------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        P A B
        B A S
        hPAB
        hBA
        base
        hBbase
        hAbase
        hSbase with
    ⟨Q₀, hQ₀SSame, hAngleQ₀, hUniqueQ₀⟩

  ----------------------------------------------------------------------
  -- Lay off AQ congruent AP on the constructed ray AQ₀.
  ----------------------------------------------------------------------

  have hAQ₀ : A ≠ Q₀ := by
    intro h
    subst Q₀
    exact hQ₀SSame.1 hAbase

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        P A
        A Q₀
        hAQ₀ with
    ⟨Q, hRayQ₀Q, hAQ_PA⟩

  ----------------------------------------------------------------------
  -- Q lies on the same side of base as S.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A Q₀ hAQ₀ with
    ⟨rayLine, hAray, hQ₀ray⟩

  have hBoffRay :
      ¬ HilbertIncidence.OnLine B rayLine := by

    intro hBray

    have hEq :
        base = rayLine :=
      HilbertPlaneIncidence.line_unique
        A B hAB
        base rayLine
        hAbase hBbase
        hAray hBray

    have hQ₀base :
        HilbertIncidence.OnLine Q₀ base := by
      rw [hEq]
      exact hQ₀ray

    exact hQ₀SSame.1 hQ₀base

  have hRayQ₀Q₀ :
      HilbertSameRay Geo A Q₀ Q₀ :=
    hilbert_sameRay_refl
      Geo A Q₀ hAQ₀.symm

  have hQ₀QSame :
      HilbertSameSide Geo Q₀ Q base :=
    hilbert_sameRay_points_sameSide
      Geo
      A Q₀
      Q₀ Q
      B
      rayLine base
      hAray hQ₀ray
      hAbase hBbase
      hBoffRay
      hRayQ₀Q₀
      hRayQ₀Q

  have hSQ₀Same :
      HilbertSameSide Geo S Q₀ base :=
    hilbert_sameSide_symm
      Geo Q₀ S base hQ₀SSame

  have hSQSame :
      HilbertSameSide Geo S Q base :=
    hilbert_sameSide_trans
      Geo S Q₀ Q base
      hSQ₀Same
      hQ₀QSame

  ----------------------------------------------------------------------
  -- Hence P and Q lie on opposite sides of base.
  ----------------------------------------------------------------------

  have hOppositePQ :
      HilbertOppositeSide Geo P Q base :=
    hilbert_oppositeSide_transport_right
      Geo P S Q base
      hOppositePS
      hSQSame

  ----------------------------------------------------------------------
  -- Let H be the intersection of segment PQ with base.
  ----------------------------------------------------------------------

  rcases hOppositePQ.2.2 with
    ⟨H, hPHQ, hHbase⟩

  have hPHQData :=
    HilbertOrder.between_incidence
      P H Q hPHQ

  ----------------------------------------------------------------------
  -- Replace Q₀ by Q in the reflected angle.
  ----------------------------------------------------------------------

  have hAngleBAQ₀_BAQ :
      Geo.Angle B A Q₀ =
      Geo.Angle B A Q :=
    hilbert_angle_eq_of_sameRay_second
      Geo A B Q₀ Q hRayQ₀Q

  have hAnglePAQ :
      Geo.AngleCongruent P A B B A Q := by

    unfold Geometry.Geo.AngleCongruent
      at hAngleQ₀ ⊢

    rw [← hAngleBAQ₀_BAQ]

    exact hAngleQ₀

  have hAnglePAB_QAB :
      Geo.AngleCongruent P A B Q A B :=
    (Geo.angle_congruent_reverse_second
      P A B B A Q).mp hAnglePAQ

  ----------------------------------------------------------------------
  -- AP is congruent to AQ.
  ----------------------------------------------------------------------

  have hAP_AQ :
      Geo.Congruent A P A Q := by

    have hAQ_AP :
        Geo.Congruent A Q A P :=
      CongruentSwapSecond
        Geo A Q P A hAQ_PA

    exact
      hilbert_congruent_symmetry
        Geo A Q A P hAQ_AP

  ----------------------------------------------------------------------
  -- SAS for triangles APB and AQB gives BP congruent BQ.
  ----------------------------------------------------------------------

  have hAPB :
      ¬ Collinear Geo A P B := by
    intro h
    exact hABP
      (PrimCollinearRotate Geo A P B h)

  have hQAB :
      ¬ Collinear Geo A Q B := by

    intro hQAB

    rcases hQAB with
      ⟨l, hAl, hQl, hBl⟩

    have hEq :
        l = base :=
      HilbertPlaneIncidence.line_unique
        A B hAB
        l base
        hAl hBl
        hAbase hBbase

    have hQbase :
        HilbertIncidence.OnLine Q base := by
      rw [← hEq]
      exact hQl

    exact hOppositePQ.2.1 hQbase

  have hAB_AB :
      Geo.Congruent A B A B :=
    hilbert_congruent_reflexive
      Geo A B

  have hSAS_PAB_QAB :=
    SAS
      Geo
      A P B
      A Q B
      hAPB
      hQAB
      hAP_AQ
      hAnglePAB_QAB
      hAB_AB

  have hPB_QB :
      Geo.Congruent P B Q B :=
    hSAS_PAB_QAB.sideBC

  have hBP_BQ :
      Geo.Congruent B P B Q :=
    CongruentReverseBoth
      Geo P B Q B hPB_QB

  ----------------------------------------------------------------------
  -- The line AB is the perpendicular-bisector axis of P and Q.
  -- Hence H is the midpoint of PQ.
  ----------------------------------------------------------------------

  have hPH_HQ :
      Geo.Congruent P H H Q :=
    hilbert_equidistant_line_bisects_segment
      Geo
      A B P Q H
      base
      hAB
      hAbase
      hBbase
      hHbase
      hOppositePQ
      hAP_AQ
      hBP_BQ
      hPHQ

  ----------------------------------------------------------------------
  -- Generic final step.
  --
  -- If R is a point of base distinct from H and equidistant from
  -- P and Q, then RH is perpendicular to PQ at H.
  ----------------------------------------------------------------------

  have hRight_of_equidistant
      (R : Geo.Point)
      (hRbase : HilbertIncidence.OnLine R base)
      (hRH : R ≠ H)
      (hRP_RQ : Geo.Congruent R P R Q) :
      HilbertRightAngle Geo R H P := by

    rcases
        HilbertOrder.between_extension
          R H hRH with
      ⟨C, hRHC⟩

    have hRHP :
        ¬ Collinear Geo R H P :=
      hilbert_not_collinear_of_off_line
        Geo R H P base
        hRH
        hRbase
        hHbase
        hOppositePQ.1

    have hRHQ :
        ¬ Collinear Geo R H Q :=
      hilbert_not_collinear_of_off_line
        Geo R H Q base
        hRH
        hRbase
        hHbase
        hOppositePQ.2.1

    have hRH_RH :
        Geo.Congruent R H R H :=
      hilbert_congruent_reflexive
        Geo R H

    have hHP_HQ :
        Geo.Congruent H P H Q :=
      CongruentReverseFirst
        Geo P H H Q hPH_HQ

    have hSSS :=
      HilbertSSS
        Geo
        R H P
        R H Q
        hRHP
        hRH_RH
        hHP_HQ
        hRP_RQ

    have hRHP_RHQ :
        Geo.AngleCongruent R H P R H Q :=
      hSSS.2.angleB

    have hQHP :
        Geo.Between Q H P :=
      hPHQData.2.2.2.2

    have hVertical :
        Geo.AngleCongruent R H Q C H P :=
      VerticalAngles
        Geo
        R H Q C P
        hRHC
        hQHP
        hRHQ

    have hRHQ_PHC :
        Geo.AngleCongruent R H Q P H C :=
      (Geo.angle_congruent_reverse_second
        R H Q C H P).mp hVertical

    have hRHP_PHC :
        Geo.AngleCongruent R H P P H C :=
      Geometry.Geo.angle_congruent_transitivity
        Geo
        R H P
        R H Q
        P H C
        hRHP_RHQ
        hRHQ_PHC

    exact
      ⟨C,
       hRHC,
       hRHP_PHC⟩

  ----------------------------------------------------------------------
  -- At least one of A and B is distinct from H.
  ----------------------------------------------------------------------

  by_cases hHA : H = A

  ·
    have hBH : B ≠ H := by
      intro hBH'
      apply hAB
      exact hHA.symm.trans hBH'.symm

    exact
      ⟨H,
       B,
       hHbase,
       hBbase,
       hRight_of_equidistant
         B
         hBbase
         hBH
         hBP_BQ⟩

  ·
    have hAH : A ≠ H := by
      intro hAH'
      exact hHA hAH'.symm

    exact
      ⟨H,
       A,
       hHbase,
       hAbase,
       hRight_of_equidistant
         A
         hAbase
         hAH
         hAP_AQ⟩


/--
Euclid, Book I, Proposition 12.

From a point outside a given straight line, a perpendicular can be
drawn to the given straight line.
-/
theorem euclid_proposition_12
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B P : Geo.Point)
    (base : Geo.Line)
    (hAB : A ≠ B)
    (hAbase : HilbertIncidence.OnLine A base)
    (hBbase : HilbertIncidence.OnLine B base)
    (hPbase : ¬ HilbertIncidence.OnLine P base) :
    ∃ H R : Geo.Point,
      HilbertIncidence.OnLine H base ∧
      HilbertIncidence.OnLine R base ∧
      HilbertRightAngle Geo R H P := by

  exact
    hilbert_perpendicular_from_point_exists
      Geo
      A B P
      base
      hAB
      hAbase
      hBbase
      hPbase

end Geometry

import CGJteamLab.HilbertBookZero
import CGJteamLab.Proposition19
import CGJteamLab.Proposition23

namespace Geometry

universe u

variable {Geo : Geometry.Geo}

/-!
Euclid, Book I, Proposition 24.

If two triangles have two corresponding sides congruent, but the
included angle of the first triangle is greater than the included
angle of the second, then the third side of the first triangle is
greater than the third side of the second.

Formal orientation:

  AB ~= DE
  AC ~= DF
  angle EDF < angle BAC
  ---------------------
  EF < BC
-/

------------------------------------------------------------------------
-- Auxiliary construction
------------------------------------------------------------------------

theorem euclid_proposition_24_construct_aux
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hAngle :
      HilbertAngleLess Geo E D F B A C) :
    exists X H : Geo.Point,
      HilbertRayMeetsSegment Geo A X B C /\
      HilbertSameRay Geo A X H /\
      Geo.Congruent A H A C /\
      Geo.AngleCongruent B A H E D F := by

  rcases hAngle with
    ⟨_hEDF, _hBAC, X, hMeet, hAngleEDF_BAX⟩

  rcases hMeet with
    ⟨Y, hBYC, hRayAXY⟩

  have hAX : A ≠ X :=
    Ne.symm hRayAXY.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        A C
        A X
        hAX with
    ⟨H, hRayAXH, hAH_AC⟩

  have hBAX_EDF :
      Geo.AngleCongruent B A X E D F :=
    Geo.angle_congruent_symmetry
      E D F
      B A X
      hAngleEDF_BAX

  have hBAH_EDF :
      Geo.AngleCongruent B A H E D F := by

    unfold Geometry.Geo.AngleCongruent at hBAX_EDF ⊢

    rw [
      ← hilbert_angle_eq_of_sameRay_second
        Geo A B X H hRayAXH
    ]

    exact hBAX_EDF

  exact
    ⟨X, H,
      ⟨Y, hBYC, hRayAXY⟩,
      hRayAXH,
      hAH_AC,
      hBAH_EDF⟩


------------------------------------------------------------------------
-- SAS part:
-- construct H on the interior ray and prove BH ~= EF.
------------------------------------------------------------------------

theorem euclid_proposition_24_sas_aux
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hDEF : Not (PrimCollinear Geo D E F))
    (hAB_DE : Geo.Congruent A B D E)
    (hAC_DF : Geo.Congruent A C D F)
    (hAngle :
      HilbertAngleLess Geo E D F B A C) :
    exists X H : Geo.Point,
      HilbertRayMeetsSegment Geo A X B C /\
      HilbertSameRay Geo A X H /\
      Geo.Congruent A H A C /\
      Geo.Congruent B H E F := by

  rcases
      euclid_proposition_24_construct_aux
        (Geo := Geo)
        A B C D E F
        hAngle with
    ⟨X, H, hMeet, hRayAXH, hAH_AC, hBAH_EDF⟩

  ----------------------------------------------------------------------
  -- AH ~= AC ~= DF.
  ----------------------------------------------------------------------

  have hAH_DF :
      Geo.Congruent A H D F :=
    bookZero_congruenceTransitive
      Geo
      A H
      A C
      D F
      hAH_AC
      hAC_DF

  ----------------------------------------------------------------------
  -- The interior ray AX cannot coincide with AB.
  --
  -- If B,A,X were collinear, then the intersection point Y of ray AX
  -- with the open segment BC would also lie on AB.  Since B-Y-C,
  -- this would force A,B,C to be collinear.
  ----------------------------------------------------------------------

  have hBAX :
      Not (PrimCollinear Geo B A X) := by

    rcases hMeet with
      ⟨Y, hBYC, hRayAXY⟩

    intro hBAXcol

    have hAX :
        A ≠ X :=
      Ne.symm hRayAXY.1

    have hAXY :
        PrimCollinear Geo A X Y :=
      hRayAXY.2.2.1

    have hBAY :
        PrimCollinear Geo B A Y :=
      hilbert_primCollinear_trans
        Geo
        B A X Y
        hAX
        hBAXcol
        hAXY

    have hABY :
        PrimCollinear Geo A B Y :=
      PrimCollinearSwap
        Geo B A Y hBAY

    have hBY :
        B ≠ Y :=
      (HilbertOrder.between_incidence
        B Y C hBYC).1

    have hBYCcol :
        PrimCollinear Geo B Y C :=
      (HilbertOrder.between_incidence
        B Y C hBYC).2.2.2.1

    have hABCcol :
        PrimCollinear Geo A B C :=
      hilbert_primCollinear_trans
        Geo
        A B Y C
        hBY
        hABY
        hBYCcol

    exact hABC hABCcol

  ----------------------------------------------------------------------
  -- Replace the ray AX by the same ray AH.
  ----------------------------------------------------------------------

  have hBA :
      B ≠ A :=
    hilbert_noncollinear_ne_first
      Geo B A X hBAX

  have hRayABB :
      HilbertSameRay Geo A B B :=
    hilbert_sameRay_refl
      Geo A B hBA

  have hBAH :
      Not (PrimCollinear Geo B A H) :=
    hilbert_noncollinear_of_sameRays
      Geo
      B A X
      B H
      hBAX
      hRayABB
      hRayAXH

  ----------------------------------------------------------------------
  -- SAS expects the first triangle in the orientation A,B,H.
  ----------------------------------------------------------------------

  have hABH :
      Not (PrimCollinear Geo A B H) := by
    intro h
    exact
      hBAH
        (PrimCollinearSwap
          Geo A B H h)

  ----------------------------------------------------------------------
  -- SAS:
  --
  -- AB ~= DE
  -- AH ~= DF
  -- angle BAH ~= angle EDF
  --
  -- therefore BH ~= EF.
  ----------------------------------------------------------------------

  have hSAS :=
    hilbert_sas_third_side_and_angle
      Geo
      A B H
      D E F
      hABH
      hDEF
      hAB_DE
      hAH_DF
      hBAH_EDF

  exact
    ⟨X, H,
      hMeet,
      hRayAXH,
      hAH_AC,
      hSAS.1⟩

------------------------------------------------------------------------
-- Hinge step:
-- AH ~= AC and AH lies on an interior ray of angle BAC imply BH < BC.
------------------------------------------------------------------------

theorem euclid_proposition_24_hinge_case1
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C H Y : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hAHY : Geo.Between A H Y)
    (hBYC : Geo.Between B Y C)
    (hAH_AC : Geo.Congruent A H A C) :
    HilbertSegmentLess Geo B H B C := by

  ----------------------------------------------------------------------
  -- Basic collinear data.
  ----------------------------------------------------------------------

  have hAHYcol :
      PrimCollinear Geo A H Y :=
    (HilbertOrder.between_incidence
      A H Y hAHY).2.2.2.1

  have hBYCcol :
      PrimCollinear Geo B Y C :=
    (HilbertOrder.between_incidence
      B Y C hBYC).2.2.2.1

  have hHY :
      H ≠ Y :=
    (HilbertOrder.between_incidence
      A H Y hAHY).2.1

  have hYC :
      Y ≠ C :=
    (HilbertOrder.between_incidence
      B Y C hBYC).2.1

  ----------------------------------------------------------------------
  -- C, Y, H are noncollinear.
  ----------------------------------------------------------------------

  have hCYH :
      Not (PrimCollinear Geo C Y H) := by

    intro hCYHcol

    have hHYA :
        PrimCollinear Geo H Y A := by

      have hAYH :
          PrimCollinear Geo A Y H :=
        PrimCollinearRotate
          Geo A H Y hAHYcol

      exact
        PrimCollinearSymm
          Geo A Y H hAYH

    have hHYC :
        PrimCollinear Geo H Y C :=
      PrimCollinearSymm
        Geo C Y H hCYHcol

    have hYAC :
        PrimCollinear Geo Y A C :=
      bookZero_24_collinear4
        Geo
        H Y A C
        hHYA
        hHYC
        hHY

    have hYCA :
        PrimCollinear Geo Y C A :=
      PrimCollinearRotate
        Geo Y A C hYAC

    have hYCB :
        PrimCollinear Geo Y C B := by

      have hBCY :
          PrimCollinear Geo B C Y :=
        PrimCollinearRotate
          Geo B Y C hBYCcol

      exact
        PrimCollinearSymm
          Geo B C Y hBCY

    have hCAB :
        PrimCollinear Geo C A B :=
      bookZero_24_collinear4
        Geo
        Y C A B
        hYCA
        hYCB
        hYC

    have hCBA :
        PrimCollinear Geo C B A :=
      PrimCollinearRotate
        Geo C A B hCAB

    have hABCcol :
        PrimCollinear Geo A B C :=
      PrimCollinearSymm
        Geo C B A hCBA

    exact hABC hABCcol

  ----------------------------------------------------------------------
  -- A, H, C are noncollinear.
  ----------------------------------------------------------------------

  have hAH :
      A ≠ H :=
    (HilbertOrder.between_incidence
      A H Y hAHY).1

  have hAHC :
      Not (PrimCollinear Geo A H C) := by

    intro hAHCcol

    have hHCYcol :
        PrimCollinear Geo H C Y :=
      bookZero_24_collinear4
        Geo
        A H C Y
        hAHCcol
        hAHYcol
        hAH

    have hHYC :
        PrimCollinear Geo H Y C :=
      PrimCollinearRotate
        Geo H C Y hHCYcol

    have hCYHcol :
        PrimCollinear Geo C Y H :=
      PrimCollinearSymm
        Geo H Y C hHYC

    exact hCYH hCYHcol

  ----------------------------------------------------------------------
  -- Further noncollinearity orientations.
  ----------------------------------------------------------------------

  have hHCY :
      Not (PrimCollinear Geo H C Y) := by

    intro hHCYcol

    have hHYC :
        PrimCollinear Geo H Y C :=
      PrimCollinearRotate
        Geo H C Y hHCYcol

    have hCYHcol :
        PrimCollinear Geo C Y H :=
      PrimCollinearSymm
        Geo H Y C hHYC

    exact hCYH hCYHcol

  have hACH :
      Not (PrimCollinear Geo A C H) := by

    intro hACHcol

    have hAHCcol :
        PrimCollinear Geo A H C :=
      PrimCollinearRotate
        Geo A C H hACHcol

    exact hAHC hAHCcol

  have hCAH :
      Not (PrimCollinear Geo C A H) := by

    intro hCAHcol

    have hCHA :
        PrimCollinear Geo C H A :=
      PrimCollinearRotate
        Geo C A H hCAHcol

    have hAHCcol :
        PrimCollinear Geo A H C :=
      PrimCollinearSymm
        Geo C H A hCHA

    exact hAHC hAHCcol

  ----------------------------------------------------------------------
  -- Reverse A-H-Y.
  ----------------------------------------------------------------------

  have hYHA :
      Geo.Between Y H A :=
    (HilbertOrder.between_incidence
      A H Y hAHY).2.2.2.2

  ----------------------------------------------------------------------
  -- First I.16:
  --
  -- triangle C-Y-H, with HY extended through H to A:
  --
  -- angle YCH < angle CHA.
  ----------------------------------------------------------------------

  have hYCH_CHA :
      HilbertAngleLess Geo Y C H C H A :=
    euclid_proposition_16_first
      Geo
      C Y H A
      hCYH
      hYHA

  ----------------------------------------------------------------------
  -- Reverse angle YCH to HCY.
  ----------------------------------------------------------------------

  have hYCH_HCY :
      Geo.AngleCongruent Y C H H C Y := by

    have hRefl :
        Geo.AngleCongruent Y C H Y C H :=
      Geometry.Geo.angle_congruent_reflexive
        Geo Y C H

    exact
      (Geo.angle_congruent_reverse_second
        Y C H
        Y C H).mp
        hRefl

  have hHCY_YCH :
      Geo.AngleCongruent H C Y Y C H :=
    Geo.angle_congruent_symmetry
      Y C H
      H C Y
      hYCH_HCY

  have hHCY_CHA :
      HilbertAngleLess Geo H C Y C H A :=
    hilbert_angleLess_transport_left
      Geo
      Y C H
      H C Y
      C H A
      hYCH_CHA
      hHCY
      hHCY_YCH

  ----------------------------------------------------------------------
  -- Reverse angle CHA to AHC.
  ----------------------------------------------------------------------

  have hCHA_AHC :
      Geo.AngleCongruent C H A A H C := by

    have hRefl :
        Geo.AngleCongruent C H A C H A :=
      Geometry.Geo.angle_congruent_reflexive
        Geo C H A

    exact
      (Geo.angle_congruent_reverse_second
        C H A
        C H A).mp
        hRefl

  have hHCY_AHC :
      HilbertAngleLess Geo H C Y A H C :=
    hilbert_angleLess_transport_right
      Geo
      H C Y
      C H A
      A H C
      hHCY_CHA
      hAHC
      hCHA_AHC

  ----------------------------------------------------------------------
  -- AH ~= AC, so triangle A-H-C is isosceles:
  --
  -- angle AHC ~= angle ACH.
  ----------------------------------------------------------------------

  have hIso :
      Geo.AngleCongruent A H C A C H :=
    hilbert_isosceles_base_angles
      Geo
      A H C
      hAHC
      hAH_AC

  have hHCY_ACH :
      HilbertAngleLess Geo H C Y A C H :=
    hilbert_angleLess_transport_right
      Geo
      H C Y
      A H C
      A C H
      hHCY_AHC
      hACH
      hIso

  ----------------------------------------------------------------------
  -- Second I.16:
  --
  -- triangle C-A-H, with AH extended through H to Y:
  --
  -- angle ACH < angle CHY.
  ----------------------------------------------------------------------

  have hACH_CHY :
      HilbertAngleLess Geo A C H C H Y :=
    euclid_proposition_16_first
      Geo
      C A H Y
      hCAH
      hAHY

  ----------------------------------------------------------------------
  -- Therefore:
  --
  -- angle HCY < angle CHY.
  ----------------------------------------------------------------------

  have hHCY_CHY :
      HilbertAngleLess Geo H C Y C H Y :=
    hilbert_angleLess_trans
      Geo
      H C Y
      A C H
      C H Y
      hHCY_ACH
      hACH_CHY

  ----------------------------------------------------------------------
  -- The ray HY meets the open segment CB at Y.
  ----------------------------------------------------------------------

  have hCYB :
      Geo.Between C Y B :=
    (HilbertOrder.between_incidence
      B Y C hBYC).2.2.2.2

  have hHY' :
      H ≠ Y :=
    (HilbertOrder.between_incidence
      A H Y hAHY).2.1

  have hRayHYY :
      HilbertSameRay Geo H Y Y :=
    hilbert_sameRay_refl
      Geo H Y hHY'.symm

  have hInsideHY :
      HilbertRayMeetsSegment Geo H Y C B :=
    ⟨Y, hCYB, hRayHYY⟩

  ----------------------------------------------------------------------
  -- Triangle C-H-B is nondegenerate.
  ----------------------------------------------------------------------

  have hCHB :
      Not (PrimCollinear Geo C H B) := by

    intro hCHBcol

    have hBHC :
        PrimCollinear Geo B H C :=
      PrimCollinearSymm
        Geo C H B hCHBcol

    have hBCH :
        PrimCollinear Geo B C H :=
      PrimCollinearRotate
        Geo B H C hBHC

    have hHCB :
        PrimCollinear Geo H C B :=
      PrimCollinearSymm
        Geo B C H hBCH

    have hBCY :
        PrimCollinear Geo B C Y :=
      PrimCollinearRotate
        Geo B Y C hBYCcol

    have hYCB :
        PrimCollinear Geo Y C B :=
      PrimCollinearSymm
        Geo B C Y hBCY

    have hYBC :
        PrimCollinear Geo Y B C :=
      PrimCollinearRotate
        Geo Y C B hYCB

    have hCBY :
        PrimCollinear Geo C B Y :=
      PrimCollinearSymm
        Geo Y B C hYBC

    have hCB :
        C ≠ B :=
      (HilbertOrder.between_incidence
        B Y C hBYC).2.2.1.symm

    have hHCYcol :
        PrimCollinear Geo H C Y :=
      hilbert_primCollinear_trans
        Geo
        H C B Y
        hCB
        hHCB
        hCBY

    exact hHCY hHCYcol

  ----------------------------------------------------------------------
  -- CHY is a proper interior subangle of CHB.
  ----------------------------------------------------------------------

  have hCHY_CHB :
      HilbertAngleLess Geo C H Y C H B :=
    hilbert_interior_angle_less
      Geo
      H Y C B
      hCHB
      hInsideHY

  ----------------------------------------------------------------------
  -- Combine:
  --
  -- HCY < CHY < CHB.
  ----------------------------------------------------------------------

  have hHCY_CHB :
      HilbertAngleLess Geo H C Y C H B :=
    hilbert_angleLess_trans
      Geo
      H C Y
      C H Y
      C H B
      hHCY_CHY
      hCHY_CHB

  ----------------------------------------------------------------------
  -- Since C-Y-B, rays CY and CB coincide.
  ----------------------------------------------------------------------

  have hRayCYB :
      HilbertSameRay Geo C Y B :=
    hilbert_sameRay_of_between
      Geo C Y B hCYB

  have hHCY_HCB :
      Geo.AngleCongruent H C Y H C B := by

    unfold Geometry.Geo.AngleCongruent

    rw [
      hilbert_angle_eq_of_sameRay_second
        Geo C H Y B hRayCYB
    ]

    exact Relation.EqvGen.refl _

  have hHCBnc :
      Not (PrimCollinear Geo H C B) :=
    fun hHCBcol => by

      have hBCH :
          PrimCollinear Geo B C H :=
        PrimCollinearSymm
          Geo H C B hHCBcol

      have hBHC :
          PrimCollinear Geo B H C :=
        PrimCollinearRotate
          Geo B C H hBCH

      have hCHBcol :
          PrimCollinear Geo C H B :=
        PrimCollinearSymm
          Geo B H C hBHC

      exact hCHB hCHBcol

  have hHCB_HCY :
      Geo.AngleCongruent H C B H C Y :=
    Geo.angle_congruent_symmetry
      H C Y
      H C B
      hHCY_HCB

  have hHCB_CHB :
      HilbertAngleLess Geo H C B C H B :=
    hilbert_angleLess_transport_left
      Geo
      H C Y
      H C B
      C H B
      hHCY_CHB
      hHCBnc
      hHCB_HCY

  ----------------------------------------------------------------------
  -- Reverse HCB to BCH.
  ----------------------------------------------------------------------

  have hHCB_BCH :
      Geo.AngleCongruent H C B B C H := by

    have hRefl :
        Geo.AngleCongruent H C B H C B :=
      Geometry.Geo.angle_congruent_reflexive
        Geo H C B

    exact
      (Geo.angle_congruent_reverse_second
        H C B
        H C B).mp
        hRefl

  have hBCH_HCB :
      Geo.AngleCongruent B C H H C B :=
    Geo.angle_congruent_symmetry
      H C B
      B C H
      hHCB_BCH

  have hBCHnc :
      Not (PrimCollinear Geo B C H) := by

    intro hBCHcol

    have hBHC :
        PrimCollinear Geo B H C :=
      PrimCollinearRotate
        Geo B C H hBCHcol

    have hCHBcol :
        PrimCollinear Geo C H B :=
      PrimCollinearSymm
        Geo B H C hBHC

    exact hCHB hCHBcol

  have hBCH_CHB :
      HilbertAngleLess Geo B C H C H B :=
    hilbert_angleLess_transport_left
      Geo
      H C B
      B C H
      C H B
      hHCB_CHB
      hBCHnc
      hBCH_HCB

  ----------------------------------------------------------------------
  -- Reverse CHB to BHC.
  ----------------------------------------------------------------------

  have hCHB_BHC :
      Geo.AngleCongruent C H B B H C := by

    have hRefl :
        Geo.AngleCongruent C H B C H B :=
      Geometry.Geo.angle_congruent_reflexive
        Geo C H B

    exact
      (Geo.angle_congruent_reverse_second
        C H B
        C H B).mp
        hRefl

  have hBHCnc :
      Not (PrimCollinear Geo B H C) := by

    intro hBHCcol

    have hCHBcol :
        PrimCollinear Geo C H B :=
      PrimCollinearSymm
        Geo B H C hBHCcol

    exact hCHB hCHBcol

  have hBCH_BHC :
      HilbertAngleLess Geo B C H B H C :=
    hilbert_angleLess_transport_right
      Geo
      B C H
      C H B
      B H C
      hBCH_CHB
      hBHCnc
      hCHB_BHC

  ----------------------------------------------------------------------
  -- Proposition I.19:
  --
  -- angle BCH < angle BHC  ==>  BH < BC.
  ----------------------------------------------------------------------

  exact
    euclid_proposition_19
      Geo
      B H C
      hBHCnc
      hBCH_BHC


theorem euclid_proposition_24_hinge_case3
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C H Y : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hAYH : Geo.Between A Y H)
    (hBYC : Geo.Between B Y C)
    (hAH_AC : Geo.Congruent A H A C) :
    HilbertSegmentLess Geo B H B C := by

  ----------------------------------------------------------------------
  -- Basic collinear data.
  ----------------------------------------------------------------------

  have hAYHcol :
      PrimCollinear Geo A Y H :=
    (HilbertOrder.between_incidence
      A Y H hAYH).2.2.2.1

  have hBYCcol :
      PrimCollinear Geo B Y C :=
    (HilbertOrder.between_incidence
      B Y C hBYC).2.2.2.1

  have hYH :
      Y ≠ H :=
    (HilbertOrder.between_incidence
      A Y H hAYH).2.1

  have hYC :
      Y ≠ C :=
    (HilbertOrder.between_incidence
      B Y C hBYC).2.1

  have hAH :
      A ≠ H :=
    (HilbertOrder.between_incidence
      A Y H hAYH).2.2.1

  have hBC :
      B ≠ C :=
    (HilbertOrder.between_incidence
      B Y C hBYC).2.2.1

  ----------------------------------------------------------------------
  -- Reversed betweenness relations.
  ----------------------------------------------------------------------

  have hHYA :
      Geo.Between H Y A :=
    (HilbertOrder.between_incidence
      A Y H hAYH).2.2.2.2

  have hCYB :
      Geo.Between C Y B :=
    (HilbertOrder.between_incidence
      B Y C hBYC).2.2.2.2

  ----------------------------------------------------------------------
  -- Triangle H-C-A is nondegenerate.
  ----------------------------------------------------------------------

  have hHCA :
      Not (PrimCollinear Geo H C A) := by

    intro hHCAcol

    have hHAC :
        PrimCollinear Geo H A C :=
      PrimCollinearRotate
        Geo H C A hHCAcol

    have hHYAcol :
        PrimCollinear Geo H Y A :=
      PrimCollinearSymm
        Geo A Y H hAYHcol

    have hHAY :
        PrimCollinear Geo H A Y :=
      PrimCollinearRotate
        Geo H Y A hHYAcol

    have hACY :
        PrimCollinear Geo A C Y :=
      bookZero_24_collinear4
        Geo
        H A C Y
        hHAC
        hHAY
        hAH.symm

    have hCYA :
        PrimCollinear Geo C Y A :=
      PrimCollinearCycle
        Geo A C Y hACY

    have hCYBcol :
        PrimCollinear Geo C Y B :=
      PrimCollinearSymm
        Geo B Y C hBYCcol

    have hYAB :
        PrimCollinear Geo Y A B :=
      bookZero_24_collinear4
        Geo
        C Y A B
        hCYA
        hCYBcol
        hYC.symm

    have hYBA :
        PrimCollinear Geo Y B A :=
      PrimCollinearRotate
        Geo Y A B hYAB

    have hYBC :
        PrimCollinear Geo Y B C :=
      PrimCollinearSwap
        Geo B Y C hBYCcol

    have hYB :
        Y ≠ B :=
      (HilbertOrder.between_incidence
        B Y C hBYC).1.symm

    have hBAC :
        PrimCollinear Geo B A C :=
      bookZero_24_collinear4
        Geo
        Y B A C
        hYBA
        hYBC
        hYB

    have hABCcol :
        PrimCollinear Geo A B C :=
      PrimCollinearSwap
        Geo B A C hBAC

    exact hABC hABCcol

  ----------------------------------------------------------------------
  -- Triangle C-H-B is nondegenerate.
  ----------------------------------------------------------------------

  have hCHB :
      Not (PrimCollinear Geo C H B) := by

    intro hCHBcol

    -- C-H-B -> H-C-B.
    have hBHC :
        PrimCollinear Geo B H C :=
      PrimCollinearSymm
        Geo C H B hCHBcol

    have hHCB :
        PrimCollinear Geo H C B :=
      PrimCollinearCycle
        Geo B H C hBHC

    -- B-Y-C -> C-B-Y.
    have hYCB :
        PrimCollinear Geo Y C B :=
      PrimCollinearCycle
        Geo B Y C hBYCcol

    have hCBY :
        PrimCollinear Geo C B Y :=
      PrimCollinearCycle
        Geo Y C B hYCB

    have hCB :
        C ≠ B :=
      hBC.symm

    -- H-C-B and C-B-Y -> H-C-Y.
    have hHCYcol :
        PrimCollinear Geo H C Y :=
      hilbert_primCollinear_trans
        Geo
        H C B Y
        hCB
        hHCB
        hCBY

    -- H-C-Y -> Y-H-C.
    have hYCH :
        PrimCollinear Geo Y C H :=
      PrimCollinearSymm
        Geo H C Y hHCYcol

    have hYHC :
        PrimCollinear Geo Y H C :=
      PrimCollinearRotate
        Geo Y C H hYCH

    -- A-Y-H and Y-H-C -> A-Y-C.
    have hAYC :
        PrimCollinear Geo A Y C :=
      hilbert_primCollinear_trans
        Geo
        A Y H C
        hYH
        hAYHcol
        hYHC

    have hACY :
        PrimCollinear Geo A C Y :=
      PrimCollinearRotate
        Geo A Y C hAYC

    have hCYBcol :
        PrimCollinear Geo C Y B :=
      PrimCollinearSymm
        Geo B Y C hBYCcol

    have hCY :
        C ≠ Y :=
      hYC.symm

    -- A-C-Y and C-Y-B -> A-C-B.
    have hACB :
        PrimCollinear Geo A C B :=
      hilbert_primCollinear_trans
        Geo
        A C Y B
        hCY
        hACY
        hCYBcol

    have hABCcol :
        PrimCollinear Geo A B C :=
      PrimCollinearRotate
        Geo A C B hACB

    exact hABC hABCcol

  ----------------------------------------------------------------------
  -- Metric/angle part comes next.
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- At C, ray CY meets the open segment HA at Y.
  --
  -- Hence angle HCY < angle HCA.
  ----------------------------------------------------------------------

  have hRayCYY :
      HilbertSameRay Geo C Y Y :=
    hilbert_sameRay_refl
      Geo C Y hYC

  have hInsideCY :
      HilbertRayMeetsSegment Geo C Y H A :=
    ⟨Y, hHYA, hRayCYY⟩

  have hHCY_HCA :
      HilbertAngleLess Geo H C Y H C A :=
    hilbert_interior_angle_less
      Geo
      C Y H A
      hHCA
      hInsideCY

  ----------------------------------------------------------------------
  -- Since C-Y-B, rays CY and CB coincide.
  ----------------------------------------------------------------------

  have hRayCYB :
      HilbertSameRay Geo C Y B :=
    hilbert_sameRay_of_between
      Geo C Y B hCYB

  have hHCY_HCB :
      Geo.AngleCongruent H C Y H C B := by

    unfold Geometry.Geo.AngleCongruent

    rw [
      hilbert_angle_eq_of_sameRay_second
        Geo C H Y B hRayCYB
    ]

    exact Relation.EqvGen.refl _

  have hHCBnc :
      Not (PrimCollinear Geo H C B) :=
    fun hHCBcol => by

      have hBCH :
          PrimCollinear Geo B C H :=
        PrimCollinearSymm
          Geo H C B hHCBcol

      have hBHC :
          PrimCollinear Geo B H C :=
        PrimCollinearRotate
          Geo B C H hBCH

      have hCHBcol :
          PrimCollinear Geo C H B :=
        PrimCollinearSymm
          Geo B H C hBHC

      exact hCHB hCHBcol

  have hHCB_HCY :
      Geo.AngleCongruent H C B H C Y :=
    Geo.angle_congruent_symmetry
      H C Y
      H C B
      hHCY_HCB

  have hHCB_HCA :
      HilbertAngleLess Geo H C B H C A :=
    hilbert_angleLess_transport_left
      Geo
      H C Y
      H C B
      H C A
      hHCY_HCA
      hHCBnc
      hHCB_HCY

  ----------------------------------------------------------------------
  -- AH ~= AC, so triangle A-H-C is isosceles.
  --
  -- angle AHC ~= angle HCA.
  ----------------------------------------------------------------------

  have hAHC :
      Not (PrimCollinear Geo A H C) := by

    intro hAHCcol

    have hACH :
        PrimCollinear Geo A C H :=
      PrimCollinearRotate
        Geo A H C hAHCcol

    have hHCAcol :
        PrimCollinear Geo H C A :=
      PrimCollinearSymm
        Geo A C H hACH

    exact hHCA hHCAcol

  have hIso :
      Geo.AngleCongruent A H C A C H :=
    hilbert_isosceles_base_angles
      Geo
      A H C
      hAHC
      hAH_AC

  have hAHC_HCA :
      Geo.AngleCongruent A H C H C A :=
    (Geo.angle_congruent_reverse_second
      A H C
      A C H).mp
      hIso

  have hHCA_AHC :
      Geo.AngleCongruent H C A A H C :=
    Geo.angle_congruent_symmetry
      A H C
      H C A
      hAHC_HCA

  have hHCB_AHC :
      HilbertAngleLess Geo H C B A H C :=
    hilbert_angleLess_transport_right
      Geo
      H C B
      H C A
      A H C
      hHCB_HCA
      hAHC
      hHCA_AHC

  ----------------------------------------------------------------------
  -- At H, ray HY meets the open segment CB at Y.
  --
  -- Hence angle CHY < angle CHB.
  ----------------------------------------------------------------------

  have hRayHYY :
      HilbertSameRay Geo H Y Y :=
    hilbert_sameRay_refl
      Geo H Y hYH

  have hInsideHY :
      HilbertRayMeetsSegment Geo H Y C B :=
    ⟨Y, hCYB, hRayHYY⟩

  have hCHY_CHB :
      HilbertAngleLess Geo C H Y C H B :=
    hilbert_interior_angle_less
      Geo
      H Y C B
      hCHB
      hInsideHY

  ----------------------------------------------------------------------
  -- Since H-Y-A, rays HY and HA coincide.
  ----------------------------------------------------------------------

  have hRayHYA :
      HilbertSameRay Geo H Y A :=
    hilbert_sameRay_of_between
      Geo H Y A hHYA

  have hCHY_CHA :
      Geo.AngleCongruent C H Y C H A := by

    unfold Geometry.Geo.AngleCongruent

    rw [
      hilbert_angle_eq_of_sameRay_second
        Geo H C Y A hRayHYA
    ]

    exact Relation.EqvGen.refl _

  have hCHA_AHC :
      Geo.AngleCongruent C H A A H C := by

    have hRefl :
        Geo.AngleCongruent C H A C H A :=
      Geometry.Geo.angle_congruent_reflexive
        Geo C H A

    exact
      (Geo.angle_congruent_reverse_second
        C H A
        C H A).mp
        hRefl

  have hCHY_AHC :
    Geo.AngleCongruent C H Y A H C :=
  Geo.angle_congruent_transitivity
    C H Y
    C H A
    A H C
    hCHY_CHA
    hCHA_AHC


  have hAHC_CHY :
      Geo.AngleCongruent A H C C H Y :=
    Geo.angle_congruent_symmetry
      C H Y
      A H C
      hCHY_AHC

  have hAHC_CHB :
      HilbertAngleLess Geo A H C C H B :=
    hilbert_angleLess_transport_left
      Geo
      C H Y
      A H C
      C H B
      hCHY_CHB
      hAHC
      hAHC_CHY

  ----------------------------------------------------------------------
  -- Reverse the whole angle CHB to BHC.
  ----------------------------------------------------------------------

  have hCHB_BHC :
      Geo.AngleCongruent C H B B H C := by

    have hRefl :
        Geo.AngleCongruent C H B C H B :=
      Geometry.Geo.angle_congruent_reflexive
        Geo C H B

    exact
      (Geo.angle_congruent_reverse_second
        C H B
        C H B).mp
        hRefl

  have hBHCnc :
      Not (PrimCollinear Geo B H C) := by

    intro hBHCcol

    have hCHBcol :
        PrimCollinear Geo C H B :=
      PrimCollinearSymm
        Geo B H C hBHCcol

    exact hCHB hCHBcol

  have hAHC_BHC :
      HilbertAngleLess Geo A H C B H C :=
    hilbert_angleLess_transport_right
      Geo
      A H C
      C H B
      B H C
      hAHC_CHB
      hBHCnc
      hCHB_BHC

  ----------------------------------------------------------------------
  -- Combine the two strict inequalities:
  --
  -- HCB < AHC < BHC.
  ----------------------------------------------------------------------

  have hHCB_BHC :
      HilbertAngleLess Geo H C B B H C :=
    hilbert_angleLess_trans
      Geo
      H C B
      A H C
      B H C
      hHCB_AHC
      hAHC_BHC

  ----------------------------------------------------------------------
  -- Reverse HCB to BCH.
  ----------------------------------------------------------------------

  have hHCB_BCH :
      Geo.AngleCongruent H C B B C H := by

    have hRefl :
        Geo.AngleCongruent H C B H C B :=
      Geometry.Geo.angle_congruent_reflexive
        Geo H C B

    exact
      (Geo.angle_congruent_reverse_second
        H C B
        H C B).mp
        hRefl

  have hBCH_HCB :
      Geo.AngleCongruent B C H H C B :=
    Geo.angle_congruent_symmetry
      H C B
      B C H
      hHCB_BCH

  have hBCHnc :
      Not (PrimCollinear Geo B C H) := by

    intro hBCHcol

    have hBHCcol :
        PrimCollinear Geo B H C :=
      PrimCollinearRotate
        Geo B C H hBCHcol

    have hCHBcol :
        PrimCollinear Geo C H B :=
      PrimCollinearSymm
        Geo B H C hBHCcol

    exact hCHB hCHBcol

  have hBCH_BHC :
      HilbertAngleLess Geo B C H B H C :=
    hilbert_angleLess_transport_left
      Geo
      H C B
      B C H
      B H C
      hHCB_BHC
      hBCHnc
      hBCH_HCB

  ----------------------------------------------------------------------
  -- Proposition I.19:
  --
  -- angle BCH < angle BHC  ==>  BH < BC.
  ----------------------------------------------------------------------

  exact
    euclid_proposition_19
      Geo
      B H C
      hBHCnc
      hBCH_BHC


theorem euclid_proposition_24_hinge_aux
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C H X : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hMeet :
      HilbertRayMeetsSegment Geo A X B C)
    (hRay :
      HilbertSameRay Geo A X H)
    (hAH_AC :
      Geo.Congruent A H A C) :
    HilbertSegmentLess Geo B H B C := by

  rcases hMeet with
    ⟨Y, hBYC, hRayAXY⟩

  have hRayAHY :
      HilbertSameRay Geo A H Y :=
    bookZero_36_ray3
      Geo
      A X H Y
      hRay
      hRayAXY

  have hRayAYH :
      HilbertSameRay Geo A Y H :=
    bookZero_39_ray5
      Geo
      A H Y
      hRayAHY

  have hAY :
      A ≠ Y :=
    (hRayAXY.2.1).symm

  have hAH :
      A ≠ H :=
    (hRay.2.1).symm

  rcases
      euclid_proposition_22_sameRay_trichotomy
        (Geo := Geo)
        A Y H
        hAY
        hAH
        hRayAYH with
    hAHY | hYH | hAYH

  ·
    -- Case 1: A-H-Y.
    exact
      euclid_proposition_24_hinge_case1
        (Geo := Geo)
        A B C H Y
        hABC
        hAHY
        hBYC
        hAH_AC

  ·
    -- Case 2: Y = H.
    subst H

    exact
      ⟨Y,
        hBYC,
        hilbert_congruent_reflexive
          Geo B Y⟩

  ·
    -- Case 3: A-Y-H.
    exact
      euclid_proposition_24_hinge_case3
        (Geo := Geo)
        A B C H Y
        hABC
        hAYH
        hBYC
        hAH_AC

theorem euclid_proposition_24
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E F : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hDEF : Not (PrimCollinear Geo D E F))
    (hAB_DE : Geo.Congruent A B D E)
    (hAC_DF : Geo.Congruent A C D F)
    (hAngle :
      HilbertAngleLess Geo E D F B A C) :
    HilbertSegmentLess Geo E F B C := by

  rcases
      euclid_proposition_24_sas_aux
        (Geo := Geo)
        A B C D E F
        hABC
        hDEF
        hAB_DE
        hAC_DF
        hAngle with
    ⟨X, H, hMeet, hRayAXH, hAH_AC, hBH_EF⟩

  have hBH_BC :
      HilbertSegmentLess Geo B H B C :=
    euclid_proposition_24_hinge_aux
      (Geo := Geo)
      A B C H X
      hABC
      hMeet
      hRayAXH
      hAH_AC

  exact
    bookZero_32_lessThanCongruence2
      Geo
      B H
      B C
      E F
      hBH_BC
      hBH_EF

end Geometry

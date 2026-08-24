import CGJteamLab.HilbertInterface

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

theorem hilbert_right_angle_exists_nondegenerate
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A C B : Geo.Point)
    (hACB : Geo.Between A C B) :
    ∃ X : Geo.Point,
      Not (PrimCollinear Geo A C X) ∧
      HilbertRightAngle Geo A C X := by

  have hACBData :=
    HilbertOrder.between_incidence A C B hACB

  have hAC : A ≠ C :=
    hACBData.1

  have hCB : C ≠ B :=
    hACBData.2.1

  have hAB : A ≠ B :=
    hACBData.2.2.1

  ----------------------------------------------------------------------
  -- The given line AB.
  ----------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        A B hAB with
    ⟨base, hAbase, hBbase⟩

  have hCbase :
      HilbertIncidence.OnLine C base :=
    hilbert_between_on_line
      Geo A C B base
      hAbase hBbase hACB

  ----------------------------------------------------------------------
  -- Choose an arbitrary point D off AB.
  ----------------------------------------------------------------------

  rcases
      hilbert_point_off_line Geo base with
    ⟨D, hDbase⟩

  have hACD :
      ¬ Collinear Geo A C D :=
    hilbert_not_collinear_of_off_line
      Geo A C D base
      hAC
      hAbase
      hCbase
      hDbase

  have hBC : B ≠ C :=
    hCB.symm

  ----------------------------------------------------------------------
  -- Copy angle ACD onto ray CB, on the side selected by D.
  --
  -- This produces E with
  --
  --     angle ACD congruent angle BCE.
  ----------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        A C D
        B C D
        hACD
        hBC
        base
        hBbase
        hCbase
        hDbase with
    ⟨E, hEDSame, hAngleE, hUniqueE⟩
  ----------------------------------------------------------------------
  -- If C, E, D are collinear, then E and D determine the same ray
  -- from C, because they lie on the same side of the base line.
  -- In this case D already determines the required right angle.
  ----------------------------------------------------------------------

  by_cases hCED :
      Collinear Geo C E D

  · have hEC : E ≠ C := by
      intro h
      subst E
      exact hEDSame.1 hCbase

    have hDC : D ≠ C := by
      intro h
      subst D
      exact hDbase hCbase

    have hNotECD :
        ¬ Geo.Between E C D := by

      intro hECD

      have hOppED :
          HilbertOppositeSide Geo E D base :=
        ⟨hEDSame.1,
         hEDSame.2.1,
         ⟨C, hECD, hCbase⟩⟩

      exact
        (hilbert_oppositeSide_not_sameSide
          Geo E D base hOppED)
          hEDSame

    have hRayED :
        HilbertSameRay Geo C E D :=
      ⟨hEC, hDC, hCED, hNotECD⟩

    have hAngleBED :
        Geo.Angle B C E =
        Geo.Angle B C D :=
      hilbert_angle_eq_of_sameRay_second
        Geo C B E D hRayED

    have hAngleACD_BCD :
        Geo.AngleCongruent A C D B C D := by

      unfold Geometry.Geo.AngleCongruent
        at hAngleE ⊢

      rw [← hAngleBED]
      exact hAngleE

    have hAngleACD_DCB :
        Geo.AngleCongruent A C D D C B := by

      unfold Geometry.Geo.AngleCongruent
        at hAngleACD_BCD ⊢

      rw [Geometry.Geo.angle_swap Geo B C D]
        at hAngleACD_BCD

      exact hAngleACD_BCD

    refine ⟨D, hACD, ?_⟩
    refine ⟨B, hACB, ?_⟩
    exact hAngleACD_DCB

  · -- hCED : not Collinear Geo C E D

    have hCD : C ≠ D := by
      intro h
      subst D
      exact hDbase hCbase

    have hCE : C ≠ E := by
      intro h
      subst E
      exact hEDSame.1 hCbase

    ----------------------------------------------------------------------
    -- On ray CD choose F with CF congruent CE.
    ----------------------------------------------------------------------

    rcases
        HilbertCongruence.segment_construction
          (Geo := Geo)
          C E
          C D
          hCD with
      ⟨F, hRayDF, hCF_CE⟩

    have hCF : C ≠ F :=
      hRayDF.2.1.symm

    have hCDF :
        Collinear Geo C D F :=
      hRayDF.2.2.1

    ----------------------------------------------------------------------
    -- F, C, E are noncollinear.
    ----------------------------------------------------------------------

    have hFCE :
        ¬ Collinear Geo F C E := by

      intro hFCE

      have hDCF :
          Collinear Geo D C F :=
        PrimCollinearSwap
          Geo C D F hCDF

      have hCFE :
          Collinear Geo C F E :=
        PrimCollinearSwap
          Geo F C E hFCE

      have hDCE :
          Collinear Geo D C E :=
        hilbert_primCollinear_trans
          Geo
          D C F E
          hCF
          hDCF
          hCFE

      have hCED' :
          Collinear Geo C E D :=
        PrimCollinearCycle
          Geo D C E hDCE

      exact hCED hCED'

    have hFE : F ≠ E := by
      intro hFE
      subst F

      have hCED' :
          Collinear Geo C E D :=
        PrimCollinearRotate
          Geo C D E hCDF

      exact hCED hCED'
    ----------------------------------------------------------------------
    -- Let X be the midpoint of FE.
    ----------------------------------------------------------------------

    rcases
        HilbertMidpointExists
          Geo F E hFE with
      ⟨X, hMidX⟩

    have hFXE :
        Geo.Between F X E :=
      hMidX.1

    have hFX_XE :
        Geo.Congruent F X X E :=
      hMidX.2

    have hFX : F ≠ X :=
      (HilbertOrder.between_incidence
        F X E hFXE).1

    have hFXEcol :
        Collinear Geo F X E :=
      (HilbertOrder.between_incidence
        F X E hFXE).2.2.2.1

    ----------------------------------------------------------------------
    -- Triangle CFX is nondegenerate.
    ----------------------------------------------------------------------

    have hCFX :
        ¬ Collinear Geo C F X := by

      intro hCFX

      have hCFE' :
          Collinear Geo C F E :=
        hilbert_primCollinear_trans
          Geo
          C F X E
          hFX
          hCFX
          hFXEcol

      exact
        hFCE
          (PrimCollinearSwap Geo C F E hCFE')

    ----------------------------------------------------------------------
    -- SSS for triangles CFX and CEX.
    ----------------------------------------------------------------------

    have hFX_EX :
        Geo.Congruent F X E X :=
      (Geo.congruent_reverse_second
        F X X E).mp hFX_XE

    have hCX_CX :
        Geo.Congruent C X C X :=
      hilbert_congruent_reflexive
        Geo C X

    have hSSS :=
      HilbertSSS
        Geo
        C F X
        C E X
        hCFX
        hCF_CE
        hFX_EX
        hCX_CX

    have hFCX_ECX :
        Geo.AngleCongruent F C X E C X :=
      hSSS.2.angleA

    ----------------------------------------------------------------------
    -- Replace ray CF by the original ray CD.
    ----------------------------------------------------------------------

    have hRayFD :
        HilbertSameRay Geo C F D :=
      hilbert_sameRay_symm
        Geo C D F hRayDF

    have hAngleFCX_DCX :
        Geo.Angle F C X =
        Geo.Angle D C X :=
      hilbert_angle_eq_of_sameRay_first
        Geo C F D X hRayFD

    have hDCX_ECX :
        Geo.AngleCongruent D C X E C X := by

      unfold Geometry.Geo.AngleCongruent
        at hFCX_ECX ⊢

      rw [← hAngleFCX_DCX]

      exact hFCX_ECX
    ----------------------------------------------------------------------
    -- Reference lines CD and CE.
    ----------------------------------------------------------------------

    rcases
        HilbertPlaneIncidence.line_through
          C D hCD with
      ⟨lineCD, hClineCD, hDlineCD⟩

    rcases
        HilbertPlaneIncidence.line_through
          C E hCE with
      ⟨lineCE, hClineCE, hElineCE⟩

    ----------------------------------------------------------------------
    -- F lies on line CD.
    ----------------------------------------------------------------------

    have hFlineCD :
        HilbertIncidence.OnLine F lineCD :=
      hilbert_collinear_on_line
        Geo C D F lineCD
        hCD
        hClineCD
        hDlineCD
        hCDF

    ----------------------------------------------------------------------
    -- A is not on line CD.
    ----------------------------------------------------------------------

    have hAoffCD :
        ¬ HilbertIncidence.OnLine A lineCD := by

      intro hAlineCD

      exact hACD
        ⟨lineCD,
         hAlineCD,
         hClineCD,
         hDlineCD⟩

    ----------------------------------------------------------------------
    -- X is not on line CD.
    ----------------------------------------------------------------------

    have hXoffCD :
        ¬ HilbertIncidence.OnLine X lineCD := by

      intro hXlineCD

      exact hCFX
        ⟨lineCD,
         hClineCD,
         hFlineCD,
         hXlineCD⟩

    ----------------------------------------------------------------------
    -- B is not on line CE.
    ----------------------------------------------------------------------

    have hBoffCE :
        ¬ HilbertIncidence.OnLine B lineCE := by

      intro hBlineCE

      have hBaseEq :
          base = lineCE :=
        HilbertPlaneIncidence.line_unique
          B C hBC
          base lineCE
          hBbase hCbase
          hBlineCE hClineCE

      have hEbase :
          HilbertIncidence.OnLine E base := by
        rw [hBaseEq]
        exact hElineCE

      exact hEDSame.1 hEbase

    ----------------------------------------------------------------------
    -- X is not on line CE.
    ----------------------------------------------------------------------

    have hCEX :
        ¬ Collinear Geo C E X :=
      hSSS.1

    have hXoffCE :
        ¬ HilbertIncidence.OnLine X lineCE := by

      intro hXlineCE

      exact hCEX
        ⟨lineCE,
         hClineCE,
         hElineCE,
         hXlineCE⟩

    ----------------------------------------------------------------------
    -- E and X lie on the same side of line CD.
    ----------------------------------------------------------------------

    have hEXF :
        Geo.Between E X F :=
      (HilbertOrder.between_incidence
        F X E hFXE).2.2.2.2

    have hEFC :
        ¬ Collinear Geo E F C := by
      intro hEFC

      have hFCE' :
          Collinear Geo F C E :=
        PrimCollinearCycle
          Geo E F C hEFC

      exact hFCE hFCE'

    rcases
        hilbert_between_points_sameSide_transversal
          Geo E X C F hEXF hEFC with
      ⟨lineCF, hClineCF, hFlineCF, hSameEX_CF⟩

    have hLineCF_CD :
        lineCF = lineCD :=
      HilbertPlaneIncidence.line_unique
        C F hCF
        lineCF lineCD
        hClineCF hFlineCF
        hClineCD hFlineCD

    have hSameEX_CD :
        HilbertSameSide Geo E X lineCD := by
      rw [← hLineCF_CD]
      exact hSameEX_CF

    ----------------------------------------------------------------------
    -- F and X lie on the same side of line CE.
    ----------------------------------------------------------------------

    have hFEC :
        ¬ Collinear Geo F E C := by
      intro hFEC

      have hFCE' :
          Collinear Geo F C E :=
        PrimCollinearRotate
          Geo F E C hFEC

      exact hFCE hFCE'

    rcases
        hilbert_between_points_sameSide_transversal
          Geo F X C E hFXE hFEC with
      ⟨lineCE', hClineCE', hElineCE', hSameFX_CE⟩

    have hLineCE'_CE :
        lineCE' = lineCE :=
      HilbertPlaneIncidence.line_unique
        C E hCE
        lineCE' lineCE
        hClineCE' hElineCE'
        hClineCE hElineCE

    have hSameFX_CE' :
        HilbertSameSide Geo F X lineCE := by
      rw [← hLineCE'_CE]
      exact hSameFX_CE
    ----------------------------------------------------------------------
    -- Determine the order of the rays CD and CE in the half-plane
    -- bounded by the original line AB.
    ----------------------------------------------------------------------

    have hDCE :
        ¬ Collinear Geo D C E := by
      intro hDCE'
      exact
        hCED
          (PrimCollinearCycle
            Geo D C E hDCE')

    have hSameDE :
        HilbertSameSide Geo D E base :=
      hilbert_sameSide_symm
        Geo E D base hEDSame

    have hRayOrder :
        HilbertRayMeetsSegment Geo C D E A ∨
        HilbertRayMeetsSegment Geo C E D A :=
      hilbert_sameSide_rays_order
        Geo
        C D A E
        base
        hAC.symm
        hCbase
        hAbase
        hDbase
        hEDSame.1
        hSameDE
        hDCE
    rcases hRayOrder with hCaseD | hCaseE

    ----------------------------------------------------------------------
    -- Case 1: ray CD meets the open segment EA.
    ----------------------------------------------------------------------

        ----------------------------------------------------------------------
    -- Case 1: ray CD meets the open segment EA.
    ----------------------------------------------------------------------

    · rcases hCaseD with
        ⟨Y, hEYA, hRayDY⟩

      have hCY : C ≠ Y :=
        hRayDY.2.1.symm

      have hYlineCD :
          HilbertIncidence.OnLine Y lineCD := by

        rcases hRayDY.2.2.1 with
          ⟨m, hCm, hDm, hYm⟩

        have hm :
            m = lineCD :=
          HilbertPlaneIncidence.line_unique
            C D hCD
            m lineCD
            hCm hDm
            hClineCD hDlineCD

        rw [← hm]
        exact hYm

      --------------------------------------------------------------------
      -- E and A are on opposite sides of CD.
      --------------------------------------------------------------------

      have hOppEA_CD :
          HilbertOppositeSide Geo E A lineCD :=
        ⟨hSameEX_CD.1,
         hAoffCD,
         ⟨Y, hEYA, hYlineCD⟩⟩

      have hOppAE_CD :
          HilbertOppositeSide Geo A E lineCD :=
        hilbert_oppositeSide_symm
          Geo E A lineCD hOppEA_CD

      have hOppAX_CD :
          HilbertOppositeSide Geo A X lineCD :=
        hilbert_oppositeSide_transport_right
          Geo A E X lineCD
          hOppAE_CD
          hSameEX_CD

      have hNotSameAX_CD :
          ¬ HilbertSameSide Geo A X lineCD := by
        intro hSameAX

        exact
          (hilbert_oppositeSide_not_sameSide
            Geo A X lineCD hOppAX_CD)
            hSameAX

      --------------------------------------------------------------------
      -- F and Y are on the same side of CE because both lie
      -- on the same ray CD.
      --------------------------------------------------------------------

      have hSameFY_CE :
          HilbertSameSide Geo F Y lineCE := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := D)
            (X := F)
            (Y := Y)
            (C := E)
            (base := lineCD)
            (cross := lineCE)
            hClineCD
            hDlineCD
            hClineCE
            hElineCE
            hSameEX_CD.1
            hRayDF
            hRayDY

      --------------------------------------------------------------------
      -- Y and A are on the same side of CE.
      --------------------------------------------------------------------

      have hEYAData :=
        HilbertOrder.between_incidence
          E Y A hEYA

      rcases hEYAData.2.2.2.1 with
        ⟨lineEA, hElineEA, hYlineEA, hAlineEA⟩

      have hCoffEA :
          ¬ HilbertIncidence.OnLine C lineEA := by
        intro hClineEA

        have hEq :
            lineEA = base :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            lineEA base
            hAlineEA hClineEA
            hAbase hCbase

        have hEbase :
            HilbertIncidence.OnLine E base := by
          rw [← hEq]
          exact hElineEA

        exact hEDSame.1 hEbase

      have hRayEAY :
          HilbertSameRay Geo E A Y :=
        hilbert_sameRay_symm
          Geo E Y A
          (hilbert_sameRay_of_between
            Geo E Y A hEYA)


      have hAE : A ≠ E :=
        hEYAData.2.2.1.symm

      have hRayEAA :
          HilbertSameRay Geo E A A :=
        hilbert_sameRay_refl
          Geo E A hAE

      have hSameYA_CE :
          HilbertSameSide Geo Y A lineCE := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := E)
            (R := A)
            (X := Y)
            (Y := A)
            (C := C)
            (base := lineEA)
            (cross := lineCE)
            hElineEA
            hAlineEA
            hElineCE
            hClineCE
            hCoffEA
            hRayEAY
            hRayEAA

      have hSameFA_CE :
          HilbertSameSide Geo F A lineCE :=
        hilbert_sameSide_trans
          Geo F Y A lineCE
          hSameFY_CE
          hSameYA_CE

      have hSameAF_CE :
          HilbertSameSide Geo A F lineCE :=
        hilbert_sameSide_symm
          Geo F A lineCE hSameFA_CE

      --------------------------------------------------------------------
      -- A and B are on opposite sides of CE because A-C-B.
      --------------------------------------------------------------------

      have hAoffCE :
          ¬ HilbertIncidence.OnLine A lineCE := by
        intro hAlineCE

        have hEq :
            base = lineCE :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            base lineCE
            hAbase hCbase
            hAlineCE hClineCE

        have hEbase :
            HilbertIncidence.OnLine E base := by
          rw [hEq]
          exact hElineCE

        exact hEDSame.1 hEbase

      have hOppAB_CE :
          HilbertOppositeSide Geo A B lineCE :=
        ⟨hAoffCE,
         hBoffCE,
         ⟨C, hACB, hClineCE⟩⟩

      have hOppBA_CE :
          HilbertOppositeSide Geo B A lineCE :=
        hilbert_oppositeSide_symm
          Geo A B lineCE hOppAB_CE

      have hOppBF_CE :
          HilbertOppositeSide Geo B F lineCE :=
        hilbert_oppositeSide_transport_right
          Geo B A F lineCE
          hOppBA_CE
          hSameAF_CE

      have hOppBX_CE :
          HilbertOppositeSide Geo B X lineCE :=
        hilbert_oppositeSide_transport_right
          Geo B F X lineCE
          hOppBF_CE
          hSameFX_CE'

      have hNotSameBX_CE :
          ¬ HilbertSameSide Geo B X lineCE := by
        intro hSameBX

        exact
          (hilbert_oppositeSide_not_sameSide
            Geo B X lineCE hOppBX_CE)
            hSameBX

      --------------------------------------------------------------------
      -- The two angle configurations have the same side pattern.
      --------------------------------------------------------------------

      have hSideConfiguration :
          HilbertSameSide Geo A X lineCD ↔
          HilbertSameSide Geo B X lineCE := by
        constructor
        · intro hAX
          exact False.elim (hNotSameAX_CD hAX)
        · intro hBX
          exact False.elim (hNotSameBX_CE hBX)

            --------------------------------------------------------------------
      -- F and D lie on the same side of the original base.
      --------------------------------------------------------------------

      have hRayCDD :
          HilbertSameRay Geo C D D :=
        hilbert_sameRay_refl
          Geo C D hCD.symm

      have hSameFD_base :
          HilbertSameSide Geo F D base := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := D)
            (X := F)
            (Y := D)
            (C := A)
            (base := lineCD)
            (cross := base)
            hClineCD
            hDlineCD
            hCbase
            hAbase
            hAoffCD
            hRayDF
            hRayCDD

      have hSameFE_base :
          HilbertSameSide Geo F E base :=
        hilbert_sameSide_trans
          Geo F D E base
          hSameFD_base
          hSameDE

      --------------------------------------------------------------------
      -- Since X lies between F and E, and F,E are on the same side
      -- of base, X cannot lie on base.
      --------------------------------------------------------------------

      have hXoffBase :
          ¬ HilbertIncidence.OnLine X base := by
        intro hXbase

        have hOppFE_base :
            HilbertOppositeSide Geo F E base :=
          ⟨hSameFE_base.1,
           hSameFE_base.2.1,
           ⟨X, hFXE, hXbase⟩⟩

        exact
          (hilbert_oppositeSide_not_sameSide
            Geo F E base hOppFE_base)
            hSameFE_base

      --------------------------------------------------------------------
      -- Hence ACX and BCX are genuine angles.
      --------------------------------------------------------------------

      have hACX :
          ¬ Collinear Geo A C X :=
        hilbert_not_collinear_of_off_line
          Geo A C X base
          hAC
          hAbase
          hCbase
          hXoffBase

      have hBCX :
          ¬ Collinear Geo B C X :=
        hilbert_not_collinear_of_off_line
          Geo B C X base
          hBC
          hBbase
          hCbase
          hXoffBase

      --------------------------------------------------------------------
      -- Add the two congruent component angles:
      --
      --   ACD ~= BCE
      --   DCX ~= ECX
      --
      -- therefore ACX ~= BCX.
      --------------------------------------------------------------------

      have hACX_BCX :
          Geo.AngleCongruent A C X B C X :=
        hilbert_angle_addition
          Geo
          A C D X
          B C E X
          lineCD lineCE
          hCD
          hCE
          hClineCD
          hDlineCD
          hClineCE
          hElineCE
          hAoffCD
          hXoffCD
          hBoffCE
          hXoffCE
          hSideConfiguration
          hACX
          hBCX
          hAngleE
          hDCX_ECX

      have hACX_XCB :
          Geo.AngleCongruent A C X X C B :=
        (Geo.angle_congruent_reverse_second
          A C X B C X).mp hACX_BCX

      --------------------------------------------------------------------
      -- This is precisely a right angle at C.
      --------------------------------------------------------------------

      refine ⟨X, hACX, ?_⟩
      refine ⟨B, hACB, ?_⟩
      exact hACX_XCB


    ----------------------------------------------------------------------
    -- Case 2: ray CE meets the open segment DA.
    ----------------------------------------------------------------------

    · rcases hCaseE with
        ⟨Y, hDYA, hRayEY⟩

      have hCY : C ≠ Y :=
        hRayEY.2.1.symm

      have hYlineCE :
          HilbertIncidence.OnLine Y lineCE := by

        rcases hRayEY.2.2.1 with
          ⟨m, hCm, hEm, hYm⟩

        have hm :
            m = lineCE :=
          HilbertPlaneIncidence.line_unique
            C E hCE
            m lineCE
            hCm hEm
            hClineCE hElineCE

        rw [← hm]
        exact hYm

      --------------------------------------------------------------------
      -- Since Y lies between D and A and Y lies on line CE,
      -- D and A are on opposite sides of line CE.
      --------------------------------------------------------------------
      have hDoffCE :
          ¬ HilbertIncidence.OnLine D lineCE := by
        intro hDlineCE

        exact hCED
          ⟨lineCE,
           hClineCE,
           hElineCE,
           hDlineCE⟩
      have hAoffCE :
          ¬ HilbertIncidence.OnLine A lineCE := by
        intro hAlineCE

        have hBaseEq :
            base = lineCE :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            base lineCE
            hAbase hCbase
            hAlineCE hClineCE

        have hEbase :
            HilbertIncidence.OnLine E base := by
          rw [hBaseEq]
          exact hElineCE

        exact hEDSame.1 hEbase

      have hOppDA_CE :
          HilbertOppositeSide Geo D A lineCE :=
        ⟨hDoffCE,
         hAoffCE,
         ⟨Y, hDYA, hYlineCE⟩⟩

            --------------------------------------------------------------------
      -- Y and A lie on the same side of CD.
      --------------------------------------------------------------------

      have hDYAData :=
        HilbertOrder.between_incidence
          D Y A hDYA

      rcases hDYAData.2.2.2.1 with
        ⟨lineDA, hDlineDA, hYlineDA, hAlineDA⟩

      have hCoffDA :
          ¬ HilbertIncidence.OnLine C lineDA := by
        intro hClineDA

        have hEq :
            lineDA = base :=
          HilbertPlaneIncidence.line_unique
            A C hAC
            lineDA base
            hAlineDA hClineDA
            hAbase hCbase

        have hDbase' :
            HilbertIncidence.OnLine D base := by
          rw [← hEq]
          exact hDlineDA

        exact hDbase hDbase'

      have hRayDAY :
          HilbertSameRay Geo D A Y :=
        hilbert_sameRay_symm
          Geo D Y A
          (hilbert_sameRay_of_between
            Geo D Y A hDYA)

      have hDA : A ≠ D :=
        hDYAData.2.2.1.symm

      have hRayDAA :
          HilbertSameRay Geo D A A :=
        hilbert_sameRay_refl
          Geo D A hDA

      have hSameYA_CD :
          HilbertSameSide Geo Y A lineCD := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := D)
            (R := A)
            (X := Y)
            (Y := A)
            (C := C)
            (base := lineDA)
            (cross := lineCD)
            hDlineDA
            hAlineDA
            hDlineCD
            hClineCD
            hCoffDA
            hRayDAY
            hRayDAA

      --------------------------------------------------------------------
      -- E and Y lie on the same side of CD because both lie
      -- on ray CE.
      --------------------------------------------------------------------

      have hRayCEE :
          HilbertSameRay Geo C E E :=
        hilbert_sameRay_refl
          Geo C E hCE.symm

      have hSameEY_CD :
          HilbertSameSide Geo E Y lineCD := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := E)
            (X := E)
            (Y := Y)
            (C := D)
            (base := lineCE)
            (cross := lineCD)
            hClineCE
            hElineCE
            hClineCD
            hDlineCD
            hDoffCE
            hRayCEE
            hRayEY

      have hSameEA_CD :
          HilbertSameSide Geo E A lineCD :=
        hilbert_sameSide_trans
          Geo E Y A lineCD
          hSameEY_CD
          hSameYA_CD

      have hSameAE_CD :
          HilbertSameSide Geo A E lineCD :=
        hilbert_sameSide_symm
          Geo E A lineCD hSameEA_CD

      have hSameAX_CD :
          HilbertSameSide Geo A X lineCD :=
        hilbert_sameSide_trans
          Geo A E X lineCD
          hSameAE_CD
          hSameEX_CD

      --------------------------------------------------------------------
      -- D and B lie on the same side of CE.
      --
      -- CE cuts sides AD and AB of triangle ADB at Y and C.
      --------------------------------------------------------------------

      have hAYD :
          Geo.Between A Y D :=
        hDYAData.2.2.2.2

      have hADB :
          ¬ PrimCollinear Geo A D B := by
        rintro ⟨l, hAl, hDl, hBl⟩

        have hEq :
            l = base :=
          HilbertPlaneIncidence.line_unique
            A B hAB
            l base
            hAl hBl
            hAbase hBbase

        have hDbase' :
            HilbertIncidence.OnLine D base := by
          rw [← hEq]
          exact hDl

        exact hDbase hDbase'

      have hSameDB_CE :
          HilbertSameSide Geo D B lineCE :=
        hilbert_third_side_endpoints_sameSide
          Geo
          A D B
          Y C
          lineCE
          hADB
          hAYD
          hACB
          hYlineCE
          hClineCE

      --------------------------------------------------------------------
      -- D and F are on the same side of CE because both lie
      -- on ray CD.
      --------------------------------------------------------------------

      have hRayCDD :
          HilbertSameRay Geo C D D :=
        hilbert_sameRay_refl
          Geo C D hCD.symm

      have hSameDF_CE :
          HilbertSameSide Geo D F lineCE := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := D)
            (X := D)
            (Y := F)
            (C := E)
            (base := lineCD)
            (cross := lineCE)
            hClineCD
            hDlineCD
            hClineCE
            hElineCE
            hSameEX_CD.1
            hRayCDD
            hRayDF

      have hSameBD_CE :
          HilbertSameSide Geo B D lineCE :=
        hilbert_sameSide_symm
          Geo D B lineCE hSameDB_CE

      have hSameBF_CE :
          HilbertSameSide Geo B F lineCE :=
        hilbert_sameSide_trans
          Geo B D F lineCE
          hSameBD_CE
          hSameDF_CE

      have hSameBX_CE :
          HilbertSameSide Geo B X lineCE :=
        hilbert_sameSide_trans
          Geo B F X lineCE
          hSameBF_CE
          hSameFX_CE'

      --------------------------------------------------------------------
      -- Both component configurations are same-side configurations.
      --------------------------------------------------------------------

      have hSideConfiguration :
          HilbertSameSide Geo A X lineCD ↔
          HilbertSameSide Geo B X lineCE :=
        ⟨fun _ => hSameBX_CE,
         fun _ => hSameAX_CD⟩

      --------------------------------------------------------------------
      -- X is off the original base AB.
      --------------------------------------------------------------------

      have hSameFD_base :
          HilbertSameSide Geo F D base := by
        exact
          hilbert_sameRay_points_sameSide
            (Geo := Geo)
            (O := C)
            (R := D)
            (X := F)
            (Y := D)
            (C := A)
            (base := lineCD)
            (cross := base)
            hClineCD
            hDlineCD
            hCbase
            hAbase
            hAoffCD
            hRayDF
            hRayCDD

      have hSameFE_base :
          HilbertSameSide Geo F E base :=
        hilbert_sameSide_trans
          Geo F D E base
          hSameFD_base
          hSameDE

      have hXoffBase :
          ¬ HilbertIncidence.OnLine X base := by
        intro hXbase

        have hOppFE_base :
            HilbertOppositeSide Geo F E base :=
          ⟨hSameFE_base.1,
           hSameFE_base.2.1,
           ⟨X, hFXE, hXbase⟩⟩

        exact
          (hilbert_oppositeSide_not_sameSide
            Geo F E base hOppFE_base)
            hSameFE_base

      have hACX :
          ¬ Collinear Geo A C X :=
        hilbert_not_collinear_of_off_line
          Geo A C X base
          hAC
          hAbase
          hCbase
          hXoffBase

      have hBCX :
          ¬ Collinear Geo B C X :=
        hilbert_not_collinear_of_off_line
          Geo B C X base
          hBC
          hBbase
          hCbase
          hXoffBase

      --------------------------------------------------------------------
      -- Angle addition.
      --------------------------------------------------------------------

      have hACX_BCX :
          Geo.AngleCongruent A C X B C X :=
        hilbert_angle_addition
          Geo
          A C D X
          B C E X
          lineCD lineCE
          hCD
          hCE
          hClineCD
          hDlineCD
          hClineCE
          hElineCE
          hAoffCD
          hXoffCD
          hBoffCE
          hXoffCE
          hSideConfiguration
          hACX
          hBCX
          hAngleE
          hDCX_ECX

      have hACX_XCB :
          Geo.AngleCongruent A C X X C B :=
        (Geo.angle_congruent_reverse_second
          A C X B C X).mp hACX_BCX

      refine ⟨X, hACX, ?_⟩
      refine ⟨B, hACB, ?_⟩
      exact hACX_XCB



theorem hilbert_right_angle_exists
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A C B : Geo.Point)
    (hACB : Geo.Between A C B) :
    ∃ X : Geo.Point,
      HilbertRightAngle Geo A C X := by

  rcases
      hilbert_right_angle_exists_nondegenerate
        Geo A C B hACB with
    ⟨X, _hACX, hRight⟩

  exact ⟨X, hRight⟩


------------------------------------------------------------------------
-- Hilbert Theorem 21: congruence of all right angles
------------------------------------------------------------------------

theorem hilbert_right_angle_same_foot_angle_cases
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base) :
    Geo.AngleCongruent X F A X F D ∨
    HilbertAngleLess Geo X F A X F D ∨
    HilbertAngleLess Geo X F D X F A := by

  have hXFA :
      ¬ PrimCollinear Geo X F A :=
    hilbert_not_collinear_of_off_line
      Geo
      X F A
      base
      hFX.symm
      hXbase
      hFbase
      hSame.1

  have hXFD :
      ¬ PrimCollinear Geo X F D :=
    hilbert_not_collinear_of_off_line
      Geo
      X F D
      base
      hFX.symm
      hXbase
      hFbase
      hSame.2.1

  exact
    angle_trichotomy
      Geo
      X F A
      X F D
      hXFA
      hXFD

/--
If angle XFA is strictly smaller than angle XFD, with A and D
on the same side of the base XF, then ray FA meets the open
segment XD.
-/
theorem hilbert_right_angle_less_ray_inside
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hLess :
      HilbertAngleLess Geo X F A X F D) :
    HilbertRayMeetsSegment Geo F A X D := by

  rcases hLess with
    ⟨hXFA, hXFD, J, hInsideJ, hAngle⟩

  rcases hInsideJ with
    ⟨H, hXHD, hRayFJH⟩

  have hDHX :
      Geo.Between D H X :=
    (HilbertOrder.between_incidence
      X H D hXHD).2.2.2.2

  have hDXF :
      ¬ PrimCollinear Geo D X F := by
    intro h
    exact
      hXFD
        (PrimCollinearCycle
          Geo D X F h)

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        D H F X
        hDHX
        hDXF
    with
    ⟨lineFX,
      hFlineFX,
      hXlineFX,
      hDHSame_lineFX⟩

  have hLineEq :
      lineFX = base :=
    HilbertPlaneIncidence.line_unique
      F X hFX
      lineFX base
      hFlineFX hXlineFX
      hFbase hXbase

  have hDHSame :
      HilbertSameSide Geo D H base := by
    rw [← hLineEq]
    exact hDHSame_lineFX

  have hAHSame :
      HilbertSameSide Geo A H base :=
    hilbert_sameSide_trans
      Geo
      A D H
      base
      hSame
      hDHSame

  have hXFJ :
      ¬ PrimCollinear Geo X F J :=
    (hilbert_interior_angle_less
      Geo
      F J X D
      hXFD
      ⟨H, hXHD, hRayFJH⟩).1

  have hFJ :
      F ≠ J :=
    hRayFJH.1.symm

  rcases
      HilbertPlaneIncidence.line_through
        F J hFJ
    with
    ⟨lineFJ,
      hFlineFJ,
      hJlineFJ⟩

  have hXoffFJ :
      ¬ HilbertIncidence.OnLine X lineFJ := by
    intro hXline
    exact
      hXFJ
        ⟨lineFJ,
          hXline,
          hFlineFJ,
          hJlineFJ⟩

  have hRayFJJ :
      HilbertSameRay Geo F J J :=
    hilbert_sameRay_refl
      Geo F J hFJ.symm

  have hJHSame :
      HilbertSameSide Geo J H base :=
    hilbert_sameRay_points_sameSide
      Geo
      F J
      J H
      X
      lineFJ base
      hFlineFJ
      hJlineFJ
      hFbase
      hXbase
      hXoffFJ
      hRayFJJ
      hRayFJH

  have hHJSame :
      HilbertSameSide Geo H J base :=
    hilbert_sameSide_symm
      Geo J H base hJHSame

  have hAJSame :
      HilbertSameSide Geo A J base :=
    hilbert_sameSide_trans
      Geo
      A H J
      base
      hAHSame
      hHJSame

  rcases
      hilbert_angle_unique_common_ray
        Geo
        X F A J
        base
        hFX.symm
        hXbase
        hFbase
        hAJSame.1
        hAJSame
        hAngle
    with
    ⟨Z,
      hRayZA,
      hRayZJ⟩

  have hRayAJ :
      HilbertSameRay Geo F A J :=
    hilbert_sameRay_of_common
      Geo
      F Z A J
      hRayZA
      hRayZJ

  have hRayJA :
      HilbertSameRay Geo F J A :=
    hilbert_sameRay_symm
      Geo
      F A J
      hRayAJ

  have hRayFAH :
      HilbertSameRay Geo F A H :=
    hilbert_sameRay_of_common
      Geo
      F J A H
      hRayJA
      hRayFJH

  exact
    ⟨H,
      hXHD,
      hRayFAH⟩

/--
A right angle may be expressed using any chosen point on the
opposite base ray.
-/
theorem hilbert_right_angle_chosen_supplement
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (D F X Y : Geo.Point)
    (hXFY : Geo.Between X F Y)
    (hXFD : ¬ PrimCollinear Geo X F D)
    (hRight : HilbertRightAngle Geo X F D) :
    Geo.AngleCongruent X F D D F Y := by

  rcases hRight with
    ⟨E, hXFE, hRightE⟩

  have hRefl :
      Geo.AngleCongruent X F D X F D :=
    Geo.angle_congruent_reflexive
      X F D

  have hSupp :
      Geo.AngleCongruent D F E D F Y :=
    hilbert_adjacent_angles_congruent
      Geo
      X F D E
      X F D Y
      hXFE
      hXFY
      hXFD
      hXFD
      hRefl

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X F D
      D F E
      D F Y
      hRightE
      hSupp

/--
If ray FA meets the open segment XD and X-F-Y, then ray FD
meets the open segment AY, provided A and D lie on the same
side of the base XY.
-/
theorem hilbert_right_angle_inside_flip
    [HilbertIncidence Geo]
    [HilbertOrder Geo]
    (A D F X Y : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hYbase : HilbertIncidence.OnLine Y base)
    (hSame : HilbertSameSide Geo A D base)
    (hXFY : Geo.Between X F Y)
    (hInside :
      HilbertRayMeetsSegment Geo F A X D) :
    HilbertRayMeetsSegment Geo F D A Y := by

  rcases hInside with
    ⟨H, hXHD, hRayFAH⟩

  have hFA :
      F ≠ A := by
    intro h
    subst A
    exact hSame.1 hFbase

  have hXFYData :=
    HilbertOrder.between_incidence
      X F Y hXFY

  have hFY :
      F ≠ Y :=
    hXFYData.2.1

  have hXY :
      X ≠ Y :=
    hXFYData.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        F A hFA
    with
    ⟨lineFA,
      hFlineFA,
      hAlineFA⟩

  have hHlineFA :
      HilbertIncidence.OnLine H lineFA :=
    hilbert_collinear_on_line
      Geo
      F A H
      lineFA
      hFA
      hFlineFA
      hAlineFA
      hRayFAH.2.2.1

  have hXYD :
      ¬ Collinear Geo X Y D :=
    hilbert_not_collinear_of_off_line
      Geo
      X Y D
      base
      hXY
      hXbase
      hYbase
      hSame.2.1

  have hYDsame :
      HilbertSameSide Geo Y D lineFA :=
    hilbert_third_side_endpoints_sameSide
      Geo
      X Y D
      F H
      lineFA
      hXYD
      hXFY
      hXHD
      hFlineFA
      hHlineFA

  have hDYsame :
      HilbertSameSide Geo D Y lineFA :=
    hilbert_sameSide_symm
      Geo Y D lineFA hYDsame

  have hFYD :
      ¬ Collinear Geo F Y D :=
    hilbert_not_collinear_of_off_line
      Geo
      F Y D
      base
      hFY
      hFbase
      hYbase
      hSame.2.1

  have hDFY :
      ¬ Collinear Geo D F Y := by
    intro h
    exact
      hFYD
        (PrimCollinearCycle
          Geo D F Y h)

  rcases
      hilbert_sameSide_rays_order
        Geo
        F D A Y
        lineFA
        hFA
        hFlineFA
        hAlineFA
        hDYsame.1
        hDYsame.2.1
        hDYsame
        hDFY
    with
    hFD | hFYmeet

  · rcases hFD with
      ⟨K, hYKA, hRayFDK⟩

    have hAKY :
        Geo.Between A K Y :=
      (HilbertOrder.between_incidence
        Y K A hYKA).2.2.2.2

    exact
      ⟨K,
        hAKY,
        hRayFDK⟩

  · rcases hFYmeet with
      ⟨K, hDKA, hRayFYK⟩

    have hKbase :
        HilbertIncidence.OnLine K base :=
      hilbert_collinear_on_line
        Geo
        F Y K
        base
        hFY
        hFbase
        hYbase
        hRayFYK.2.2.1

    have hOppDA :
        HilbertOppositeSide Geo D A base :=
      ⟨hSame.2.1,
        hSame.1,
        ⟨K,
          hDKA,
          hKbase⟩⟩

    have hSameDA :
        HilbertSameSide Geo D A base :=
      hilbert_sameSide_symm
        Geo A D base hSame

    exact
      False.elim
        ((hilbert_oppositeSide_not_sameSide
            Geo D A base hOppDA)
          hSameDA)

/--
A strict inequality between two right angles with the same first
base ray is impossible when their second rays lie in the same
half-plane.
-/
theorem hilbert_right_angle_less_impossible
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo X F D)
    (hLess :
      HilbertAngleLess Geo X F A X F D) :
    False := by

  have hXFA :
      ¬ PrimCollinear Geo X F A :=
    hLess.1

  have hXFD :
      ¬ PrimCollinear Geo X F D :=
    hLess.2.1

  rcases
      HilbertOrder.between_extension
        X F hFX.symm
    with
    ⟨Y, hXFY⟩

  have hXFYData :=
    HilbertOrder.between_incidence
      X F Y hXFY

  have hFY :
      F ≠ Y :=
    hXFYData.2.1

  have hYbase :
      HilbertIncidence.OnLine Y base :=
    hilbert_collinear_on_line
      Geo
      X F Y
      base
      hXFYData.1
      hXbase
      hFbase
      hXFYData.2.2.2.1

  have hInsideA :
      HilbertRayMeetsSegment Geo F A X D :=
    hilbert_right_angle_less_ray_inside
      Geo
      A D F X
      base
      hFbase
      hXbase
      hFX
      hSame
      hLess

  have hInsideD :
      HilbertRayMeetsSegment Geo F D A Y :=
    hilbert_right_angle_inside_flip
      Geo
      A D F X Y
      base
      hFbase
      hXbase
      hYbase
      hSame
      hXFY
      hInsideA

  have hAFY :
      ¬ PrimCollinear Geo A F Y := by

    have hFYA :
        ¬ PrimCollinear Geo F Y A :=
      hilbert_not_collinear_of_off_line
        Geo
        F Y A
        base
        hFY
        hFbase
        hYbase
        hSame.1

    intro h

    exact
      hFYA
        (PrimCollinearCycle
          Geo A F Y h)

  have hDFY :
      ¬ PrimCollinear Geo D F Y := by

    have hFYD :
        ¬ PrimCollinear Geo F Y D :=
      hilbert_not_collinear_of_off_line
        Geo
        F Y D
        base
        hFY
        hFbase
        hYbase
        hSame.2.1

    intro h

    exact
      hFYD
        (PrimCollinearCycle
          Geo D F Y h)

  have hXFA_AFY :
      Geo.AngleCongruent X F A A F Y :=
    hilbert_right_angle_chosen_supplement
      Geo
      A F X Y
      hXFY
      hXFA
      hRightA

  have hXFD_DFY :
      Geo.AngleCongruent X F D D F Y :=
    hilbert_right_angle_chosen_supplement
      Geo
      D F X Y
      hXFY
      hXFD
      hRightD

  have hXFA_DFY :
      HilbertAngleLess Geo X F A D F Y :=
    hilbert_angleLess_transport_right
      Geo
      X F A
      X F D
      D F Y
      hLess
      hDFY
      hXFD_DFY

  have hAFY_XFA :
      Geo.AngleCongruent A F Y X F A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X F A
      A F Y
      hXFA_AFY

  have hAFY_DFY :
      HilbertAngleLess Geo A F Y D F Y :=
    hilbert_angleLess_transport_left
      Geo
      X F A
      A F Y
      D F Y
      hXFA_DFY
      hAFY
      hAFY_XFA

  rcases hInsideD with
    ⟨K, hAKY, hRayFDK⟩

  have hYKA :
      Geo.Between Y K A :=
    (HilbertOrder.between_incidence
      A K Y hAKY).2.2.2.2

  have hInsideDrev :
      HilbertRayMeetsSegment Geo F D Y A :=
    ⟨K,
      hYKA,
      hRayFDK⟩

  have hYFA :
      ¬ PrimCollinear Geo Y F A := by

    intro h

    exact
      hAFY
        (PrimCollinearSymm
          Geo Y F A h)

  have hYFD_YFA :
      HilbertAngleLess Geo Y F D Y F A :=
    hilbert_interior_angle_less
      Geo
      F D Y A
      hYFA
      hInsideDrev

  have hYFDrefl :
      Geo.AngleCongruent Y F D Y F D :=
    Geo.angle_congruent_reflexive
      Y F D

  have hDFY_YFD :
      Geo.AngleCongruent D F Y Y F D :=
    (Geo.angle_congruent_reverse_first
      Y F D
      Y F D).mp
      hYFDrefl

  have hDFY_YFA :
      HilbertAngleLess Geo D F Y Y F A :=
    hilbert_angleLess_transport_left
      Geo
      Y F D
      D F Y
      Y F A
      hYFD_YFA
      hDFY
      hDFY_YFD

  have hYFArefl :
      Geo.AngleCongruent Y F A Y F A :=
    Geo.angle_congruent_reflexive
      Y F A

  have hYFA_AFY :
      Geo.AngleCongruent Y F A A F Y :=
    (Geo.angle_congruent_reverse_second
      Y F A
      Y F A).mp
      hYFArefl

  have hDFY_AFY :
      HilbertAngleLess Geo D F Y A F Y :=
    hilbert_angleLess_transport_right
      Geo
      D F Y
      Y F A
      A F Y
      hDFY_YFA
      hAFY
      hYFA_AFY

  have hCycle :
      HilbertAngleLess Geo A F Y A F Y :=
    hilbert_angleLess_trans
      Geo
      A F Y
      D F Y
      A F Y
      hAFY_DFY
      hDFY_AFY

  exact
    (hilbert_angleLess_irrefl
      Geo A F Y)
      hCycle

/--
Two right angles erected from the same base ray into the same
half-plane are congruent.
-/
theorem hilbert_same_base_right_angles_congruent
[HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F X : Geo.Point)
    (base : Geo.Line)
    (hFbase : HilbertIncidence.OnLine F base)
    (hXbase : HilbertIncidence.OnLine X base)
    (hFX : F ≠ X)
    (hSame : HilbertSameSide Geo A D base)
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo X F D) :
    Geo.AngleCongruent X F A X F D := by

  rcases
      hilbert_right_angle_same_foot_angle_cases
        Geo
        A D F X
        base
        hFbase
        hXbase
        hFX
        hSame
    with
    hCong | hLessAD | hLessDA

  · exact hCong

  · exact
      False.elim
        (hilbert_right_angle_less_impossible
          Geo
          A D F X
          base
          hFbase
          hXbase
          hFX
          hSame
          hRightA
          hRightD
          hLessAD)

  · have hSameDA :
        HilbertSameSide Geo D A base :=
      hilbert_sameSide_symm
        Geo A D base hSame

    exact
      False.elim
        (hilbert_right_angle_less_impossible
          Geo
          D A F X
          base
          hFbase
          hXbase
          hFX
          hSameDA
          hRightD
          hRightA
          hLessDA)

/--
All right angles are congruent.

This is Hilbert Theorem 21 in a form with explicit carrier lines
for the two first arms.
-/
theorem hilbert_all_right_angles_congruent_lines
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A D F G X E : Geo.Point)
    (base1 base2 : Geo.Line)
    (hFbase1 : HilbertIncidence.OnLine F base1)
    (hXbase1 : HilbertIncidence.OnLine X base1)
    (hAoff : Not (HilbertIncidence.OnLine A base1))
    (hGbase2 : HilbertIncidence.OnLine G base2)
    (hEbase2 : HilbertIncidence.OnLine E base2)
    (hDoff : Not (HilbertIncidence.OnLine D base2))
    (hRightA : HilbertRightAngle Geo X F A)
    (hRightD : HilbertRightAngle Geo E G D) :
    Geo.AngleCongruent X F A E G D := by

  rcases hRightA with
    ⟨Y, hXFY, hRightAeq⟩

  rcases hRightD with
    ⟨T, hEGT, hRightDeq⟩

  have hXF :
      X ≠ F :=
    (HilbertOrder.between_incidence
      X F Y hXFY).1

  have hEG :
      E ≠ G :=
    (HilbertOrder.between_incidence
      E G T hEGT).1

  have hGE :
      G ≠ E :=
    hEG.symm

  have hXFA :
      Not (PrimCollinear Geo X F A) :=
    hilbert_not_collinear_of_off_line
      Geo
      X F A
      base1
      hXF
      hXbase1
      hFbase1
      hAoff

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        X F A
        E G D
        hXFA
        hEG
        base2
        hEbase2
        hGbase2
        hDoff
    with
    ⟨K, hKDSame, hCopy, _hUnique⟩

  have hEGK :
      Not (PrimCollinear Geo E G K) :=
    hilbert_not_collinear_of_off_line
      Geo
      E G K
      base2
      hEG
      hEbase2
      hGbase2
      hKDSame.1

  have hSupp :
      Geo.AngleCongruent A F Y K G T :=
    hilbert_adjacent_angles_congruent
      Geo
      X F A Y
      E G K T
      hXFY
      hEGT
      hXFA
      hEGK
      hCopy

  have hEGK_XFA :
      Geo.AngleCongruent E G K X F A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      X F A
      E G K
      hCopy

  have hEGK_AFY :
      Geo.AngleCongruent E G K A F Y :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E G K
      X F A
      A F Y
      hEGK_XFA
      hRightAeq

  have hEGK_KGT :
      Geo.AngleCongruent E G K K G T :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E G K
      A F Y
      K G T
      hEGK_AFY
      hSupp

  have hRightK :
      HilbertRightAngle Geo E G K :=
    ⟨T,
      hEGT,
      hEGK_KGT⟩

  have hRightD' :
      HilbertRightAngle Geo E G D :=
    ⟨T,
      hEGT,
      hRightDeq⟩

  have hKGD :
      Geo.AngleCongruent E G K E G D :=
    hilbert_same_base_right_angles_congruent
      Geo
      K D G E
      base2
      hGbase2
      hEbase2
      hGE
      hKDSame
      hRightK
      hRightD'

  exact
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X F A
      E G K
      E G D
      hCopy
      hKGD

theorem hilbert_all_right_angles_congruent
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A O B A' O' B' : Geo.Point)
    (hAOB : Not (PrimCollinear Geo A O B))
    (hA'OB' : Not (PrimCollinear Geo A' O' B'))
    (hRight : HilbertRightAngle Geo A O B)
    (hRight' : HilbertRightAngle Geo A' O' B') :
    Geo.AngleCongruent A O B A' O' B' := by

  have hAO :
      A ≠ O :=
    hilbert_noncollinear_ne_first
      Geo A O B hAOB

  have hA'O' :
      A' ≠ O' :=
    hilbert_noncollinear_ne_first
      Geo A' O' B' hA'OB'

  rcases
      HilbertPlaneIncidence.line_through
        A O hAO
    with
    ⟨base1, hAbase1, hObase1⟩

  rcases
      HilbertPlaneIncidence.line_through
        A' O' hA'O'
    with
    ⟨base2, hA'base2, hO'base2⟩

  have hBoff :
      Not (HilbertIncidence.OnLine B base1) := by
    intro hBbase1
    exact
      hAOB
        ⟨base1,
          hAbase1,
          hObase1,
          hBbase1⟩

  have hB'off :
      Not (HilbertIncidence.OnLine B' base2) := by
    intro hB'base2
    exact
      hA'OB'
        ⟨base2,
          hA'base2,
          hO'base2,
          hB'base2⟩

  exact
    hilbert_all_right_angles_congruent_lines
      Geo
      B B'
      O O'
      A A'
      base1 base2
      hObase1
      hAbase1
      hBoff
      hO'base2
      hA'base2
      hB'off
      hRight
      hRight'

end Geometry

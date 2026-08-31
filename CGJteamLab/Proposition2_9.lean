import CGJteamLab.Proposition2_9Construction
import CGJteamLab.HilbertAngleDecomposition
import CGJteamLab.HilbertSquareTransport
import CGJteamLab.Proposition06
import CGJteamLab.Proposition32
import CGJteamLab.Proposition34
import CGJteamLab.Proposition46
import CGJteamLab.Proposition47

namespace Geometry

universe u
variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid II.9
--
-- Source-faithful synthetic proof for the oriented branch A-C-D-B.
-- No Book II proposition is used.  The proof follows I.5, I.29, I.32,
-- I.34, I.6 and four applications of I.47, with scissors bookkeeping.
------------------------------------------------------------------------

/--
Right-angle configuration for the source-faithful Euclid II.9 construction.

Starting from the permanent construction layer through C-G-E, recover the
four right angles needed later: ADF, EGF, ACE and BCE.  No side equality
GE=GF or DF=DB is used here.
-/
theorem proposition2_9_right_angle_configuration
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    ∃ E F G : Geo.Point,
      Geo.Between E F B ∧
      Geo.Between C G E ∧
      Geo.Between A C D ∧
      Geo.Congruent C E C B ∧
      IsParallelogram Geo D F G C ∧
      HilbertRightAngle Geo A D F ∧
      HilbertRightAngle Geo E G F ∧
      Not (Collinear Geo A C E) ∧
      HilbertRightAngle Geo A C E ∧
      Not (Collinear Geo B C E) ∧
      HilbertRightAngle Geo B C E := by

  rcases
      proposition2_9_G_between_CE
        Geo A B C D hMidC hCDB with
    ⟨E, F, G,
      hEFB,
      hCGE,
      hACD,
      hDCE,
      hRightDCE,
      hCE_CB,
      _hCE_DF,
      hParDFGC,
      _hDF_GC,
      _hFG_CD⟩

  --------------------------------------------------------------------
  -- DCE -> DCG -> GCD -> CDF -> ADF.
  --------------------------------------------------------------------

  have hCGEdata :=
    HilbertOrder.between_incidence
      C G E hCGE

  have hCG : C ≠ G :=
    hCGEdata.1

  have hCGEcol :
      Collinear Geo C G E :=
    hCGEdata.2.2.2.1

  have hRayCGE :
      HilbertSameRay Geo C G E :=
    hilbert_sameRay_of_between
      Geo C G E hCGE

  have hDCG :
      Not (Collinear Geo D C G) := by
    intro hDCGcol

    have hDCEcol :
        Collinear Geo D C E :=
      hilbert_primCollinear_trans
        Geo
        D C G E
        hCG
        hDCGcol
        hCGEcol

    exact hDCE hDCEcol

  have hAngleDCG_DCE :
      Geo.Angle D C G =
      Geo.Angle D C E :=
    hilbert_angle_eq_of_sameRay_second
      Geo C D G E hRayCGE

  have hReflDCE :
      Geo.AngleCongruent D C E D C E :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      D C E
      hDCE

  have hDCE_DCG :
      Geo.AngleCongruent D C E D C G := by
    unfold Geometry.Geo.AngleCongruent
      at hReflDCE ⊢
    rw [hAngleDCG_DCE]
    exact hReflDCE

  have hRightDCG :
      HilbertRightAngle Geo D C G :=
    hilbert_right_angle_transport
      Geo
      D C E
      D C G
      hDCE
      hDCG
      hRightDCE
      hDCE_DCG

  have hGCD :
      Not (Collinear Geo G C D) := by
    intro hGCDcol
    exact hDCG
      (PrimCollinearSymm
        Geo G C D hGCDcol)

  have hReflDCG :
      Geo.AngleCongruent D C G D C G :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      D C G
      hDCG

  have hDCG_GCD :
      Geo.AngleCongruent D C G G C D :=
    (Geo.angle_congruent_reverse_second
      D C G
      D C G).mp hReflDCG

  have hRightGCD :
      HilbertRightAngle Geo G C D :=
    hilbert_right_angle_transport
      Geo
      D C G
      G C D
      hDCG
      hGCD
      hRightDCG
      hDCG_GCD

  have hParCDFG :
      IsParallelogram Geo C D F G :=
    ⟨ParallelSymmetry
        Geo F G C D hParDFGC.2,
      hParDFGC.1⟩

  have hRightCDF :
      HilbertRightAngle Geo C D F :=
    parallelogram_adjacent_right_angle
      Geo
      C D F G
      hParCDFG
      hRightGCD

  have hDCA :
      Geo.Between D C A :=
    (HilbertOrder.between_incidence
      A C D hACD).2.2.2.2

  have hRayDCA :
      HilbertSameRay Geo D C A :=
    hilbert_sameRay_of_between
      Geo D C A hDCA

  have hNC_CDFG :=
    parallelogram_vertices_noncollinear
      Geo C D F G hParCDFG

  have hCDF :
      Not (Collinear Geo C D F) :=
    hNC_CDFG.2.1

  have hACDdata :=
    HilbertOrder.between_incidence
      A C D hACD

  have hAD : A ≠ D :=
    hACDdata.2.2.1

  have hACDcol :
      Collinear Geo A C D :=
    hACDdata.2.2.2.1

  have hADCcol :
      Collinear Geo A D C := by
    rcases hACDcol with
      ⟨base, hAbase, hCbase, hDbase⟩
    exact
      ⟨base, hAbase, hDbase, hCbase⟩

  have hADF :
      Not (Collinear Geo A D F) := by
    intro hADFcol

    rcases hADFcol with
      ⟨lineADF, hAadf, hDadf, hFadf⟩

    have hCadf :
        HilbertIncidence.OnLine C lineADF :=
      hilbert_collinear_on_line
        Geo
        A D C
        lineADF
        hAD
        hAadf
        hDadf
        hADCcol

    exact hCDF
      ⟨lineADF,
        hCadf,
        hDadf,
        hFadf⟩

  have hAngleCDF_ADF :
      Geo.Angle C D F =
      Geo.Angle A D F :=
    hilbert_angle_eq_of_sameRay_first
      Geo D C A F hRayDCA

  have hReflCDF :
      Geo.AngleCongruent C D F C D F :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      C D F
      hCDF

  have hCDF_ADF :
      Geo.AngleCongruent C D F A D F := by
    unfold Geometry.Geo.AngleCongruent
      at hReflCDF ⊢
    rw [← hAngleCDF_ADF]
    exact hReflCDF

  have hRightADF :
      HilbertRightAngle Geo A D F :=
    hilbert_right_angle_transport
      Geo
      C D F
      A D F
      hCDF
      hADF
      hRightCDF
      hCDF_ADF

  --------------------------------------------------------------------
  -- CDF -> DFG -> FGC -> CGF -> FGE -> EGF.
  --------------------------------------------------------------------

  have hRightDFG :
      HilbertRightAngle Geo D F G :=
    parallelogram_adjacent_right_angle
      Geo
      D F G C
      hParDFGC
      hRightCDF

  have hParFGCD :
      IsParallelogram Geo F G C D :=
    ⟨hParDFGC.2,
      ParallelSymmetry
        Geo D F G C hParDFGC.1⟩

  have hRightFGC :
      HilbertRightAngle Geo F G C :=
    parallelogram_adjacent_right_angle
      Geo
      F G C D
      hParFGCD
      hRightDFG

  have hNC_FGCD :=
    parallelogram_vertices_noncollinear
      Geo F G C D hParFGCD

  have hFGC :
      Not (Collinear Geo F G C) :=
    hNC_FGCD.2.1

  have hCGF :
      Not (Collinear Geo C G F) := by
    intro hCGFcol
    exact hFGC
      (PrimCollinearSymm
        Geo C G F hCGFcol)

  have hReflFGC :
      Geo.AngleCongruent F G C F G C :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      F G C
      hFGC

  have hFGC_CGF :
      Geo.AngleCongruent F G C C G F :=
    (Geo.angle_congruent_reverse_second
      F G C
      F G C).mp hReflFGC

  have hRightCGF :
      HilbertRightAngle Geo C G F :=
    hilbert_right_angle_transport
      Geo
      F G C
      C G F
      hFGC
      hCGF
      hRightFGC
      hFGC_CGF

  have hCGF_FGE :
      Geo.AngleCongruent C G F F G E :=
    hilbert_right_angle_opposite_extension
      Geo
      C G F E
      hCGF
      hRightCGF
      hCGE

  have hGE : G ≠ E :=
    hCGEdata.2.1

  have hGEC :
      Collinear Geo G E C := by
    rcases hCGEcol with
      ⟨lineCE, hCce, hGce, hEce⟩
    exact
      ⟨lineCE, hGce, hEce, hCce⟩

  have hFGE :
      Not (Collinear Geo F G E) := by
    intro hFGEcol

    have hFGCcol :
        Collinear Geo F G C :=
      hilbert_primCollinear_trans
        Geo
        F G E C
        hGE
        hFGEcol
        hGEC

    exact hFGC hFGCcol

  have hRightFGE :
      HilbertRightAngle Geo F G E :=
    hilbert_right_angle_transport
      Geo
      C G F
      F G E
      hCGF
      hFGE
      hRightCGF
      hCGF_FGE

  have hEGF :
      Not (Collinear Geo E G F) := by
    intro hEGFcol
    exact hFGE
      (PrimCollinearSymm
        Geo E G F hEGFcol)

  have hReflFGE :
      Geo.AngleCongruent F G E F G E :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      F G E
      hFGE

  have hFGE_EGF :
      Geo.AngleCongruent F G E E G F :=
    (Geo.angle_congruent_reverse_second
      F G E
      F G E).mp hReflFGE

  have hRightEGF :
      HilbertRightAngle Geo E G F :=
    hilbert_right_angle_transport
      Geo
      F G E
      E G F
      hFGE
      hEGF
      hRightFGE
      hFGE_EGF

  --------------------------------------------------------------------
  -- DCE -> BCE along C-D-B.
  --------------------------------------------------------------------

  have hCDBdata :=
    HilbertOrder.between_incidence
      C D B hCDB

  have hDB : D ≠ B :=
    hCDBdata.2.1

  have hCB : C ≠ B :=
    hCDBdata.2.2.1

  have hCDBcol :
      Collinear Geo C D B :=
    hCDBdata.2.2.2.1

  have hRayCDB :
      HilbertSameRay Geo C D B :=
    hilbert_sameRay_of_between
      Geo C D B hCDB

  have hBCE :
      Not (Collinear Geo B C E) := by
    intro hBCEcol

    have hCBE :
        Collinear Geo C B E :=
      PrimCollinearSwap
        Geo B C E hBCEcol

    have hDCB :
        Collinear Geo D C B := by
      rcases hCDBcol with
        ⟨base, hCbase, hDbase, hBbase⟩
      exact
        ⟨base, hDbase, hCbase, hBbase⟩

    have hDCEcol :
        Collinear Geo D C E :=
      hilbert_primCollinear_trans
        Geo
        D C B E
        hCB
        hDCB
        hCBE

    exact hDCE hDCEcol

  have hAngleDCE_BCE :
      Geo.Angle D C E =
      Geo.Angle B C E :=
    hilbert_angle_eq_of_sameRay_first
      Geo C D B E hRayCDB

  have hDCE_BCE :
      Geo.AngleCongruent D C E B C E := by
    unfold Geometry.Geo.AngleCongruent
      at hReflDCE ⊢
    rw [← hAngleDCE_BCE]
    exact hReflDCE

  have hRightBCE :
      HilbertRightAngle Geo B C E :=
    hilbert_right_angle_transport
      Geo
      D C E
      B C E
      hDCE
      hBCE
      hRightDCE
      hDCE_BCE

  --------------------------------------------------------------------
  -- DCE -> ACE across the opposite extension A-C-D.
  --------------------------------------------------------------------

  have hACE :
      Not (Collinear Geo A C E) := by
    intro hACEcol

    have hDCAcol :
        Collinear Geo D C A :=
      PrimCollinearSymm
        Geo A C D hACDcol

    have hCAE :
        Collinear Geo C A E :=
      PrimCollinearSwap
        Geo A C E hACEcol

    have hCA : C ≠ A :=
      hACDdata.1.symm

    have hDCEcol :
        Collinear Geo D C E :=
      hilbert_primCollinear_trans
        Geo
        D C A E
        hCA
        hDCAcol
        hCAE

    exact hDCE hDCEcol

  have hDCE_ECA :
      Geo.AngleCongruent D C E E C A :=
    hilbert_right_angle_opposite_extension
      Geo
      D C E A
      hDCE
      hRightDCE
      hDCA

  have hDCE_ACE :
      Geo.AngleCongruent D C E A C E :=
    (Geo.angle_congruent_reverse_second
      D C E
      E C A).mp hDCE_ECA

  have hRightACE :
      HilbertRightAngle Geo A C E :=
    hilbert_right_angle_transport
      Geo
      D C E
      A C E
      hDCE
      hACE
      hRightDCE
      hDCE_ACE

  exact
    ⟨E, F, G,
      hEFB,
      hCGE,
      hACD,
      hCE_CB,
      hParDFGC,
      hRightADF,
      hRightEGF,
      hACE,
      hRightACE,
      hBCE,
      hRightBCE⟩

------------------------------------------------------------------------

------------------------------------------------------------------------
-- Euclid II.9 -- classical angle block
--
-- This file returns to the exact Euclidean DAG:
--
--   I.5 + I.32
--       |
--       v
--   equal half-right angles
--       |
--       v
--   angle AEB is right
--       |
--   E-F-B
--       |
--       v
--   angle AEF is right
------------------------------------------------------------------------

theorem proposition2_9_classical_angle_block
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    ∃ E F G R S : Geo.Point,
      Geo.Between E F B ∧
      Geo.Between C G E ∧
      Geo.Between A C D ∧
      Geo.Congruent C E C B ∧
      IsParallelogram Geo D F G C ∧
      HilbertRightAngle Geo A D F ∧
      HilbertRightAngle Geo E G F ∧
      Not (Collinear Geo A C E) ∧
      HilbertRightAngle Geo A C E ∧
      Not (Collinear Geo B C E) ∧
      HilbertRightAngle Geo B C E ∧
      Geo.Between E R B ∧
      Geo.Between E S A ∧
      Geo.AngleCongruent E C R B C R ∧
      Geo.AngleCongruent E C S A C S ∧
      Geo.AngleCongruent A E C B E C ∧
      HilbertRightAngle Geo A E B ∧
      HilbertRightAngle Geo A E F := by

  rcases
      proposition2_9_right_angle_configuration
        Geo
        A B C D
        hMidC
        hCDB
    with
    ⟨E, F, G,
      hEFB,
      hCGE,
      hACD,
      hCE_CB,
      hPar,
      hRightADF,
      hRightEGF,
      hNoncolACE,
      hRightACE,
      hNoncolBCE,
      hRightBCE⟩

  --------------------------------------------------------------------
  -- Basic midpoint/order data.
  --------------------------------------------------------------------

  have hACB :
      Geo.Between A C B :=
    hMidC.1

  have hBCA :
      Geo.Between B C A :=
    (HilbertOrder.between_incidence
      A C B hACB).2.2.2.2

  have hACBdata :=
    HilbertOrder.between_incidence
      A C B hACB

  have hAB :
      A ≠ B :=
    hACBdata.2.2.1

  have hACBcol :
      PrimCollinear Geo A C B :=
    hACBdata.2.2.2.1

  --------------------------------------------------------------------
  -- AC = CE.
  --------------------------------------------------------------------

  have hCA_CB :
      Geo.Congruent C A C B :=
    CongruentReverseFirst
      Geo
      A C C B
      hMidC.2

  have hCB_CE :
      Geo.Congruent C B C E :=
    hilbert_congruent_symmetry
      Geo
      C E
      C B
      hCE_CB

  have hCA_CE :
      Geo.Congruent C A C E :=
    hilbert_congruent_transitivity
      Geo
      C A
      C B
      C E
      hCA_CB
      hCB_CE

  --------------------------------------------------------------------
  -- I.5 in triangle ACE:
  --
  --     angle EAC = angle AEC.
  --------------------------------------------------------------------

  have hCAE :
      Not (PrimCollinear Geo C A E) := by
    intro h
    exact
      hNoncolACE
        (PrimCollinearSwap
          Geo C A E h)

  have hCAE_CEA :
      Geo.AngleCongruent
        C A E
        C E A :=
    hilbert_isosceles_base_angles
      Geo
      C A E
      hCAE
      hCA_CE

  have hEAC_AEC :
      Geo.AngleCongruent
        E A C
        A E C :=
    AngleCongruentReverse
      Geo
      C A E
      C E A
      hCAE_CEA

  --------------------------------------------------------------------
  -- I.5 in triangle CEB:
  --
  --     angle CEB = angle EBC.
  --------------------------------------------------------------------

  have hCEB :
      Not (PrimCollinear Geo C E B) := by
    intro h

    have hEBC :
        PrimCollinear Geo E B C :=
      PrimCollinearCycle
        Geo C E B h

    have hBCE :
        PrimCollinear Geo B C E :=
      PrimCollinearCycle
        Geo E B C hEBC

    exact hNoncolBCE hBCE

  have hCEB_CBE :
      Geo.AngleCongruent
        C E B
        C B E :=
    hilbert_isosceles_base_angles
      Geo
      C E B
      hCEB
      hCE_CB

  have hBEC_EBC :
      Geo.AngleCongruent
        B E C
        E B C :=
    AngleCongruentReverse
      Geo
      C E B
      C B E
      hCEB_CBE

  --------------------------------------------------------------------
  -- I.32 exterior applied to triangle EAC, with A-C-B.
  --
  -- It produces R on EB such that
  --
  --     AEC = ECR
  --     EAC = RCB.
  --
  -- I.5 therefore says that CR bisects angle ECB.
  --------------------------------------------------------------------

  have hEAC :
      Not (PrimCollinear Geo E A C) := by
    intro h

    have hACE :
        PrimCollinear Geo A C E :=
      PrimCollinearCycle
        Geo E A C h

    exact hNoncolACE hACE

  rcases
      euclid_proposition_32_exterior
        E A C B
        hEAC
        hACB
    with
    ⟨R,
      hERB,
      hAEC_ECR,
      hEAC_RCB⟩

  have hECR_AEC :
      Geo.AngleCongruent
        E C R
        A E C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A E C
      E C R
      hAEC_ECR

  have hECR_EAC :
      Geo.AngleCongruent
        E C R
        E A C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E C R
      A E C
      E A C
      hECR_AEC
      (Geometry.Geo.angle_congruent_symmetry
        Geo
        E A C
        A E C
        hEAC_AEC)

  have hECR_RCB :
      Geo.AngleCongruent
        E C R
        R C B :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E C R
      E A C
      R C B
      hECR_EAC
      hEAC_RCB

  have hBisectR :
      Geo.AngleCongruent
        E C R
        B C R :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      E C R
      R C B).mp
      hECR_RCB

  --------------------------------------------------------------------
  -- I.32 exterior applied to triangle EBC, with B-C-A.
  --
  -- It produces S on EA such that
  --
  --     BEC = ECS
  --     EBC = SCA.
  --
  -- I.5 therefore says that CS bisects angle ECA.
  --------------------------------------------------------------------

  have hEBC :
      Not (PrimCollinear Geo E B C) := by
    intro h

    have hBCE :
        PrimCollinear Geo B C E :=
      PrimCollinearCycle
        Geo E B C h

    exact hNoncolBCE hBCE

  rcases
      euclid_proposition_32_exterior
        E B C A
        hEBC
        hBCA
    with
    ⟨S,
      hESA,
      hBEC_ECS,
      hEBC_SCA⟩

  have hECS_BEC :
      Geo.AngleCongruent
        E C S
        B E C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B E C
      E C S
      hBEC_ECS

  have hECS_EBC :
      Geo.AngleCongruent
        E C S
        E B C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E C S
      B E C
      E B C
      hECS_BEC
      hBEC_EBC

  have hECS_SCA :
      Geo.AngleCongruent
        E C S
        S C A :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E C S
      E B C
      S C A
      hECS_EBC
      hEBC_SCA

  have hBisectS :
      Geo.AngleCongruent
        E C S
        A C S :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      E C S
      S C A).mp
      hECS_SCA

  --------------------------------------------------------------------
  -- Interior-ray witnesses for the two right angles at C.
  --------------------------------------------------------------------

  have hNoncolECB :
      Not (PrimCollinear Geo E C B) := by
    intro h
    exact
      hNoncolBCE
        (PrimCollinearSymm
          Geo E C B h)

  have hNoncolECA :
      Not (PrimCollinear Geo E C A) := by
    intro h
    exact
      hNoncolACE
        (PrimCollinearSymm
          Geo E C A h)

  have hRC :
      R ≠ C := by
    intro hRC
    subst R

    have hECBcol :
        PrimCollinear Geo E C B :=
      (HilbertOrder.between_incidence
        E C B hERB).2.2.2.1

    exact hNoncolECB hECBcol

  have hSC :
      S ≠ C := by
    intro hSC
    subst S

    have hECAcol :
        PrimCollinear Geo E C A :=
      (HilbertOrder.between_incidence
        E C A hESA).2.2.2.1

    exact hNoncolECA hECAcol

  have hInsideR :
      HilbertRayMeetsSegment Geo C R E B :=
    ⟨R,
      hERB,
      hilbert_sameRay_refl
        Geo C R hRC⟩

  have hInsideS :
      HilbertRayMeetsSegment Geo C S E A :=
    ⟨S,
      hESA,
      hilbert_sameRay_refl
        Geo C S hSC⟩

  --------------------------------------------------------------------
  -- The two whole angles ECA and ECB are congruent because ACE is
  -- right and A-C-B.  This is the exact "two right angles" bridge.
  --------------------------------------------------------------------

  have hACE_ECB :
      Geo.AngleCongruent
        A C E
        E C B :=
    hilbert_right_angle_opposite_extension
      Geo
      A C E B
      hNoncolACE
      hRightACE
      hACB

  have hECA_ECB :
      Geo.AngleCongruent
        E C A
        E C B :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      A C E
      E C B).mp
      hACE_ECB

  have hECB_ECA :
      Geo.AngleCongruent
        E C B
        E C A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E C A
      E C B
      hECA_ECB

  --------------------------------------------------------------------
  -- Halves of congruent right angles are congruent:
  --
  --     ECR = ECS.
  --------------------------------------------------------------------

  have hECR_ECS :
      Geo.AngleCongruent
        E C R
        E C S :=
    hilbert_angleDecomposition_halves_congruent_of_whole_congruent
      Geo
      C E B R
      C E A S
      hNoncolECB
      hNoncolECA
      hInsideR
      hInsideS
      hBisectR
      hBisectS
      hECB_ECA

  --------------------------------------------------------------------
  -- Therefore the two half-right angles at E are congruent:
  --
  --     AEC = BEC.
  --------------------------------------------------------------------

  have hECS_BEC' :
      Geo.AngleCongruent
        E C S
        B E C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B E C
      E C S
      hBEC_ECS

  have hAEC_ECS :
      Geo.AngleCongruent
        A E C
        E C S :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A E C
      E C R
      E C S
      hAEC_ECR
      hECR_ECS

  have hAEC_BEC :
      Geo.AngleCongruent
        A E C
        B E C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      A E C
      E C S
      B E C
      hAEC_ECS
      hECS_BEC'

  --------------------------------------------------------------------
  -- EC is an interior ray of angle AEB.
  --------------------------------------------------------------------

  have hCEA :
      Not (PrimCollinear Geo C E A) := by
    intro h

    have hEAC' :
        PrimCollinear Geo E A C :=
      PrimCollinearCycle
        Geo C E A h

    have hACE' :
        PrimCollinear Geo A C E :=
      PrimCollinearCycle
        Geo E A C hEAC'

    exact hNoncolACE hACE'

  have hCE :
      C ≠ E :=
    hilbert_noncollinear_ne_first
      Geo C E A hCEA

  have hInsideC :
      HilbertRayMeetsSegment Geo E C A B :=
    ⟨C,
      hACB,
      hilbert_sameRay_refl
        Geo E C hCE⟩

  --------------------------------------------------------------------
  -- A,E,B are noncollinear.
  --------------------------------------------------------------------

  have hNoncolAEB :
      Not (PrimCollinear Geo A E B) := by
    intro hAEB

    have hABE :
        PrimCollinear Geo A B E :=
      PrimCollinearRotate
        Geo A E B hAEB

    have hCAB :
        PrimCollinear Geo C A B :=
      PrimCollinearSwap
        Geo A C B hACBcol

    have hCAE' :
        PrimCollinear Geo C A E :=
      hilbert_primCollinear_trans
        Geo
        C A B E
        hAB
        hCAB
        hABE

    exact
      hNoncolACE
        (PrimCollinearSwap
          Geo C A E hCAE')

  --------------------------------------------------------------------
  -- Match the second components:
  --
  --     CEB = RCB.
  --------------------------------------------------------------------

  have hAEC_CEB :
      Geo.AngleCongruent
        A E C
        C E B :=
    (Geometry.Geo.angle_congruent_reverse_second
      Geo
      A E C
      B E C).mp
      hAEC_BEC

  have hCEB_AEC :
      Geo.AngleCongruent
        C E B
        A E C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A E C
      C E B
      hAEC_CEB

  have hCEB_ECR :
      Geo.AngleCongruent
        C E B
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C E B
      A E C
      E C R
      hCEB_AEC
      hAEC_ECR

  have hCEB_RCB :
      Geo.AngleCongruent
        C E B
        R C B :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      C E B
      E C R
      R C B
      hCEB_ECR
      hECR_RCB

  --------------------------------------------------------------------
  -- Add the two half-right angles:
  --
  --     angle AEB = angle ECB.
  --------------------------------------------------------------------

  have hAEB_ECB :
      Geo.AngleCongruent
        A E B
        E C B :=
    hilbert_angleDecomposition_angle_addition_interior
      Geo
      E A B C
      C E B R
      hNoncolAEB
      hNoncolECB
      hInsideC
      hInsideR
      hAEC_ECR
      hCEB_RCB

  --------------------------------------------------------------------
  -- ECB is right, hence AEB is right.
  --------------------------------------------------------------------

  have hRightECB :
      HilbertRightAngle Geo E C B :=
    hilbert_right_angle_transport
      Geo
      A C E
      E C B
      hNoncolACE
      hNoncolECB
      hRightACE
      hACE_ECB

  have hECB_AEB :
      Geo.AngleCongruent
        E C B
        A E B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A E B
      E C B
      hAEB_ECB

  have hRightAEB :
      HilbertRightAngle Geo A E B :=
    hilbert_right_angle_transport
      Geo
      E C B
      A E B
      hNoncolECB
      hNoncolAEB
      hRightECB
      hECB_AEB

  --------------------------------------------------------------------
  -- Since E-F-B, EF and EB are the same ray.
  -- Therefore AEF is right as well.
  --------------------------------------------------------------------

  have hRayEFB :
      HilbertSameRay Geo E F B :=
    hilbert_sameRay_of_between
      Geo E F B hEFB

  have hRayEBF :
      HilbertSameRay Geo E B F :=
    hilbert_sameRay_symm
      Geo E F B hRayEFB

  have hAE :
      A ≠ E :=
    hilbert_noncollinear_ne_first
      Geo A E B hNoncolAEB

  have hRayEAA :
      HilbertSameRay Geo E A A :=
    hilbert_sameRay_refl
      Geo E A hAE

  have hNoncolAEF :
      Not (PrimCollinear Geo A E F) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A E B
      A F
      hNoncolAEB
      hRayEAA
      hRayEBF

  have hAngleEqAEB_AEF :
      Geo.Angle A E B =
      Geo.Angle A E F :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      E A B F
      hRayEBF

  have hAEB_AEF :
      Geo.AngleCongruent
        A E B
        A E F := by

    have hRefl :
        Geo.AngleCongruent
          A E F
          A E F :=
      Geometry.Geo.angle_congruent_reflexive
        Geo A E F

    unfold Geometry.Geo.AngleCongruent
      at hRefl ⊢

    rw [hAngleEqAEB_AEF]

    exact hRefl

  have hRightAEF :
      HilbertRightAngle Geo A E F :=
    hilbert_right_angle_transport
      Geo
      A E B
      A E F
      hNoncolAEB
      hNoncolAEF
      hRightAEB
      hAEB_AEF

  exact
    ⟨E, F, G, R, S,
      hEFB,
      hCGE,
      hACD,
      hCE_CB,
      hPar,
      hRightADF,
      hRightEGF,
      hNoncolACE,
      hRightACE,
      hNoncolBCE,
      hRightBCE,
      hERB,
      hESA,
      hBisectR,
      hBisectS,
      hAEC_BEC,
      hRightAEB,
      hRightAEF⟩

------------------------------------------------------------------------

------------------------------------------------------------------------
-- Euclid II.9 -- test 25
--
-- Source-faithful recovery of the two isosceles triangles:
--
--     EG = GF
--     DF = DB
--
-- The old segment-subtraction proof of EG = GF is deliberately ignored.
-- Both equalities are now obtained from the Euclidean angle route:
--
--     right angle + I.32 + angle subtraction + I.6.
------------------------------------------------------------------------

theorem proposition2_9_classical_isosceles_blocks
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    ∃ E F G R S : Geo.Point,
      Geo.Between E F B ∧
      Geo.Between C G E ∧
      Geo.Between A C D ∧
      Geo.Congruent C E C B ∧
      IsParallelogram Geo D F G C ∧
      HilbertRightAngle Geo A D F ∧
      HilbertRightAngle Geo E G F ∧
      Not (Collinear Geo A C E) ∧
      HilbertRightAngle Geo A C E ∧
      Not (Collinear Geo B C E) ∧
      HilbertRightAngle Geo B C E ∧
      Geo.Between E R B ∧
      Geo.Between E S A ∧
      Geo.AngleCongruent E C R B C R ∧
      Geo.AngleCongruent E C S A C S ∧
      Geo.AngleCongruent A E C B E C ∧
      HilbertRightAngle Geo A E B ∧
      HilbertRightAngle Geo A E F ∧
      Geo.Congruent G E G F ∧
      Geo.Congruent D F D B := by

  rcases
      proposition2_9_classical_angle_block
        Geo
        A B C D
        hMidC
        hCDB
    with
    ⟨E, F, G, R, S,
      hEFB,
      hCGE,
      hACD,
      hCE_CB,
      hPar,
      hRightADF,
      hRightEGF,
      hNoncolACE,
      hRightACE,
      hNoncolBCE,
      hRightBCE,
      hERB,
      hESA,
      hBisectR,
      hBisectS,
      hAEC_BEC,
      hRightAEB,
      hRightAEF⟩

  --------------------------------------------------------------------
  -- Shared order data.
  --------------------------------------------------------------------

  have hACB :
      Geo.Between A C B :=
    hMidC.1

  have hBCA :
      Geo.Between B C A :=
    (HilbertOrder.between_incidence
      A C B hACB).2.2.2.2

  have hBDC :
      Geo.Between B D C :=
    (HilbertOrder.between_incidence
      C D B hCDB).2.2.2.2

  have hEGC :
      Geo.Between E G C :=
    (HilbertOrder.between_incidence
      C G E hCGE).2.2.2.2

  have hBFE :
      Geo.Between B F E :=
    (HilbertOrder.between_incidence
      E F B hEFB).2.2.2.2

  have hDCA :
      Geo.Between D C A :=
    (HilbertOrder.between_incidence
      A C D hACD).2.2.2.2

  have hParNC :=
    parallelogram_vertices_noncollinear
      Geo D F G C hPar

  have hNoncolCDF :
      Not (Collinear Geo C D F) :=
    hParNC.1

  have hNoncolDFG :
      Not (Collinear Geo D F G) :=
    hParNC.2.1

  have hNoncolFGC :
      Not (Collinear Geo F G C) :=
    hParNC.2.2.1

  --------------------------------------------------------------------
  -- Noncollinearity of EGF.
  --------------------------------------------------------------------

  have hGE :
      G ≠ E :=
    (HilbertOrder.between_incidence
      C G E hCGE).2.1

  have hCGEcol :
      PrimCollinear Geo C G E :=
    (HilbertOrder.between_incidence
      C G E hCGE).2.2.2.1

  have hEGCcol :
      PrimCollinear Geo E G C :=
    PrimCollinearSymm
      Geo C G E hCGEcol

  have hNoncolEGF :
      Not (Collinear Geo E G F) := by
    intro hEGF

    have hFGE :
        PrimCollinear Geo F G E :=
      PrimCollinearSymm
        Geo E G F hEGF

    have hGEC :
        PrimCollinear Geo G E C :=
      PrimCollinearSwap
        Geo E G C hEGCcol

    have hFGE_C :
        PrimCollinear Geo F G C :=
      hilbert_primCollinear_trans
        Geo
        F G E C
        hGE
        hFGE
        hGEC

    exact hNoncolFGC hFGE_C

  have hNoncolGEF :
      Not (Collinear Geo G E F) := by
    intro h
    exact
      hNoncolEGF
        (PrimCollinearSwap
          Geo G E F h)

  --------------------------------------------------------------------
  -- Right angle FGC.
  --
  -- E-G-C and EGF right imply the adjacent angle FGC is right.
  --------------------------------------------------------------------

  have hEGF_FGC :
      Geo.AngleCongruent
        E G F
        F G C :=
    hilbert_right_angle_opposite_extension
      Geo
      E G F C
      hNoncolEGF
      hRightEGF
      hEGC

  have hRightFGC :
      HilbertRightAngle Geo F G C :=
    hilbert_right_angle_transport
      Geo
      E G F
      F G C
      hNoncolEGF
      hNoncolFGC
      hRightEGF
      hEGF_FGC

  --------------------------------------------------------------------
  -- Right angle ECB.
  --------------------------------------------------------------------

  have hNoncolECB :
      Not (Collinear Geo E C B) := by
    intro h
    exact
      hNoncolBCE
        (PrimCollinearSymm
          Geo E C B h)

  have hBCE_ECB :
      Geo.AngleCongruent
        B C E
        E C B := by
    have hRefl :
        Geo.AngleCongruent
          B C E
          B C E :=
      Geometry.Geo.angle_congruent_reflexive
        Geo B C E

    exact
      (Geometry.Geo.angle_congruent_reverse_second
        Geo
        B C E
        B C E).mp
        hRefl

  have hRightECB :
      HilbertRightAngle Geo E C B :=
    hilbert_right_angle_transport
      Geo
      B C E
      E C B
      hNoncolBCE
      hNoncolECB
      hRightBCE
      hBCE_ECB

  --------------------------------------------------------------------
  -- AEB is noncollinear, and EC is its interior bisector.
  --------------------------------------------------------------------

  have hACBdata :=
    HilbertOrder.between_incidence
      A C B hACB

  have hAB :
      A ≠ B :=
    hACBdata.2.2.1

  have hACBcol :
      PrimCollinear Geo A C B :=
    hACBdata.2.2.2.1

  have hNoncolAEB :
      Not (Collinear Geo A E B) := by
    intro hAEB

    have hABE :
        PrimCollinear Geo A B E :=
      PrimCollinearRotate
        Geo A E B hAEB

    have hCAB :
        PrimCollinear Geo C A B :=
      PrimCollinearSwap
        Geo A C B hACBcol

    have hCAE :
        PrimCollinear Geo C A E :=
      hilbert_primCollinear_trans
        Geo
        C A B E
        hAB
        hCAB
        hABE

    exact
      hNoncolACE
        (PrimCollinearSwap
          Geo C A E hCAE)

  have hCEA :
      Not (PrimCollinear Geo C E A) := by
    intro h

    have hEAC :
        PrimCollinear Geo E A C :=
      PrimCollinearCycle
        Geo C E A h

    have hACE :
        PrimCollinear Geo A C E :=
      PrimCollinearCycle
        Geo E A C hEAC

    exact hNoncolACE hACE

  have hCE :
      C ≠ E :=
    hilbert_noncollinear_ne_first
      Geo C E A hCEA

  have hInsideC_AEB :
      HilbertRayMeetsSegment Geo E C A B :=
    ⟨C,
      hACB,
      hilbert_sameRay_refl
        Geo E C hCE⟩

  --------------------------------------------------------------------
  -- CR is the interior bisector of the right angle ECB.
  --------------------------------------------------------------------

  have hRC :
      R ≠ C := by
    intro hRC
    subst R

    have hECBcol :
        PrimCollinear Geo E C B :=
      (HilbertOrder.between_incidence
        E C B hERB).2.2.2.1

    exact hNoncolECB hECBcol

  have hInsideR_ECB :
      HilbertRayMeetsSegment Geo C R E B :=
    ⟨R,
      hERB,
      hilbert_sameRay_refl
        Geo C R hRC⟩

  --------------------------------------------------------------------
  -- Since AEB and ECB are right angles, their halves AEC and ECR
  -- are congruent.
  --------------------------------------------------------------------

  have hAEB_ECB :
      Geo.AngleCongruent
        A E B
        E C B :=
    hilbert_all_right_angles_congruent
      Geo
      A E B
      E C B
      hNoncolAEB
      hNoncolECB
      hRightAEB
      hRightECB

  have hAEC_ECR :
      Geo.AngleCongruent
        A E C
        E C R :=
    hilbert_angleDecomposition_halves_congruent_of_whole_congruent
      Geo
      E A B C
      C E B R
      hNoncolAEB
      hNoncolECB
      hInsideC_AEB
      hInsideR_ECB
      hAEC_BEC
      hBisectR
      hAEB_ECB

  have hBEC_AEC :
      Geo.AngleCongruent
        B E C
        A E C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      A E C
      B E C
      hAEC_BEC

  have hBEC_ECR :
      Geo.AngleCongruent
        B E C
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B E C
      A E C
      E C R
      hBEC_AEC
      hAEC_ECR

  --------------------------------------------------------------------
  -- Transport angle FEG to BEC using E-F-B and E-G-C.
  --------------------------------------------------------------------

  have hRayEFB :
      HilbertSameRay Geo E F B :=
    hilbert_sameRay_of_between
      Geo E F B hEFB

  have hRayEGC :
      HilbertSameRay Geo E G C :=
    hilbert_sameRay_of_between
      Geo E G C hEGC

  have hFEG_BEC_eq :
      Geo.Angle F E G =
      Geo.Angle B E C := by
    calc
      Geo.Angle F E G
          = Geo.Angle B E G :=
        hilbert_angle_eq_of_sameRay_first
          Geo E F B G hRayEFB
      _ = Geo.Angle B E C :=
        hilbert_angle_eq_of_sameRay_second
          Geo E B G C hRayEGC

  have hFEG_BEC :
      Geo.AngleCongruent
        F E G
        B E C := by
    have hRefl :
        Geo.AngleCongruent
          B E C
          B E C :=
      Geometry.Geo.angle_congruent_reflexive
        Geo B E C

    unfold Geometry.Geo.AngleCongruent
      at hRefl ⊢

    rw [hFEG_BEC_eq]

    exact hRefl

  have hFEG_ECR :
      Geo.AngleCongruent
        F E G
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      F E G
      B E C
      E C R
      hFEG_BEC
      hBEC_ECR

  --------------------------------------------------------------------
  -- I.32 in triangle FEG, extending EG through G to C.
  --------------------------------------------------------------------

  have hNoncolFEG :
      Not (Collinear Geo F E G) := by
    intro h
    exact
      hNoncolEGF
        (PrimCollinearCycle
          Geo F E G h)

  rcases
      euclid_proposition_32_exterior
        F E G C
        hNoncolFEG
        hEGC
    with
    ⟨T,
      hFTC,
      hEFG_FGT,
      hFEG_TGC⟩

  have hTG :
      T ≠ G := by
    intro hTG
    subst T

    have hFGCcol :
        PrimCollinear Geo F G C :=
      (HilbertOrder.between_incidence
        F G C hFTC).2.2.2.1

    exact hNoncolFGC hFGCcol

  have hInsideT_FGC :
      HilbertRayMeetsSegment Geo G T F C :=
    ⟨T,
      hFTC,
      hilbert_sameRay_refl
        Geo G T hTG⟩

  --------------------------------------------------------------------
  -- The I.32 component TGC is the same half-right angle as ECR.
  --------------------------------------------------------------------

  have hTGC_FEG :
      Geo.AngleCongruent
        T G C
        F E G :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      F E G
      T G C
      hFEG_TGC

  have hTGC_ECR :
      Geo.AngleCongruent
        T G C
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      T G C
      F E G
      E C R
      hTGC_FEG
      hFEG_ECR

  have hTGC_BCR :
      Geo.AngleCongruent
        T G C
        B C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      T G C
      E C R
      B C R
      hTGC_ECR
      hBisectR

  have hCGT_BCR :
      Geo.AngleCongruent
        C G T
        B C R :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      T G C
      B C R).mp
      hTGC_BCR

  --------------------------------------------------------------------
  -- FGC and ECB are right.  Subtract the equal components CGT/BCR.
  -- The remaining components FGT/ECR are congruent.
  --------------------------------------------------------------------

  have hFGC_ECB :
      Geo.AngleCongruent
        F G C
        E C B :=
    hilbert_all_right_angles_congruent
      Geo
      F G C
      E C B
      hNoncolFGC
      hNoncolECB
      hRightFGC
      hRightECB

  have hFGT_ECR :
      Geo.AngleCongruent
        F G T
        E C R :=
    hilbert_angleDecomposition_angle_subtraction
      Geo
      G F C T
      E C B R
      hNoncolFGC
      hNoncolECB
      hInsideT_FGC
      hInsideR_ECB
      hFGC_ECB
      hCGT_BCR

  --------------------------------------------------------------------
  -- Therefore the two base angles of triangle GEF are congruent.
  --------------------------------------------------------------------

  have hEFG_ECR :
      Geo.AngleCongruent
        E F G
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E F G
      F G T
      E C R
      hEFG_FGT
      hFGT_ECR

  have hGEF_BEC :
      Geo.AngleCongruent
        G E F
        B E C := by

    have hGEF_BEC_eq :
        Geo.Angle G E F =
        Geo.Angle B E C := by
      calc
        Geo.Angle G E F
            = Geo.Angle C E F :=
          hilbert_angle_eq_of_sameRay_first
            Geo E G C F hRayEGC
        _ = Geo.Angle C E B :=
          hilbert_angle_eq_of_sameRay_second
            Geo E C F B hRayEFB
        _ = Geo.Angle B E C :=
          Geometry.Geo.angle_swap
            Geo C E B

    have hRefl :
        Geo.AngleCongruent
          B E C
          B E C :=
      Geometry.Geo.angle_congruent_reflexive
        Geo B E C

    unfold Geometry.Geo.AngleCongruent
      at hRefl ⊢

    rw [hGEF_BEC_eq]

    exact hRefl

  have hGEF_ECR :
      Geo.AngleCongruent
        G E F
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      G E F
      B E C
      E C R
      hGEF_BEC
      hBEC_ECR

  have hGFE_ECR :
      Geo.AngleCongruent
        G F E
        E C R :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      E F G
      E C R).mp
      hEFG_ECR

  have hECR_GFE :
      Geo.AngleCongruent
        E C R
        G F E :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      G F E
      E C R
      hGFE_ECR

  have hGEF_GFE :
      Geo.AngleCongruent
        G E F
        G F E :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      G E F
      E C R
      G F E
      hGEF_ECR
      hECR_GFE

  have hGE_GF :
      Geo.Congruent G E G F :=
    euclid_proposition_6
      Geo
      G E F
      hNoncolGEF
      hGEF_GFE

  --------------------------------------------------------------------
  --------------------------------------------------------------------
  -- SECOND CLASSICAL ISOSCELES BLOCK: DF = DB
  --------------------------------------------------------------------
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- ECA is right.
  --------------------------------------------------------------------

  have hNoncolECA :
      Not (Collinear Geo E C A) := by
    intro h
    exact
      hNoncolACE
        (PrimCollinearSymm
          Geo E C A h)

  have hACE_ECA :
      Geo.AngleCongruent
        A C E
        E C A := by
    have hRefl :
        Geo.AngleCongruent
          A C E
          A C E :=
      Geometry.Geo.angle_congruent_reflexive
        Geo A C E

    exact
      (Geometry.Geo.angle_congruent_reverse_second
        Geo
        A C E
        A C E).mp
        hRefl

  have hRightECA :
      HilbertRightAngle Geo E C A :=
    hilbert_right_angle_transport
      Geo
      A C E
      E C A
      hNoncolACE
      hNoncolECA
      hRightACE
      hACE_ECA

  --------------------------------------------------------------------
  -- CS is the interior bisector of ECA.
  --------------------------------------------------------------------

  have hSC :
      S ≠ C := by
    intro hSC
    subst S

    have hECAcol :
        PrimCollinear Geo E C A :=
      (HilbertOrder.between_incidence
        E C A hESA).2.2.2.1

    exact hNoncolECA hECAcol

  have hInsideS_ECA :
      HilbertRayMeetsSegment Geo C S E A :=
    ⟨S,
      hESA,
      hilbert_sameRay_refl
        Geo C S hSC⟩

  --------------------------------------------------------------------
  -- AEC and ECS are halves of congruent right angles AEB and ECA.
  --------------------------------------------------------------------

  have hAEB_ECA :
      Geo.AngleCongruent
        A E B
        E C A :=
    hilbert_all_right_angles_congruent
      Geo
      A E B
      E C A
      hNoncolAEB
      hNoncolECA
      hRightAEB
      hRightECA

  have hAEC_ECS :
      Geo.AngleCongruent
        A E C
        E C S :=
    hilbert_angleDecomposition_halves_congruent_of_whole_congruent
      Geo
      E A B C
      C E A S
      hNoncolAEB
      hNoncolECA
      hInsideC_AEB
      hInsideS_ECA
      hAEC_BEC
      hBisectS
      hAEB_ECA

  --------------------------------------------------------------------
  -- I.5 in CEB: BEC = EBC.
  --------------------------------------------------------------------

  have hCEB :
      Not (PrimCollinear Geo C E B) := by
    intro h

    have hEBC :
        PrimCollinear Geo E B C :=
      PrimCollinearCycle
        Geo C E B h

    have hBCE :
        PrimCollinear Geo B C E :=
      PrimCollinearCycle
        Geo E B C hEBC

    exact hNoncolBCE hBCE

  have hCEB_CBE :
      Geo.AngleCongruent
        C E B
        C B E :=
    hilbert_isosceles_base_angles
      Geo
      C E B
      hCEB
      hCE_CB

  have hBEC_EBC :
      Geo.AngleCongruent
        B E C
        E B C :=
    AngleCongruentReverse
      Geo
      C E B
      C B E
      hCEB_CBE

  have hEBC_BEC :
      Geo.AngleCongruent
        E B C
        B E C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      B E C
      E B C
      hBEC_EBC

  have hEBC_AEC :
      Geo.AngleCongruent
        E B C
        A E C :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E B C
      B E C
      A E C
      hEBC_BEC
      hBEC_AEC

  have hEBC_ECS :
      Geo.AngleCongruent
        E B C
        E C S :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E B C
      A E C
      E C S
      hEBC_AEC
      hAEC_ECS

  --------------------------------------------------------------------
  -- Transport FBD to EBC using B-F-E and B-D-C.
  --------------------------------------------------------------------

  have hRayBFE :
      HilbertSameRay Geo B F E :=
    hilbert_sameRay_of_between
      Geo B F E hBFE

  have hRayBDC :
      HilbertSameRay Geo B D C :=
    hilbert_sameRay_of_between
      Geo B D C hBDC

  have hFBD_EBC_eq :
      Geo.Angle F B D =
      Geo.Angle E B C := by
    calc
      Geo.Angle F B D
          = Geo.Angle E B D :=
        hilbert_angle_eq_of_sameRay_first
          Geo B F E D hRayBFE
      _ = Geo.Angle E B C :=
        hilbert_angle_eq_of_sameRay_second
          Geo B E D C hRayBDC

  have hFBD_EBC :
      Geo.AngleCongruent
        F B D
        E B C := by
    have hRefl :
        Geo.AngleCongruent
          E B C
          E B C :=
      Geometry.Geo.angle_congruent_reflexive
        Geo E B C

    unfold Geometry.Geo.AngleCongruent
      at hRefl ⊢

    rw [hFBD_EBC_eq]

    exact hRefl

  have hFBD_ECS :
      Geo.AngleCongruent
        F B D
        E C S :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      F B D
      E B C
      E C S
      hFBD_EBC
      hEBC_ECS

  --------------------------------------------------------------------
  -- Triangle FBD is noncollinear.
  --------------------------------------------------------------------

  have hDB :
      D ≠ B :=
    (HilbertOrder.between_incidence
      C D B hCDB).2.1

  have hCDBcol :
      PrimCollinear Geo C D B :=
    (HilbertOrder.between_incidence
      C D B hCDB).2.2.2.1

  have hNoncolFBD :
      Not (Collinear Geo F B D) := by
    intro hFBD

    have hDBF :
        PrimCollinear Geo D B F :=
      PrimCollinearSymm
        Geo F B D hFBD

    have hCDB_F :
        PrimCollinear Geo C D F :=
      hilbert_primCollinear_trans
        Geo
        C D B F
        hDB
        hCDBcol
        hDBF

    exact hNoncolCDF hCDB_F

  --------------------------------------------------------------------
  -- I.32 in triangle FBD, extending BD through D to C.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_32_exterior
        F B D C
        hNoncolFBD
        hBDC
    with
    ⟨U,
      hFUC,
      hBFD_FDU,
      hFBD_UDC⟩

  --------------------------------------------------------------------
  -- CDF is right: DA and DC are the same ray from D.
  --------------------------------------------------------------------

  have hRayDCA :
      HilbertSameRay Geo D C A :=
    hilbert_sameRay_of_between
      Geo D C A hDCA

  have hRayDAC :
      HilbertSameRay Geo D A C :=
    hilbert_sameRay_symm
      Geo D C A hRayDCA

  have hADF_CDF_eq :
      Geo.Angle A D F =
      Geo.Angle C D F :=
    hilbert_angle_eq_of_sameRay_first
      Geo D A C F hRayDAC

  have hADF_CDF :
      Geo.AngleCongruent
        A D F
        C D F := by
    have hRefl :
        Geo.AngleCongruent
          C D F
          C D F :=
      Geometry.Geo.angle_congruent_reflexive
        Geo C D F

    unfold Geometry.Geo.AngleCongruent
      at hRefl ⊢

    rw [hADF_CDF_eq]

    exact hRefl

  have hNoncolADF :
      Not (Collinear Geo A D F) := by
    intro hADF

    have hADCcol :
        PrimCollinear Geo A D C := by
      have hACDcol :
          PrimCollinear Geo A C D :=
        (HilbertOrder.between_incidence
          A C D hACD).2.2.2.1
      exact
        PrimCollinearRotate
          Geo A C D hACDcol

    have hDAF :
        PrimCollinear Geo D A F :=
      PrimCollinearSwap
        Geo A D F hADF

    have hCDA :
        PrimCollinear Geo C D A :=
      PrimCollinearSymm
        Geo A D C hADCcol

    have hCDF :
        PrimCollinear Geo C D F :=
      hilbert_primCollinear_trans
        Geo
        C D A F
        (HilbertOrder.between_incidence
          A C D hACD).2.2.1.symm
        hCDA
        hDAF

    exact hNoncolCDF hCDF

  have hRightCDF :
      HilbertRightAngle Geo C D F :=
    hilbert_right_angle_transport
      Geo
      A D F
      C D F
      hNoncolADF
      hNoncolCDF
      hRightADF
      hADF_CDF

  --------------------------------------------------------------------
  -- U is an interior ray of CDF.
  --------------------------------------------------------------------

  have hCUF :
      Geo.Between C U F :=
    (HilbertOrder.between_incidence
      F U C hFUC).2.2.2.2

  have hUD :
      U ≠ D := by
    intro hUD
    subst U

    have hCDFcol :
        PrimCollinear Geo C D F :=
      (HilbertOrder.between_incidence
        C D F hCUF).2.2.2.1

    exact hNoncolCDF hCDFcol

  have hInsideU_CDF :
      HilbertRayMeetsSegment Geo D U C F :=
    ⟨U,
      hCUF,
      hilbert_sameRay_refl
        Geo D U hUD⟩

  --------------------------------------------------------------------
  -- The I.32 component CDU is congruent to ECS.
  --------------------------------------------------------------------

  have hUDC_FBD :
      Geo.AngleCongruent
        U D C
        F B D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      F B D
      U D C
      hFBD_UDC

  have hUDC_ECS :
      Geo.AngleCongruent
        U D C
        E C S :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      U D C
      F B D
      E C S
      hUDC_FBD
      hFBD_ECS

  have hCDU_ECS :
      Geo.AngleCongruent
        C D U
        E C S :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      U D C
      E C S).mp
      hUDC_ECS

  --------------------------------------------------------------------
  -- CDF and ECA are right.  Subtract the equal left components
  -- CDU/ECS.  The remaining components FDU/ACS are congruent.
  --------------------------------------------------------------------

  have hCDF_ECA :
      Geo.AngleCongruent
        C D F
        E C A :=
    hilbert_all_right_angles_congruent
      Geo
      C D F
      E C A
      hNoncolCDF
      hNoncolECA
      hRightCDF
      hRightECA

  have hFDU_ACS :
      Geo.AngleCongruent
        F D U
        A C S :=
    hilbert_angleDecomposition_angle_subtraction_right
      Geo
      D C F U
      E C A S
      hNoncolCDF
      hNoncolECA
      hInsideU_CDF
      hInsideS_ECA
      hCDF_ECA
      hCDU_ECS

  have hACS_ECS :
      Geo.AngleCongruent
        A C S
        E C S :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E C S
      A C S
      hBisectS

  have hFDU_ECS :
      Geo.AngleCongruent
        F D U
        E C S :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      F D U
      A C S
      E C S
      hFDU_ACS
      hACS_ECS

  --------------------------------------------------------------------
  -- Therefore the two base angles of triangle DFB are congruent.
  --------------------------------------------------------------------

  have hBFD_ECS :
      Geo.AngleCongruent
        B F D
        E C S :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B F D
      F D U
      E C S
      hBFD_FDU
      hFDU_ECS

  have hDFB_ECS :
      Geo.AngleCongruent
        D F B
        E C S :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      B F D
      E C S).mp
      hBFD_ECS

  have hDBF_ECS :
      Geo.AngleCongruent
        D B F
        E C S :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      F B D
      E C S).mp
      hFBD_ECS

  have hECS_DBF :
      Geo.AngleCongruent
        E C S
        D B F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      D B F
      E C S
      hDBF_ECS

  have hDFB_DBF :
      Geo.AngleCongruent
        D F B
        D B F :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      D F B
      E C S
      D B F
      hDFB_ECS
      hECS_DBF

  have hNoncolDFB :
      Not (Collinear Geo D F B) := by
    intro h
    exact
      hNoncolFBD
        (PrimCollinearCycle
          Geo D F B h)

  have hDF_DB :
      Geo.Congruent D F D B :=
    euclid_proposition_6
      Geo
      D F B
      hNoncolDFB
      hDFB_DBF

  exact
    ⟨E, F, G, R, S,
      hEFB,
      hCGE,
      hACD,
      hCE_CB,
      hPar,
      hRightADF,
      hRightEGF,
      hNoncolACE,
      hRightACE,
      hNoncolBCE,
      hRightBCE,
      hERB,
      hESA,
      hBisectR,
      hBisectS,
      hAEC_BEC,
      hRightAEB,
      hRightAEF,
      hGE_GF,
      hDF_DB⟩

------------------------------------------------------------------------

------------------------------------------------------------------------
-- Euclid II.9 -- test 26
--
-- Source-faithful metric/scissors bridge:
--
--   I.34: GF = CD
--
--   I.47 on:
--     ACE
--     EGF
--     AEF
--     ADF
--
-- No Book-II proposition is used.
------------------------------------------------------------------------

theorem proposition2_9_four_pythagoras_blocks
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    ∃ E F G : Geo.Point,

      ------------------------------------------------------------------
      -- Classical side equalities needed later.
      ------------------------------------------------------------------

      Geo.Congruent C A C E ∧
      Geo.Congruent G E G F ∧
      Geo.Congruent G F C D ∧
      Geo.Congruent D F D B ∧

      ------------------------------------------------------------------
      -- I.47 on triangle C-A-E, right at C.
      --
      -- The square on AE equals the squares on CA and CE.
      ------------------------------------------------------------------

      (∃ QAE0 QAE1 QCA0 QCA1 QCE0 QCE1 : Geo.Point,
        IsSquare Geo A E QAE1 QAE0 ∧
        IsSquare Geo C A QCA0 QCA1 ∧
        IsSquare Geo C E QCE1 QCE0 ∧
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo A E QAE1 QAE0)
          (hilbertParallelogramTerm Geo C A QCA0 QCA1 +
           hilbertParallelogramTerm Geo C E QCE1 QCE0)) ∧

      ------------------------------------------------------------------
      -- I.47 on triangle G-E-F, right at G.
      --
      -- The square on EF equals the squares on GE and GF.
      ------------------------------------------------------------------

      (∃ QEF0 QEF1 QGE0 QGE1 QGF0 QGF1 : Geo.Point,
        IsSquare Geo E F QEF1 QEF0 ∧
        IsSquare Geo G E QGE0 QGE1 ∧
        IsSquare Geo G F QGF1 QGF0 ∧
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo E F QEF1 QEF0)
          (hilbertParallelogramTerm Geo G E QGE0 QGE1 +
           hilbertParallelogramTerm Geo G F QGF1 QGF0)) ∧

      ------------------------------------------------------------------
      -- I.47 on triangle E-A-F, right at E.
      --
      -- The square on AF equals the squares on EA and EF.
      ------------------------------------------------------------------

      (∃ QAF0 QAF1 QEA0 QEA1 QEF2 QEF3 : Geo.Point,
        IsSquare Geo A F QAF1 QAF0 ∧
        IsSquare Geo E A QEA0 QEA1 ∧
        IsSquare Geo E F QEF3 QEF2 ∧
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo A F QAF1 QAF0)
          (hilbertParallelogramTerm Geo E A QEA0 QEA1 +
           hilbertParallelogramTerm Geo E F QEF3 QEF2)) ∧

      ------------------------------------------------------------------
      -- I.47 on triangle D-A-F, right at D.
      --
      -- The square on AF equals the squares on DA and DF.
      ------------------------------------------------------------------

      (∃ QAF2 QAF3 QDA0 QDA1 QDF0 QDF1 : Geo.Point,
        IsSquare Geo A F QAF3 QAF2 ∧
        IsSquare Geo D A QDA0 QDA1 ∧
        IsSquare Geo D F QDF1 QDF0 ∧
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo A F QAF3 QAF2)
          (hilbertParallelogramTerm Geo D A QDA0 QDA1 +
           hilbertParallelogramTerm Geo D F QDF1 QDF0)) := by

  rcases
      proposition2_9_classical_isosceles_blocks
        Geo
        A B C D
        hMidC
        hCDB
    with
    ⟨E, F, G, R, S,
      hEFB,
      hCGE,
      hACD,
      hCE_CB,
      hPar,
      hRightADF,
      hRightEGF,
      hNoncolACE,
      hRightACE,
      hNoncolBCE,
      hRightBCE,
      hERB,
      hESA,
      hBisectR,
      hBisectS,
      hAEC_BEC,
      hRightAEB,
      hRightAEF,
      hGE_GF,
      hDF_DB⟩

  --------------------------------------------------------------------
  -- AC = CE.
  --------------------------------------------------------------------

  have hCA_CB :
      Geo.Congruent C A C B :=
    CongruentReverseFirst
      Geo
      A C C B
      hMidC.2

  have hCB_CE :
      Geo.Congruent C B C E :=
    hilbert_congruent_symmetry
      Geo
      C E C B
      hCE_CB

  have hCA_CE :
      Geo.Congruent C A C E :=
    hilbert_congruent_transitivity
      Geo
      C A
      C B
      C E
      hCA_CB
      hCB_CE

  --------------------------------------------------------------------
  -- I.34 on parallelogram D-F-G-C:
  --
  --     FG = CD,
  --
  -- hence GF = CD.
  --------------------------------------------------------------------

  have hI34 :=
    euclid_proposition_34
      Geo
      D F G C
      hPar

  have hFG_CD :
      Geo.Congruent F G C D :=
    hI34.1.2

  have hGF_CD :
      Geo.Congruent G F C D :=
    CongruentReverseFirst
      Geo
      F G C D
      hFG_CD

  --------------------------------------------------------------------
  -- Noncollinearity for triangle C-A-E.
  --------------------------------------------------------------------

  have hNoncolCAE :
      Not (Collinear Geo C A E) := by
    intro h
    exact
      hNoncolACE
        (PrimCollinearSwap
          Geo C A E h)

  --------------------------------------------------------------------
  -- Noncollinearity for triangle G-E-F.
  --------------------------------------------------------------------

  have hGE :
      G ≠ E :=
    (HilbertOrder.between_incidence
      C G E hCGE).2.1

  have hCGEcol :
      PrimCollinear Geo C G E :=
    (HilbertOrder.between_incidence
      C G E hCGE).2.2.2.1

  have hParNC :=
    parallelogram_vertices_noncollinear
      Geo D F G C hPar

  have hNoncolFGC :
      Not (Collinear Geo F G C) :=
    hParNC.2.2.1

  have hNoncolGEF :
      Not (Collinear Geo G E F) := by
    intro hGEF

    have hFGE :
        PrimCollinear Geo F G E :=
      PrimCollinearCycle
        Geo E F G
        (PrimCollinearCycle
          Geo G E F hGEF)

    have hGEC :
        PrimCollinear Geo G E C :=
      PrimCollinearCycle
        Geo C G E hCGEcol

    have hFGC :
        PrimCollinear Geo F G C :=
      hilbert_primCollinear_trans
        Geo
        F G E C
        hGE
        hFGE
        hGEC

    exact hNoncolFGC hFGC

  --------------------------------------------------------------------
  -- Noncollinearity for triangle E-A-F.
  --
  -- E-F-B and A,E,B noncollinear.
  --------------------------------------------------------------------

  have hACB :
      Geo.Between A C B :=
    hMidC.1

  have hACBdata :=
    HilbertOrder.between_incidence
      A C B hACB

  have hAB :
      A ≠ B :=
    hACBdata.2.2.1

  have hACBcol :
      PrimCollinear Geo A C B :=
    hACBdata.2.2.2.1

  have hNoncolAEB :
      Not (Collinear Geo A E B) := by
    intro hAEB

    have hABE :
        PrimCollinear Geo A B E :=
      PrimCollinearRotate
        Geo A E B hAEB

    have hCAB :
        PrimCollinear Geo C A B :=
      PrimCollinearSwap
        Geo A C B hACBcol

    have hCAE :
        PrimCollinear Geo C A E :=
      hilbert_primCollinear_trans
        Geo
        C A B E
        hAB
        hCAB
        hABE

    exact
      hNoncolACE
        (PrimCollinearSwap
          Geo C A E hCAE)

  have hRayEFB :
      HilbertSameRay Geo E F B :=
    hilbert_sameRay_of_between
      Geo E F B hEFB

  have hRayEBF :
      HilbertSameRay Geo E B F :=
    hilbert_sameRay_symm
      Geo E F B hRayEFB

  have hAE :
      A ≠ E :=
    hilbert_noncollinear_ne_first
      Geo A E B hNoncolAEB

  have hRayEAA :
      HilbertSameRay Geo E A A :=
    hilbert_sameRay_refl
      Geo E A hAE

  have hNoncolAEF :
      Not (Collinear Geo A E F) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A E B
      A F
      hNoncolAEB
      hRayEAA
      hRayEBF

  have hNoncolEAF_clean :
      Not (Collinear Geo E A F) := by
    intro h
    exact
      hNoncolAEF
        (PrimCollinearSwap
          Geo E A F h)

  --------------------------------------------------------------------
  -- Noncollinearity for triangle D-A-F.
  --------------------------------------------------------------------

  have hNoncolCDF :
      Not (Collinear Geo C D F) :=
    hParNC.1

  have hADCcol :
      PrimCollinear Geo A D C := by
    have hACDcol :
        PrimCollinear Geo A C D :=
      (HilbertOrder.between_incidence
        A C D hACD).2.2.2.1
    exact
      PrimCollinearRotate
        Geo A C D hACDcol

  have hCDA :
      PrimCollinear Geo C D A :=
    PrimCollinearSymm
      Geo A D C hADCcol

  have hDA :
      D ≠ A :=
    (HilbertOrder.between_incidence
      A C D hACD).2.2.1.symm

  have hNoncolDAF :
      Not (Collinear Geo D A F) := by
    intro hDAF

    have hCDF :
        PrimCollinear Geo C D F :=
      hilbert_primCollinear_trans
        Geo
        C D A F
        hDA
        hCDA
        hDAF

    exact hNoncolCDF hCDF

  --------------------------------------------------------------------
  -- I.47 #1: C-A-E.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        C A E
        hNoncolCAE
        hRightACE
    with
    ⟨QAE0, QAE1,
      QCA0, QCA1,
      QCE0, QCE1,
      hSqAE,
      hSqCA,
      hSqCE,
      hPythACE⟩

  --------------------------------------------------------------------
  -- I.47 #2: G-E-F.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        G E F
        hNoncolGEF
        hRightEGF
    with
    ⟨QEF0, QEF1,
      QGE0, QGE1,
      QGF0, QGF1,
      hSqEF,
      hSqGE,
      hSqGF,
      hPythEGF⟩

  --------------------------------------------------------------------
  -- I.47 #3: E-A-F.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        E A F
        hNoncolEAF_clean
        hRightAEF
    with
    ⟨QAF0, QAF1,
      QEA0, QEA1,
      QEF2, QEF3,
      hSqAF,
      hSqEA,
      hSqEF2,
      hPythAEF⟩

  --------------------------------------------------------------------
  -- I.47 #4: D-A-F.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        D A F
        hNoncolDAF
        hRightADF
    with
    ⟨QAF2, QAF3,
      QDA0, QDA1,
      QDF0, QDF1,
      hSqAF2,
      hSqDA,
      hSqDF,
      hPythADF⟩

  exact
    ⟨E, F, G,
      hCA_CE,
      hGE_GF,
      hGF_CD,
      hDF_DB,

      ⟨QAE0, QAE1,
        QCA0, QCA1,
        QCE0, QCE1,
        hSqAE,
        hSqCA,
        hSqCE,
        hPythACE⟩,

      ⟨QEF0, QEF1,
        QGE0, QGE1,
        QGF0, QGF1,
        hSqEF,
        hSqGE,
        hSqGF,
        hPythEGF⟩,

      ⟨QAF0, QAF1,
        QEA0, QEA1,
        QEF2, QEF3,
        hSqAF,
        hSqEA,
        hSqEF2,
        hPythAEF⟩,

      ⟨QAF2, QAF3,
        QDA0, QDA1,
        QDF0, QDF1,
        hSqAF2,
        hSqDA,
        hSqDF,
        hPythADF⟩⟩

------------------------------------------------------------------------

/--
Euclid II.9, oriented case C-D-B.

If AB is bisected at C and D lies strictly between C and B, then there
exist squares on AD, DB, AC and CD such that the sum of the squares on
AD and DB is equicomplementable with two copies of the square on AC
together with two copies of the square on CD.

This is the scissors-calculus form of

    AD^2 + DB^2 = 2 * (AC^2 + CD^2).
-/
theorem euclid_proposition_2_9_oriented
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hCDB : Geo.Between C D B) :
    ∃ SAD0 SAD1 SDB0 SDB1 SAC0 SAC1 SCD0 SCD1 : Geo.Point,
      IsSquare Geo A D SAD0 SAD1 ∧
      IsSquare Geo D B SDB0 SDB1 ∧
      IsSquare Geo A C SAC0 SAC1 ∧
      IsSquare Geo C D SCD0 SCD1 ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A D SAD0 SAD1 +
         hilbertParallelogramTerm Geo D B SDB0 SDB1)
        ((hilbertParallelogramTerm Geo A C SAC0 SAC1 +
          hilbertParallelogramTerm Geo A C SAC0 SAC1) +
         (hilbertParallelogramTerm Geo C D SCD0 SCD1 +
          hilbertParallelogramTerm Geo C D SCD0 SCD1)) := by

  --------------------------------------------------------------------
  -- Recover the four source-faithful I.47 decompositions.
  --------------------------------------------------------------------

  rcases
      proposition2_9_four_pythagoras_blocks
        Geo
        A B C D
        hMidC
        hCDB
    with
    ⟨E, F, G,
      hCA_CE,
      hGE_GF,
      hGF_CD,
      hDF_DB,

      ⟨QAE0, QAE1,
        QCA0, QCA1,
        QCE0, QCE1,
        hSqAE,
        hSqCA,
        hSqCE,
        hPythACE⟩,

      ⟨QEF0, QEF1,
        QGE0, QGE1,
        QGF0, QGF1,
        hSqEF,
        hSqGE,
        hSqGF,
        hPythEGF⟩,

      ⟨QAF0, QAF1,
        QEA0, QEA1,
        QEF2, QEF3,
        hSqAF,
        hSqEA,
        hSqEF2,
        hPythAEF⟩,

      ⟨QAF2, QAF3,
        QDA0, QDA1,
        QDF0, QDF1,
        hSqAF2,
        hSqDA,
        hSqDF,
        hPythADF⟩⟩

  --------------------------------------------------------------------
  -- Construct actual target squares on AD, DB, AC and CD by I.46.
  --------------------------------------------------------------------

  have hACD :
      Geo.Between A C D := by

    rcases
        proposition2_9_classical_isosceles_blocks
          Geo
          A B C D
          hMidC
          hCDB
      with
      ⟨_E, _F, _G, _R, _S,
        _hEFB,
        _hCGE,
        hACD',
        _hCE_CB,
        _hPar,
        _hRightADF,
        _hRightEGF,
        _hNoncolACE,
        _hRightACE,
        _hNoncolBCE,
        _hRightBCE,
        _hERB,
        _hESA,
        _hBisectR,
        _hBisectS,
        _hAEC_BEC,
        _hRightAEB,
        _hRightAEF,
        _hGE_GF,
        _hDF_DB⟩

    exact hACD'

  have hACDdata :=
    HilbertOrder.between_incidence
      A C D hACD

  have hAD :
      A ≠ D :=
    hACDdata.2.2.1

  have hAC :
      A ≠ C :=
    hACDdata.1

  have hCDBdata :=
    HilbertOrder.between_incidence
      C D B hCDB

  have hDB :
      D ≠ B :=
    hCDBdata.2.1

  have hCD :
      C ≠ D :=
    hCDBdata.1

  rcases
      euclid_proposition_46
        Geo A D hAD
    with
    ⟨SAD0, SAD1, hSqAD⟩

  rcases
      euclid_proposition_46
        Geo D B hDB
    with
    ⟨SDB0, SDB1, hSqDB⟩

  rcases
      euclid_proposition_46
        Geo A C hAC
    with
    ⟨SAC0, SAC1, hSqAC⟩

  rcases
      euclid_proposition_46
        Geo C D hCD
    with
    ⟨SCD0, SCD1, hSqCD⟩

  --------------------------------------------------------------------
  -- Abbreviations for the target terms.
  --------------------------------------------------------------------

  let tAD :=
    hilbertParallelogramTerm Geo A D SAD0 SAD1

  let tDB :=
    hilbertParallelogramTerm Geo D B SDB0 SDB1

  let tAC :=
    hilbertParallelogramTerm Geo A C SAC0 SAC1

  let tCD :=
    hilbertParallelogramTerm Geo C D SCD0 SCD1

  --------------------------------------------------------------------
  -- STEP A.
  --
  -- I.47 on ADF:
  --
  --     AF^2 = DA^2 + DF^2
  --
  -- and DA = AD, DF = DB, hence
  --
  --     AF^2 = AD^2 + DB^2.
  --------------------------------------------------------------------

  have hDA_AD :
      Geo.Congruent D A A D :=
    CongruentReverseFirst
      Geo
      A D
      A D
      (hilbert_congruent_reflexive
        Geo A D)

  have hSqDA_to_AD :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D A QDA0 QDA1)
        tAD :=
    hilbert_square_transport
      Geo
      D A QDA0 QDA1
      A D SAD0 SAD1
      hSqDA
      hSqAD
      hDA_AD

  have hSqDF_to_DB :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D F QDF1 QDF0)
        tDB :=
    hilbert_square_transport
      Geo
      D F QDF1 QDF0
      D B SDB0 SDB1
      hSqDF
      hSqDB
      hDF_DB

  have hDA_DF_to_LHS :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D A QDA0 QDA1 +
         hilbertParallelogramTerm Geo D F QDF1 QDF0)
        (tAD + tDB) :=
    i47_aux_equicomplementable_add
      Geo
      hSqDA_to_AD
      hSqDF_to_DB

  have hAF2_to_LHS :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A F QAF3 QAF2)
        (tAD + tDB) :=
    equicomplementable_trans
      Geo
      hPythADF
      hDA_DF_to_LHS

  --------------------------------------------------------------------
  -- STEP B.
  --
  -- Move from the ADF square on AF to the AEF square on AF.
  --------------------------------------------------------------------

  have hAF_refl :
      Geo.Congruent A F A F :=
    hilbert_congruent_reflexive
      Geo A F

  have hSqAF2_to_AF :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A F QAF3 QAF2)
        (hilbertParallelogramTerm Geo A F QAF1 QAF0) :=
    hilbert_square_transport
      Geo
      A F QAF3 QAF2
      A F QAF1 QAF0
      hSqAF2
      hSqAF
      hAF_refl

  have hLHS_to_AF2 :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        (hilbertParallelogramTerm Geo A F QAF3 QAF2) :=
    equicomplementable_symm
      Geo hAF2_to_LHS

  have hLHS_to_AF :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        (hilbertParallelogramTerm Geo A F QAF1 QAF0) :=
    equicomplementable_trans
      Geo
      hLHS_to_AF2
      hSqAF2_to_AF

  have hLHS_to_EA_EF :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        (hilbertParallelogramTerm Geo E A QEA0 QEA1 +
         hilbertParallelogramTerm Geo E F QEF3 QEF2) :=
    equicomplementable_trans
      Geo
      hLHS_to_AF
      hPythAEF

  --------------------------------------------------------------------
  -- STEP C.
  --
  -- Identify the AEF squares on EA and EF with the ACE/EGF squares
  -- on AE and EF.
  --------------------------------------------------------------------

  have hEA_AE :
      Geo.Congruent E A A E :=
    CongruentReverseFirst
      Geo
      A E
      A E
      (hilbert_congruent_reflexive
        Geo A E)

  have hSqEA_to_AE :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E A QEA0 QEA1)
        (hilbertParallelogramTerm Geo A E QAE1 QAE0) :=
    hilbert_square_transport
      Geo
      E A QEA0 QEA1
      A E QAE1 QAE0
      hSqEA
      hSqAE
      hEA_AE

  have hEF_refl :
      Geo.Congruent E F E F :=
    hilbert_congruent_reflexive
      Geo E F

  have hSqEF2_to_EF :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E F QEF3 QEF2)
        (hilbertParallelogramTerm Geo E F QEF1 QEF0) :=
    hilbert_square_transport
      Geo
      E F QEF3 QEF2
      E F QEF1 QEF0
      hSqEF2
      hSqEF
      hEF_refl

  have hEA_EF_to_AE_EF :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E A QEA0 QEA1 +
         hilbertParallelogramTerm Geo E F QEF3 QEF2)
        (hilbertParallelogramTerm Geo A E QAE1 QAE0 +
         hilbertParallelogramTerm Geo E F QEF1 QEF0) :=
    i47_aux_equicomplementable_add
      Geo
      hSqEA_to_AE
      hSqEF2_to_EF

  have hLHS_to_AE_EF :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        (hilbertParallelogramTerm Geo A E QAE1 QAE0 +
         hilbertParallelogramTerm Geo E F QEF1 QEF0) :=
    equicomplementable_trans
      Geo
      hLHS_to_EA_EF
      hEA_EF_to_AE_EF

  --------------------------------------------------------------------
  -- STEP D.
  --
  -- Apply I.47 on ACE and EGF simultaneously:
  --
  --   AE^2 + EF^2
  --     =
  --   (CA^2 + CE^2) + (GE^2 + GF^2).
  --------------------------------------------------------------------

  have hAE_EF_to_four :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A E QAE1 QAE0 +
         hilbertParallelogramTerm Geo E F QEF1 QEF0)
        ((hilbertParallelogramTerm Geo C A QCA0 QCA1 +
          hilbertParallelogramTerm Geo C E QCE1 QCE0) +
         (hilbertParallelogramTerm Geo G E QGE0 QGE1 +
          hilbertParallelogramTerm Geo G F QGF1 QGF0)) :=
    i47_aux_equicomplementable_add
      Geo
      hPythACE
      hPythEGF

  have hLHS_to_four :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        ((hilbertParallelogramTerm Geo C A QCA0 QCA1 +
          hilbertParallelogramTerm Geo C E QCE1 QCE0) +
         (hilbertParallelogramTerm Geo G E QGE0 QGE1 +
          hilbertParallelogramTerm Geo G F QGF1 QGF0)) :=
    equicomplementable_trans
      Geo
      hLHS_to_AE_EF
      hAE_EF_to_four

  --------------------------------------------------------------------
  -- STEP E.
  --
  -- CA = CE = AC and GE = GF = CD.
  -- Transport the four source squares to two copies of AC and two
  -- copies of CD.
  --------------------------------------------------------------------

  have hCA_AC :
      Geo.Congruent C A A C :=
    CongruentReverseFirst
      Geo
      A C
      A C
      (hilbert_congruent_reflexive
        Geo A C)

  have hSqCA_to_AC :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo C A QCA0 QCA1)
        tAC :=
    hilbert_square_transport
      Geo
      C A QCA0 QCA1
      A C SAC0 SAC1
      hSqCA
      hSqAC
      hCA_AC

  have hCE_CA :
      Geo.Congruent C E C A :=
    hilbert_congruent_symmetry
      Geo
      C A
      C E
      hCA_CE

  have hCE_AC :
      Geo.Congruent C E A C :=
    CongruentSwapSecond
      Geo
      C E
      C A
      hCE_CA

  have hSqCE_to_AC :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo C E QCE1 QCE0)
        tAC :=
    hilbert_square_transport
      Geo
      C E QCE1 QCE0
      A C SAC0 SAC1
      hSqCE
      hSqAC
      hCE_AC

  have hGE_CD :
      Geo.Congruent G E C D :=
    hilbert_congruent_transitivity
      Geo
      G E
      G F
      C D
      hGE_GF
      hGF_CD

  have hSqGE_to_CD :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo G E QGE0 QGE1)
        tCD :=
    hilbert_square_transport
      Geo
      G E QGE0 QGE1
      C D SCD0 SCD1
      hSqGE
      hSqCD
      hGE_CD

  have hSqGF_to_CD :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo G F QGF1 QGF0)
        tCD :=
    hilbert_square_transport
      Geo
      G F QGF1 QGF0
      C D SCD0 SCD1
      hSqGF
      hSqCD
      hGF_CD

  have hCA_CE_to_2AC :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo C A QCA0 QCA1 +
         hilbertParallelogramTerm Geo C E QCE1 QCE0)
        (tAC + tAC) :=
    i47_aux_equicomplementable_add
      Geo
      hSqCA_to_AC
      hSqCE_to_AC

  have hGE_GF_to_2CD :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo G E QGE0 QGE1 +
         hilbertParallelogramTerm Geo G F QGF1 QGF0)
        (tCD + tCD) :=
    i47_aux_equicomplementable_add
      Geo
      hSqGE_to_CD
      hSqGF_to_CD

  have hFour_to_RHS :
      HilbertScissorsEquicomplementable Geo
        ((hilbertParallelogramTerm Geo C A QCA0 QCA1 +
          hilbertParallelogramTerm Geo C E QCE1 QCE0) +
         (hilbertParallelogramTerm Geo G E QGE0 QGE1 +
          hilbertParallelogramTerm Geo G F QGF1 QGF0))
        ((tAC + tAC) + (tCD + tCD)) :=
    i47_aux_equicomplementable_add
      Geo
      hCA_CE_to_2AC
      hGE_GF_to_2CD

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        ((tAC + tAC) + (tCD + tCD)) :=
    equicomplementable_trans
      Geo
      hLHS_to_four
      hFour_to_RHS

  exact
    ⟨SAD0, SAD1,
      SDB0, SDB1,
      SAC0, SAC1,
      SCD0, SCD1,
      hSqAD,
      hSqDB,
      hSqAC,
      hSqCD,
      hFinal⟩


/--
Euclid II.9, both orientations of the unequal cut.

The midpoint C bisects AB.  The second cut D is assumed to lie on one
of the two open half-segments determined by C:

    C-D-B  or  C-D-A.

The conclusion is independent of which side contains D.
-/
theorem euclid_proposition_2_9
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hSide : Geo.Between C D B ∨ Geo.Between C D A) :
    ∃ SAD0 SAD1 SDB0 SDB1 SAC0 SAC1 SCD0 SCD1 : Geo.Point,
      IsSquare Geo A D SAD0 SAD1 ∧
      IsSquare Geo D B SDB0 SDB1 ∧
      IsSquare Geo A C SAC0 SAC1 ∧
      IsSquare Geo C D SCD0 SCD1 ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A D SAD0 SAD1 +
         hilbertParallelogramTerm Geo D B SDB0 SDB1)
        ((hilbertParallelogramTerm Geo A C SAC0 SAC1 +
          hilbertParallelogramTerm Geo A C SAC0 SAC1) +
         (hilbertParallelogramTerm Geo C D SCD0 SCD1 +
          hilbertParallelogramTerm Geo C D SCD0 SCD1)) := by

  rcases hSide with hCDB | hCDA

  --------------------------------------------------------------------
  -- Right half: this is exactly the oriented theorem.
  --------------------------------------------------------------------

  · exact
      euclid_proposition_2_9_oriented
        Geo A B C D hMidC hCDB

  --------------------------------------------------------------------
  -- Left half: swap A and B, apply the oriented theorem, then
  -- transport the four square terms back to the requested orientation.
  --------------------------------------------------------------------

  · have hBCA :
        Geo.Between B C A :=
      (HilbertOrder.between_incidence
        A C B hMidC.1).2.2.2.2

    have hCA_BC :
        Geo.Congruent C A B C :=
      CongruentReverseBoth
        Geo
        A C C B
        hMidC.2

    have hBC_CA :
        Geo.Congruent B C C A :=
      hilbert_congruent_symmetry
        Geo
        C A B C
        hCA_BC

    have hMidSwap :
        HilbertIsMidpoint Geo C B A :=
      ⟨hBCA, hBC_CA⟩

    rcases
        euclid_proposition_2_9_oriented
          Geo B A C D hMidSwap hCDA
      with
      ⟨SBD0, SBD1,
        SDA0, SDA1,
        SBC0, SBC1,
        SCD0, SCD1,
        hSqBD,
        hSqDA,
        hSqBC,
        hSqCD,
        hSwap⟩

    ------------------------------------------------------------------
    -- Construct target-oriented squares AD, DB and AC.
    ------------------------------------------------------------------

    have hCDAdata :=
      HilbertOrder.between_incidence
        C D A hCDA

    have hAD :
        A ≠ D :=
      hCDAdata.2.1.symm

    have hAC :
        A ≠ C :=
      (HilbertOrder.between_incidence
        A C B hMidC.1).1

    have hDB :
        D ≠ B := by
      intro hDBEq
      subst D

      have hNotCBA :
          ¬ Geo.Between C B A :=
        (HilbertOrder.between_unique
          (Geo := Geo)
          B C A
          (HilbertOrder.between_incidence
            B C A hBCA).2.2.2.1
          hBCA).1

      exact hNotCBA hCDA

    rcases
        euclid_proposition_46
          Geo A D hAD
      with
      ⟨SAD0, SAD1, hSqAD⟩

    rcases
        euclid_proposition_46
          Geo D B hDB
      with
      ⟨SDB0, SDB1, hSqDB⟩

    rcases
        euclid_proposition_46
          Geo A C hAC
      with
      ⟨SAC0, SAC1, hSqAC⟩

    let tBD :=
      hilbertParallelogramTerm Geo B D SBD0 SBD1

    let tDA :=
      hilbertParallelogramTerm Geo D A SDA0 SDA1

    let tBC :=
      hilbertParallelogramTerm Geo B C SBC0 SBC1

    let tCD :=
      hilbertParallelogramTerm Geo C D SCD0 SCD1

    let tAD :=
      hilbertParallelogramTerm Geo A D SAD0 SAD1

    let tDB :=
      hilbertParallelogramTerm Geo D B SDB0 SDB1

    let tAC :=
      hilbertParallelogramTerm Geo A C SAC0 SAC1

    ------------------------------------------------------------------
    -- LHS transport:
    --
    --     BD^2 + DA^2  ->  DB^2 + AD^2  =  AD^2 + DB^2.
    ------------------------------------------------------------------

    have hBD_DB :
        Geo.Congruent B D D B :=
      CongruentSwapSecond
        Geo
        B D
        B D
        (hilbert_congruent_reflexive
          Geo B D)

    have hDA_AD :
        Geo.Congruent D A A D :=
      CongruentSwapSecond
        Geo
        D A
        D A
        (hilbert_congruent_reflexive
          Geo D A)

    have hSqBD_to_DB :
        HilbertScissorsEquicomplementable Geo
          tBD tDB :=
      hilbert_square_transport
        Geo
        B D SBD0 SBD1
        D B SDB0 SDB1
        hSqBD
        hSqDB
        hBD_DB

    have hSqDA_to_AD :
        HilbertScissorsEquicomplementable Geo
          tDA tAD :=
      hilbert_square_transport
        Geo
        D A SDA0 SDA1
        A D SAD0 SAD1
        hSqDA
        hSqAD
        hDA_AD

    have hLhs0 :
        HilbertScissorsEquicomplementable Geo
          (tBD + tDA)
          (tDB + tAD) :=
      i47_aux_equicomplementable_add
        Geo
        hSqBD_to_DB
        hSqDA_to_AD

    have hLhs :
        HilbertScissorsEquicomplementable Geo
          (tBD + tDA)
          (tAD + tDB) := by
      simpa only [Multiset.add_comm tDB tAD] using hLhs0

    ------------------------------------------------------------------
    -- RHS transport:
    --
    --     2 BC^2 + 2 CD^2  ->  2 AC^2 + 2 CD^2.
    ------------------------------------------------------------------

    have hBC_AC :
        Geo.Congruent B C A C :=
      CongruentSwapSecond
        Geo
        B C
        C A
        hBC_CA

    have hSqBC_to_AC :
        HilbertScissorsEquicomplementable Geo
          tBC tAC :=
      hilbert_square_transport
        Geo
        B C SBC0 SBC1
        A C SAC0 SAC1
        hSqBC
        hSqAC
        hBC_AC

    have h2BC_to_2AC :
        HilbertScissorsEquicomplementable Geo
          (tBC + tBC)
          (tAC + tAC) :=
      i47_aux_equicomplementable_add
        Geo
        hSqBC_to_AC
        hSqBC_to_AC

    have h2CD_refl :
        HilbertScissorsEquicomplementable Geo
          (tCD + tCD)
          (tCD + tCD) :=
      equicomplementable_of_scissorsEq
        Geo
        (HilbertScissorsEq.refl
          (Geo := Geo)
          (tCD + tCD))

    have hRhs :
        HilbertScissorsEquicomplementable Geo
          ((tBC + tBC) + (tCD + tCD))
          ((tAC + tAC) + (tCD + tCD)) :=
      i47_aux_equicomplementable_add
        Geo
        h2BC_to_2AC
        h2CD_refl

    ------------------------------------------------------------------
    -- Compose:
    --
    -- desired LHS -> swapped LHS -> swapped RHS -> desired RHS.
    ------------------------------------------------------------------

    have hFinal :
        HilbertScissorsEquicomplementable Geo
          (tAD + tDB)
          ((tAC + tAC) + (tCD + tCD)) :=
      equicomplementable_trans
        Geo
        (equicomplementable_symm
          Geo hLhs)
        (equicomplementable_trans
          Geo hSwap hRhs)

    exact
      ⟨SAD0, SAD1,
        SDB0, SDB1,
        SAC0, SAC1,
        SCD0, SCD1,
        hSqAD,
        hSqDB,
        hSqAC,
        hSqCD,
        hFinal⟩

end Geometry

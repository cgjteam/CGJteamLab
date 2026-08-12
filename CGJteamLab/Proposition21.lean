import CGJteamLab.HilbertBookZero
import CGJteamLab.Proposition20
import CGJteamLab.Proposition16

namespace Geometry

variable (Geo : Geometry.Geo)

theorem euclid_proposition_21_segment_helper
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C E H : Geo.Point)
    (hAEC : Geo.Between A E C)
    (hBAH : Geo.Between B A H)
    (hAH_AE : Geo.Congruent A H A E)
    (hBE_BH : HilbertSegmentLess Geo B E B H)
    (hBE : Not (B = E)) :
    exists F G : Geo.Point,
      Geo.Between B A F /\
      Geo.Congruent A F A C /\
      Geo.Between B E G /\
      Geo.Congruent E G E C /\
      HilbertSegmentLess Geo B G B F := by

  ----------------------------------------------------------------------
  -- Construct F on ray AH with AF congruent to AC.
  ----------------------------------------------------------------------

  have hAH : Not (A = H) :=
    (HilbertOrder.between_incidence
      B A H hBAH).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        A C
        A H
        hAH with
    ⟨F, hRayAHF, hAF_AC⟩

  ----------------------------------------------------------------------
  -- Since A-E-C, we have AE < AC.
  ----------------------------------------------------------------------

  have hAE_AC :
      HilbertSegmentLess Geo A E A C :=
    ⟨E, hAEC,
      hilbert_congruent_reflexive Geo A E⟩

  ----------------------------------------------------------------------
  -- Replace AC by the congruent AF:
  -- AE < AF.
  ----------------------------------------------------------------------

  have hAC_AF :
      Geo.Congruent A C A F :=
    hilbert_congruent_symmetry
      Geo A F A C hAF_AC

  have hAE_AF :
      HilbertSegmentLess Geo A E A F :=
    bookZero_30_lessThanCongruence
      Geo
      A E
      A C
      A F
      hAE_AC
      hAC_AF

  ----------------------------------------------------------------------
  -- Replace AE by the congruent AH:
  -- AH < AF.
  ----------------------------------------------------------------------

  have hAE_AH :
      Geo.Congruent A E A H :=
    hilbert_congruent_symmetry
      Geo A H A E hAH_AE

  have hAH_AF :
      HilbertSegmentLess Geo A H A F :=
    bookZero_32_lessThanCongruence2
      Geo
      A E
      A F
      A H
      hAE_AF
      hAE_AH

  ----------------------------------------------------------------------
  -- F was constructed on ray AH, hence A-H-F.
  ----------------------------------------------------------------------

  have hAHF :
      Geo.Between A H F :=
    bookZero_51_lessThanBetween
      Geo
      A H F
      hAH_AF
      hRayAHF

  ----------------------------------------------------------------------
  -- Therefore B-A-F and B-H-F.
  ----------------------------------------------------------------------

  have hBAF :
      Geo.Between B A F :=
    bookZero_3_7b
      Geo
      B A H F
      hBAH
      hAHF

  have hBHF :
      Geo.Between B H F :=
    bookZero_3_7a
      Geo
      B A H F
      hBAH
      hAHF

  ----------------------------------------------------------------------
  -- Construct G beyond E on line BE with EG congruent to EC.
  ----------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        B E hBE with
    ⟨R, hBER⟩

  have hER : Not (E = R) :=
    (HilbertOrder.between_incidence
      B E R hBER).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        E C
        E R
        hER with
    ⟨G, hRayERG, hEG_EC⟩

  have hRayEBB :
      HilbertSameRay Geo E B B :=
    hilbert_sameRay_refl
      Geo E B hBE

  have hBEG :
      Geo.Between B E G :=
    hilbert_between_transport_sameRays
      Geo
      B E R
      B G
      hBER
      hRayEBB
      hRayERG

  ----------------------------------------------------------------------
  -- From
  --
  --   A-E-C,  A-H-F,
  --   AE congruent AH,
  --   AC congruent AF,
  --
  -- subtract equal initial parts:
  --
  --   EC congruent HF.
  ----------------------------------------------------------------------

  have hEC_HF :
      Geo.Congruent E C H F :=
    bookZero_differenceOfParts
      Geo
      A E C
      A H F
      hAE_AH
      hAC_AF
      hAEC
      hAHF

  ----------------------------------------------------------------------
  -- EG congruent EC congruent HF.
  ----------------------------------------------------------------------

  have hEG_HF :
      Geo.Congruent E G H F :=
    hilbert_congruent_transitivity
      Geo
      E G
      E C
      H F
      hEG_EC
      hEC_HF

  ----------------------------------------------------------------------
  -- Add equal parts to BE < BH:
  --
  --   BE < BH,
  --   B-E-G,
  --   B-H-F,
  --   EG congruent HF
  --
  -- gives BG < BF.
  ----------------------------------------------------------------------

  have hBG_BF :
      HilbertSegmentLess Geo B G B F :=
    bookZero_53_lessThanAdditive
      Geo
      B E
      B H
      G F
      hBE_BH
      hBEG
      hBHF
      hEG_HF

  exact
    ⟨F, G,
      hBAF,
      hAF_AC,
      hBEG,
      hEG_EC,
      hBG_BF⟩

theorem euclid_proposition_21_angle
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hAEC : Geo.Between A E C)
    (hBDE : Geo.Between B D E) :
    HilbertAngleLess Geo B A C B D C := by

  ----------------------------------------------------------------------
  -- Noncollinearity of triangle BAE.
  ----------------------------------------------------------------------

  have hAECcol : PrimCollinear Geo A E C :=
    (HilbertOrder.between_incidence
      A E C hAEC).2.2.2.1

  have hACEcol : PrimCollinear Geo A C E := by
    rcases
        bookZero_22_collinearOrder
          Geo A E C hAECcol with
      ⟨_, _, _, hACEcol, _⟩
    exact hACEcol

  have hACAcol : PrimCollinear Geo A C A := by
    rcases hACEcol with ⟨l, hAl, hCl, hEl⟩
    exact ⟨l, hAl, hCl, hAl⟩

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    rcases
        bookZero_23_NCorder
          Geo A B C hABC with
      ⟨_, _, _, hACB, _⟩
    exact hACB

  have hAE : Not (A = E) :=
    (HilbertOrder.between_incidence
      A E C hAEC).1

  have hAEB :
      Not (PrimCollinear Geo A E B) :=
    bookZero_27_NChelper
      Geo
      A C B
      A E
      hACB
      hACAcol
      hACEcol
      hAE

  have hBAE :
      Not (PrimCollinear Geo B A E) := by
    rcases
        bookZero_23_NCorder
          Geo A E B hAEB with
      ⟨_, _, hBAE, _, _⟩
    exact hBAE

  ----------------------------------------------------------------------
  -- Noncollinearity of triangle CED.
  --
  -- First replace B by D on the line BE, obtaining D,E,A
  -- noncollinear.  Then replace A by C on the line EA.
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- Noncollinearity of triangle CED.
  --
  -- First move C along the line AE, then D along the line BE.
  ----------------------------------------------------------------------

  have hAEEcol : PrimCollinear Geo A E E := by
    rcases hAECcol with ⟨l, hAl, hEl, hCl⟩
    exact ⟨l, hAl, hEl, hEl⟩

  have hCE : C ≠ E :=
    (HilbertOrder.between_incidence
      A E C hAEC).2.1.symm

  have hCEB :
      Not (PrimCollinear Geo C E B) :=
    bookZero_27_NChelper
      Geo
      A E B
      C E
      hAEB
      hAECcol
      hAEEcol
      hCE

  have hBEC :
      Not (PrimCollinear Geo B E C) := by
    rcases
        bookZero_23_NCorder
          Geo C E B hCEB with
      ⟨_, _, _, _, hBEC⟩
    exact hBEC

  have hBDEcol : PrimCollinear Geo B D E :=
    (HilbertOrder.between_incidence
      B D E hBDE).2.2.2.1

  have hBEDcol : PrimCollinear Geo B E D := by
    rcases
        bookZero_22_collinearOrder
          Geo B D E hBDEcol with
      ⟨_, _, _, hBEDcol, _⟩
    exact hBEDcol

  have hBEEcol : PrimCollinear Geo B E E := by
    rcases hBEDcol with ⟨l, hBl, hEl, hDl⟩
    exact ⟨l, hBl, hEl, hEl⟩

  have hDE : D ≠ E :=
    (HilbertOrder.between_incidence
      B D E hBDE).2.1

  have hDEC :
      Not (PrimCollinear Geo D E C) :=
    bookZero_27_NChelper
      Geo
      B E C
      D E
      hBEC
      hBEDcol
      hBEEcol
      hDE

  have hCED :
      Not (PrimCollinear Geo C E D) := by
    rcases
        bookZero_23_NCorder
          Geo D E C hDEC with
      ⟨_, _, _, _, hCED⟩
    exact hCED

  ----------------------------------------------------------------------
  -- First use of Proposition I.16.
  --
  -- In triangle CED, extend ED through D to B.
  -- Hence angle CED < angle CDB.
  ----------------------------------------------------------------------

  have hEDB : Geo.Between E D B :=
    (HilbertOrder.between_incidence
      B D E hBDE).2.2.2.2

  have hLessCED_CDB :
      HilbertAngleLess Geo C E D C D B :=
    (euclid_proposition_16
      Geo
      C E D B
      hCED
      hEDB).2

  ----------------------------------------------------------------------
  -- Second use of Proposition I.16.
  --
  -- In triangle BAE, extend AE through E to C.
  -- Hence angle BAE < angle BEC.
  ----------------------------------------------------------------------

  have hLessBAE_BEC :
      HilbertAngleLess Geo B A E B E C :=
    (euclid_proposition_16
      Geo
      B A E C
      hBAE
      hAEC).2

  ----------------------------------------------------------------------
  -- Replace angle BAE by angle BAC.
  -- Since A-E-C, the rays AE and AC are the same.
  ----------------------------------------------------------------------

  have hBAC :
      Not (PrimCollinear Geo B A C) := by
    rcases
        bookZero_23_NCorder
          Geo A B C hABC with
      ⟨hBAC, _, _, _, _⟩
    exact hBAC

  have hRayAEC :
      HilbertSameRay Geo A E C :=
    hilbert_sameRay_of_between
      Geo A E C hAEC

  have hBAEeqBAC :
      Geo.Angle B A E = Geo.Angle B A C :=
    hilbert_angle_eq_of_sameRay_second
      Geo A B E C hRayAEC

  have hBAC_BAE :
      Geo.AngleCongruent B A C B A E := by
    have hRefl :
        Geo.AngleCongruent B A C B A C :=
      Geometry.Geo.angle_congruent_reflexive
        Geo B A C

    unfold Geometry.Geo.AngleCongruent at hRefl ⊢
    rw [hBAEeqBAC]
    exact hRefl

  have hLessBAC_BEC :
      HilbertAngleLess Geo B A C B E C :=
    hilbert_angleLess_transport_left
      Geo
      B A E
      B A C
      B E C
      hLessBAE_BEC
      hBAC
      hBAC_BAE

  ----------------------------------------------------------------------
  -- Replace angle BEC by angle CED.
  -- Since E-D-B, the rays ED and EB are the same.
  ----------------------------------------------------------------------

  have hRayEDB :
      HilbertSameRay Geo E D B :=
    hilbert_sameRay_of_between
      Geo E D B hEDB

  have hBECeqCED :
      Geo.Angle B E C = Geo.Angle C E D := by
    calc
      Geo.Angle B E C = Geo.Angle C E B :=
        Geo.angle_swap B E C
      _ = Geo.Angle C E D :=
        (hilbert_angle_eq_of_sameRay_second
          Geo E C D B hRayEDB).symm

  have hBEC_CED :
      Geo.AngleCongruent B E C C E D := by
    have hRefl :
        Geo.AngleCongruent C E D C E D :=
      Geometry.Geo.angle_congruent_reflexive
        Geo C E D

    unfold Geometry.Geo.AngleCongruent at hRefl ⊢
    rw [hBECeqCED]
    exact hRefl

  have hLessBAC_CED :
      HilbertAngleLess Geo B A C C E D :=
    hilbert_angleLess_transport_right
      Geo
      B A C
      B E C
      C E D
      hLessBAC_BEC
      hCED
      hBEC_CED

  ----------------------------------------------------------------------
  -- Transitivity:
  --
  -- angle BAC < angle CED < angle CDB.
  ----------------------------------------------------------------------

  have hLessBAC_CDB :
      HilbertAngleLess Geo B A C C D B :=
    hilbert_angleLess_trans
      Geo
      B A C
      C E D
      C D B
      hLessBAC_CED
      hLessCED_CDB

  ----------------------------------------------------------------------
  -- Reverse the arms of the final unoriented angle:
  -- angle CDB = angle BDC.
  ----------------------------------------------------------------------

  have hCDB_BDC :
      Geo.AngleCongruent C D B B D C := by
    have hRefl :
        Geo.AngleCongruent C D B C D B :=
      Geometry.Geo.angle_congruent_reflexive
        Geo C D B

    exact
      (Geo.angle_congruent_reverse_second
        C D B
        C D B).mp hRefl

  ----------------------------------------------------------------------
  -- Noncollinearity of C,D,B.
  --
  -- If C,D,B were collinear, then since E,D,B are collinear,
  -- the distinct points D,B would force B,E,C to be collinear,
  -- contradicting hBEC.
  ----------------------------------------------------------------------

  have hCDB :
      Not (PrimCollinear Geo C D B) := by
    intro hCDBcol

    have hEDBcol :
        PrimCollinear Geo E D B :=
      (HilbertOrder.between_incidence
        E D B hEDB).2.2.2.1

    have hDBE :
        PrimCollinear Geo D B E := by
      rcases
          bookZero_22_collinearOrder
            Geo E D B hEDBcol with
        ⟨_, hDBE, _, _, _⟩
      exact hDBE

    have hDBC :
        PrimCollinear Geo D B C := by
      rcases
          bookZero_22_collinearOrder
            Geo C D B hCDBcol with
        ⟨_, hDBC, _, _, _⟩
      exact hDBC

    have hDB : D ≠ B :=
      (HilbertOrder.between_incidence
        E D B hEDB).2.1

    have hBECcol :
        PrimCollinear Geo B E C :=
      bookZero_24_collinear4
        Geo
        D B E C
        hDBE
        hDBC
        hDB

    exact hBEC hBECcol

  ----------------------------------------------------------------------
  -- Reorder noncollinearity C,D,B -> B,D,C.
  ----------------------------------------------------------------------

  have hBDC :
      Not (PrimCollinear Geo B D C) := by
    rcases
        bookZero_23_NCorder
          Geo C D B hCDB with
      ⟨_, _, _, _, hBDC⟩
    exact hBDC

  ----------------------------------------------------------------------
  -- Final transport:
  -- angle BAC < angle CDB = angle BDC.
  ----------------------------------------------------------------------

  exact
    hilbert_angleLess_transport_right
      Geo
      B A C
      C D B
      B D C
      hLessBAC_CDB
      hBDC
      hCDB_BDC

theorem euclid_proposition_21
    [HilbertIncidence Geo]
    [HilbertCongruence Geo]
    (A B C D E : Geo.Point)
    (hABC : Not (PrimCollinear Geo A B C))
    (hAEC : Geo.Between A E C)
    (hBDE : Geo.Between B D E) :
    (exists X Y : Geo.Point,
      Geo.Between B A X /\
      Geo.Congruent A X A C /\
      Geo.Between B D Y /\
      Geo.Congruent D Y D C /\
      HilbertSegmentLess Geo B Y B X) /\
    HilbertAngleLess Geo B A C B D C := by

  ----------------------------------------------------------------------
  -- Recover the noncollinearity of triangle BAE.
  ----------------------------------------------------------------------

  have hAECcol : PrimCollinear Geo A E C :=
    (HilbertOrder.between_incidence
      A E C hAEC).2.2.2.1

  have hACEcol : PrimCollinear Geo A C E := by
    rcases
        bookZero_22_collinearOrder
          Geo A E C hAECcol with
      ⟨_, _, _, hACEcol, _⟩
    exact hACEcol

  have hACAcol : PrimCollinear Geo A C A := by
    rcases hACEcol with ⟨l, hAl, hCl, hEl⟩
    exact ⟨l, hAl, hCl, hAl⟩

  have hACB :
      Not (PrimCollinear Geo A C B) := by
    rcases
        bookZero_23_NCorder
          Geo A B C hABC with
      ⟨_, _, _, hACB, _⟩
    exact hACB

  have hAE : Not (A = E) :=
    (HilbertOrder.between_incidence
      A E C hAEC).1

  have hAEB :
      Not (PrimCollinear Geo A E B) :=
    bookZero_27_NChelper
      Geo
      A C B
      A E
      hACB
      hACAcol
      hACEcol
      hAE

  have hBAE :
      Not (PrimCollinear Geo B A E) := by
    rcases
        bookZero_23_NCorder
          Geo A E B hAEB with
      ⟨_, _, hBAE, _, _⟩
    exact hBAE

  ----------------------------------------------------------------------
  -- Proposition I.20 in triangle BAE:
  --
  -- BE < BA + AE.
  --
  -- H represents the endpoint of BA + AE:
  -- B-A-H and AH congruent AE.
  ----------------------------------------------------------------------

  have hABE :
      Not (PrimCollinear Geo A B E) := by
    rcases
        bookZero_23_NCorder
          Geo B A E hBAE with
      ⟨hABE, _, _, _, _⟩
    exact hABE

  rcases
      euclid_proposition_20
        Geo A B E hABE with
    ⟨H, hBAH, hAH_AE, hBE_BH⟩

  ----------------------------------------------------------------------
  -- BE is non-null.
  ----------------------------------------------------------------------

  have hBE : Not (B = E) := by
    intro hBEeq
    subst E
    exact hBAE
      (by
        rcases hAECcol with ⟨l, hAl, hBl, hCl⟩
        exact ⟨l, hBl, hAl, hBl⟩)

  ----------------------------------------------------------------------
  -- Apply the I.21 segment helper.
  --
  -- It extends
  --
  --     BE < BA + AE
  --
  -- by the equal remainders EC and HF, obtaining
  --
  --     BE + EC < BA + AC.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_21_segment_helper
        Geo
        A B C E H
        hAEC
        hBAH
        hAH_AE
        hBE_BH
        hBE with
    ⟨X, G,
      hBAX,
      hAX_AC,
      hBEG,
      hEG_EC,
      hBG_BX⟩

  ----------------------------------------------------------------------
  -- Proposition I.20 in triangle ECD:
  --
  -- CD < CE + ED.
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- Noncollinearity of triangle ECD.
  ----------------------------------------------------------------------

  have hAEEcol : PrimCollinear Geo A E E := by
    rcases hAECcol with ⟨l, hAl, hEl, hCl⟩
    exact ⟨l, hAl, hEl, hEl⟩

  have hCE : C ≠ E :=
    (HilbertOrder.between_incidence
      A E C hAEC).2.1.symm

  have hCEB :
      Not (PrimCollinear Geo C E B) :=
    bookZero_27_NChelper
      Geo
      A E B
      C E
      hAEB
      hAECcol
      hAEEcol
      hCE

  have hBEC :
      Not (PrimCollinear Geo B E C) := by
    rcases
        bookZero_23_NCorder
          Geo C E B hCEB with
      ⟨_, _, _, _, hBEC⟩
    exact hBEC

  have hBDEcol : PrimCollinear Geo B D E :=
    (HilbertOrder.between_incidence
      B D E hBDE).2.2.2.1

  have hBEDcol : PrimCollinear Geo B E D := by
    rcases
        bookZero_22_collinearOrder
          Geo B D E hBDEcol with
      ⟨_, _, _, hBEDcol, _⟩
    exact hBEDcol

  have hBEEcol : PrimCollinear Geo B E E := by
    rcases hBEDcol with ⟨l, hBl, hEl, hDl⟩
    exact ⟨l, hBl, hEl, hEl⟩

  have hDE : D ≠ E :=
    (HilbertOrder.between_incidence
      B D E hBDE).2.1

  have hDEC :
      Not (PrimCollinear Geo D E C) :=
    bookZero_27_NChelper
      Geo
      B E C
      D E
      hBEC
      hBEDcol
      hBEEcol
      hDE

  have hECD :
      Not (PrimCollinear Geo E C D) := by
    rcases
        bookZero_23_NCorder
          Geo D E C hDEC with
      ⟨_, hECD, _, _, _⟩
    exact hECD

  rcases
      euclid_proposition_20
        Geo E C D hECD with
    ⟨K, hCEK, hEK_ED, hCD_CK⟩

  ----------------------------------------------------------------------
  -- E-D-B.
  ----------------------------------------------------------------------

  have hEDB : Geo.Between E D B :=
    (HilbertOrder.between_incidence
      B D E hBDE).2.2.2.2

  have hCDE :
      Not (PrimCollinear Geo C D E) := by
    rcases
        bookZero_23_NCorder
          Geo E C D hECD with
      ⟨_, hCDE, _, _, _⟩
    exact hCDE

  have hCD : C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D E hCDE

  ----------------------------------------------------------------------
  -- Apply the same segment helper:
  --
  -- CD + DB < CE + EB.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_21_segment_helper
        Geo
        E C B D K
        hEDB
        hCEK
        hEK_ED
        hCD_CK
        hCD with
    ⟨U, V,
      hCEU,
      hEU_EB,
      hCDV,
      hDV_DB,
      hCV_CU⟩

  ----------------------------------------------------------------------
  -- C and D are distinct.
  ----------------------------------------------------------------------

  have hCDE :
      Not (PrimCollinear Geo C D E) := by
    rcases
        bookZero_23_NCorder
          Geo E C D hECD with
      ⟨_, hCDE, _, _, _⟩
    exact hCDE

  have hCD : C ≠ D :=
    hilbert_noncollinear_ne_first
      Geo C D E hCDE

  ----------------------------------------------------------------------
  -- Since B-D-E, equivalently E-D-B.
  ----------------------------------------------------------------------

  have hEDB : Geo.Between E D B :=
    (HilbertOrder.between_incidence
      B D E hBDE).2.2.2.2

  ----------------------------------------------------------------------
  -- Apply the segment helper to triangle ECD.
  --
  -- From
  --
  --   CD < CE + ED
  --
  -- and E-D-B, obtain
  --
  --   CD + DB < CE + EB.
  ----------------------------------------------------------------------

  rcases
      euclid_proposition_21_segment_helper
        Geo
        E C B D K
        hEDB
        hCEK
        hEK_ED
        hCD_CK
        hCD with
    ⟨U, V,
      hCEU,
      hEU_EB,
      hCDV,
      hDV_DB,
      hCV_CU⟩

  ----------------------------------------------------------------------
  -- The two representatives
  --
  --   CU = CE + EB
  --   BG = BE + EC
  --
  -- are congruent.
  --
  -- Reverse B-E-G to G-E-B and apply additivity.
  ----------------------------------------------------------------------

  have hGEB : Geo.Between G E B :=
    (HilbertOrder.between_incidence
      B E G hBEG).2.2.2.2

  have hCE_GE :
      Geo.Congruent C E G E :=
    (bookZero_doubleReverse
      Geo
      E G E C
      hEG_EC).1

  have hCU_GB :
      Geo.Congruent C U G B :=
    bookZero_sumOfParts
      Geo
      C E U
      G E B
      hCE_GE
      hEU_EB
      hCEU
      hGEB

  have hCU_BG :
      Geo.Congruent C U B G :=
    CongruentSwapSecond
      Geo
      C U G B
      hCU_GB

  ----------------------------------------------------------------------
  -- Transport CV < CU across CU congruent BG.
  ----------------------------------------------------------------------

  have hCV_BG :
      HilbertSegmentLess Geo C V B G :=
    bookZero_30_lessThanCongruence
      Geo
      C V
      C U
      B G
      hCV_CU
      hCU_BG

  ----------------------------------------------------------------------
  -- Transitivity:
  --
  -- CV < BG < BX.
  ----------------------------------------------------------------------

  have hCV_BX :
      HilbertSegmentLess Geo C V B X :=
    bookZero_52_lessThanTransitive
      Geo
      C V
      B G
      B X
      hCV_BG
      hBG_BX

  ----------------------------------------------------------------------
  -- Construct Y so that BY represents BD + DC:
  --
  -- B-D-Y and DY congruent DC.
  ----------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        D C
        D E
        hDE with
    ⟨Y, hRayDEY, hDY_DC⟩

  have hBD : B ≠ D :=
    (HilbertOrder.between_incidence
      B D E hBDE).1

  have hRayDBB :
      HilbertSameRay Geo D B B :=
    hilbert_sameRay_refl
      Geo D B hBD

  have hBDY :
      Geo.Between B D Y :=
    hilbert_between_transport_sameRays
      Geo
      B D E
      B Y
      hBDE
      hRayDBB
      hRayDEY

  ----------------------------------------------------------------------
  -- CV and BY represent the same sum:
  --
  -- CV = CD + DB,
  -- BY = BD + DC.
  ----------------------------------------------------------------------

  have hVDC : Geo.Between V D C :=
    (HilbertOrder.between_incidence
      C D V hCDV).2.2.2.2

  have hVD_BD :
      Geo.Congruent V D B D :=
    CongruentReverseBoth
      Geo
      D V
      D B
      hDV_DB

  have hDC_DY :
      Geo.Congruent D C D Y :=
    hilbert_congruent_symmetry
      Geo
      D Y
      D C
      hDY_DC

  have hVC_BY :
      Geo.Congruent V C B Y :=
    bookZero_sumOfParts
      Geo
      V D C
      B D Y
      hVD_BD
      hDC_DY
      hVDC
      hBDY

  have hCV_BY :
      Geo.Congruent C V B Y :=
    CongruentReverseFirst
      Geo
      V C
      B Y
      hVC_BY

  ----------------------------------------------------------------------
  -- Replace CV by the congruent representative BY.
  ----------------------------------------------------------------------

  have hBY_BX :
      HilbertSegmentLess Geo B Y B X :=
    bookZero_32_lessThanCongruence2
      Geo
      C V
      B X
      B Y
      hCV_BX
      hCV_BY

  ----------------------------------------------------------------------
  -- Angle part of Proposition I.21.
  ----------------------------------------------------------------------

  have hAngle :
      HilbertAngleLess Geo B A C B D C :=
    euclid_proposition_21_angle
      Geo
      A B C D E
      hABC
      hAEC
      hBDE

  ----------------------------------------------------------------------
  -- Proposition I.21.
  ----------------------------------------------------------------------

  exact
    ⟨⟨X, Y,
       hBAX,
       hAX_AC,
       hBDY,
       hDY_DC,
       hBY_BX⟩,
     hAngle⟩

end Geometry

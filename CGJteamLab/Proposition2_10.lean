import CGJteamLab.Proposition2_9Construction
import CGJteamLab.Proposition34
import CGJteamLab.HilbertAngleDecomposition
import CGJteamLab.Proposition06
import CGJteamLab.Proposition32
import CGJteamLab.Proposition46
import CGJteamLab.Proposition47
import CGJteamLab.HilbertSquareTransport

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid II.10
--
-- Source-faithful synthetic reconstruction for the oriented order
--
--     A - C - B - D.
--
-- The proof follows the classical route through I.11, I.3, I.31,
-- I.29, Postulate 5, I.5, I.15, I.32, I.6, I.34 and four uses of
-- I.47.  The final equality is expressed in the scissors calculus as
-- equicomplementability of the corresponding square terms.
--
-- No Book II proposition is used.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Euclid II.10 -- order and perpendicular configuration
--
-- Source configuration:
--
--     A --- C --- B --- D
--
-- C is the midpoint of AB and D lies beyond B.
--
-- This first test packages:
--
--   * the complete order normalization A-C-B-D;
--   * the perpendicular CE at C;
--   * CE = AC = CB;
--   * the right angles ACE and ECB.
--
-- No parallel line, no point F, no point G, and no Book II proposition
-- is used.
------------------------------------------------------------------------

/--
Euclid II.10 -- order normalization.

From

    A-C-B
    A-B-D

deduce the full directed order data needed later:

    A-C-B
    C-B-D
    A-C-D
    D-B-A.
-/
theorem proposition2_10_order
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D) :
    Geo.Between A C B /\
    Geo.Between C B D /\
    Geo.Between A C D /\
    Geo.Between D B A := by

  have hACB :
      Geo.Between A C B :=
    hMidC.1

  have hInner :=
    hilbert_between_inner_trans
      Geo
      A C B D
      hACB
      hABD

  have hCBD :
      Geo.Between C B D :=
    hInner.1

  have hACD :
      Geo.Between A C D :=
    hInner.2

  have hDBA :
      Geo.Between D B A :=
    (HilbertOrder.between_incidence
      A B D hABD).2.2.2.2

  exact
    ⟨hACB,
      hCBD,
      hACD,
      hDBA⟩

------------------------------------------------------------------------

/--
Euclid II.10 -- equal perpendicular at the midpoint.

In the configuration

    A --- C --- B --- D

construct E on a perpendicular through C such that

    CE = AC = CB.
-/
theorem proposition2_10_configuration
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D) :
    exists E : Geo.Point,
      Geo.Between A C B /\
      Geo.Between C B D /\
      Geo.Between A C D /\
      Geo.Between D B A /\
      Geo.Congruent C E A C /\
      Geo.Congruent C E C B /\
      Not (Collinear Geo A C E) /\
      HilbertRightAngle Geo A C E /\
      Not (Collinear Geo E C B) /\
      HilbertRightAngle Geo E C B := by

  rcases
      proposition2_10_order
        Geo
        A B C D
        hMidC
        hABD
    with
    ⟨hACB,
      hCBD,
      hACD,
      hDBA⟩

  have hACBdata :=
    HilbertOrder.between_incidence
      A C B hACB

  have hAC :
      A ≠ C :=
    hACBdata.1

  have hCA :
      C ≠ A :=
    hAC.symm

  have hCB :
      C ≠ B :=
    hACBdata.2.1

  have hACBcol :
      Collinear Geo A C B :=
    hACBdata.2.2.2.1

  rcases
      proposition2_9_erect_perpendicular
        Geo
        C A
        A C
        hCA
    with
    ⟨E,
      hECA,
      hRightECA,
      hCE_AC⟩

  have hACE :
      Not (Collinear Geo A C E) := by
    intro hACEcol
    exact
      hECA
        (PrimCollinearSymm
          Geo A C E hACEcol)

  have hECA_ACE :
      Geo.AngleCongruent
        E C A
        A C E :=
    bookZero_56_ABCequalsCBA
      Geo
      E C A
      hECA

  have hRightACE :
      HilbertRightAngle Geo A C E :=
    hilbert_right_angle_transport
      Geo
      E C A
      A C E
      hECA
      hACE
      hRightECA
      hECA_ACE

  have hAC_CB :
      Geo.Congruent A C C B :=
    hMidC.2

  have hCE_CB :
      Geo.Congruent C E C B :=
    hilbert_congruent_transitivity
      Geo
      C E
      A C
      C B
      hCE_AC
      hAC_CB

  have hECB :
      Not (Collinear Geo E C B) := by
    intro hECBcol

    have hBCE :
        Collinear Geo B C E :=
      PrimCollinearSymm
        Geo E C B hECBcol

    have hCBE :
        Collinear Geo C B E :=
      PrimCollinearSwap
        Geo B C E hBCE

    have hACEcol :
        Collinear Geo A C E :=
      hilbert_primCollinear_trans
        Geo
        A C B E
        hCB
        hACBcol
        hCBE

    exact hACE hACEcol

  have hACE_ECB :
      Geo.AngleCongruent
        A C E
        E C B :=
    hilbert_right_angle_opposite_extension
      Geo
      A C E B
      hACE
      hRightACE
      hACB

  have hRightECB :
      HilbertRightAngle Geo E C B :=
    hilbert_right_angle_transport
      Geo
      A C E
      E C B
      hACE
      hECB
      hRightACE
      hACE_ECB

  exact
    ⟨E,
      hACB,
      hCBD,
      hACD,
      hDBA,
      hCE_AC,
      hCE_CB,
      hACE,
      hRightACE,
      hECB,
      hRightECB⟩

------------------------------------------------------------------------
-- Euclid II.10 -- parallelogram block
--
-- Starting from test01:
--
--     A --- C --- B --- D
--
-- and the equal perpendicular CE at C, construct the fourth point F
-- so that C-D-F-E is a parallelogram.
--
-- This packages the two I.31 constructions used by Euclid:
--
--     EF || AD  (equivalently EF || CD)
--     DF || CE
--
-- and immediately records the I.34 consequence EF = CD together with
-- the right angle EFD needed later for triangle EFG.
------------------------------------------------------------------------

theorem proposition2_10_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D) :
    exists E F : Geo.Point,
      Geo.Between A C B /\
      Geo.Between C B D /\
      Geo.Between A C D /\
      Geo.Between D B A /\
      Geo.Congruent C E A C /\
      Geo.Congruent C E C B /\
      Not (Collinear Geo A C E) /\
      HilbertRightAngle Geo A C E /\
      Not (Collinear Geo E C D) /\
      HilbertRightAngle Geo E C D /\
      IsParallelogram Geo C D F E /\
      Geo.Parallel C D F E /\
      Geo.Parallel D F E C /\
      Geo.Congruent C D F E /\
      Geo.Congruent D F E C /\
      Not (Collinear Geo E F D) /\
      HilbertRightAngle Geo E F D := by

  --------------------------------------------------------------------
  -- Recover the complete test01 package.
  --------------------------------------------------------------------

  rcases
      proposition2_10_configuration
        Geo A B C D hMidC hABD
    with
    ⟨E,
      hACB,
      hCBD,
      hACD,
      hDBA,
      hCE_AC,
      hCE_CB,
      hACE,
      hRightACE,
      hECB,
      hRightECB⟩

  --------------------------------------------------------------------
  -- Order and incidence data on A-C-B-D.
  --------------------------------------------------------------------

  have hCBDdata :=
    HilbertOrder.between_incidence
      C B D hCBD

  have hCB :
      C ≠ B :=
    hCBDdata.1

  have hBD :
      B ≠ D :=
    hCBDdata.2.1

  have hCD :
      C ≠ D :=
    hCBDdata.2.2.1

  have hCBDcol :
      Collinear Geo C B D :=
    hCBDdata.2.2.2.1

  have hACDdata :=
    HilbertOrder.between_incidence
      A C D hACD

  have hAC :
      A ≠ C :=
    hACDdata.1

  have hACDcol :
      Collinear Geo A C D :=
    hACDdata.2.2.2.1

  --------------------------------------------------------------------
  -- E,C,D are noncollinear.
  --
  -- If C,D,E were collinear, then A,C,D together with C,D,E would
  -- force A,C,E collinear.
  --------------------------------------------------------------------

  have hCDE :
      Not (Collinear Geo C D E) := by

    intro hCDEcol

    have hACEcol :
        Collinear Geo A C E :=
      hilbert_primCollinear_trans
        Geo
        A C D E
        hCD
        hACDcol
        hCDEcol

    exact hACE hACEcol

  have hECD :
      Not (Collinear Geo E C D) := by

    intro hECDcol

    exact
      hCDE
        (PrimCollinearCycle
          Geo E C D hECDcol)

  --------------------------------------------------------------------
  -- Since C-B-D, rays CB and CD agree.
  -- Transport the right angle ECB to ECD.
  --------------------------------------------------------------------

  have hRayCBD :
      HilbertSameRay Geo C B D :=
    hilbert_sameRay_of_between
      Geo C B D hCBD

  have hAngleECB_ECD :
      Geo.Angle E C B =
      Geo.Angle E C D :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      C E B D
      hRayCBD

  have hReflECB :
      Geo.AngleCongruent
        E C B
        E C B :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      E C B
      hECB

  have hECB_ECD :
      Geo.AngleCongruent
        E C B
        E C D := by

    unfold Geometry.Geo.AngleCongruent
      at hReflECB ⊢

    rw [← hAngleECB_ECD]

    exact hReflECB

  have hRightECD :
      HilbertRightAngle Geo E C D :=
    hilbert_right_angle_transport
      Geo
      E C B
      E C D
      hECB
      hECD
      hRightECB
      hECB_ECD

  --------------------------------------------------------------------
  -- Complete the parallelogram C-D-F-E.
  --
  -- This is the reusable two-I.31 construction already available in
  -- the permanent Hilbert interface.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo
        C D E
        hCDE
    with
    ⟨F, hParCDFE⟩

  have hParCD_FE :
      Geo.Parallel C D F E :=
    hParCDFE.1

  have hParDF_EC :
      Geo.Parallel D F E C :=
    hParCDFE.2

  --------------------------------------------------------------------
  -- I.34: opposite sides of C-D-F-E are congruent.
  --
  -- In particular:
  --
  --     CD = FE
  --     DF = EC.
  --------------------------------------------------------------------

  have hI34 :=
    euclid_proposition_34
      Geo
      C D F E
      hParCDFE

  have hCD_FE :
      Geo.Congruent C D F E :=
    hI34.1.1

  have hDF_EC :
      Geo.Congruent D F E C :=
    hI34.1.2

  --------------------------------------------------------------------
  -- The right angle ECD propagates around the parallelogram.
  --
  -- First:
  --
  --     ECD right  ->  CDF right.
  --------------------------------------------------------------------

  have hRightCDF :
      HilbertRightAngle Geo C D F :=
    parallelogram_adjacent_right_angle
      Geo
      C D F E
      hParCDFE
      hRightECD

  --------------------------------------------------------------------
  -- Cyclic orientation D-F-E-C of the same parallelogram.
  --------------------------------------------------------------------

  have hParDFEC :
      IsParallelogram Geo D F E C :=
    ⟨hParCDFE.2,
      ParallelSymmetry
        Geo
        C D F E
        hParCDFE.1⟩

  --------------------------------------------------------------------
  -- Second adjacent right angle:
  --
  --     CDF right  ->  DFE right.
  --------------------------------------------------------------------

  have hRightDFE :
      HilbertRightAngle Geo D F E :=
    parallelogram_adjacent_right_angle
      Geo
      D F E C
      hParDFEC
      hRightCDF

  --------------------------------------------------------------------
  -- Noncollinearity at F and arm reversal:
  --
  --     DFE right  ->  EFD right.
  --------------------------------------------------------------------

  have hNC_DFEC :=
    parallelogram_vertices_noncollinear
      Geo D F E C hParDFEC

  have hDFE :
      Not (Collinear Geo D F E) :=
    hNC_DFEC.2.1

  have hEFD :
      Not (Collinear Geo E F D) := by

    intro hEFDcol

    exact
      hDFE
        (PrimCollinearSymm
          Geo E F D hEFDcol)

  have hDFE_EFD :
      Geo.AngleCongruent
        D F E
        E F D :=
    bookZero_56_ABCequalsCBA
      Geo
      D F E
      hDFE

  have hRightEFD :
      HilbertRightAngle Geo E F D :=
    hilbert_right_angle_transport
      Geo
      D F E
      E F D
      hDFE
      hEFD
      hRightDFE
      hDFE_EFD

  --------------------------------------------------------------------
  -- Final package.
  --------------------------------------------------------------------

  exact
    ⟨E, F,
      hACB,
      hCBD,
      hACD,
      hDBA,
      hCE_AC,
      hCE_CB,
      hACE,
      hRightACE,
      hECD,
      hRightECD,
      hParCDFE,
      hParCD_FE,
      hParDF_EC,
      hCD_FE,
      hDF_EC,
      hEFD,
      hRightEFD⟩

------------------------------------------------------------------------
-- Euclid II.10 -- classical angle block
--
-- Source-faithful angle block.
--
-- Starting from test02:
--
--     A --- C --- B --- D
--           |
--           E -------- F
--
-- with
--
--     CE = AC = CB
--     ACE right
--
-- prove, by the Euclidean I.5 + I.32 route, that
--
--     AEC = BEC
--
-- and consequently
--
--     AEB is a right angle.
--
-- This is the II.10 version of the classical angle block already
-- developed during II.9.  No Book II proposition is invoked.
------------------------------------------------------------------------

theorem proposition2_10_classical_angle_block
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D) :
    exists E F R S : Geo.Point,
      Geo.Between A C B /\
      Geo.Between C B D /\
      Geo.Between A C D /\
      Geo.Congruent C E A C /\
      Geo.Congruent C E C B /\
      IsParallelogram Geo C D F E /\
      Geo.Congruent C D F E /\
      Not (Collinear Geo A C E) /\
      HilbertRightAngle Geo A C E /\
      Not (Collinear Geo E C B) /\
      HilbertRightAngle Geo E C B /\
      Geo.Between E R B /\
      Geo.Between E S A /\
      Geo.AngleCongruent E C R B C R /\
      Geo.AngleCongruent E C S A C S /\
      Geo.AngleCongruent A E C B E C /\
      Not (Collinear Geo A E B) /\
      HilbertRightAngle Geo A E B /\
      Not (Collinear Geo E F D) /\
      HilbertRightAngle Geo E F D := by

  --------------------------------------------------------------------
  -- Recover the construction through F from test02.
  --------------------------------------------------------------------

  rcases
      proposition2_10_parallelogram
        Geo A B C D hMidC hABD
    with
    ⟨E, F,
      hACB,
      hCBD,
      hACD,
      _hDBA,
      hCE_AC,
      hCE_CB,
      hACE,
      hRightACE,
      hECD,
      _hRightECD,
      hParCDFE,
      _hParCD_FE,
      _hParDF_EC,
      hCD_FE,
      _hDF_EC,
      hEFD,
      hRightEFD⟩

  --------------------------------------------------------------------
  -- Shared order data.
  --------------------------------------------------------------------

  have hACBdata :=
    HilbertOrder.between_incidence
      A C B hACB

  have hAC :
      A ≠ C :=
    hACBdata.1

  have hCB :
      C ≠ B :=
    hACBdata.2.1

  have hAB :
      A ≠ B :=
    hACBdata.2.2.1

  have hACBcol :
      PrimCollinear Geo A C B :=
    hACBdata.2.2.2.1

  have hBCA :
      Geo.Between B C A :=
    hACBdata.2.2.2.2

  have hCBDdata :=
    HilbertOrder.between_incidence
      C B D hCBD

  have hBD :
      B ≠ D :=
    hCBDdata.2.1

  have hCD :
      C ≠ D :=
    hCBDdata.2.2.1

  have hCBDcol :
      PrimCollinear Geo C B D :=
    hCBDdata.2.2.2.1

  --------------------------------------------------------------------
  -- Recover ECB from ECD along the same ray CB = CD.
  --------------------------------------------------------------------

  have hRayCBD :
      HilbertSameRay Geo C B D :=
    hilbert_sameRay_of_between
      Geo C B D hCBD

  have hECB :
      Not (PrimCollinear Geo E C B) := by

    intro hECBcol

    have hECDcol :
        PrimCollinear Geo E C D :=
      hilbert_primCollinear_trans
        Geo
        E C B D
        hCB
        hECBcol
        hCBDcol

    exact hECD hECDcol

  have hAngleECB_ECD :
      Geo.Angle E C B =
      Geo.Angle E C D :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      C E B D
      hRayCBD

  have hReflECD :
      Geo.AngleCongruent
        E C D
        E C D :=
    HilbertCongruence.angle_congruence_reflexive
      (Geo := Geo)
      E C D
      hECD

  have hECD_ECB :
      Geo.AngleCongruent
        E C D
        E C B := by

    unfold Geometry.Geo.AngleCongruent
      at hReflECD ⊢

    rw [hAngleECB_ECD]

    exact hReflECD

  have hRightECB :
      HilbertRightAngle Geo E C B :=
    hilbert_right_angle_transport
      Geo
      E C D
      E C B
      hECD
      hECB
      _hRightECD
      hECD_ECB

  --------------------------------------------------------------------
  -- Normalize CE = AC = CB to CA = CE.
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
      hACE
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

    exact
      hECB
        (PrimCollinearSwap
          Geo C E B h)

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
  -- I.32 exterior on triangle EAC, extended through C to B.
  --
  -- Obtain R on EB:
  --
  --     AEC = ECR
  --     EAC = RCB
  --
  -- hence CR bisects angle ECB.
  --------------------------------------------------------------------

  have hEAC :
      Not (PrimCollinear Geo E A C) := by

    intro h

    have hACEcol :
        PrimCollinear Geo A C E :=
      PrimCollinearCycle
        Geo E A C h

    exact hACE hACEcol

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
  -- I.32 exterior on triangle EBC, extended through C to A.
  --
  -- Obtain S on EA:
  --
  --     BEC = ECS
  --     EBC = SCA
  --
  -- hence CS bisects angle ECA.
  --------------------------------------------------------------------

  have hEBC :
      Not (PrimCollinear Geo E B C) := by

    intro h

    exact
      hECB
        (PrimCollinearRotate
          Geo E B C h)

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

  have hECA :
      Not (PrimCollinear Geo E C A) := by

    intro h

    exact
      hACE
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

    exact hECB hECBcol

  have hSC :
      S ≠ C := by

    intro hSC

    subst S

    have hECAcol :
        PrimCollinear Geo E C A :=
      (HilbertOrder.between_incidence
        E C A hESA).2.2.2.1

    exact hECA hECAcol

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
  -- The whole angles ECA and ECB are congruent because ACE is right
  -- and A-C-B.
  --------------------------------------------------------------------

  have hACE_ECB :
      Geo.AngleCongruent
        A C E
        E C B :=
    hilbert_right_angle_opposite_extension
      Geo
      A C E B
      hACE
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
      hECB
      hECA
      hInsideR
      hInsideS
      hBisectR
      hBisectS
      hECB_ECA

  --------------------------------------------------------------------
  -- Therefore:
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

    exact hACE hACE'

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

  have hAEB :
      Not (PrimCollinear Geo A E B) := by

    intro hAEBcol

    have hABE :
        PrimCollinear Geo A B E :=
      PrimCollinearRotate
        Geo A E B hAEBcol

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
      hACE
        (PrimCollinearSwap
          Geo C A E hCAE')

  --------------------------------------------------------------------
  -- Match the second component:
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
      hAEB
      hECB
      hInsideC
      hInsideR
      hAEC_ECR
      hCEB_RCB

  --------------------------------------------------------------------
  -- ECB is right, hence AEB is right.
  --------------------------------------------------------------------

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
      hECB
      hAEB
      hRightECB
      hECB_AEB

  --------------------------------------------------------------------
  -- Final package.
  --------------------------------------------------------------------

  exact
    ⟨E, F, R, S,
      hACB,
      hCBD,
      hACD,
      hCE_AC,
      hCE_CB,
      hParCDFE,
      hCD_FE,
      hACE,
      hRightACE,
      hECB,
      hRightECB,
      hERB,
      hESA,
      hBisectR,
      hBisectS,
      hAEC_BEC,
      hAEB,
      hRightAEB,
      hEFD,
      hRightEFD⟩

------------------------------------------------------------------------
-- Euclid II.10 -- oriented intersection block
--
-- Main directed-intersection gate.
--
-- From the configuration already constructed in test03,
--
--     A --- C --- B --- D
--           |              |
--           E ------------ F
--
-- with C-D-F-E a parallelogram, prove that the two lines EB and FD
-- meet in a point G in exactly the Euclidean orientation
--
--     E-B-G
--     F-D-G.
--
-- The proof has two layers.
--
-- 1. Existence of the intersection:
--
--    If EB and DF were disjoint, then both EB and EC would be
--    parallels through E to DF.  Hilbert IV (parallel uniqueness)
--    would identify EB with EC, contradicting noncollinearity E-C-B.
--
-- 2. Directed order:
--
--    * E and B lie on the same side of DF, so G cannot lie between
--      E and B.
--
--    * B and G lie on the same side of EC, so E cannot lie between
--      B and G.
--
--      Hence E-B-G.
--
--    * E-B-G crosses CD at B.  Since E and F are on the same side of
--      CD, F and G are on opposite sides of CD.  Their common line is
--      DF, whose unique intersection with CD is D.  Hence F-D-G.
------------------------------------------------------------------------

theorem proposition2_10_oriented_intersection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D) :
    exists E F G R S : Geo.Point,
      Geo.Between A C B /\
      Geo.Between C B D /\
      Geo.Between A C D /\
      Geo.Congruent C E A C /\
      Geo.Congruent C E C B /\
      IsParallelogram Geo C D F E /\
      Geo.Congruent C D F E /\
      Not (Collinear Geo A C E) /\
      HilbertRightAngle Geo A C E /\
      Not (Collinear Geo E C B) /\
      HilbertRightAngle Geo E C B /\
      Geo.AngleCongruent A E C B E C /\
      Not (Collinear Geo A E B) /\
      HilbertRightAngle Geo A E B /\
      Not (Collinear Geo E F D) /\
      HilbertRightAngle Geo E F D /\
      Geo.Between E B G /\
      Geo.Between F D G /\
      Geo.Between E R B /\
      Geo.Between E S A /\
      Geo.AngleCongruent E C R B C R /\
      Geo.AngleCongruent E C S A C S := by

  --------------------------------------------------------------------
  -- Recover the classical angle block.
  --------------------------------------------------------------------

  rcases
      proposition2_10_classical_angle_block
        Geo A B C D hMidC hABD
    with
    ⟨E, F, R, S,
      hACB,
      hCBD,
      hACD,
      hCE_AC,
      hCE_CB,
      hParCDFE,
      hCD_FE,
      hACE,
      hRightACE,
      hECB,
      hRightECB,
      hERB,
      hESA,
      hBisectR,
      hBisectS,
      hAEC_BEC,
      hAEB,
      hRightAEB,
      hEFD,
      hRightEFD⟩

  --------------------------------------------------------------------
  -- Parallelogram nondegeneracy.
  --------------------------------------------------------------------

  have hParNC :=
    parallelogram_vertices_noncollinear
      Geo C D F E hParCDFE

  have hECD :
      Not (Collinear Geo E C D) :=
    hParNC.1

  have hCDF :
      Not (Collinear Geo C D F) :=
    hParNC.2.1

  have hDCE :
      Not (Collinear Geo D C E) := by

    intro h

    exact
      hECD
        (PrimCollinearSymm
          Geo D C E h)

  --------------------------------------------------------------------
  -- Parallel EC || DF.
  --------------------------------------------------------------------

  have hParDF_EC :
      Geo.Parallel D F E C :=
    hParCDFE.2

  have hParEC_DF :
      Geo.Parallel E C D F :=
    ParallelSymmetry
      Geo
      D F E C
      hParDF_EC

  have hEC :
      E ≠ C :=
    hParEC_DF.1

  have hDF :
      D ≠ F :=
    hParEC_DF.2.1

  have hFD :
      F ≠ D :=
    hDF.symm

  --------------------------------------------------------------------
  -- E,B,C is noncollinear and therefore E != B.
  --------------------------------------------------------------------

  have hEBC :
      Not (Collinear Geo E B C) := by

    intro h

    exact
      hECB
        (PrimCollinearRotate
          Geo E B C h)

  have hEB :
      E ≠ B :=
    hilbert_noncollinear_ne_first
      Geo E B C hEBC

  --------------------------------------------------------------------
  -- Supporting incidence lines EC, DF, EB, CD.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        E C hEC
    with
    ⟨lineEC, hEec, hCec⟩

  rcases
      HilbertPlaneIncidence.line_through
        D F hDF
    with
    ⟨lineDF, hDdf, hFdf⟩

  rcases
      HilbertPlaneIncidence.line_through
        E B hEB
    with
    ⟨lineEB, hEeb, hBeb⟩

  have hCBDdata :=
    HilbertOrder.between_incidence
      C B D hCBD

  have hCB :
      C ≠ B :=
    hCBDdata.1

  have hBD :
      B ≠ D :=
    hCBDdata.2.1

  have hCD :
      C ≠ D :=
    hCBDdata.2.2.1

  rcases
      HilbertPlaneIncidence.line_through
        C D hCD
    with
    ⟨lineCD, hCcd, hDcd⟩

  have hBcd :
      HilbertIncidence.OnLine B lineCD :=
    hilbert_between_on_line
      Geo
      C B D
      lineCD
      hCcd hDcd
      hCBD

  --------------------------------------------------------------------
  -- Incidence lines EC and DF are disjoint because EC || DF.
  --------------------------------------------------------------------

  have hLinesEC_DF :
      HilbertLinesDisjoint Geo lineEC lineDF := by

    rintro ⟨X, hXec, hXdf⟩

    have hX_EC :
        X ∈ Geo.PointLine E C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        E C X
        lineEC
        hEC
        hEec hCec).mpr
        hXec

    have hX_DF :
        X ∈ Geo.PointLine D F :=
      (hilbert_mem_pointLine_iff_onLine
        Geo
        D F X
        lineDF
        hDF
        hDdf hFdf).mpr
        hXdf

    exact
      Set.disjoint_left.mp
        hParEC_DF.2.2
        hX_EC
        hX_DF

  have hEoffDF :
      Not (HilbertIncidence.OnLine E lineDF) := by

    intro hEdf

    exact
      hLinesEC_DF
        ⟨E, hEec, hEdf⟩

  --------------------------------------------------------------------
  -- EB and DF must meet.
  --
  -- If not, EB and EC are the two lines through E parallel to DF.
  -- Hilbert IV identifies them, forcing B onto EC.
  --------------------------------------------------------------------

  have hMeetEB_DF :
      HilbertLinesMeet Geo lineEB lineDF := by

    by_contra hLinesEB_DF

    have hLineEB_EC :
        lineEB = lineEC :=
      HilbertEuclideanPlane.parallel_unique
        (Geo := Geo)
        lineDF
        E
        hEoffDF
        lineEB
        lineEC
        hEeb
        hLinesEB_DF
        hEec
        hLinesEC_DF

    have hBec :
        HilbertIncidence.OnLine B lineEC := by

      rw [← hLineEB_EC]

      exact hBeb

    exact
      hECB
        ⟨lineEC,
          hEec,
          hCec,
          hBec⟩

  rcases hMeetEB_DF with
    ⟨G, hGeb, hGdf⟩

  --------------------------------------------------------------------
  -- Collinearity E-B-G.
  --------------------------------------------------------------------

  have hEBGcol :
      Collinear Geo E B G :=
    ⟨lineEB,
      hEeb,
      hBeb,
      hGeb⟩

  --------------------------------------------------------------------
  -- E and B are on the same side of DF.
  --
  -- C and B are on the same side of DF because C-B-D and F is off
  -- CD.  E and C are on the same side of DF because EC || DF.
  --------------------------------------------------------------------

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        C B F D
        hCBD
        hCDF
    with
    ⟨lineFD1,
      hFfd1,
      hDfd1,
      hSameCB_fd1⟩

  have hLineFD1_DF :
      lineFD1 = lineDF :=
    HilbertPlaneIncidence.line_unique
      F D hFD
      lineFD1 lineDF
      hFfd1 hDfd1
      hFdf hDdf

  have hSameCB_DF :
      HilbertSameSide Geo C B lineDF := by

    rw [← hLineFD1_DF]

    exact hSameCB_fd1

  rcases
      parallel_endpoints_sameSide
        Geo
        E C D F
        hParEC_DF
    with
    ⟨lineDF2,
      hDdf2,
      hFdf2,
      hSameEC_df2⟩

  have hLineDF2_DF :
      lineDF2 = lineDF :=
    HilbertPlaneIncidence.line_unique
      D F hDF
      lineDF2 lineDF
      hDdf2 hFdf2
      hDdf hFdf

  have hSameEC_DF :
      HilbertSameSide Geo E C lineDF := by

    rw [← hLineDF2_DF]

    exact hSameEC_df2

  have hSameEB_DF :
      HilbertSameSide Geo E B lineDF :=
    hilbert_sameSide_trans
      Geo
      E C B
      lineDF
      hSameEC_DF
      hSameCB_DF

  --------------------------------------------------------------------
  -- Hence G is distinct from E and B.
  --------------------------------------------------------------------

  have hEG :
      E ≠ G := by

    intro h

    subst G

    exact
      hSameEB_DF.1
        hGdf

  have hBG :
      B ≠ G := by

    intro h

    subst G

    exact
      hSameEB_DF.2.1
        hGdf

  --------------------------------------------------------------------
  -- D and B are on the same side of EC.
  --
  -- Use D-B-C and the transversal EC.
  --------------------------------------------------------------------

  have hDBC :
      Geo.Between D B C :=
    hCBDdata.2.2.2.2

  rcases
      hilbert_between_points_sameSide_transversal
        Geo
        D B E C
        hDBC
        hDCE
    with
    ⟨lineEC1,
      hEec1,
      hCec1,
      hSameDB_ec1⟩

  have hLineEC1_EC :
      lineEC1 = lineEC :=
    HilbertPlaneIncidence.line_unique
      E C hEC
      lineEC1 lineEC
      hEec1 hCec1
      hEec hCec

  have hSameDB_EC :
      HilbertSameSide Geo D B lineEC := by

    rw [← hLineEC1_EC]

    exact hSameDB_ec1

  --------------------------------------------------------------------
  -- D and G lie on the same line DF, which is disjoint from EC.
  -- Therefore D and G are on the same side of EC.
  --------------------------------------------------------------------

  have hDoffEC :
      Not (HilbertIncidence.OnLine D lineEC) := by

    intro hDec

    exact
      hLinesEC_DF
        ⟨D, hDec, hDdf⟩

  have hGoffEC :
      Not (HilbertIncidence.OnLine G lineEC) := by

    intro hGec

    exact
      hLinesEC_DF
        ⟨G, hGec, hGdf⟩

  have hNoMeetDG_EC :
      Not (HilbertSegmentMeetsLine Geo D G lineEC) := by

    intro hMeet

    rcases hMeet with
      ⟨X, hDXG, hXec⟩

    have hXdf :
        HilbertIncidence.OnLine X lineDF :=
      hilbert_between_on_line
        Geo
        D X G
        lineDF
        hDdf hGdf
        hDXG

    exact
      hLinesEC_DF
        ⟨X, hXec, hXdf⟩

  have hSameDG_EC :
      HilbertSameSide Geo D G lineEC :=
    ⟨hDoffEC,
      hGoffEC,
      Relation.ReflTransGen.single
        ⟨hDoffEC,
          hGoffEC,
          hNoMeetDG_EC⟩⟩

  have hSameBD_EC :
      HilbertSameSide Geo B D lineEC :=
    hilbert_sameSide_symm
      Geo
      D B
      lineEC
      hSameDB_EC

  have hSameBG_EC :
      HilbertSameSide Geo B G lineEC :=
    hilbert_sameSide_trans
      Geo
      B D G
      lineEC
      hSameBD_EC
      hSameDG_EC

  --------------------------------------------------------------------
  -- Trichotomy on E,B,G.
  --
  -- Case 1: E-B-G -- desired.
  --
  -- Case 2: B-E-G -- impossible because E lies on EC while B and G
  --         are on the same side of EC.
  --
  -- Case 3: E-G-B -- impossible because G lies on DF while E and B
  --         are on the same side of DF.
  --------------------------------------------------------------------

  have hEBG :
      Geo.Between E B G := by

    rcases
        hilbert_between_trichotomy
          Geo
          E B G
          hEB
          hBG
          hEG
          hEBGcol
      with
      hCaseEBG | hCaseBEG | hCaseEGB

    · exact hCaseEBG

    · have hOppBG_EC :
          HilbertOppositeSide Geo B G lineEC :=
        ⟨hSameBG_EC.1,
          hSameBG_EC.2.1,
          ⟨E,
            hCaseBEG,
            hEec⟩⟩

      exact
        False.elim
          ((hilbert_oppositeSide_not_sameSide
            Geo
            B G
            lineEC
            hOppBG_EC)
            hSameBG_EC)

    · have hOppEB_DF :
          HilbertOppositeSide Geo E B lineDF :=
        ⟨hSameEB_DF.1,
          hSameEB_DF.2.1,
          ⟨G,
            hCaseEGB,
            hGdf⟩⟩

      exact
        False.elim
          ((hilbert_oppositeSide_not_sameSide
            Geo
            E B
            lineDF
            hOppEB_DF)
            hSameEB_DF)

  --------------------------------------------------------------------
  -- Prepare EF || CD.
  --------------------------------------------------------------------

  have hParCD_FE :
      Geo.Parallel C D F E :=
    hParCDFE.1

  have hParFE_CD :
      Geo.Parallel F E C D :=
    ParallelSymmetry
      Geo
      C D F E
      hParCD_FE

  rcases
      parallel_endpoints_sameSide
        Geo
        F E C D
        hParFE_CD
    with
    ⟨lineCD1,
      hCcd1,
      hDcd1,
      hSameFE_cd1⟩

  have hLineCD1_CD :
      lineCD1 = lineCD :=
    HilbertPlaneIncidence.line_unique
      C D hCD
      lineCD1 lineCD
      hCcd1 hDcd1
      hCcd hDcd

  have hSameFE_CD :
      HilbertSameSide Geo F E lineCD := by

    rw [← hLineCD1_CD]

    exact hSameFE_cd1

  have hEoffCD :
      Not (HilbertIncidence.OnLine E lineCD) :=
    hSameFE_CD.2.1

  --------------------------------------------------------------------
  -- G is not on CD.
  --
  -- Otherwise B and G determine both EB and CD, forcing E onto CD.
  --------------------------------------------------------------------

  have hGoffCD :
      Not (HilbertIncidence.OnLine G lineCD) := by

    intro hGcd

    have hLineEB_CD :
        lineEB = lineCD :=
      HilbertPlaneIncidence.line_unique
        B G hBG
        lineEB lineCD
        hBeb hGeb
        hBcd hGcd

    have hEcd :
        HilbertIncidence.OnLine E lineCD := by

      rw [← hLineEB_CD]

      exact hEeb

    exact hEoffCD hEcd

  --------------------------------------------------------------------
  -- E and G are on opposite sides of CD, with crossing point B.
  --------------------------------------------------------------------

  have hOppEG_CD :
      HilbertOppositeSide Geo E G lineCD :=
    ⟨hEoffCD,
      hGoffCD,
      ⟨B,
        hEBG,
        hBcd⟩⟩

  --------------------------------------------------------------------
  -- F and E are on the same side of CD.
  -- Transport the opposite-side relation from E to F.
  --------------------------------------------------------------------

  have hSameEF_CD :
      HilbertSameSide Geo E F lineCD :=
    hilbert_sameSide_symm
      Geo
      F E
      lineCD
      hSameFE_CD

  have hOppGE_CD :
      HilbertOppositeSide Geo G E lineCD :=
    hilbert_oppositeSide_symm
      Geo
      E G
      lineCD
      hOppEG_CD

  have hOppGF_CD :
      HilbertOppositeSide Geo G F lineCD :=
    hilbert_oppositeSide_transport_right
      Geo
      G E F
      lineCD
      hOppGE_CD
      hSameEF_CD

  have hOppFG_CD :
      HilbertOppositeSide Geo F G lineCD :=
    hilbert_oppositeSide_symm
      Geo
      G F
      lineCD
      hOppGF_CD

  --------------------------------------------------------------------
  -- Therefore segment FG meets CD.
  --
  -- Let H be the crossing point.  Since F,G lie on DF, H is also on
  -- DF.  The two distinct lines CD and DF already meet at D, hence
  -- incidence uniqueness gives H = D.
  --------------------------------------------------------------------

  rcases hOppFG_CD.2.2 with
    ⟨H, hFHG, hHcd⟩

  have hHdf :
      HilbertIncidence.OnLine H lineDF :=
    hilbert_between_on_line
      Geo
      F H G
      lineDF
      hFdf hGdf
      hFHG

  have hHD :
      H = D := by

    by_contra hHD

    have hLineCD_DF :
        lineCD = lineDF :=
      HilbertPlaneIncidence.line_unique
        H D hHD
        lineCD lineDF
        hHcd hDcd
        hHdf hDdf

    have hFcd :
        HilbertIncidence.OnLine F lineCD := by

      rw [hLineCD_DF]

      exact hFdf

    exact
      hSameFE_CD.1
        hFcd

  subst H

  have hFDG :
      Geo.Between F D G :=
    hFHG

  --------------------------------------------------------------------
  -- Final package.
  --------------------------------------------------------------------

  exact
    ⟨E, F, G, R, S,
      hACB,
      hCBD,
      hACD,
      hCE_AC,
      hCE_CB,
      hParCDFE,
      hCD_FE,
      hACE,
      hRightACE,
      hECB,
      hRightECB,
      hAEC_BEC,
      hAEB,
      hRightAEB,
      hEFD,
      hRightEFD,
      hEBG,
      hFDG,
      hERB,
      hESA,
      hBisectR,
      hBisectS⟩

------------------------------------------------------------------------
-- Euclid II.10 -- classical isosceles blocks
--
-- Classical isosceles blocks.
--
-- Source route:
--
--   I.5, I.15, I.29, I.32, I.6
--
-- First:
--
--   angle EBC is half a right angle,
--   angle DBG is its vertical angle,
--   angle BDG is right,
--   hence by I.32 angle DGB is the other half-right angle,
--   so DB = DG by I.6.
--
-- Second:
--
--   angle EGF is the same half-right angle as DGB,
--   angle EFG is right,
--   hence by I.32 angle FEG is the other half-right angle,
--   so GF = EF by I.6.
--
-- The phrase "half a right angle" is represented synthetically by
-- congruence with ECR, where CR is the bisector of the right angle
-- ECB already constructed in test03.
------------------------------------------------------------------------

theorem proposition2_10_classical_isosceles_blocks
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D) :
    exists E F G R S : Geo.Point,
      Geo.Between A C B /\
      Geo.Between C B D /\
      Geo.Between A C D /\
      Geo.Between E B G /\
      Geo.Between F D G /\
      Geo.Congruent C E A C /\
      Geo.Congruent C E C B /\
      IsParallelogram Geo C D F E /\
      Geo.Congruent C D F E /\
      Not (Collinear Geo A C E) /\
      HilbertRightAngle Geo A C E /\
      Not (Collinear Geo E C B) /\
      HilbertRightAngle Geo E C B /\
      Geo.Between E R B /\
      Geo.Between E S A /\
      Geo.AngleCongruent E C R B C R /\
      Geo.AngleCongruent E C S A C S /\
      Geo.AngleCongruent A E C B E C /\
      Not (Collinear Geo A E B) /\
      HilbertRightAngle Geo A E B /\
      Not (Collinear Geo E F D) /\
      HilbertRightAngle Geo E F D /\
      Geo.Congruent D B D G /\
      Geo.Congruent G F E F := by

  --------------------------------------------------------------------
  -- Recover the directed intersection and the complete angle block.
  --------------------------------------------------------------------

  rcases
      proposition2_10_oriented_intersection
        Geo A B C D hMidC hABD
    with
    ⟨E, F, G, R, S,
      hACB,
      hCBD,
      hACD,
      hCE_AC,
      hCE_CB,
      hParCDFE,
      hCD_FE,
      hACE,
      hRightACE,
      hECB,
      hRightECB,
      hAEC_BEC,
      hAEB,
      hRightAEB,
      hEFD,
      hRightEFD,
      hEBG,
      hFDG,
      hERB,
      hESA,
      hBisectR,
      hBisectS⟩

  --------------------------------------------------------------------
  -- Shared order data.
  --------------------------------------------------------------------

  have hACBdata :=
    HilbertOrder.between_incidence
      A C B hACB

  have hAB :
      A ≠ B :=
    hACBdata.2.2.1

  have hCBDdata :=
    HilbertOrder.between_incidence
      C B D hCBD

  have hCB :
      C ≠ B :=
    hCBDdata.1

  have hBD :
      B ≠ D :=
    hCBDdata.2.1

  have hCD :
      C ≠ D :=
    hCBDdata.2.2.1

  have hDBC :
      Geo.Between D B C :=
    hCBDdata.2.2.2.2

  have hFDGdata :=
    HilbertOrder.between_incidence
      F D G hFDG

  have hFD :
      F ≠ D :=
    hFDGdata.1

  have hDG :
      D ≠ G :=
    hFDGdata.2.1

  have hFG :
      F ≠ G :=
    hFDGdata.2.2.1

  have hGDF :
      Geo.Between G D F :=
    hFDGdata.2.2.2.2

  have hEBGdata :=
    HilbertOrder.between_incidence
      E B G hEBG

  have hEB :
      E ≠ B :=
    hEBGdata.1

  have hBG :
      B ≠ G :=
    hEBGdata.2.1

  have hEG :
      E ≠ G :=
    hEBGdata.2.2.1

  have hGBE :
      Geo.Between G B E :=
    hEBGdata.2.2.2.2

  --------------------------------------------------------------------
  -- Parallelogram nondegeneracy and right angle CDF.
  --
  -- The adjacent-right-angle theorem is the packaged I.29 consequence
  -- used here.
  --------------------------------------------------------------------

  have hParNC :=
    parallelogram_vertices_noncollinear
      Geo C D F E hParCDFE

  have hECD :
      Not (Collinear Geo E C D) :=
    hParNC.1

  have hCDF :
      Not (Collinear Geo C D F) :=
    hParNC.2.1

  have hRayCBD :
      HilbertSameRay Geo C B D :=
    hilbert_sameRay_of_between
      Geo C B D hCBD

  have hAngleECB_ECD :
      Geo.Angle E C B =
      Geo.Angle E C D :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      C E B D
      hRayCBD

  have hReflECB :
      Geo.AngleCongruent
        E C B
        E C B :=
    Geometry.Geo.angle_congruent_reflexive
      Geo E C B

  have hECB_ECD :
      Geo.AngleCongruent
        E C B
        E C D := by

    unfold Geometry.Geo.AngleCongruent
      at hReflECB ⊢

    rw [← hAngleECB_ECD]

    exact hReflECB

  have hRightECD :
      HilbertRightAngle Geo E C D :=
    hilbert_right_angle_transport
      Geo
      E C B
      E C D
      hECB
      hECD
      hRightECB
      hECB_ECD

  have hRightCDF :
      HilbertRightAngle Geo C D F :=
    parallelogram_adjacent_right_angle
      Geo
      C D F E
      hParCDFE
      hRightECD

  --------------------------------------------------------------------
  -- Reference half-right angle ECR.
  --
  -- AEB and ECB are right, EC and CR bisect them, so AEC = ECR.
  -- Since AEC = BEC, also BEC = ECR.
  --------------------------------------------------------------------

  have hCEA :
      Not (PrimCollinear Geo C E A) := by

    intro h

    have hEAC :
        PrimCollinear Geo E A C :=
      PrimCollinearCycle
        Geo C E A h

    have hACEcol :
        PrimCollinear Geo A C E :=
      PrimCollinearCycle
        Geo E A C hEAC

    exact hACE hACEcol

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

  have hRC :
      R ≠ C := by

    intro hRC

    subst R

    have hECBcol :
        PrimCollinear Geo E C B :=
      (HilbertOrder.between_incidence
        E C B hERB).2.2.2.1

    exact hECB hECBcol

  have hInsideR_ECB :
      HilbertRayMeetsSegment Geo C R E B :=
    ⟨R,
      hERB,
      hilbert_sameRay_refl
        Geo C R hRC⟩

  have hAEB_ECB :
      Geo.AngleCongruent
        A E B
        E C B :=
    hilbert_all_right_angles_congruent
      Geo
      A E B
      E C B
      hAEB
      hECB
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
      hAEB
      hECB
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
  -- I.5 in triangle CEB:
  --
  --     BEC = EBC.
  --------------------------------------------------------------------

  have hCEB :
      Not (PrimCollinear Geo C E B) := by

    intro h

    exact
      hECB
        (PrimCollinearSwap
          Geo C E B h)

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

  have hEBC_ECR :
      Geo.AngleCongruent
        E B C
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E B C
      B E C
      E C R
      hEBC_BEC
      hBEC_ECR

  --------------------------------------------------------------------
  --------------------------------------------------------------------
  -- FIRST ISOSCELES BLOCK: DB = DG
  --------------------------------------------------------------------
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- I.15:
  --
  -- E-B-G and C-B-D give vertical angles
  --
  --     EBC = GBD.
  --------------------------------------------------------------------

  have hEBC :
      Not (Collinear Geo E B C) := by

    intro h

    exact
      hECB
        (PrimCollinearRotate
          Geo E B C h)

  have hEBC_GBD :
      Geo.AngleCongruent
        E B C
        G B D :=
    VerticalAngles
      Geo
      E B C
      G D
      hEBG
      hCBD
      hEBC

  have hGBD_EBC :
      Geo.AngleCongruent
        G B D
        E B C :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E B C
      G B D
      hEBC_GBD

  have hGBD_ECR :
      Geo.AngleCongruent
        G B D
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      G B D
      E B C
      E C R
      hGBD_EBC
      hEBC_ECR

  --------------------------------------------------------------------
  -- BDG is right.
  --
  -- CDF is right.  From D, B and C determine the same ray.
  -- Then F-D-G replaces DF by its opposite ray.
  --------------------------------------------------------------------

  have hRayDBC :
      HilbertSameRay Geo D B C :=
    hilbert_sameRay_of_between
      Geo D B C hDBC

  have hRayDCB :
      HilbertSameRay Geo D C B :=
    hilbert_sameRay_symm
      Geo D B C hRayDBC

  have hDF :
      D ≠ F :=
    hFD.symm

  have hRayDFF :
      HilbertSameRay Geo D F F :=
    hilbert_sameRay_refl
      Geo D F hDF.symm

  have hBDF :
      Not (Collinear Geo B D F) :=
    hilbert_noncollinear_of_sameRays
      Geo
      C D F
      B F
      hCDF
      hRayDCB
      hRayDFF

  have hAngleCDF_BDF :
      Geo.Angle C D F =
      Geo.Angle B D F :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      D C B F
      hRayDCB

  have hReflCDF :
      Geo.AngleCongruent
        C D F
        C D F :=
    Geometry.Geo.angle_congruent_reflexive
      Geo C D F

  have hCDF_BDF :
      Geo.AngleCongruent
        C D F
        B D F := by

    unfold Geometry.Geo.AngleCongruent
      at hReflCDF ⊢

    rw [← hAngleCDF_BDF]

    exact hReflCDF

  have hRightBDF :
      HilbertRightAngle Geo B D F :=
    hilbert_right_angle_transport
      Geo
      C D F
      B D F
      hCDF
      hBDF
      hRightCDF
      hCDF_BDF

  have hFDB :
      Not (Collinear Geo F D B) := by

    intro h

    exact
      hBDF
        (PrimCollinearSymm
          Geo F D B h)

  have hBDF_FDB :
      Geo.AngleCongruent
        B D F
        F D B :=
    bookZero_56_ABCequalsCBA
      Geo
      B D F
      hBDF

  have hRightFDB :
      HilbertRightAngle Geo F D B :=
    hilbert_right_angle_transport
      Geo
      B D F
      F D B
      hBDF
      hFDB
      hRightBDF
      hBDF_FDB

  have hBDG :
      Not (Collinear Geo B D G) := by

    intro hBDGcol

    have hGDFcol :
        PrimCollinear Geo G D F :=
      (HilbertOrder.between_incidence
        G D F hGDF).2.2.2.1

    have hDGF :
        PrimCollinear Geo D G F :=
      PrimCollinearSwap
        Geo G D F hGDFcol

    have hBDG_F :
        PrimCollinear Geo B D F :=
      hilbert_primCollinear_trans
        Geo
        B D G F
        hDG
        hBDGcol
        hDGF

    exact hBDF hBDG_F

  have hFDB_BDG :
      Geo.AngleCongruent
        F D B
        B D G :=
    hilbert_right_angle_opposite_extension
      Geo
      F D B G
      hFDB
      hRightFDB
      hFDG

  have hRightBDG :
      HilbertRightAngle Geo B D G :=
    hilbert_right_angle_transport
      Geo
      F D B
      B D G
      hFDB
      hBDG
      hRightFDB
      hFDB_BDG

  --------------------------------------------------------------------
  -- I.32 in triangle GBD.
  --
  -- Extend BD through D:
  --
  --     B-D-X.
  --
  -- The exterior right angle GDX is decomposed into the two remote
  -- angles BGD and GBD.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        B D hBD
    with
    ⟨X, hBDX⟩

  have hGDX :
      Not (Collinear Geo G D X) := by

    intro hGDXcol

    have hBDXcol :
        PrimCollinear Geo B D X :=
      (HilbertOrder.between_incidence
        B D X hBDX).2.2.2.1

    have hDX :
        D ≠ X :=
      (HilbertOrder.between_incidence
        B D X hBDX).2.1

    have hXDG :
        PrimCollinear Geo X D G :=
      PrimCollinearSymm
        Geo G D X hGDXcol

    have hBDGcol :
        PrimCollinear Geo B D G :=
      hilbert_primCollinear_trans
        Geo
        B D X G
        hDX
        hBDXcol
        (PrimCollinearSwap
          Geo X D G hXDG)

    exact hBDG hBDGcol

  have hBDG_GDX :
      Geo.AngleCongruent
        B D G
        G D X :=
    hilbert_right_angle_opposite_extension
      Geo
      B D G X
      hBDG
      hRightBDG
      hBDX

  have hRightGDX :
      HilbertRightAngle Geo G D X :=
    hilbert_right_angle_transport
      Geo
      B D G
      G D X
      hBDG
      hGDX
      hRightBDG
      hBDG_GDX

  have hGBD :
      Not (PrimCollinear Geo G B D) := by

    intro h

    exact
      hBDG
        (PrimCollinearCycle
          Geo G B D h)

  rcases
      euclid_proposition_32_exterior
        G B D X
        hGBD
        hBDX
    with
    ⟨T,
      hGTX,
      hBGD_GDT,
      hGBD_TDX⟩

  have hTD :
      T ≠ D := by

    intro hTD

    subst T

    have hGDXcol :
        PrimCollinear Geo G D X :=
      (HilbertOrder.between_incidence
        G D X hGTX).2.2.2.1

    exact hGDX hGDXcol

  have hInsideT_GDX :
      HilbertRayMeetsSegment Geo D T G X :=
    ⟨T,
      hGTX,
      hilbert_sameRay_refl
        Geo D T hTD⟩

  --------------------------------------------------------------------
  -- The I.32 component TDX is the known half-right angle ECR.
  --------------------------------------------------------------------

  have hTDX_GBD :
      Geo.AngleCongruent
        T D X
        G B D :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      G B D
      T D X
      hGBD_TDX

  have hTDX_ECR :
      Geo.AngleCongruent
        T D X
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      T D X
      G B D
      E C R
      hTDX_GBD
      hGBD_ECR

  have hXDT_ECR :
      Geo.AngleCongruent
        X D T
        E C R :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      T D X
      E C R).mp
      hTDX_ECR

  have hXDT_BCR :
      Geo.AngleCongruent
        X D T
        B C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      X D T
      E C R
      B C R
      hXDT_ECR
      hBisectR

  --------------------------------------------------------------------
  -- GDX and ECB are right.  Subtract equal half-right components.
  -- The remaining angle GDT is another copy of ECR.
  --------------------------------------------------------------------

  have hGDX_ECB :
      Geo.AngleCongruent
        G D X
        E C B :=
    hilbert_all_right_angles_congruent
      Geo
      G D X
      E C B
      hGDX
      hECB
      hRightGDX
      hRightECB

  have hGDT_ECR :
      Geo.AngleCongruent
        G D T
        E C R :=
    hilbert_angleDecomposition_angle_subtraction
      Geo
      D G X T
      E C B R
      hGDX
      hECB
      hInsideT_GDX
      hInsideR_ECB
      hGDX_ECB
      hXDT_BCR

  have hBGD_ECR :
      Geo.AngleCongruent
        B G D
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      B G D
      G D T
      E C R
      hBGD_GDT
      hGDT_ECR

  --------------------------------------------------------------------
  -- Thus the two base angles of triangle DBG are congruent.
  --------------------------------------------------------------------

  have hDBG_ECR :
      Geo.AngleCongruent
        D B G
        E C R :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      G B D
      E C R).mp
      hGBD_ECR

  have hDGB_ECR :
      Geo.AngleCongruent
        D G B
        E C R :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      B G D
      E C R).mp
      hBGD_ECR

  have hECR_DGB :
      Geo.AngleCongruent
        E C R
        D G B :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      D G B
      E C R
      hDGB_ECR

  have hDBG_DGB :
      Geo.AngleCongruent
        D B G
        D G B :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      D B G
      E C R
      D G B
      hDBG_ECR
      hECR_DGB

  have hDBG :
      Not (Collinear Geo D B G) := by

    intro h

    exact
      hBDG
        (PrimCollinearSwap
          Geo D B G h)

  have hDB_DG :
      Geo.Congruent D B D G :=
    euclid_proposition_6
      Geo
      D B G
      hDBG
      hDBG_DGB

  --------------------------------------------------------------------
  --------------------------------------------------------------------
  -- SECOND ISOSCELES BLOCK: GF = EF
  --------------------------------------------------------------------
  --------------------------------------------------------------------

  --------------------------------------------------------------------
  -- EGF is the same half-right angle as BGD = DGB.
  --
  -- From G:
  --
  --     GE and GB are the same ray,
  --     GF and GD are the same ray.
  --------------------------------------------------------------------

  have hRayGBE :
      HilbertSameRay Geo G B E :=
    hilbert_sameRay_of_between
      Geo G B E hGBE

  have hRayGEB :
      HilbertSameRay Geo G E B :=
    hilbert_sameRay_symm
      Geo G B E hRayGBE

  have hRayGDF :
      HilbertSameRay Geo G D F :=
    hilbert_sameRay_of_between
      Geo G D F hGDF

  have hRayGFD :
      HilbertSameRay Geo G F D :=
    hilbert_sameRay_symm
      Geo G D F hRayGDF

  have hAngleEGF_BGD :
      Geo.Angle E G F =
      Geo.Angle B G D := by

    calc
      Geo.Angle E G F
          = Geo.Angle B G F :=
        hilbert_angle_eq_of_sameRay_first
          Geo
          G E B F
          hRayGEB

      _ = Geo.Angle B G D :=
        hilbert_angle_eq_of_sameRay_second
          Geo
          G B F D
          hRayGFD

  have hReflBGD :
      Geo.AngleCongruent
        B G D
        B G D :=
    Geometry.Geo.angle_congruent_reflexive
      Geo B G D

  have hEGF_BGD :
      Geo.AngleCongruent
        E G F
        B G D := by

    unfold Geometry.Geo.AngleCongruent
      at hReflBGD ⊢

    rw [hAngleEGF_BGD]

    exact hReflBGD

  have hEGF_ECR :
      Geo.AngleCongruent
        E G F
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E G F
      B G D
      E C R
      hEGF_BGD
      hBGD_ECR

  --------------------------------------------------------------------
  -- EFG is right.
  --
  -- EFD is right and D,G are on the same ray from F.
  --------------------------------------------------------------------

  have hRayFDG :
      HilbertSameRay Geo F D G :=
    hilbert_sameRay_of_between
      Geo F D G hFDG

  have hEF :
      E ≠ F :=
    hilbert_noncollinear_ne_first
      Geo E F D hEFD

  have hFE :
      F ≠ E :=
    hEF.symm

  have hRayFEE :
      HilbertSameRay Geo F E E :=
    hilbert_sameRay_refl
      Geo F E hEF

  have hEFG :
      Not (Collinear Geo E F G) :=
    hilbert_noncollinear_of_sameRays
      Geo
      E F D
      E G
      hEFD
      hRayFEE
      hRayFDG

  have hAngleEFD_EFG :
      Geo.Angle E F D =
      Geo.Angle E F G :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      F E D G
      hRayFDG

  have hReflEFD :
      Geo.AngleCongruent
        E F D
        E F D :=
    Geometry.Geo.angle_congruent_reflexive
      Geo E F D

  have hEFD_EFG :
      Geo.AngleCongruent
        E F D
        E F G := by

    unfold Geometry.Geo.AngleCongruent
      at hReflEFD ⊢

    rw [← hAngleEFD_EFG]

    exact hReflEFD

  have hRightEFG :
      HilbertRightAngle Geo E F G :=
    hilbert_right_angle_transport
      Geo
      E F D
      E F G
      hEFD
      hEFG
      hRightEFD
      hEFD_EFG

  --------------------------------------------------------------------
  -- Extend GF through F:
  --
  --     G-F-Y.
  --
  -- The adjacent exterior angle EFY is right.
  --------------------------------------------------------------------

  have hGF :
      G ≠ F :=
    hFG.symm

  rcases
      HilbertOrder.between_extension
        G F hGF
    with
    ⟨Y, hGFY⟩

  have hGFE :
      Not (Collinear Geo G F E) := by

    intro h

    exact
      hEFG
        (PrimCollinearSymm
          Geo G F E h)

  have hEFY :
      Not (Collinear Geo E F Y) := by

    intro hEFYcol

    have hGFYcol :
        PrimCollinear Geo G F Y :=
      (HilbertOrder.between_incidence
        G F Y hGFY).2.2.2.1

    have hFY :
        F ≠ Y :=
      (HilbertOrder.between_incidence
        G F Y hGFY).2.1

    have hYFE :
        PrimCollinear Geo Y F E :=
      PrimCollinearSymm
        Geo E F Y hEFYcol

    have hGFEcol :
        PrimCollinear Geo G F E :=
      hilbert_primCollinear_trans
        Geo
        G F Y E
        hFY
        hGFYcol
        (PrimCollinearSwap
          Geo Y F E hYFE)

    exact hGFE hGFEcol

  have hEFG_GFE :
      Geo.AngleCongruent
        E F G
        G F E :=
    bookZero_56_ABCequalsCBA
      Geo
      E F G
      hEFG

  have hRightGFE :
      HilbertRightAngle Geo G F E :=
    hilbert_right_angle_transport
      Geo
      E F G
      G F E
      hEFG
      hGFE
      hRightEFG
      hEFG_GFE

  have hGFE_EFY :
      Geo.AngleCongruent
        G F E
        E F Y :=
    hilbert_right_angle_opposite_extension
      Geo
      G F E Y
      hGFE
      hRightGFE
      hGFY

  have hRightEFY :
      HilbertRightAngle Geo E F Y :=
    hilbert_right_angle_transport
      Geo
      G F E
      E F Y
      hGFE
      hEFY
      hRightGFE
      hGFE_EFY

  --------------------------------------------------------------------
  -- I.32 in triangle EGF, extending GF through F to Y.
  --------------------------------------------------------------------

  have hEGF :
      Not (PrimCollinear Geo E G F) := by

    intro h

    exact
      hEFG
        (PrimCollinearRotate
          Geo E G F h)

  rcases
      euclid_proposition_32_exterior
        E G F Y
        hEGF
        hGFY
    with
    ⟨U,
      hEUY,
      hGEF_EFU,
      hEGF_UFY⟩

  have hUF :
      U ≠ F := by

    intro hUF

    subst U

    have hEFYcol :
        PrimCollinear Geo E F Y :=
      (HilbertOrder.between_incidence
        E F Y hEUY).2.2.2.1

    exact hEFY hEFYcol

  have hInsideU_EFY :
      HilbertRayMeetsSegment Geo F U E Y :=
    ⟨U,
      hEUY,
      hilbert_sameRay_refl
        Geo F U hUF⟩

  --------------------------------------------------------------------
  -- The I.32 component UFY is the known half-right ECR.
  --------------------------------------------------------------------

  have hUFY_EGF :
      Geo.AngleCongruent
        U F Y
        E G F :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E G F
      U F Y
      hEGF_UFY

  have hUFY_ECR :
      Geo.AngleCongruent
        U F Y
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      U F Y
      E G F
      E C R
      hUFY_EGF
      hEGF_ECR

  have hYFU_ECR :
      Geo.AngleCongruent
        Y F U
        E C R :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      U F Y
      E C R).mp
      hUFY_ECR

  have hYFU_BCR :
      Geo.AngleCongruent
        Y F U
        B C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      Y F U
      E C R
      B C R
      hYFU_ECR
      hBisectR

  --------------------------------------------------------------------
  -- EFY and ECB are right.  Subtract equal half-right components.
  -- The remaining angle EFU is another copy of ECR.
  --------------------------------------------------------------------

  have hEFY_ECB :
      Geo.AngleCongruent
        E F Y
        E C B :=
    hilbert_all_right_angles_congruent
      Geo
      E F Y
      E C B
      hEFY
      hECB
      hRightEFY
      hRightECB

  have hEFU_ECR :
      Geo.AngleCongruent
        E F U
        E C R :=
    hilbert_angleDecomposition_angle_subtraction
      Geo
      F E Y U
      E C B R
      hEFY
      hECB
      hInsideU_EFY
      hInsideR_ECB
      hEFY_ECB
      hYFU_BCR

  have hGEF_ECR :
      Geo.AngleCongruent
        G E F
        E C R :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      G E F
      E F U
      E C R
      hGEF_EFU
      hEFU_ECR

  --------------------------------------------------------------------
  -- Thus the two base angles of triangle FGE are congruent.
  --------------------------------------------------------------------

  have hFGE_ECR :
      Geo.AngleCongruent
        F G E
        E C R :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      E G F
      E C R).mp
      hEGF_ECR

  have hFEG_ECR :
      Geo.AngleCongruent
        F E G
        E C R :=
    (Geometry.Geo.angle_congruent_reverse_first
      Geo
      G E F
      E C R).mp
      hGEF_ECR

  have hECR_FEG :
      Geo.AngleCongruent
        E C R
        F E G :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      F E G
      E C R
      hFEG_ECR

  have hFGE_FEG :
      Geo.AngleCongruent
        F G E
        F E G :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      F G E
      E C R
      F E G
      hFGE_ECR
      hECR_FEG

  have hFGE :
      Not (Collinear Geo F G E) := by

    intro h

    have hEGFcol :
        PrimCollinear Geo E G F :=
      PrimCollinearSymm
        Geo F G E h

    exact
      hEFG
        (PrimCollinearRotate
          Geo E G F hEGFcol)

  have hFG_FE :
      Geo.Congruent F G F E :=
    euclid_proposition_6
      Geo
      F G E
      hFGE
      hFGE_FEG

  have hGF_EF :
      Geo.Congruent G F E F :=
    CongruentReverseBoth
      Geo
      F G
      F E
      hFG_FE

  --------------------------------------------------------------------
  -- Final package.
  --------------------------------------------------------------------

  exact
    ⟨E, F, G, R, S,
      hACB,
      hCBD,
      hACD,
      hEBG,
      hFDG,
      hCE_AC,
      hCE_CB,
      hParCDFE,
      hCD_FE,
      hACE,
      hRightACE,
      hECB,
      hRightECB,
      hERB,
      hESA,
      hBisectR,
      hBisectS,
      hAEC_BEC,
      hAEB,
      hRightAEB,
      hEFD,
      hRightEFD,
      hDB_DG,
      hGF_EF⟩

------------------------------------------------------------------------
-- Euclid II.10 -- four Pythagoras blocks
--
-- Four source-faithful applications of Euclid I.47.
--
-- The preceding classical block provides:
--
--   CE = AC = CB,
--   DB = DG,
--   GF = EF,
--   EF = CD.
--
-- The four right triangles used by Euclid II.10 are:
--
--   C-A-E    right at C:
--       AE^2 = CA^2 + CE^2
--
--   F-E-G    right at F:
--       EG^2 = FE^2 + FG^2
--
--   E-A-G    right at E:
--       AG^2 = EA^2 + EG^2
--
--   D-A-G    right at D:
--       AG^2 = DA^2 + DG^2
--
-- This helper builds and packages these four I.47 decompositions.
-- The final scissors assembly follows below.
------------------------------------------------------------------------

theorem proposition2_10_four_pythagoras_blocks
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D) :
    exists E F G : Geo.Point,

      ------------------------------------------------------------------
      -- Classical side equalities.
      ------------------------------------------------------------------

      Geo.Congruent C A C E /\
      Geo.Congruent F E C D /\
      Geo.Congruent G F C D /\
      Geo.Congruent D B D G /\

      ------------------------------------------------------------------
      -- I.47 #1: C-A-E, right at C.
      ------------------------------------------------------------------

      (exists QAE0 QAE1 QCA0 QCA1 QCE0 QCE1 : Geo.Point,
        IsSquare Geo A E QAE1 QAE0 /\
        IsSquare Geo C A QCA0 QCA1 /\
        IsSquare Geo C E QCE1 QCE0 /\
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo A E QAE1 QAE0)
          (hilbertParallelogramTerm Geo C A QCA0 QCA1 +
           hilbertParallelogramTerm Geo C E QCE1 QCE0)) /\

      ------------------------------------------------------------------
      -- I.47 #2: F-E-G, right at F.
      ------------------------------------------------------------------

      (exists QEG0 QEG1 QFE0 QFE1 QFG0 QFG1 : Geo.Point,
        IsSquare Geo E G QEG1 QEG0 /\
        IsSquare Geo F E QFE0 QFE1 /\
        IsSquare Geo F G QFG1 QFG0 /\
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo E G QEG1 QEG0)
          (hilbertParallelogramTerm Geo F E QFE0 QFE1 +
           hilbertParallelogramTerm Geo F G QFG1 QFG0)) /\

      ------------------------------------------------------------------
      -- I.47 #3: E-A-G, right at E.
      ------------------------------------------------------------------

      (exists QAG0 QAG1 QEA0 QEA1 QEG2 QEG3 : Geo.Point,
        IsSquare Geo A G QAG1 QAG0 /\
        IsSquare Geo E A QEA0 QEA1 /\
        IsSquare Geo E G QEG3 QEG2 /\
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo A G QAG1 QAG0)
          (hilbertParallelogramTerm Geo E A QEA0 QEA1 +
           hilbertParallelogramTerm Geo E G QEG3 QEG2)) /\

      ------------------------------------------------------------------
      -- I.47 #4: D-A-G, right at D.
      ------------------------------------------------------------------

      (exists QAG2 QAG3 QDA0 QDA1 QDG0 QDG1 : Geo.Point,
        IsSquare Geo A G QAG3 QAG2 /\
        IsSquare Geo D A QDA0 QDA1 /\
        IsSquare Geo D G QDG1 QDG0 /\
        HilbertScissorsEquicomplementable Geo
          (hilbertParallelogramTerm Geo A G QAG3 QAG2)
          (hilbertParallelogramTerm Geo D A QDA0 QDA1 +
           hilbertParallelogramTerm Geo D G QDG1 QDG0)) := by

  --------------------------------------------------------------------
  -- Recover the complete classical configuration.
  --------------------------------------------------------------------

  rcases
      proposition2_10_classical_isosceles_blocks
        Geo A B C D hMidC hABD
    with
    ⟨E, F, G, R, S,
      hACB,
      hCBD,
      hACD,
      hEBG,
      hFDG,
      hCE_AC,
      hCE_CB,
      hParCDFE,
      hCD_FE,
      hACE,
      hRightACE,
      hECB,
      hRightECB,
      _hERB,
      _hESA,
      _hBisectR,
      _hBisectS,
      _hAEC_BEC,
      hAEB,
      hRightAEB,
      hEFD,
      hRightEFD,
      hDB_DG,
      hGF_EF⟩

  --------------------------------------------------------------------
  -- Normalize the side equalities needed by the scissors layer.
  --------------------------------------------------------------------

  have hAC_CE :
      Geo.Congruent A C C E :=
    hilbert_congruent_symmetry
      Geo
      C E
      A C
      hCE_AC

  have hCA_CE :
      Geo.Congruent C A C E :=
    CongruentReverseFirst
      Geo
      A C
      C E
      hAC_CE

  have hFE_CD :
      Geo.Congruent F E C D :=
    hilbert_congruent_symmetry
      Geo
      C D
      F E
      hCD_FE

  have hEF_CD :
      Geo.Congruent E F C D :=
    CongruentReverseFirst
      Geo
      F E
      C D
      hFE_CD

  have hGF_CD :
      Geo.Congruent G F C D :=
    hilbert_congruent_transitivity
      Geo
      G F
      E F
      C D
      hGF_EF
      hEF_CD

  --------------------------------------------------------------------
  -- Parallelogram nondegeneracy.
  --------------------------------------------------------------------

  have hParNC :=
    parallelogram_vertices_noncollinear
      Geo C D F E hParCDFE

  have hECD :
      Not (Collinear Geo E C D) :=
    hParNC.1

  have hCDF :
      Not (Collinear Geo C D F) :=
    hParNC.2.1

  --------------------------------------------------------------------
  -- Recover the right angle CDF from ECB.
  --------------------------------------------------------------------

  have hRayCBD :
      HilbertSameRay Geo C B D :=
    hilbert_sameRay_of_between
      Geo C B D hCBD

  have hAngleECB_ECD :
      Geo.Angle E C B =
      Geo.Angle E C D :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      C E B D
      hRayCBD

  have hReflECB :
      Geo.AngleCongruent
        E C B
        E C B :=
    Geometry.Geo.angle_congruent_reflexive
      Geo E C B

  have hECB_ECD :
      Geo.AngleCongruent
        E C B
        E C D := by

    unfold Geometry.Geo.AngleCongruent
      at hReflECB ⊢

    rw [← hAngleECB_ECD]

    exact hReflECB

  have hRightECD :
      HilbertRightAngle Geo E C D :=
    hilbert_right_angle_transport
      Geo
      E C B
      E C D
      hECB
      hECD
      hRightECB
      hECB_ECD

  have hRightCDF :
      HilbertRightAngle Geo C D F :=
    parallelogram_adjacent_right_angle
      Geo
      C D F E
      hParCDFE
      hRightECD

  --------------------------------------------------------------------
  -- Right triangle #1: C-A-E.
  --------------------------------------------------------------------

  have hCAE :
      Not (Collinear Geo C A E) := by

    intro h

    exact
      hACE
        (PrimCollinearSwap
          Geo C A E h)

  --------------------------------------------------------------------
  -- Right triangle #2: F-E-G.
  --
  -- EFD is right and D,G lie on the same ray from F.
  --------------------------------------------------------------------

  have hRayFDG :
      HilbertSameRay Geo F D G :=
    hilbert_sameRay_of_between
      Geo F D G hFDG

  have hEF :
      E ≠ F :=
    hilbert_noncollinear_ne_first
      Geo E F D hEFD

  have hRayFEE :
      HilbertSameRay Geo F E E :=
    hilbert_sameRay_refl
      Geo F E hEF

  have hEFG :
      Not (Collinear Geo E F G) :=
    hilbert_noncollinear_of_sameRays
      Geo
      E F D
      E G
      hEFD
      hRayFEE
      hRayFDG

  have hAngleEFD_EFG :
      Geo.Angle E F D =
      Geo.Angle E F G :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      F E D G
      hRayFDG

  have hReflEFD :
      Geo.AngleCongruent
        E F D
        E F D :=
    Geometry.Geo.angle_congruent_reflexive
      Geo E F D

  have hEFD_EFG :
      Geo.AngleCongruent
        E F D
        E F G := by

    unfold Geometry.Geo.AngleCongruent
      at hReflEFD ⊢

    rw [← hAngleEFD_EFG]

    exact hReflEFD

  have hRightEFG :
      HilbertRightAngle Geo E F G :=
    hilbert_right_angle_transport
      Geo
      E F D
      E F G
      hEFD
      hEFG
      hRightEFD
      hEFD_EFG

  have hFEG :
      Not (Collinear Geo F E G) := by

    intro h

    exact
      hEFG
        (PrimCollinearSwap
          Geo F E G h)

  --------------------------------------------------------------------
  -- Right triangle #3: E-A-G.
  --
  -- AEB is right and B,G lie on the same ray from E.
  --------------------------------------------------------------------

  have hRayEBG :
      HilbertSameRay Geo E B G :=
    hilbert_sameRay_of_between
      Geo E B G hEBG

  have hAE :
      A ≠ E :=
    hilbert_noncollinear_ne_first
      Geo A E B hAEB

  have hRayEAA :
      HilbertSameRay Geo E A A :=
    hilbert_sameRay_refl
      Geo E A hAE

  have hAEG :
      Not (Collinear Geo A E G) :=
    hilbert_noncollinear_of_sameRays
      Geo
      A E B
      A G
      hAEB
      hRayEAA
      hRayEBG

  have hAngleAEB_AEG :
      Geo.Angle A E B =
      Geo.Angle A E G :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      E A B G
      hRayEBG

  have hReflAEB :
      Geo.AngleCongruent
        A E B
        A E B :=
    Geometry.Geo.angle_congruent_reflexive
      Geo A E B

  have hAEB_AEG :
      Geo.AngleCongruent
        A E B
        A E G := by

    unfold Geometry.Geo.AngleCongruent
      at hReflAEB ⊢

    rw [← hAngleAEB_AEG]

    exact hReflAEB

  have hRightAEG :
      HilbertRightAngle Geo A E G :=
    hilbert_right_angle_transport
      Geo
      A E B
      A E G
      hAEB
      hAEG
      hRightAEB
      hAEB_AEG

  have hEAG :
      Not (Collinear Geo E A G) := by

    intro h

    exact
      hAEG
        (PrimCollinearSwap
          Geo E A G h)

  --------------------------------------------------------------------
  -- Right triangle #4: D-A-G.
  --
  -- First move from CDF to CDG across F-D-G.
  --------------------------------------------------------------------

  have hFDC :
      Not (Collinear Geo F D C) := by

    intro h

    exact
      hCDF
        (PrimCollinearSymm
          Geo F D C h)

  have hCDF_FDC :
      Geo.AngleCongruent
        C D F
        F D C :=
    bookZero_56_ABCequalsCBA
      Geo
      C D F
      hCDF

  have hRightFDC :
      HilbertRightAngle Geo F D C :=
    hilbert_right_angle_transport
      Geo
      C D F
      F D C
      hCDF
      hFDC
      hRightCDF
      hCDF_FDC

  have hFDC_CDG :
      Geo.AngleCongruent
        F D C
        C D G :=
    hilbert_right_angle_opposite_extension
      Geo
      F D C G
      hFDC
      hRightFDC
      hFDG

  have hCDG :
      Not (Collinear Geo C D G) := by

    intro hCDGcol

    have hFDGcol :
        PrimCollinear Geo F D G :=
      (HilbertOrder.between_incidence
        F D G hFDG).2.2.2.1

    have hDG :
        D ≠ G :=
      (HilbertOrder.between_incidence
        F D G hFDG).2.1

    have hGDF :
        PrimCollinear Geo G D F :=
      PrimCollinearSymm
        Geo F D G hFDGcol

    have hCDG_F :
        PrimCollinear Geo C D F :=
      hilbert_primCollinear_trans
        Geo
        C D G F
        hDG
        hCDGcol
        (PrimCollinearSwap
          Geo G D F hGDF)

    exact hCDF hCDG_F

  have hRightCDG :
      HilbertRightAngle Geo C D G :=
    hilbert_right_angle_transport
      Geo
      F D C
      C D G
      hFDC
      hCDG
      hRightFDC
      hFDC_CDG

  --------------------------------------------------------------------
  -- D-C-A, so DC and DA determine the same ray.
  --------------------------------------------------------------------

  have hDCA :
      Geo.Between D C A :=
    (HilbertOrder.between_incidence
      A C D hACD).2.2.2.2

  have hRayDCA :
      HilbertSameRay Geo D C A :=
    hilbert_sameRay_of_between
      Geo D C A hDCA

  have hDG :
      D ≠ G :=
    (HilbertOrder.between_incidence
      F D G hFDG).2.1

  have hRayDGG :
      HilbertSameRay Geo D G G :=
    hilbert_sameRay_refl
      Geo D G hDG.symm

  have hADG :
      Not (Collinear Geo A D G) :=
    hilbert_noncollinear_of_sameRays
      Geo
      C D G
      A G
      hCDG
      hRayDCA
      hRayDGG

  have hAngleCDG_ADG :
      Geo.Angle C D G =
      Geo.Angle A D G :=
    hilbert_angle_eq_of_sameRay_first
      Geo
      D C A G
      hRayDCA

  have hReflCDG :
      Geo.AngleCongruent
        C D G
        C D G :=
    Geometry.Geo.angle_congruent_reflexive
      Geo C D G

  have hCDG_ADG :
      Geo.AngleCongruent
        C D G
        A D G := by

    unfold Geometry.Geo.AngleCongruent
      at hReflCDG ⊢

    rw [← hAngleCDG_ADG]

    exact hReflCDG

  have hRightADG :
      HilbertRightAngle Geo A D G :=
    hilbert_right_angle_transport
      Geo
      C D G
      A D G
      hCDG
      hADG
      hRightCDG
      hCDG_ADG

  have hDAG :
      Not (Collinear Geo D A G) := by

    intro h

    exact
      hADG
        (PrimCollinearSwap
          Geo D A G h)

  --------------------------------------------------------------------
  -- I.47 #1: C-A-E.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        C A E
        hCAE
        hRightACE
    with
    ⟨QAE0, QAE1,
      QCA0, QCA1,
      QCE0, QCE1,
      hSqAE,
      hSqCA,
      hSqCE,
      hPythCAE⟩

  --------------------------------------------------------------------
  -- I.47 #2: F-E-G.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        F E G
        hFEG
        hRightEFG
    with
    ⟨QEG0, QEG1,
      QFE0, QFE1,
      QFG0, QFG1,
      hSqEG,
      hSqFE,
      hSqFG,
      hPythFEG⟩

  --------------------------------------------------------------------
  -- I.47 #3: E-A-G.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        E A G
        hEAG
        hRightAEG
    with
    ⟨QAG0, QAG1,
      QEA0, QEA1,
      QEG2, QEG3,
      hSqAG,
      hSqEA,
      hSqEG2,
      hPythEAG⟩

  --------------------------------------------------------------------
  -- I.47 #4: D-A-G.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_47
        Geo
        D A G
        hDAG
        hRightADG
    with
    ⟨QAG2, QAG3,
      QDA0, QDA1,
      QDG0, QDG1,
      hSqAG2,
      hSqDA,
      hSqDG,
      hPythDAG⟩

  --------------------------------------------------------------------
  -- Package the four decompositions exactly as returned by I.47.
  --------------------------------------------------------------------

  exact
    ⟨E, F, G,
      hCA_CE,
      hFE_CD,
      hGF_CD,
      hDB_DG,

      ⟨QAE0, QAE1,
        QCA0, QCA1,
        QCE0, QCE1,
        hSqAE,
        hSqCA,
        hSqCE,
        hPythCAE⟩,

      ⟨QEG0, QEG1,
        QFE0, QFE1,
        QFG0, QFG1,
        hSqEG,
        hSqFE,
        hSqFG,
        hPythFEG⟩,

      ⟨QAG0, QAG1,
        QEA0, QEA1,
        QEG2, QEG3,
        hSqAG,
        hSqEA,
        hSqEG2,
        hPythEAG⟩,

      ⟨QAG2, QAG3,
        QDA0, QDA1,
        QDG0, QDG1,
        hSqAG2,
        hSqDA,
        hSqDG,
        hPythDAG⟩⟩

------------------------------------------------------------------------
-- Euclid II.10 -- final scissors assembly
--
-- Final scissors assembly.
--
-- Geometry and all four uses of I.47 are already complete above.
-- This file performs only the Common-Notion / scissors bookkeeping:
--
--   AG^2 = AD^2 + DB^2,
--   AG^2 = AE^2 + EG^2,
--   AE^2 = AC^2 + AC^2,
--   EG^2 = CD^2 + CD^2.
--
-- Hence
--
--   AD^2 + DB^2 = 2 AC^2 + 2 CD^2.
------------------------------------------------------------------------

theorem euclid_proposition_2_10_oriented
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D : Geo.Point)
    (hMidC : HilbertIsMidpoint Geo C A B)
    (hABD : Geo.Between A B D) :
    exists SAD0 SAD1 SDB0 SDB1 SAC0 SAC1 SCD0 SCD1 : Geo.Point,
      IsSquare Geo A D SAD0 SAD1 /\
      IsSquare Geo D B SDB0 SDB1 /\
      IsSquare Geo A C SAC0 SAC1 /\
      IsSquare Geo C D SCD0 SCD1 /\
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
      proposition2_10_four_pythagoras_blocks
        Geo
        A B C D
        hMidC
        hABD
    with
    ⟨E, F, G,
      hCA_CE,
      hFE_CD,
      hGF_CD,
      hDB_DG,

      ⟨QAE0, QAE1,
        QCA0, QCA1,
        QCE0, QCE1,
        hSqAE,
        hSqCA,
        hSqCE,
        hPythCAE⟩,

      ⟨QEG0, QEG1,
        QFE0, QFE1,
        QFG0, QFG1,
        hSqEG,
        hSqFE,
        hSqFG,
        hPythFEG⟩,

      ⟨QAG0, QAG1,
        QEA0, QEA1,
        QEG2, QEG3,
        hSqAG,
        hSqEA,
        hSqEG2,
        hPythEAG⟩,

      ⟨QAG2, QAG3,
        QDA0, QDA1,
        QDG0, QDG1,
        hSqAG2,
        hSqDA,
        hSqDG,
        hPythDAG⟩⟩

  --------------------------------------------------------------------
  -- Construct the four actual target squares by I.46.
  --------------------------------------------------------------------

  have hABDdata :=
    HilbertOrder.between_incidence
      A B D hABD

  have hAD :
      A ≠ D :=
    hABDdata.2.2.1

  have hDB :
      D ≠ B :=
    hABDdata.2.1.symm

  have hAC :
      A ≠ C :=
    (HilbertOrder.between_incidence
      A C B hMidC.1).1

  have hACD :
      Geo.Between A C D :=
    (hilbert_between_inner_trans
      Geo A C B D hMidC.1 hABD).2

  have hCD :
      C ≠ D :=
    (HilbertOrder.between_incidence
      A C D hACD).2.1

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
  -- Abbreviations for the four target square terms.
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
  -- I.47 on D-A-G:
  --
  --     AG^2 = DA^2 + DG^2.
  --
  -- Transport DA -> AD and DG -> DB.
  --------------------------------------------------------------------

  have hDA_AD :
      Geo.Congruent D A A D :=
    CongruentReverseFirst
      Geo
      A D
      A D
      (hilbert_congruent_reflexive
        Geo A D)

  have hDG_DB :
      Geo.Congruent D G D B :=
    hilbert_congruent_symmetry
      Geo
      D B
      D G
      hDB_DG

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

  have hSqDG_to_DB :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D G QDG1 QDG0)
        tDB :=
    hilbert_square_transport
      Geo
      D G QDG1 QDG0
      D B SDB0 SDB1
      hSqDG
      hSqDB
      hDG_DB

  have hDA_DG_to_LHS :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo D A QDA0 QDA1 +
         hilbertParallelogramTerm Geo D G QDG1 QDG0)
        (tAD + tDB) :=
    i47_aux_equicomplementable_add
      Geo
      hSqDA_to_AD
      hSqDG_to_DB

  have hAG2_to_LHS :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A G QAG3 QAG2)
        (tAD + tDB) :=
    equicomplementable_trans
      Geo
      hPythDAG
      hDA_DG_to_LHS

  --------------------------------------------------------------------
  -- STEP B.
  --
  -- Move from the D-A-G square on AG to the E-A-G square on AG.
  --------------------------------------------------------------------

  have hAG_refl :
      Geo.Congruent A G A G :=
    hilbert_congruent_reflexive
      Geo A G

  have hSqAG2_to_AG :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A G QAG3 QAG2)
        (hilbertParallelogramTerm Geo A G QAG1 QAG0) :=
    hilbert_square_transport
      Geo
      A G QAG3 QAG2
      A G QAG1 QAG0
      hSqAG2
      hSqAG
      hAG_refl

  have hLHS_to_AG2 :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        (hilbertParallelogramTerm Geo A G QAG3 QAG2) :=
    equicomplementable_symm
      Geo
      hAG2_to_LHS

  have hLHS_to_AG :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        (hilbertParallelogramTerm Geo A G QAG1 QAG0) :=
    equicomplementable_trans
      Geo
      hLHS_to_AG2
      hSqAG2_to_AG

  have hLHS_to_EA_EG :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        (hilbertParallelogramTerm Geo E A QEA0 QEA1 +
         hilbertParallelogramTerm Geo E G QEG3 QEG2) :=
    equicomplementable_trans
      Geo
      hLHS_to_AG
      hPythEAG

  --------------------------------------------------------------------
  -- STEP C.
  --
  -- Identify the E-A-G leg squares with the hypotenuse squares from
  -- C-A-E and F-E-G.
  --------------------------------------------------------------------

  have hEA_AE :
      Geo.Congruent E A A E :=
    CongruentReverseFirst
      Geo
      A E
      A E
      (hilbert_congruent_reflexive
        Geo A E)

  have hEG_refl :
      Geo.Congruent E G E G :=
    hilbert_congruent_reflexive
      Geo E G

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

  have hSqEG2_to_EG :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E G QEG3 QEG2)
        (hilbertParallelogramTerm Geo E G QEG1 QEG0) :=
    hilbert_square_transport
      Geo
      E G QEG3 QEG2
      E G QEG1 QEG0
      hSqEG2
      hSqEG
      hEG_refl

  have hEA_EG_to_AE_EG :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo E A QEA0 QEA1 +
         hilbertParallelogramTerm Geo E G QEG3 QEG2)
        (hilbertParallelogramTerm Geo A E QAE1 QAE0 +
         hilbertParallelogramTerm Geo E G QEG1 QEG0) :=
    i47_aux_equicomplementable_add
      Geo
      hSqEA_to_AE
      hSqEG2_to_EG

  have hLHS_to_AE_EG :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        (hilbertParallelogramTerm Geo A E QAE1 QAE0 +
         hilbertParallelogramTerm Geo E G QEG1 QEG0) :=
    equicomplementable_trans
      Geo
      hLHS_to_EA_EG
      hEA_EG_to_AE_EG

  --------------------------------------------------------------------
  -- STEP D.
  --
  -- Apply I.47 on C-A-E and F-E-G simultaneously:
  --
  --     AE^2 + EG^2
  --       =
  --     (CA^2 + CE^2) + (FE^2 + FG^2).
  --------------------------------------------------------------------

  have hAE_EG_to_four :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A E QAE1 QAE0 +
         hilbertParallelogramTerm Geo E G QEG1 QEG0)
        ((hilbertParallelogramTerm Geo C A QCA0 QCA1 +
          hilbertParallelogramTerm Geo C E QCE1 QCE0) +
         (hilbertParallelogramTerm Geo F E QFE0 QFE1 +
          hilbertParallelogramTerm Geo F G QFG1 QFG0)) :=
    i47_aux_equicomplementable_add
      Geo
      hPythCAE
      hPythFEG

  have hLHS_to_four :
      HilbertScissorsEquicomplementable Geo
        (tAD + tDB)
        ((hilbertParallelogramTerm Geo C A QCA0 QCA1 +
          hilbertParallelogramTerm Geo C E QCE1 QCE0) +
         (hilbertParallelogramTerm Geo F E QFE0 QFE1 +
          hilbertParallelogramTerm Geo F G QFG1 QFG0)) :=
    equicomplementable_trans
      Geo
      hLHS_to_AE_EG
      hAE_EG_to_four

  --------------------------------------------------------------------
  -- STEP E.
  --
  -- Transport CA and CE to AC.
  --------------------------------------------------------------------

  have hCA_AC :
      Geo.Congruent C A A C :=
    CongruentReverseFirst
      Geo
      A C
      A C
      (hilbert_congruent_reflexive
        Geo A C)

  have hCE_CA :
      Geo.Congruent C E C A :=
    hilbert_congruent_symmetry
      Geo
      C A
      C E
      hCA_CE

  have hCE_AC :
      Geo.Congruent C E A C :=
    hilbert_congruent_transitivity
      Geo
      C E
      C A
      A C
      hCE_CA
      hCA_AC

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

  have hCA_CE_to_2AC :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo C A QCA0 QCA1 +
         hilbertParallelogramTerm Geo C E QCE1 QCE0)
        (tAC + tAC) :=
    i47_aux_equicomplementable_add
      Geo
      hSqCA_to_AC
      hSqCE_to_AC

  --------------------------------------------------------------------
  -- STEP F.
  --
  -- Transport FE and FG to CD.
  --------------------------------------------------------------------

  have hFG_CD :
      Geo.Congruent F G C D :=
    CongruentReverseFirst
      Geo
      G F
      C D
      hGF_CD

  have hSqFE_to_CD :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo F E QFE0 QFE1)
        tCD :=
    hilbert_square_transport
      Geo
      F E QFE0 QFE1
      C D SCD0 SCD1
      hSqFE
      hSqCD
      hFE_CD

  have hSqFG_to_CD :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo F G QFG1 QFG0)
        tCD :=
    hilbert_square_transport
      Geo
      F G QFG1 QFG0
      C D SCD0 SCD1
      hSqFG
      hSqCD
      hFG_CD

  have hFE_FG_to_2CD :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo F E QFE0 QFE1 +
         hilbertParallelogramTerm Geo F G QFG1 QFG0)
        (tCD + tCD) :=
    i47_aux_equicomplementable_add
      Geo
      hSqFE_to_CD
      hSqFG_to_CD

  --------------------------------------------------------------------
  -- STEP G.
  --
  -- Assemble the two doubled target squares.
  --------------------------------------------------------------------

  have hFour_to_RHS :
      HilbertScissorsEquicomplementable Geo
        ((hilbertParallelogramTerm Geo C A QCA0 QCA1 +
          hilbertParallelogramTerm Geo C E QCE1 QCE0) +
         (hilbertParallelogramTerm Geo F E QFE0 QFE1 +
          hilbertParallelogramTerm Geo F G QFG1 QFG0))
        ((tAC + tAC) + (tCD + tCD)) :=
    i47_aux_equicomplementable_add
      Geo
      hCA_CE_to_2AC
      hFE_FG_to_2CD

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

end Geometry

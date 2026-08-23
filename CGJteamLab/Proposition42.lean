import CGJteamLab.Proposition38
import CGJteamLab.Proposition41

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.42
--
-- To construct, in a given rectilinear angle, a parallelogram equal
-- to a given triangle.
--
-- Proof architecture used in this file:
--
--   1. Bisect BC at E.
--   2. Prove ABE ~ AEC from I.38 by comparing both triangles with one
--      auxiliary remote triangle DUV on an equal base.
--   3. Copy the prescribed angle at E on the side of EC containing A,
--      and draw through A the parallel to EC.
--   4. Prove that the copied angle ray meets that parallel.  The
--      Euclidean input is the transitivity/uniqueness theory of
--      parallels already available in HilbertInterface.
--   5. Choose the intersection F on the correct ray, complete EFGC to
--      a parallelogram, and identify its upper carrier with the line
--      through A.  The conclusion is Collinear F A G; this includes
--      the legitimate special case F = A.
--   6. Apply I.41 on the genuine side FG and use I.37 along the common
--      upper carrier to compare triangle GEC with triangle AEC.
--   7. Chain the scissors equalities to obtain ABC ~ FECG.
--
-- All construction steps are derived from existing project infrastructure.
------------------------------------------------------------------------

/--
The midpoint E of BC divides triangle ABC into two
equicomplementable triangles ABE and AEC.

The present I.38 interface expects distinct apex points, so both halves
are compared with the same auxiliary remote triangle DUV on an equal
base.  Transitivity then gives ABE ~ AEC without any additional area
assumption.
-/
theorem i42_median_bisects_area
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C E : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hE : HilbertIsMidpoint Geo E B C) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B E)
      (hilbertScissorsTriangle Geo A E C) := by

  --------------------------------------------------------------------
  -- Midpoint data: B-E-C and BE ~= EC.
  --------------------------------------------------------------------

  have hBEC :
      Geo.Between B E C :=
    hE.1

  have hBECData :=
    HilbertOrder.between_incidence
      B E C hBEC

  have hBE :
      Not (B = E) :=
    hBECData.1

  have hEC :
      Not (E = C) :=
    hBECData.2.1

  have hBC :
      Not (B = C) :=
    hBECData.2.2.1

  have hBECcol :
      Collinear Geo B E C :=
    hBECData.2.2.2.1

  have hBCA :
      Not (Collinear Geo B C A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle
          Geo C A B
          (PrimCollinearCycle
            Geo B C A h))

  --------------------------------------------------------------------
  -- Choose D on the parallel through A to the base line BC.
  --------------------------------------------------------------------

  rcases
      hilbert_parallel_through_point_exists
        Geo B C A hBC hBCA
    with
    ⟨D, hAD, hBC_AD⟩

  --------------------------------------------------------------------
  -- Transport BC || AD to BE || AD.
  --------------------------------------------------------------------

  have hBE_AD :
      Geo.Parallel B E A D :=
    collinear_parallel_trans
      Geo
      B E C
      A D
      hBE
      hBECcol
      hBC_AD

  have hAD_BE :
      Geo.Parallel A D B E :=
    ParallelSymmetry
      Geo B E A D hBE_AD

  --------------------------------------------------------------------
  -- Transport the same parallelism to EC || AD.
  --------------------------------------------------------------------

  have hEB_AD :
      Geo.Parallel E B A D :=
    ParallelSwapFirstLine
      Geo B E A D hBE_AD

  have hECB :
      Collinear Geo E C B :=
    PrimCollinearCycle
      Geo B E C hBECcol

  have hEC_AD :
      Geo.Parallel E C A D :=
    collinear_parallel_trans
      Geo
      E C B
      A D
      hEC
      hECB
      hEB_AD

  have hAD_EC :
      Geo.Parallel A D E C :=
    ParallelSymmetry
      Geo E C A D hEC_AD

  --------------------------------------------------------------------
  -- Construct a remote base UV beyond C:
  --
  --     B - E - C - U - V
  --
  -- with UV ~= BE ~= EC.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        E C hEC
    with
    ⟨U, hECU⟩

  have hECUData :=
    HilbertOrder.between_incidence
      E C U hECU

  have hCU :
      Not (C = U) :=
    hECUData.2.1

  rcases
      HilbertOrder.between_extension
        C U hCU
    with
    ⟨R, hCUR⟩

  have hUR :
      Not (U = R) :=
    (HilbertOrder.between_incidence
      C U R hCUR).2.1

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        B E
        U R
        hUR
    with
    ⟨V, hRayURV, hUV_BE⟩

  --------------------------------------------------------------------
  -- Since V lies on ray UR and C-U-R, we have C-U-V.
  --------------------------------------------------------------------

  have hRayUCC :
      HilbertSameRay Geo U C C :=
    hilbert_sameRay_refl
      Geo U C hCU

  have hCUV :
      Geo.Between C U V :=
    hilbert_between_transport_sameRays
      Geo
      C U R
      C V
      hCUR
      hRayUCC
      hRayURV

  --------------------------------------------------------------------
  -- Recover the two order configurations required by our I.38.
  --------------------------------------------------------------------

  have hBEU :
      Geo.Between B E U :=
    (hilbert_between_outer_trans
      Geo B E C U
      hBEC hECU).2

  have hEUV :
      Geo.Between E U V :=
    (hilbert_between_outer_trans
      Geo E C U V
      hECU hCUV).1

  --------------------------------------------------------------------
  -- UV ~= BE and hence UV ~= EC.
  --------------------------------------------------------------------

  have hBE_UV :
      Geo.Congruent B E U V :=
    hilbert_congruent_symmetry
      Geo U V B E hUV_BE

  have hEC_BE :
      Geo.Congruent E C B E :=
    hilbert_congruent_symmetry
      Geo B E E C hE.2

  have hEC_UV :
      Geo.Congruent E C U V :=
    hilbert_congruent_transitivity
      Geo
      E C
      B E
      U V
      hEC_BE
      hBE_UV

  --------------------------------------------------------------------
  -- I.38 twice, with the SAME remote triangle DUV.
  --
  --     ABE ~ DUV
  --     AEC ~ DUV
  --------------------------------------------------------------------

  have hFirst :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B E)
        (hilbertScissorsTriangle Geo D U V) :=
    euclid_proposition_38
      Geo
      A B E
      D U V
      hAD_BE
      hBEU
      hEUV
      hBE_UV

  have hSecond :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A E C)
        (hilbertScissorsTriangle Geo D U V) :=
    euclid_proposition_38
      Geo
      A E C
      D U V
      hAD_EC
      hECU
      hCUV
      hEC_UV

  --------------------------------------------------------------------
  -- Therefore ABE and AEC are equicomplementable.
  --------------------------------------------------------------------

  exact
    equicomplementable_trans
      Geo
      hFirst
      (equicomplementable_symm
        Geo hSecond)

/--
Initial data for the I.42 construction: copy angle XYZ at E with first
arm EC on the side containing A, and construct the parallel through A
to EC.
-/
theorem i42_angle_parallel_setup
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A E C X Y Z : Geo.Point)
    (hAEC : Not (Collinear Geo A E C))
    (hXYZ : Not (Collinear Geo X Y Z)) :
    ∃ base : Geo.Line,
      ∃ R Q : Geo.Point,
        HilbertIncidence.OnLine C base ∧
        HilbertIncidence.OnLine E base ∧
        HilbertSameSide Geo R A base ∧
        Geo.AngleCongruent X Y Z C E R ∧
        Geo.Parallel E C A Q := by

  --------------------------------------------------------------------
  -- Base EC.
  --------------------------------------------------------------------

  have hCEA :
      Not (Collinear Geo C E A) := by
    intro h
    exact
      hAEC
        (PrimCollinearSymm
          Geo C E A h)

  have hCE :
      Not (C = E) :=
    hilbert_noncollinear_ne_first
      Geo C E A hCEA

  have hEC :
      Not (E = C) := by
    intro h
    exact hCE h.symm

  rcases
      HilbertPlaneIncidence.line_through
        C E hCE
    with
    ⟨base, hCbase, hEbase⟩

  --------------------------------------------------------------------
  -- A is off the base EC.
  --------------------------------------------------------------------

  have hAoff :
      Not (HilbertIncidence.OnLine A base) := by
    intro hAbase
    exact
      hAEC
        ⟨base,
          hAbase,
          hEbase,
          hCbase⟩

  --------------------------------------------------------------------
  -- Copy angle XYZ at E, with first arm EC,
  -- on the side of EC containing A.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        X Y Z
        C E A
        hXYZ
        hCE
        base
        hCbase
        hEbase
        hAoff
    with
    ⟨R, hRASame, hAngleR, _⟩

  --------------------------------------------------------------------
  -- Parallel to EC through A.
  --------------------------------------------------------------------

  have hECA :
      Not (Collinear Geo E C A) := by
    intro h
    exact
      hAEC
        (PrimCollinearCycle
          Geo C A E
          (PrimCollinearCycle
            Geo E C A h))

  rcases
      hilbert_parallel_through_point_exists
        Geo E C A hEC hECA
    with
    ⟨Q, _hAQ, hEC_AQ⟩

  exact
    ⟨base,
      R,
      Q,
      hCbase,
      hEbase,
      hRASame,
      hAngleR,
      hEC_AQ⟩

/--
The carrier of the copied angle ray ER meets the parallel AQ through A.
If the two carriers were disjoint, ER and EC would both be parallel to
AQ; Euclidean parallel transitivity would then force ER || EC,
contradicting their common point E.
-/
theorem i42_angle_parallel_intersection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A E C X Y Z : Geo.Point)
    (hAEC : Not (Collinear Geo A E C))
    (hXYZ : Not (Collinear Geo X Y Z)) :
    ∃ base : Geo.Line,
      ∃ R Q F : Geo.Point,
        HilbertIncidence.OnLine C base ∧
        HilbertIncidence.OnLine E base ∧
        HilbertSameSide Geo R A base ∧
        Geo.AngleCongruent X Y Z C E R ∧
        Geo.Parallel E C A Q ∧
        Collinear Geo E R F ∧
        Collinear Geo A F Q := by

  rcases
      i42_angle_parallel_setup
        Geo A E C X Y Z
        hAEC hXYZ
    with
    ⟨base,
      R,
      Q,
      hCbase,
      hEbase,
      hRASame,
      hAngleR,
      hEC_AQ⟩

  --------------------------------------------------------------------
  -- ER is a genuine line.
  --------------------------------------------------------------------

  have hER :
      Not (E = R) := by
    intro h
    subst R
    exact hRASame.1 hEbase

  rcases
      HilbertPlaneIncidence.line_through
        E R hER
    with
    ⟨rayLine, hEray, hRray⟩

  --------------------------------------------------------------------
  -- AQ is the parallel through A.
  --------------------------------------------------------------------

  have hAQ :
      Not (A = Q) :=
    hEC_AQ.2.1

  rcases
      HilbertPlaneIncidence.line_through
        A Q hAQ
    with
    ⟨topLine, hAtop, hQtop⟩

  --------------------------------------------------------------------
  -- ER and AQ must meet.
  --
  -- Otherwise ER || AQ.  Since EC || AQ as well, either ER and EC
  -- have the same carrier, contradicting R being off EC, or the
  -- Euclidean parallel-transitivity theorem gives ER || EC,
  -- contradicting their common point E.
  --------------------------------------------------------------------

  have hMeet :
      HilbertLinesMeet Geo rayLine topLine := by

    by_contra hDisjoint

    have hER_AQ :
        Geo.Parallel E R A Q :=
      intersection_test_parallel_of_lines_disjoint
        Geo
        E R A Q
        rayLine topLine
        hER hAQ
        hEray hRray
        hAtop hQtop
        hDisjoint

    have hDistinct :
        Geo.PointLine E R ≠
        Geo.PointLine E C := by

      intro hSame

      have hR_ER :
          R ∈ Geo.PointLine E R :=
        intersection_test_right_mem
          Geo E R

      have hR_EC :
          R ∈ Geo.PointLine E C := by
        rw [← hSame]
        exact hR_ER

      have hRbase :
          HilbertIncidence.OnLine R base :=
        (hilbert_mem_pointLine_iff_onLine
          Geo
          E C R
          base
          hEC_AQ.1
          hEbase
          hCbase).mp hR_EC

      exact hRASame.1 hRbase

    have hER_EC :
        Geo.Parallel E R E C :=
      hilbert_parallel_transitive_distinct
        Geo
        E R
        E C
        A Q
        hER_AQ
        hEC_AQ
        hDistinct

    exact
      (intersection_test_not_parallel_of_common_point
        Geo
        E R
        E C
        E
        (intersection_test_left_mem Geo E R)
        (intersection_test_left_mem Geo E C))
        hER_EC

  --------------------------------------------------------------------
  -- Choose the intersection F.
  --------------------------------------------------------------------

  rcases hMeet with
    ⟨F, hFray, hFtop⟩

  have hERF :
      Collinear Geo E R F :=
    ⟨rayLine,
      hEray,
      hRray,
      hFray⟩

  have hAFQ :
      Collinear Geo A F Q :=
    ⟨topLine,
      hAtop,
      hFtop,
      hQtop⟩

  exact
    ⟨base,
      R,
      Q,
      F,
      hCbase,
      hEbase,
      hRASame,
      hAngleR,
      hEC_AQ,
      hERF,
      hAFQ⟩

/--
Orient the intersection point F onto the copied ray ER.  The side data
from angle construction and the parallel carrier show that R and F lie
on the same side of EC, hence on the same ray from E.  The copied angle
is therefore transferred from CER to CEF (equivalently FEC).

The proof explicitly permits the special case F = A.
-/
theorem i42_angle_parallel_oriented_intersection
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A E C X Y Z : Geo.Point)
    (hAEC : Not (Collinear Geo A E C))
    (hXYZ : Not (Collinear Geo X Y Z)) :
    ∃ base : Geo.Line,
      ∃ R Q F : Geo.Point,
        HilbertIncidence.OnLine C base ∧
        HilbertIncidence.OnLine E base ∧
        Geo.Parallel E C A Q ∧
        Collinear Geo A F Q ∧
        HilbertSameRay Geo E R F ∧
        Geo.AngleCongruent F E C X Y Z := by

  rcases
      i42_angle_parallel_intersection
        Geo A E C X Y Z
        hAEC hXYZ
    with
    ⟨base,
      R,
      Q,
      F,
      hCbase,
      hEbase,
      hRASame,
      hAngleR,
      hEC_AQ,
      hERF,
      hAFQ⟩

  --------------------------------------------------------------------
  -- A and F are on the same side of EC.
  --
  -- If F = A this is reflexivity.
  -- Otherwise AF is the same carrier as AQ, hence AF || EC.
  --------------------------------------------------------------------

  have hAFSame :
      HilbertSameSide Geo A F base := by

    by_cases hFA : F = A

    · subst F

      exact
        hilbert_sameSide_refl
          Geo A base hRASame.2.1

    · have hAF :
          A ≠ F := by
        intro h
        exact hFA h.symm

      have hAQ_EC :
          Geo.Parallel A Q E C :=
        ParallelSymmetry
          Geo E C A Q hEC_AQ

      have hAF_EC :
          Geo.Parallel A F E C :=
        collinear_parallel_trans
          Geo
          A F Q
          E C
          hAF
          hAFQ
          hAQ_EC

      rcases
          parallel_endpoints_sameSide
            Geo A F E C hAF_EC
        with
        ⟨base', hEbase', hCbase', hAFSame'⟩

      have hBaseEq :
          base = base' :=
        HilbertPlaneIncidence.line_unique
          E C
          hEC_AQ.1
          base base'
          hEbase hCbase
          hEbase' hCbase'

      rw [hBaseEq]

      exact hAFSame'

  --------------------------------------------------------------------
  -- R and A are on the same side by angle construction,
  -- and A and F are on the same side by the preceding step.
  --------------------------------------------------------------------

  have hRFSame :
      HilbertSameSide Geo R F base :=
    hilbert_sameSide_trans
      Geo R A F base
      hRASame
      hAFSame

  --------------------------------------------------------------------
  -- R and F therefore lie on the same ray from E.
  --
  -- They are collinear with E.  They cannot lie on opposite rays,
  -- since then E would lie between R and F and segment RF would
  -- meet the base EC.
  --------------------------------------------------------------------

  have hRE :
      R ≠ E := by
    intro h
    subst R
    exact hRFSame.1 hEbase

  have hFE :
      F ≠ E := by
    intro h
    subst F
    exact hRFSame.2.1 hEbase

  have hNotBetween :
      Not (Geo.Between R E F) := by

    intro hREF

    have hOpposite :
        HilbertOppositeSide Geo R F base :=
      ⟨hRFSame.1,
       hRFSame.2.1,
       ⟨E, hREF, hEbase⟩⟩

    exact
      (hilbert_oppositeSide_not_sameSide
        Geo R F base hOpposite)
        hRFSame

  have hRay :
      HilbertSameRay Geo E R F :=
    ⟨hRE,
     hFE,
     hERF,
     hNotBetween⟩

  --------------------------------------------------------------------
  -- Move the copied angle from the auxiliary ray ER to EF.
  --------------------------------------------------------------------

  have hAtE :
      Geo.Angle C E R =
      Geo.Angle C E F :=
    hilbert_angle_eq_of_sameRay_second
      Geo E C R F hRay

  have hAngleF :
      Geo.AngleCongruent X Y Z C E F := by

    unfold Geometry.Geo.AngleCongruent
      at hAngleR ⊢

    rw [← hAtE]

    exact hAngleR

  --------------------------------------------------------------------
  -- Put the angle in the orientation required by I.42:
  --
  --     angle FEC ~= angle XYZ.
  --------------------------------------------------------------------

  have hAngleSymm :
      Geo.AngleCongruent C E F X Y Z :=
    Geometry.Geo.angle_congruent_symmetry
      Geo X Y Z C E F hAngleF

  have hAngleWanted :
      Geo.AngleCongruent F E C X Y Z :=
    (Geo.angle_congruent_reverse_first
      C E F X Y Z).mp hAngleSymm

  exact
    ⟨base,
      R,
      Q,
      F,
      hCbase,
      hEbase,
      hEC_AQ,
      hAFQ,
      hRay,
      hAngleWanted⟩


/--
Construct the required parallelogram FECG on base EC.  The prescribed
angle is FEC ~= XYZ, and F, A, G lie on one carrier parallel to EC.

The collinearity conclusion is deliberately used instead of a strict
statement Parallel F A E C, because Euclid's construction may have
F = A.
-/
theorem i42_construct_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A E C X Y Z : Geo.Point)
    (hAEC : Not (Collinear Geo A E C))
    (hXYZ : Not (Collinear Geo X Y Z)) :
    ∃ F G : Geo.Point,
      IsParallelogram Geo F E C G ∧
      Geo.AngleCongruent F E C X Y Z ∧
      Collinear Geo F A G := by

  --------------------------------------------------------------------
  -- Construct the prescribed angle at E and intersect its ray with
  -- the parallel through A to EC.
  --------------------------------------------------------------------

  rcases
      i42_angle_parallel_oriented_intersection
        Geo A E C X Y Z
        hAEC hXYZ
    with
    ⟨base,
      R,
      Q,
      F,
      hCbase,
      hEbase,
      hEC_AQ,
      hAFQ,
      hRay,
      hAngle⟩

  --------------------------------------------------------------------
  -- Use the carrier AQ explicitly.
  --------------------------------------------------------------------

  have hAQ :
      A ≠ Q :=
    hEC_AQ.2.1

  rcases hAFQ with
    ⟨top, hAtop, hFtop, hQtop⟩

  have hF_AQ :
      F ∈ Geo.PointLine A Q :=
    (hilbert_mem_pointLine_iff_onLine
      Geo A Q F top
      hAQ
      hAtop
      hQtop).mpr hFtop

  --------------------------------------------------------------------
  -- F is not on the base EC, since AQ || EC.
  --------------------------------------------------------------------

  have hFoff :
      Not (HilbertIncidence.OnLine F base) := by

    intro hFbase

    have hF_EC :
        F ∈ Geo.PointLine E C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo E C F base
        hEC_AQ.1
        hEbase
        hCbase).mpr hFbase

    exact
      Set.disjoint_left.mp
        hEC_AQ.2.2
        hF_EC
        hF_AQ

  --------------------------------------------------------------------
  -- Hence E,F,C are noncollinear.
  --------------------------------------------------------------------

  have hECF :
      Not (Collinear Geo E C F) :=
    hilbert_not_collinear_of_off_line
      Geo
      E C F
      base
      hEC_AQ.1
      hEbase
      hCbase
      hFoff

  have hEFC :
      Not (Collinear Geo E F C) := by
    intro h
    exact
      hECF
        (PrimCollinearRotate
          Geo E F C h)

  --------------------------------------------------------------------
  -- Complete E-F-?-C to the parallelogram EFGC.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo E F C hEFC
    with
    ⟨G, hEFGC⟩

  --------------------------------------------------------------------
  -- Reverse its orientation:
  --
  --     E F G C   ->   F E C G.
  --------------------------------------------------------------------

  have hFECG :
      IsParallelogram Geo F E C G :=
    ParallelogramReverse
      Geo E F G C hEFGC

  --------------------------------------------------------------------
  -- The upper side GF and the constructed carrier AQ are both
  -- parallel to EC.
  --------------------------------------------------------------------

  have hGF_EC :
      Geo.Parallel G F E C :=
    ParallelSymmetry
      Geo E C G F hFECG.2

  have hAQ_EC :
      Geo.Parallel A Q E C :=
    ParallelSymmetry
      Geo E C A Q hEC_AQ

  --------------------------------------------------------------------
  -- Their carriers must coincide.
  --
  -- If they were distinct, transitivity of distinct parallels would
  -- give GF || AQ.  But they share F.
  --------------------------------------------------------------------

  have hGF_AQ :
      Geo.PointLine G F =
      Geo.PointLine A Q := by

    by_contra hDistinct

    have hParallel :
        Geo.Parallel G F A Q :=
      hilbert_parallel_transitive_distinct
        Geo
        G F
        A Q
        E C
        hGF_EC
        hAQ_EC
        hDistinct

    exact
      (intersection_test_not_parallel_of_common_point
        Geo
        G F
        A Q
        F
        (intersection_test_right_mem
          Geo G F)
        hF_AQ)
        hParallel

  --------------------------------------------------------------------
  -- Therefore G also lies on AQ.
  --------------------------------------------------------------------

  have hG_GF :
      G ∈ Geo.PointLine G F :=
    intersection_test_left_mem
      Geo G F

  have hG_AQ :
      G ∈ Geo.PointLine A Q := by
    rw [← hGF_AQ]
    exact hG_GF

  have hGtop :
      HilbertIncidence.OnLine G top :=
    (hilbert_mem_pointLine_iff_onLine
      Geo A Q G top
      hAQ
      hAtop
      hQtop).mp hG_AQ

  --------------------------------------------------------------------
  -- Thus F, A, G lie on the upper carrier.
  --------------------------------------------------------------------

  have hFAG :
      Collinear Geo F A G :=
    ⟨top,
      hFtop,
      hAtop,
      hGtop⟩

  exact
    ⟨F,
      G,
      hFECG,
      hAngle,
      hFAG⟩

/--
Carrier form of Euclid I.41 used by I.42.

For a parallelogram FECG whose upper side contains A, first apply I.41
with the genuine apex G, so the strict parallel FG || EC is available.
Then I.37 transports triangle GEC to triangle AEC along the same upper
carrier.  This avoids imposing the false extra requirement F != A.
-/
theorem i42_parallelogram_double_triangle_on_carrier
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (F E C G A : Geo.Point)
    (hParallelogram : IsParallelogram Geo F E C G)
    (hFAG : Collinear Geo F A G) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo F E C G)
      (hilbertScissorsTriangle Geo A E C +
       hilbertScissorsTriangle Geo A E C) := by

  --------------------------------------------------------------------
  -- The upper side FG of the parallelogram is parallel to EC.
  --------------------------------------------------------------------

  have hGF_EC :
      Geo.Parallel G F E C :=
    ParallelSymmetry
      Geo E C G F hParallelogram.2

  have hFG_EC :
      Geo.Parallel F G E C :=
    ParallelSwapFirstLine
      Geo G F E C hGF_EC

  --------------------------------------------------------------------
  -- Apply I.41 first with G itself as the apex.
  --
  -- This is always strict: FG is a genuine side of the
  -- parallelogram.
  --------------------------------------------------------------------

  have hParDoubleG :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo F E C G)
        (hilbertScissorsTriangle Geo G E C +
         hilbertScissorsTriangle Geo G E C) :=
    euclid_proposition_41
      Geo
      F E C G G
      hParallelogram
      hFG_EC

  --------------------------------------------------------------------
  -- Triangle GEC has the same content as AEC because A lies on
  -- the carrier FG.
  --
  -- If G = A, this is reflexivity.
  -- Otherwise GA is a genuine line on the same carrier as GF,
  -- hence GA || EC and I.37 applies.
  --------------------------------------------------------------------

  have hGEC_AEC :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo G E C)
        (hilbertScissorsTriangle Geo A E C) := by

    by_cases hGAeq : G = A

    · subst G

      exact
        equicomplementable_refl
          Geo
          (hilbertScissorsTriangle Geo A E C)

    · have hGA :
          Not (G = A) :=
        hGAeq

      have hGAF :
          Collinear Geo G A F :=
        PrimCollinearSymm
          Geo F A G hFAG

      have hGA_EC :
          Geo.Parallel G A E C :=
        collinear_parallel_trans
          Geo
          G A F
          E C
          hGA
          hGAF
          hGF_EC

      exact
        euclid_proposition_37
          Geo
          G E C A
          hGA_EC

  --------------------------------------------------------------------
  -- Double the equality GEC ~ AEC.
  --------------------------------------------------------------------

  have hDouble :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo G E C +
         hilbertScissorsTriangle Geo G E C)
        (hilbertScissorsTriangle Geo A E C +
         hilbertScissorsTriangle Geo A E C) :=
    equicomplementable_add
      Geo
      hGEC_AEC
      hGEC_AEC

  exact
    equicomplementable_trans
      Geo
      hParDoubleG
      hDouble

/--
Euclid I.42.

To construct, in a given rectilinear angle `XYZ`, a parallelogram
equal to a given triangle `ABC`.
-/
theorem euclid_proposition_42
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C X Y Z : Geo.Point)
    (hABC : Not (Collinear Geo A B C))
    (hXYZ : Not (Collinear Geo X Y Z)) :
    ∃ E F G : Geo.Point,
      IsParallelogram Geo F E C G ∧
      Geo.AngleCongruent F E C X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo F E C G) := by

  --------------------------------------------------------------------
  -- B != C, and the carrier line of BC.
  --------------------------------------------------------------------

  have hBCA :
      Not (Collinear Geo B C A) := by
    intro h
    exact
      hABC
        (PrimCollinearCycle Geo C A B
          (PrimCollinearCycle Geo B C A h))

  have hBC :
      Not (B = C) :=
    hilbert_noncollinear_ne_first Geo B C A hBCA

  rcases
      HilbertPlaneIncidence.line_through B C hBC
    with
    ⟨lineBC, hBlineBC, hClineBC⟩

  have hAoffBC :
      Not (HilbertIncidence.OnLine A lineBC) := by
    intro hAonBC
    exact hABC ⟨lineBC, hAonBC, hBlineBC, hClineBC⟩

  --------------------------------------------------------------------
  -- E := midpoint of BC.
  --------------------------------------------------------------------

  rcases
      HilbertMidpointExists Geo B C hBC
    with
    ⟨E, hE⟩

  have hBEC :
      Geo.Between B E C :=
    hE.1

  have hEC :
      Not (E = C) :=
    (HilbertOrder.between_incidence B E C hBEC).2.1

  have hElineBC :
      HilbertIncidence.OnLine E lineBC :=
    hilbert_between_on_line
      Geo B E C lineBC hBlineBC hClineBC hBEC

  have hECA :
      Not (Collinear Geo E C A) :=
    hilbert_not_collinear_of_off_line
      Geo E C A lineBC hEC hElineBC hClineBC hAoffBC

  have hAEC :
      Not (Collinear Geo A E C) := by
    intro h
    exact hECA (PrimCollinearCycle Geo A E C h)

  --------------------------------------------------------------------
  -- I.38 consequence: the median divides ABC into equal-content halves.
  --------------------------------------------------------------------

  have hMedian :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B E)
        (hilbertScissorsTriangle Geo A E C) :=
    i42_median_bisects_area Geo A B C E hABC hE

  --------------------------------------------------------------------
  -- ABC splits exactly as ABE + AEC, hence ABC ~ AEC + AEC.
  --------------------------------------------------------------------

  have hSplit :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo A B E +
         hilbertScissorsTriangle Geo A E C) :=
    HilbertScissorsEq.split
      (Geo := Geo) A B C E hBEC

  have hDouble :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B E +
         hilbertScissorsTriangle Geo A E C)
        (hilbertScissorsTriangle Geo A E C +
         hilbertScissorsTriangle Geo A E C) :=
    equicomplementable_add
      Geo
      hMedian
      (equicomplementable_refl
        Geo
        (hilbertScissorsTriangle Geo A E C))

  have hABC_double :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo A E C +
         hilbertScissorsTriangle Geo A E C) :=
    equicomplementable_transport
      Geo hSplit
      (HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo A E C +
         hilbertScissorsTriangle Geo A E C))
      hDouble

  --------------------------------------------------------------------
  -- Construct the angle-XYZ parallelogram FECG on base EC.
  --------------------------------------------------------------------

  rcases
    i42_construct_parallelogram
      Geo A E C X Y Z
      hAEC hXYZ
  with
  ⟨F, G, hParallelogram, hAngle, hFAG⟩

  --------------------------------------------------------------------
  -- Euclid I.41: FECG is double triangle AEC.
  --------------------------------------------------------------------

  have hDoubleParallelogram :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo F E C G)
        (hilbertScissorsTriangle Geo A E C +
         hilbertScissorsTriangle Geo A E C) :=
    i42_parallelogram_double_triangle_on_carrier
      Geo
      F E C G A
      hParallelogram
      hFAG

  --------------------------------------------------------------------
  -- Chain everything together: ABC ~ AEC+AEC ~ FECG.
  --------------------------------------------------------------------

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertParallelogramTerm Geo F E C G) :=
    equicomplementable_trans
      Geo hABC_double
      (equicomplementable_symm Geo hDoubleParallelogram)

  exact ⟨E, F, G, hParallelogram, hAngle, hFinal⟩

end Geometry

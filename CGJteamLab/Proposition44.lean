import CGJteamLab.Proposition42
import CGJteamLab.Proposition43

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.44
--
-- To a given straight line to apply, in a given angle, a
-- parallelogram equal to a given triangle.
--
-- Euclid's proof:
--
--   1. [I.42] Construct a parallelogram BEFG equal to the given
--      triangle, with angle EBG equal to the given angle D.
--   2. Place it so that BE lies in a straight line with the given
--      line AB.
--   3. [I.31] Draw FG produced to H, and AH through A parallel to
--      BG (equivalently EF).
--   4. [Postulate 5] The angles AHF, HFE are supplementary (AH || EF
--      cut by FH), so angles BHG, GFE are together less than two
--      right angles; hence HB and FE, produced, meet -- say at K.
--   5. Draw KL through K parallel to EA (= through H), extend HA, GB
--      to L, M.  Then HLKF is a parallelogram with diameter HK, AG
--      and ME are the "diagonal" parallelograms, and LB, BF are the
--      complements.
--   6. [I.43] LB = BF (the complements about the diameter HK).
--   7. Since BF equals the given triangle (by construction) and
--      angle GBE = angle ABM [I.15, vertical angles] = D, the
--      parallelogram LB, applied to AB in angle ABM = D, equals the
--      given triangle.
--
-- Step 1 is exactly `euclid_proposition_42`, already available (and
-- already resting on its own two explicit local axioms). Steps 3-6
-- are precisely the mathematical content already established as
-- `euclid_proposition_43` -- but recovering that theorem's exact
-- hypotheses (the points H, K, L, M and the auxiliary parallelograms
-- HLKF, AG..., ME...) from the raw output of I.42 requires the two
-- further genuine existence facts of steps 3 and 4 (a line meeting a
-- constructed parallel, and Postulate 5's "lines making angles less
-- than two right angles meet"), together with careful positional
-- bookkeeping matching Euclid's diagram.
--
-- Rather than re-deriving that positional bookkeeping from primitive
-- incidence data (a substantial undertaking on the order of I.43
-- itself, and one carrying real risk of a mismatched correspondence
-- without a diagram to check against), steps 2-6 are packaged here as
-- a single explicit local axiom: transporting a parallelogram of
-- given area and given angle-at-a-vertex onto a prescribed line,
-- sharing one endpoint. This is honestly a strictly larger axiom than
-- I.42's two, but its mathematical content -- the "sliding" argument
-- -- is now known to reduce to I.43 plus two intersection-existence
-- facts, and stands as the natural next target for reduction.
------------------------------------------------------------------------

/--
First geometric construction in Euclid I.44.

Let BEFG be a parallelogram and suppose A-B-E.
Then the line through A parallel to GB meets the carrier FG.
Thus there is a point H on FG such that AH || GB.

At this stage we do not yet prove the stronger order statement H-G-F.
-/
theorem i44_construct_H
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G : Geo.Point)
    (hABE : Geo.Between A B E)
    (hPar : IsParallelogram Geo B E F G) :
    ∃ H : Geo.Point,
      Collinear Geo F G H ∧
      Geo.Parallel A H G B := by

  --------------------------------------------------------------------
  -- Basic data.
  --------------------------------------------------------------------

  have hABEData :=
    HilbertOrder.between_incidence
      A B E hABE

  have hAB : A ≠ B :=
    hABEData.1

  have hABEcol : Collinear Geo A B E :=
    hABEData.2.2.2.1

  have hBE : B ≠ E :=
    hPar.1.1

  have hFG : F ≠ G :=
    hPar.1.2.1

  have hGB : G ≠ B :=
    hPar.2.2.1

  rcases hABEcol with
    ⟨base, hAbase, hBbase, hEbase⟩

  --------------------------------------------------------------------
  -- A is not on GB.
  --
  -- Otherwise the carrier GB would also contain A and B, hence,
  -- by uniqueness of the line through A,B, it would contain E.
  -- But EF || GB.
  --------------------------------------------------------------------

  have hGBA :
      Not (Collinear Geo G B A) := by

    intro h

    rcases h with
      ⟨lineGB, hGlineGB, hBlineGB, hAlineGB⟩

    have hBaseEq :
        base = lineGB :=
      HilbertPlaneIncidence.line_unique
        A B hAB
        base lineGB
        hAbase hBbase
        hAlineGB hBlineGB

    have hElineGB :
        HilbertIncidence.OnLine E lineGB := by
      rw [← hBaseEq]
      exact hEbase

    have hE_GB :
        E ∈ Geo.PointLine G B :=
      (hilbert_mem_pointLine_iff_onLine
        Geo G B E lineGB
        hGB
        hGlineGB hBlineGB).mpr hElineGB

    exact
      Set.disjoint_left.mp
        hPar.2.2.2
        (intersection_test_left_mem Geo E F)
        hE_GB

  --------------------------------------------------------------------
  -- Draw AQ through A parallel to GB.
  --------------------------------------------------------------------

  rcases
      hilbert_parallel_through_point_exists
        Geo G B A hGB hGBA
    with
    ⟨Q, hAQ, hParGB_AQ⟩

  rcases
      HilbertPlaneIncidence.line_through
        A Q hAQ
    with
    ⟨lineAQ, hAlineAQ, hQlineAQ⟩

  rcases
      HilbertPlaneIncidence.line_through
        F G hFG
    with
    ⟨lineFG, hFlineFG, hGlineFG⟩

  --------------------------------------------------------------------
  -- FG and GB are distinct carriers.
  --------------------------------------------------------------------

  have hFG_GB_distinct :
      Geo.PointLine F G ≠ Geo.PointLine G B := by

    intro hSame

    have hF_GB :
        F ∈ Geo.PointLine G B := by
      rw [← hSame]
      exact intersection_test_left_mem Geo F G

    exact
      Set.disjoint_left.mp
        hPar.2.2.2
        (intersection_test_right_mem Geo E F)
        hF_GB

  --------------------------------------------------------------------
  -- AQ meets FG.
  --
  -- If their incidence lines were disjoint, AQ || FG.
  -- Since GB || AQ as well, Euclidean transitivity would give
  -- FG || GB, impossible because they share G.
  --------------------------------------------------------------------

  have hMeet :
      HilbertLinesMeet Geo lineAQ lineFG := by

    by_contra hDisjoint

    have hParAQ_FG :
        Geo.Parallel A Q F G :=
      intersection_test_parallel_of_lines_disjoint
        Geo A Q F G
        lineAQ lineFG
        hAQ hFG
        hAlineAQ hQlineAQ
        hFlineFG hGlineFG
        hDisjoint

    have hParFG_AQ :
        Geo.Parallel F G A Q :=
      ParallelSymmetry
        Geo A Q F G hParAQ_FG

    have hParFG_GB :
        Geo.Parallel F G G B :=
      hilbert_parallel_transitive_distinct
        Geo
        F G
        G B
        A Q
        hParFG_AQ
        hParGB_AQ
        hFG_GB_distinct

    exact
      intersection_test_not_parallel_of_common_point
        Geo
        F G
        G B
        G
        (intersection_test_right_mem Geo F G)
        (intersection_test_left_mem Geo G B)
        hParFG_GB

  --------------------------------------------------------------------
  -- Let H be the intersection.
  --------------------------------------------------------------------

  rcases hMeet with
    ⟨H, hHlineAQ, hHlineFG⟩

  have hFGH :
      Collinear Geo F G H :=
    ⟨lineFG,
      hFlineFG,
      hGlineFG,
      hHlineFG⟩

  --------------------------------------------------------------------
  -- A != H, because A lies on BE while H lies on FG and BE || FG.
  --------------------------------------------------------------------

  have hA_BE :
      A ∈ Geo.PointLine B E :=
    (hilbert_mem_pointLine_iff_onLine
      Geo B E A base
      hBE
      hBbase hEbase).mpr hAbase

  have hAH : A ≠ H := by

    intro hEq

    have hA_FG :
        A ∈ Geo.PointLine F G := by
      rw [hEq]
      exact
        (hilbert_mem_pointLine_iff_onLine
          Geo F G H lineFG
          hFG
          hFlineFG hGlineFG).mpr hHlineFG

    exact
      Set.disjoint_left.mp
        hPar.1.2.2
        hA_BE
        hA_FG

  --------------------------------------------------------------------
  -- Replace AQ by the same carrier AH.
  --------------------------------------------------------------------

  have hAHQ :
      Collinear Geo A H Q :=
    ⟨lineAQ,
      hAlineAQ,
      hHlineAQ,
      hQlineAQ⟩

  have hParAQ_GB :
      Geo.Parallel A Q G B :=
    ParallelSymmetry
      Geo G B A Q hParGB_AQ

  have hParAH_GB :
      Geo.Parallel A H G B :=
    collinear_parallel_trans
      Geo
      A H Q
      G B
      hAH
      hAHQ
      hParAQ_GB

  exact
    ⟨H, hFGH, hParAH_GB⟩

/--
The intersection point H constructed above lies beyond G on the
carrier FG:

    H - G - F.

The proof is purely order/plane-separation geometry.

Since A-B-E, the points A and E lie on opposite sides of line GB.
Because AH || GB, A and H lie on the same side of GB.
Because EF || GB, E and F lie on the same side of GB.
Hence H and F lie on opposite sides of GB.

Their connecting line is FG, and G lies on GB, so the crossing point
of segment HF with GB must be G.
-/
theorem i44_construct_H_ordered
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G : Geo.Point)
    (hABE : Geo.Between A B E)
    (hPar : IsParallelogram Geo B E F G) :
    ∃ H : Geo.Point,
      Geo.Between H G F ∧
      Geo.Parallel A H G B := by

  --------------------------------------------------------------------
  -- First construct H.
  --------------------------------------------------------------------

  rcases
      i44_construct_H
        Geo A B E F G
        hABE hPar
    with
    ⟨H, hFGH, hAH_GB⟩

  --------------------------------------------------------------------
  -- The carrier FG.
  --------------------------------------------------------------------

  have hFG :
      F ≠ G :=
    hPar.1.2.1

  rcases hFGH with
    ⟨lineFG,
      hFlineFG,
      hGlineFG,
      hHlineFG⟩

  --------------------------------------------------------------------
  -- Use the carrier GB supplied by AH || GB.
  --
  -- A and H are on the same side of GB.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo A H G B hAH_GB
    with
    ⟨lineGB,
      hGlineGB,
      hBlineGB,
      hAHSame⟩

  --------------------------------------------------------------------
  -- E and F are likewise on the same side of GB, because EF || GB.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo E F G B hPar.2
    with
    ⟨lineGB',
      hGlineGB',
      hBlineGB',
      hEFSame'⟩

  have hGB :
      G ≠ B :=
    hPar.2.2.1

  have hLineGB :
      lineGB = lineGB' :=
    HilbertPlaneIncidence.line_unique
      G B hGB
      lineGB lineGB'
      hGlineGB hBlineGB
      hGlineGB' hBlineGB'

  have hEFSame :
      HilbertSameSide Geo E F lineGB := by
    rw [hLineGB]
    exact hEFSame'

  --------------------------------------------------------------------
  -- Since A-B-E and B lies on GB, A and E are on opposite sides
  -- of GB.
  --------------------------------------------------------------------

  have hAoff :
      Not (HilbertIncidence.OnLine A lineGB) :=
    hAHSame.1

  have hEoff :
      Not (HilbertIncidence.OnLine E lineGB) :=
    hEFSame.1

  have hAEOpp :
      HilbertOppositeSide Geo A E lineGB :=
    ⟨hAoff,
     hEoff,
     ⟨B, hABE, hBlineGB⟩⟩

  --------------------------------------------------------------------
  -- Transport the two endpoints through the same-side relations:
  --
  --   A opposite E
  --   A same side H
  --   E same side F
  --
  -- gives H opposite F.
  --------------------------------------------------------------------

  have hEAOpp :
      HilbertOppositeSide Geo E A lineGB :=
    hilbert_oppositeSide_symm
      Geo A E lineGB hAEOpp

  have hEHOpp :
      HilbertOppositeSide Geo E H lineGB :=
    hilbert_oppositeSide_transport_right
      Geo E A H lineGB
      hEAOpp
      hAHSame

  have hHEOpp :
      HilbertOppositeSide Geo H E lineGB :=
    hilbert_oppositeSide_symm
      Geo E H lineGB hEHOpp

  have hHFOpp :
      HilbertOppositeSide Geo H F lineGB :=
    hilbert_oppositeSide_transport_right
      Geo H E F lineGB
      hHEOpp
      hEFSame

  --------------------------------------------------------------------
  -- Let X be the crossing point of segment HF with GB.
  --------------------------------------------------------------------

  rcases hHFOpp.2.2 with
    ⟨X, hHXF, hXlineGB⟩

  have hXlineFG :
      HilbertIncidence.OnLine X lineFG :=
    hilbert_between_on_line
      Geo H X F
      lineFG
      hHlineFG hFlineFG
      hHXF

  --------------------------------------------------------------------
  -- GB and FG are distinct lines.
  --
  -- Otherwise B would lie on FG, contradicting BE || FG.
  --------------------------------------------------------------------

  have hLinesDistinct :
      lineGB ≠ lineFG := by

    intro hEq

    have hBlineFG :
        HilbertIncidence.OnLine B lineFG := by
      rw [← hEq]
      exact hBlineGB

    have hB_FG :
        B ∈ Geo.PointLine F G :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F G B
        lineFG
        hFG
        hFlineFG hGlineFG).mpr hBlineFG

    exact
      Set.disjoint_left.mp
        hPar.1.2.2
        (intersection_test_left_mem Geo B E)
        hB_FG

  --------------------------------------------------------------------
  -- X and G both lie on GB and FG.  Since the two lines are distinct,
  -- the intersection point is unique.
  --------------------------------------------------------------------

  have hXG :
      X = G := by

    by_contra hXG

    have hEq :
        lineGB = lineFG :=
      HilbertPlaneIncidence.line_unique
        X G hXG
        lineGB lineFG
        hXlineGB hGlineGB
        hXlineFG hGlineFG

    exact hLinesDistinct hEq

  subst X

  exact
    ⟨H, hHXF, hAH_GB⟩

/--
The second intersection in Euclid I.44.

Given AH || GB and the parallelogram BEFG, the line HB meets EF.

Indeed, EF || GB. If HB were also parallel to EF, Euclidean
transitivity of parallelism would imply HB || GB, impossible because
the two lines share B.

This theorem establishes only incidence. The order statements

    H-B-K
    F-E-K

are proved separately.
-/
theorem i44_construct_K
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H : Geo.Point)
    (hPar : IsParallelogram Geo B E F G)
    (hAH_GB : Geo.Parallel A H G B) :
    ∃ K : Geo.Point,
      Collinear Geo H B K ∧
      Collinear Geo F E K := by

  --------------------------------------------------------------------
  -- HB is a genuine line.
  --------------------------------------------------------------------

  have hHB : Not (H = B) := by
    intro hEq

    have hH_GB :
        H ∈ Geo.PointLine G B := by
      rw [hEq]
      exact
        intersection_test_right_mem
          Geo G B

    exact
      Set.disjoint_left.mp
        hAH_GB.2.2
        (intersection_test_right_mem Geo A H)
        hH_GB

  --------------------------------------------------------------------
  -- EF is a genuine line.
  --------------------------------------------------------------------

  have hEF : Not (E = F) :=
    hPar.2.1

  rcases
      HilbertPlaneIncidence.line_through
        H B hHB
    with
    ⟨lineHB, hHlineHB, hBlineHB⟩

  rcases
      HilbertPlaneIncidence.line_through
        E F hEF
    with
    ⟨lineEF, hElineEF, hFlineEF⟩

  --------------------------------------------------------------------
  -- H is not on GB because AH || GB.
  --------------------------------------------------------------------

  have hHnotGB :
      Not (H ∈ Geo.PointLine G B) := by

    intro hH_GB

    exact
      Set.disjoint_left.mp
        hAH_GB.2.2
        (intersection_test_right_mem Geo A H)
        hH_GB

  --------------------------------------------------------------------
  -- Hence HB and GB are distinct carriers.
  --------------------------------------------------------------------

  have hHB_GB_distinct :
      Not (Geo.PointLine H B = Geo.PointLine G B) := by

    intro hSame

    apply hHnotGB

    rw [← hSame]

    exact
      intersection_test_left_mem
        Geo H B

  --------------------------------------------------------------------
  -- HB and EF meet.
  --------------------------------------------------------------------

  have hMeet :
      HilbertLinesMeet Geo lineHB lineEF := by

    by_contra hDisjoint

    have hParHB_EF :
        Geo.Parallel H B E F :=
      intersection_test_parallel_of_lines_disjoint
        Geo
        H B E F
        lineHB lineEF
        hHB hEF
        hHlineHB hBlineHB
        hElineEF hFlineEF
        hDisjoint

    have hParGB_EF :
        Geo.Parallel G B E F :=
      ParallelSymmetry
        Geo E F G B hPar.2

    have hParHB_GB :
        Geo.Parallel H B G B :=
      hilbert_parallel_transitive_distinct
        Geo
        H B
        G B
        E F
        hParHB_EF
        hParGB_EF
        hHB_GB_distinct

    exact
      intersection_test_not_parallel_of_common_point
        Geo
        H B
        G B
        B
        (intersection_test_right_mem Geo H B)
        (intersection_test_right_mem Geo G B)
        hParHB_GB

  --------------------------------------------------------------------
  -- Let K be the intersection.
  --------------------------------------------------------------------

  rcases hMeet with
    ⟨K, hKlineHB, hKlineEF⟩

  have hHBK :
      Collinear Geo H B K :=
    ⟨lineHB,
      hHlineHB,
      hBlineHB,
      hKlineHB⟩

  have hFEK :
      Collinear Geo F E K :=
    ⟨lineEF,
      hFlineEF,
      hElineEF,
      hKlineEF⟩

  exact
    ⟨K, hHBK, hFEK⟩

/--
The intersection K lies beyond B on the line HB:

    H - B - K.

The proof is by plane separation with respect to the line GB.

A and E are on opposite sides of GB because A-B-E.
Since AH || GB, A and H are on the same side of GB.
Since EK || GB, E and K are on the same side of GB.
Hence H and K are on opposite sides of GB.

The segment HK therefore crosses GB.  Since HB and GB meet at B,
the crossing point must be B.
-/
theorem i44_construct_K_first_order
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H : Geo.Point)
    (hABE : Geo.Between A B E)
    (hPar : IsParallelogram Geo B E F G)
    (hHGF : Geo.Between H G F)
    (hAH_GB : Geo.Parallel A H G B) :
    exists K : Geo.Point,
      Geo.Between H B K /\
      Collinear Geo F E K := by

  --------------------------------------------------------------------
  -- Construct the incidence intersection K.
  --------------------------------------------------------------------

  rcases
      i44_construct_K
        Geo A B E F G H
        hPar hAH_GB
    with
    ⟨K, hHBKcol, hFEKcol⟩

  have hABEData :=
    HilbertOrder.between_incidence
      A B E hABE

  have hHGFData :=
    HilbertOrder.between_incidence
      H G F hHGF

  have hBE : B ≠ E :=
    hPar.1.1

  have hFG : F ≠ G :=
    hPar.1.2.1

  have hGB : G ≠ B :=
    hPar.2.2.1

  --------------------------------------------------------------------
  -- K != E.
  --
  -- Otherwise H would lie both on BE and on FG, contradicting
  -- BE || FG.
  --------------------------------------------------------------------

  have hEK : E ≠ K := by

    intro hEq

    subst K

    rcases hHBKcol with
      ⟨lineHBE,
        hHlineHBE,
        hBlineHBE,
        hElineHBE⟩

    have hH_BE :
        H ∈ Geo.PointLine B E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B E H
        lineHBE
        hBE
        hBlineHBE hElineHBE).mpr
        hHlineHBE

    rcases hHGFData.2.2.2.1 with
      ⟨lineHGF,
        hHlineHGF,
        hGlineHGF,
        hFlineHGF⟩

    have hH_FG :
        H ∈ Geo.PointLine F G :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F G H
        lineHGF
        hFG
        hFlineHGF hGlineHGF).mpr
        hHlineHGF

    exact
      Set.disjoint_left.mp
        hPar.1.2.2
        hH_BE
        hH_FG

  --------------------------------------------------------------------
  -- Since E,F,K are collinear and EF || GB, also EK || GB.
  --------------------------------------------------------------------

  have hEKF :
      Collinear Geo E K F :=
    PrimCollinearCycle
      Geo F E K hFEKcol

  have hParEK_GB :
      Geo.Parallel E K G B :=
    collinear_parallel_trans
      Geo
      E K F
      G B
      hEK
      hEKF
      hPar.2

  --------------------------------------------------------------------
  -- A,H lie on the same side of GB.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo A H G B hAH_GB
    with
    ⟨lineGB,
      hGlineGB,
      hBlineGB,
      hAHSame⟩

  --------------------------------------------------------------------
  -- E,K lie on the same side of GB.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo E K G B hParEK_GB
    with
    ⟨lineGB',
      hGlineGB',
      hBlineGB',
      hEKSame'⟩

  have hLineGB :
      lineGB = lineGB' :=
    HilbertPlaneIncidence.line_unique
      G B hGB
      lineGB lineGB'
      hGlineGB hBlineGB
      hGlineGB' hBlineGB'

  have hEKSame :
      HilbertSameSide Geo E K lineGB := by
    rw [hLineGB]
    exact hEKSame'

  --------------------------------------------------------------------
  -- A and E are opposite with respect to GB because A-B-E.
  --------------------------------------------------------------------

  have hAoff :
      Not (HilbertIncidence.OnLine A lineGB) :=
    hAHSame.1

  have hEoff :
      Not (HilbertIncidence.OnLine E lineGB) :=
    hEKSame.1

  have hAEOpp :
      HilbertOppositeSide Geo A E lineGB :=
    ⟨hAoff,
     hEoff,
     ⟨B, hABE, hBlineGB⟩⟩

  --------------------------------------------------------------------
  -- Transport opposite-side data:
  --
  --   A opposite E
  --   A same H
  --   E same K
  --
  -- therefore H opposite K.
  --------------------------------------------------------------------

  have hEAOpp :
      HilbertOppositeSide Geo E A lineGB :=
    hilbert_oppositeSide_symm
      Geo A E lineGB hAEOpp

  have hEHOpp :
      HilbertOppositeSide Geo E H lineGB :=
    hilbert_oppositeSide_transport_right
      Geo
      E A H
      lineGB
      hEAOpp
      hAHSame

  have hHEOpp :
      HilbertOppositeSide Geo H E lineGB :=
    hilbert_oppositeSide_symm
      Geo E H lineGB hEHOpp

  have hHKOpp :
      HilbertOppositeSide Geo H K lineGB :=
    hilbert_oppositeSide_transport_right
      Geo
      H E K
      lineGB
      hHEOpp
      hEKSame

  --------------------------------------------------------------------
  -- Let X be the crossing point of HK with GB.
  --------------------------------------------------------------------

  rcases hHKOpp.2.2 with
    ⟨X, hHXK, hXlineGB⟩

  --------------------------------------------------------------------
  -- Recover a carrier for H,B,K.
  --------------------------------------------------------------------

  rcases hHBKcol with
    ⟨lineHB,
      hHlineHB,
      hBlineHB,
      hKlineHB⟩

  have hXlineHB :
      HilbertIncidence.OnLine X lineHB :=
    hilbert_between_on_line
      Geo H X K
      lineHB
      hHlineHB hKlineHB
      hHXK

  --------------------------------------------------------------------
  -- HB and GB are distinct because H is off GB.
  --------------------------------------------------------------------

  have hHoffGB :
      Not (HilbertIncidence.OnLine H lineGB) :=
    hAHSame.2.1

  have hLinesDistinct :
      lineHB ≠ lineGB := by

    intro hEq

    apply hHoffGB

    rw [← hEq]

    exact hHlineHB

  --------------------------------------------------------------------
  -- X and B lie on both HB and GB, hence X = B.
  --------------------------------------------------------------------

  have hXB :
      X = B := by

    by_contra hXB

    have hEq :
        lineHB = lineGB :=
      HilbertPlaneIncidence.line_unique
        X B hXB
        lineHB lineGB
        hXlineHB hBlineHB
        hXlineGB hBlineGB

    exact hLinesDistinct hEq

  subst X

  exact
    ⟨K, hHXK, hFEKcol⟩

/--
The full order information for the second intersection in Euclid I.44:

    H - B - K
    F - E - K.

The first relation was established previously.

For the second, use the line BE.  Since H,G,F are collinear and
BE || FG, the points H and F lie on the same side of BE.
Since H-B-K, the points H and K lie on opposite sides of BE.
Hence F and K lie on opposite sides of BE.

But F,E,K are collinear and E lies on BE, so E is the unique crossing
point of segment FK with BE.
-/
theorem i44_construct_K_ordered
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H : Geo.Point)
    (hABE : Geo.Between A B E)
    (hPar : IsParallelogram Geo B E F G)
    (hHGF : Geo.Between H G F)
    (hAH_GB : Geo.Parallel A H G B) :
    ∃ K : Geo.Point,
      Geo.Between H B K ∧
      Geo.Between F E K := by

  --------------------------------------------------------------------
  -- First recover K with H-B-K and F,E,K collinear.
  --------------------------------------------------------------------

  rcases
      i44_construct_K_first_order
        Geo A B E F G H
        hABE hPar hHGF hAH_GB
    with
    ⟨K, hHBK, hFEKcol⟩

  have hHGFData :=
    HilbertOrder.between_incidence
      H G F hHGF

  have hHBKData :=
    HilbertOrder.between_incidence
      H B K hHBK

  --------------------------------------------------------------------
  -- Replace FG by the same carrier FH.
  --------------------------------------------------------------------

  have hHF : H ≠ F :=
    hHGFData.2.2.1

  have hFH : F ≠ H :=
    Ne.symm hHF

  have hFGH :
      Collinear Geo F G H :=
    PrimCollinearSymm
      Geo H G F
      hHGFData.2.2.2.1

  have hFHG :
      Collinear Geo F H G :=
    PrimCollinearRotate
      Geo F G H hFGH

  have hParFG_BE :
      Geo.Parallel F G B E :=
    ParallelSymmetry
      Geo B E F G hPar.1

  have hParFH_BE :
      Geo.Parallel F H B E :=
    collinear_parallel_trans
      Geo
      F H G
      B E
      hFH
      hFHG
      hParFG_BE

  have hParHF_BE :
      Geo.Parallel H F B E :=
    ParallelSwapFirstLine
      Geo F H B E hParFH_BE

  --------------------------------------------------------------------
  -- Therefore H and F lie on the same side of BE.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo H F B E hParHF_BE
    with
    ⟨lineBE,
      hBlineBE,
      hElineBE,
      hHFSame⟩

  have hHoffBE :
      Not (HilbertIncidence.OnLine H lineBE) :=
    hHFSame.1

  have hFoffBE :
      Not (HilbertIncidence.OnLine F lineBE) :=
    hHFSame.2.1

  --------------------------------------------------------------------
  -- K is also off BE.
  --
  -- Otherwise the line HBK and BE would share the two distinct
  -- points B and K, hence would coincide, putting H on BE.
  --------------------------------------------------------------------

  have hBK : B ≠ K :=
    hHBKData.2.1

  rcases hHBKData.2.2.2.1 with
    ⟨lineHB,
      hHlineHB,
      hBlineHB,
      hKlineHB⟩

  have hKoffBE :
      Not (HilbertIncidence.OnLine K lineBE) := by

    intro hKlineBE

    have hEq :
        lineHB = lineBE :=
      HilbertPlaneIncidence.line_unique
        B K hBK
        lineHB lineBE
        hBlineHB hKlineHB
        hBlineBE hKlineBE

    apply hHoffBE

    rw [← hEq]

    exact hHlineHB

  --------------------------------------------------------------------
  -- H-B-K directly says that H and K are on opposite sides of BE.
  --------------------------------------------------------------------

  have hHKOpp :
      HilbertOppositeSide Geo H K lineBE :=
    ⟨hHoffBE,
     hKoffBE,
     ⟨B, hHBK, hBlineBE⟩⟩

  --------------------------------------------------------------------
  -- H and F are on the same side, so transport the opposite-side
  -- relation from H to F.
  --------------------------------------------------------------------

  have hKHOpp :
      HilbertOppositeSide Geo K H lineBE :=
    hilbert_oppositeSide_symm
      Geo H K lineBE hHKOpp

  have hKFOpp :
      HilbertOppositeSide Geo K F lineBE :=
    hilbert_oppositeSide_transport_right
      Geo
      K H F
      lineBE
      hKHOpp
      hHFSame

  have hFKOpp :
      HilbertOppositeSide Geo F K lineBE :=
    hilbert_oppositeSide_symm
      Geo K F lineBE hKFOpp

  --------------------------------------------------------------------
  -- Let X be the crossing point of FK with BE.
  --------------------------------------------------------------------

  rcases hFKOpp.2.2 with
    ⟨X, hFXK, hXlineBE⟩

  --------------------------------------------------------------------
  -- Recover the carrier FEK.
  --------------------------------------------------------------------

  rcases hFEKcol with
    ⟨lineFE,
      hFlineFE,
      hElineFE,
      hKlineFE⟩

  have hXlineFE :
      HilbertIncidence.OnLine X lineFE :=
    hilbert_between_on_line
      Geo F X K
      lineFE
      hFlineFE hKlineFE
      hFXK

  --------------------------------------------------------------------
  -- X and E both lie on FE and BE.  Since F is off BE, these two
  -- carriers are distinct, so their intersection is unique.
  --------------------------------------------------------------------

  have hXE :
      X = E := by

    by_contra hXE

    have hEq :
        lineFE = lineBE :=
      HilbertPlaneIncidence.line_unique
        X E hXE
        lineFE lineBE
        hXlineFE hElineFE
        hXlineBE hElineBE

    apply hFoffBE

    rw [← hEq]

    exact hFlineFE

  subst X

  exact
    ⟨K, hHBK, hFXK⟩

/--
The first diagonal parallelogram required by Euclid I.43.

From

    A-B-E
    H-G-F

together with BEFG being a parallelogram and AH || GB, we obtain

    H A B G

as a parallelogram.
-/
theorem i44_first_diagonal_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H : Geo.Point)
    (hABE : Geo.Between A B E)
    (hHGF : Geo.Between H G F)
    (hPar : IsParallelogram Geo B E F G)
    (hAH_GB : Geo.Parallel A H G B) :
    IsParallelogram Geo H A B G := by

  have hABEData :=
    HilbertOrder.between_incidence
      A B E hABE

  have hHGFData :=
    HilbertOrder.between_incidence
      H G F hHGF

  have hAB : A ≠ B :=
    hABEData.1

  have hAE : A ≠ E :=
    hABEData.2.2.1

  have hGH : G ≠ H :=
    Ne.symm hHGFData.1

  have hABEcol :
      Collinear Geo A B E :=
    hABEData.2.2.2.1

  have hHGFcol :
      Collinear Geo H G F :=
    hHGFData.2.2.2.1

  --------------------------------------------------------------------
  -- HA || BG.
  --------------------------------------------------------------------

  have hHA_GB :
      Geo.Parallel H A G B :=
    ParallelSwapFirstLine
      Geo A H G B hAH_GB

  have hHA_BG :
      Geo.Parallel H A B G :=
    ParallelSwapSecondLine
      Geo H A G B hHA_GB

  --------------------------------------------------------------------
  -- First transport BE || FG onto AE || FG.
  --------------------------------------------------------------------

  have hAE_FG :
      Geo.Parallel A E F G :=
    ParallelCollinearLeft
      Geo
      B E A F G
      hAE
      hPar.1
      hABEcol

  --------------------------------------------------------------------
  -- Then replace AE by AB.
  --------------------------------------------------------------------

  have hAB_FG :
      Geo.Parallel A B F G :=
    collinear_parallel_trans
      Geo
      A B E
      F G
      hAB
      hABEcol
      hAE_FG

  --------------------------------------------------------------------
  -- Replace FG by GH.
  --------------------------------------------------------------------

  have hFG_AB :
      Geo.Parallel F G A B :=
    ParallelSymmetry
      Geo A B F G hAB_FG

  have hGF_AB :
      Geo.Parallel G F A B :=
    ParallelSwapFirstLine
      Geo F G A B hFG_AB

  have hGHF :
      Collinear Geo G H F := by
    exact
      PrimCollinearSwap
        Geo H G F hHGFcol

  have hGH_AB :
      Geo.Parallel G H A B :=
    collinear_parallel_trans
      Geo
      G H F
      A B
      hGH
      hGHF
      hGF_AB

  have hAB_GH :
      Geo.Parallel A B G H :=
    ParallelSymmetry
      Geo G H A B hGH_AB

  exact
    ⟨hHA_BG, hAB_GH⟩

/--
Construct the transversal through K used in Euclid I.44.

Through K draw KQ parallel to BE. This line meets HA at L
and GB at M.

At this stage we record incidence and parallelism; the order
relations are proved separately.
-/
theorem i44_construct_LM
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H K : Geo.Point)
    (hABE : Geo.Between A B E)
    (hHGF : Geo.Between H G F)
    (hFEK : Geo.Between F E K)
    (hPar : IsParallelogram Geo B E F G)
    (hAH_GB : Geo.Parallel A H G B) :
    ∃ Q L M : Geo.Point,
      K ≠ Q ∧
      Geo.Parallel B E K Q ∧
      Collinear Geo H A L ∧
      Collinear Geo G B M ∧
      Collinear Geo K Q L ∧
      Collinear Geo K Q M ∧
      Collinear Geo L K M := by

  have hABEData :=
    HilbertOrder.between_incidence
      A B E hABE

  have hHGFData :=
    HilbertOrder.between_incidence
      H G F hHGF

  have hFEKData :=
    HilbertOrder.between_incidence
      F E K hFEK

  have hBE : B ≠ E :=
    hPar.1.1

  have hFG : F ≠ G :=
    hPar.1.2.1

  have hGB : G ≠ B :=
    hPar.2.2.1

  have hHA : H ≠ A :=
    Ne.symm hAH_GB.1

  have hEK : E ≠ K :=
    hFEKData.2.1

  --------------------------------------------------------------------
  -- K is not on BE.
  --------------------------------------------------------------------

  have hBEK :
      Not (Collinear Geo B E K) := by

    intro hCol

    rcases hCol with
      ⟨lineBEK,
        hBlineBEK,
        hElineBEK,
        hKlineBEK⟩

    rcases hFEKData.2.2.2.1 with
      ⟨lineFEK,
        hFlineFEK,
        hElineFEK,
        hKlineFEK⟩

    have hEq :
        lineBEK = lineFEK :=
      HilbertPlaneIncidence.line_unique
        E K hEK
        lineBEK lineFEK
        hElineBEK hKlineBEK
        hElineFEK hKlineFEK

    have hFlineBEK :
        HilbertIncidence.OnLine F lineBEK := by
      rw [hEq]
      exact hFlineFEK

    have hF_BE :
        F ∈ Geo.PointLine B E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B E F
        lineBEK
        hBE
        hBlineBEK hElineBEK).mpr
        hFlineBEK

    exact
      Set.disjoint_left.mp
        hPar.1.2.2
        hF_BE
        (intersection_test_left_mem Geo F G)

  --------------------------------------------------------------------
  -- Through K draw KQ parallel to BE.
  --------------------------------------------------------------------

  rcases
      hilbert_parallel_through_point_exists
        Geo B E K hBE hBEK
    with
    ⟨Q, hKQ, hParBE_KQ⟩

  rcases
      HilbertPlaneIncidence.line_through
        K Q hKQ
    with
    ⟨lineKQ, hKlineKQ, hQlineKQ⟩

  --------------------------------------------------------------------
  -- Prepare the carriers BE and FG.
  --------------------------------------------------------------------

  rcases hABEData.2.2.2.1 with
    ⟨lineABE,
      hAlineABE,
      hBlineABE,
      hElineABE⟩

  have hA_BE :
      A ∈ Geo.PointLine B E :=
    (hilbert_mem_pointLine_iff_onLine
      Geo B E A
      lineABE
      hBE
      hBlineABE hElineABE).mpr
      hAlineABE

  rcases hHGFData.2.2.2.1 with
    ⟨lineHGF,
      hHlineHGF,
      hGlineHGF,
      hFlineHGF⟩

  have hH_FG :
      H ∈ Geo.PointLine F G :=
    (hilbert_mem_pointLine_iff_onLine
      Geo F G H
      lineHGF
      hFG
      hFlineHGF hGlineHGF).mpr
      hHlineHGF

  have hHnotBE :
      Not (H ∈ Geo.PointLine B E) := by
    intro hH_BE
    exact
      Set.disjoint_left.mp
        hPar.1.2.2
        hH_BE
        hH_FG

  --------------------------------------------------------------------
  -- HA and BE are distinct carriers.
  --------------------------------------------------------------------

  have hHA_BE_distinct :
      Geo.PointLine H A ≠ Geo.PointLine B E := by

    intro hSame

    apply hHnotBE

    rw [← hSame]

    exact
      intersection_test_left_mem
        Geo H A

  --------------------------------------------------------------------
  -- HA meets KQ.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        H A hHA
    with
    ⟨lineHA, hHlineHA, hAlineHA⟩

  have hMeetL :
      HilbertLinesMeet Geo lineHA lineKQ := by

    by_contra hDisjoint

    have hParHA_KQ :
        Geo.Parallel H A K Q :=
      intersection_test_parallel_of_lines_disjoint
        Geo
        H A K Q
        lineHA lineKQ
        hHA hKQ
        hHlineHA hAlineHA
        hKlineKQ hQlineKQ
        hDisjoint

    have hParHA_BE :
        Geo.Parallel H A B E :=
      hilbert_parallel_transitive_distinct
        Geo
        H A
        B E
        K Q
        hParHA_KQ
        hParBE_KQ
        hHA_BE_distinct

    exact
      intersection_test_not_parallel_of_common_point
        Geo
        H A
        B E
        A
        (intersection_test_right_mem Geo H A)
        hA_BE
        hParHA_BE

  rcases hMeetL with
    ⟨L, hLlineHA, hLlineKQ⟩

  --------------------------------------------------------------------
  -- GB and BE are distinct carriers.
  --------------------------------------------------------------------

  have hG_BE :
      Not (G ∈ Geo.PointLine B E) := by

    intro hG_BE

    exact
      Set.disjoint_left.mp
        hPar.1.2.2
        hG_BE
        (intersection_test_right_mem Geo F G)

  have hGB_BE_distinct :
      Geo.PointLine G B ≠ Geo.PointLine B E := by

    intro hSame

    apply hG_BE

    rw [← hSame]

    exact
      intersection_test_left_mem
        Geo G B

  --------------------------------------------------------------------
  -- GB meets KQ.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        G B hGB
    with
    ⟨lineGB, hGlineGB, hBlineGB⟩

  have hMeetM :
      HilbertLinesMeet Geo lineGB lineKQ := by

    by_contra hDisjoint

    have hParGB_KQ :
        Geo.Parallel G B K Q :=
      intersection_test_parallel_of_lines_disjoint
        Geo
        G B K Q
        lineGB lineKQ
        hGB hKQ
        hGlineGB hBlineGB
        hKlineKQ hQlineKQ
        hDisjoint

    have hParGB_BE :
        Geo.Parallel G B B E :=
      hilbert_parallel_transitive_distinct
        Geo
        G B
        B E
        K Q
        hParGB_KQ
        hParBE_KQ
        hGB_BE_distinct

    exact
      intersection_test_not_parallel_of_common_point
        Geo
        G B
        B E
        B
        (intersection_test_right_mem Geo G B)
        (intersection_test_left_mem Geo B E)
        hParGB_BE

  rcases hMeetM with
    ⟨M, hMlineGB, hMlineKQ⟩

  --------------------------------------------------------------------
  -- Package all incidence information.
  --------------------------------------------------------------------

  have hHAL :
      Collinear Geo H A L :=
    ⟨lineHA,
      hHlineHA,
      hAlineHA,
      hLlineHA⟩

  have hGBM :
      Collinear Geo G B M :=
    ⟨lineGB,
      hGlineGB,
      hBlineGB,
      hMlineGB⟩

  have hKQL :
      Collinear Geo K Q L :=
    ⟨lineKQ,
      hKlineKQ,
      hQlineKQ,
      hLlineKQ⟩

  have hKQM :
      Collinear Geo K Q M :=
    ⟨lineKQ,
      hKlineKQ,
      hQlineKQ,
      hMlineKQ⟩

  have hLKM :
      Collinear Geo L K M :=
    ⟨lineKQ,
      hLlineKQ,
      hKlineKQ,
      hMlineKQ⟩

  exact
    ⟨Q, L, M,
      hKQ,
      hParBE_KQ,
      hHAL,
      hGBM,
      hKQL,
      hKQM,
      hLKM⟩

/--
The point A lies between H and L in the I.44 construction:

    H - A - L.

The separator is the line BE.

Because H lies on FG and FG || BE, H is off BE.
Because K,L lie on the transversal parallel to BE, K and L are on
the same side of BE. Since H-B-K and B lies on BE, H and K are on
opposite sides of BE. Hence H and L are on opposite sides of BE.

Their carrier is HA, whose intersection with BE is A, so A is the
crossing point.
-/
theorem i44_order_HAL
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H K Q L : Geo.Point)
    (hABE : Geo.Between A B E)
    (hHGF : Geo.Between H G F)
    (hHBK : Geo.Between H B K)
    (hPar : IsParallelogram Geo B E F G)
    (hAH_GB : Geo.Parallel A H G B)
    (_hKQ : K ≠ Q)
    (hParBE_KQ : Geo.Parallel B E K Q)
    (hHAL : Collinear Geo H A L)
    (hKQL : Collinear Geo K Q L) :
    Geo.Between H A L := by

  have hABEData :=
    HilbertOrder.between_incidence
      A B E hABE

  have hHGFData :=
    HilbertOrder.between_incidence
      H G F hHGF

  have hHBKData :=
    HilbertOrder.between_incidence
      H B K hHBK

  have hBE : B ≠ E :=
    hPar.1.1

  have hHF : H ≠ F :=
    hHGFData.2.2.1

  have hFH : F ≠ H :=
    Ne.symm hHF

  have hAH : A ≠ H :=
    hAH_GB.1

  --------------------------------------------------------------------
  -- H and F lie on a line parallel to BE.
  --------------------------------------------------------------------

  have hFGH :
      Collinear Geo F G H :=
    PrimCollinearSymm
      Geo H G F
      hHGFData.2.2.2.1

  have hFHG :
      Collinear Geo F H G :=
    PrimCollinearRotate
      Geo F G H hFGH

  have hParFG_BE :
      Geo.Parallel F G B E :=
    ParallelSymmetry
      Geo B E F G hPar.1

  have hParFH_BE :
      Geo.Parallel F H B E :=
    collinear_parallel_trans
      Geo
      F H G
      B E
      hFH
      hFHG
      hParFG_BE

  have hParHF_BE :
      Geo.Parallel H F B E :=
    ParallelSwapFirstLine
      Geo F H B E hParFH_BE

  rcases
      parallel_endpoints_sameSide
        Geo H F B E hParHF_BE
    with
    ⟨lineBE,
      hBlineBE,
      hElineBE,
      hHFSame⟩

  have hHoffBE :
      Not (HilbertIncidence.OnLine H lineBE) :=
    hHFSame.1

  --------------------------------------------------------------------
  -- A lies on BE.
  --------------------------------------------------------------------

  rcases hABEData.2.2.2.1 with
    ⟨lineABE,
      hAlineABE,
      hBlineABE,
      hElineABE⟩

  have hLineABE :
      lineABE = lineBE :=
    HilbertPlaneIncidence.line_unique
      B E hBE
      lineABE lineBE
      hBlineABE hElineABE
      hBlineBE hElineBE

  have hAlineBE :
      HilbertIncidence.OnLine A lineBE := by
    rw [← hLineABE]
    exact hAlineABE

  --------------------------------------------------------------------
  -- K != L.
  --
  -- Otherwise K would lie on both HA and HB. Since H != K,
  -- the carriers HA and HB would coincide, placing B on AH.
  -- But AH || GB and B lies on GB.
  --------------------------------------------------------------------

  have hKL : K ≠ L := by

    intro hEq

    subst L

    rcases hHAL with
      ⟨lineHAK,
        hHlineHAK,
        hAlineHAK,
        hKlineHAK⟩

    rcases hHBKData.2.2.2.1 with
      ⟨lineHBK,
        hHlineHBK,
        hBlineHBK,
        hKlineHBK⟩

    have hHK : H ≠ K :=
      hHBKData.2.2.1

    have hLineEq :
        lineHAK = lineHBK :=
      HilbertPlaneIncidence.line_unique
        H K hHK
        lineHAK lineHBK
        hHlineHAK hKlineHAK
        hHlineHBK hKlineHBK

    have hBlineHAK :
        HilbertIncidence.OnLine B lineHAK := by
      rw [hLineEq]
      exact hBlineHBK

    have hB_AH :
        B ∈ Geo.PointLine A H :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A H B
        lineHAK
        hAH
        hAlineHAK hHlineHAK).mpr
        hBlineHAK

    exact
      Set.disjoint_left.mp
        hAH_GB.2.2
        hB_AH
        (intersection_test_right_mem Geo G B)

  --------------------------------------------------------------------
  -- Since K,Q,L are collinear and KQ || BE, also KL || BE.
  --------------------------------------------------------------------

  have hKLQ :
      Collinear Geo K L Q :=
    PrimCollinearRotate
      Geo K Q L hKQL

  have hParKQ_BE :
      Geo.Parallel K Q B E :=
    ParallelSymmetry
      Geo B E K Q hParBE_KQ

  have hParKL_BE :
      Geo.Parallel K L B E :=
    collinear_parallel_trans
      Geo
      K L Q
      B E
      hKL
      hKLQ
      hParKQ_BE

  rcases
      parallel_endpoints_sameSide
        Geo K L B E hParKL_BE
    with
    ⟨lineBE',
      hBlineBE',
      hElineBE',
      hKLSame'⟩

  have hLineBE :
      lineBE = lineBE' :=
    HilbertPlaneIncidence.line_unique
      B E hBE
      lineBE lineBE'
      hBlineBE hElineBE
      hBlineBE' hElineBE'

  have hKLSame :
      HilbertSameSide Geo K L lineBE := by
    rw [hLineBE]
    exact hKLSame'

  have hKoffBE :
      Not (HilbertIncidence.OnLine K lineBE) :=
    hKLSame.1

  --------------------------------------------------------------------
  -- H-B-K means that H and K are opposite with respect to BE.
  --------------------------------------------------------------------

  have hHKOpp :
      HilbertOppositeSide Geo H K lineBE :=
    ⟨hHoffBE,
     hKoffBE,
     ⟨B, hHBK, hBlineBE⟩⟩

  --------------------------------------------------------------------
  -- Move K to L on the same side.
  --------------------------------------------------------------------

  have hHLOpp :
      HilbertOppositeSide Geo H L lineBE :=
    hilbert_oppositeSide_transport_right
      Geo
      H K L
      lineBE
      hHKOpp
      hKLSame

  --------------------------------------------------------------------
  -- Let X be the crossing point of HL with BE.
  --------------------------------------------------------------------

  rcases hHLOpp.2.2 with
    ⟨X, hHXL, hXlineBE⟩

  --------------------------------------------------------------------
  -- Since H,A,L are collinear, X also lies on the carrier HAL.
  --------------------------------------------------------------------

  rcases hHAL with
    ⟨lineHAL,
      hHlineHAL,
      hAlineHAL,
      hLlineHAL⟩

  have hXlineHAL :
      HilbertIncidence.OnLine X lineHAL :=
    hilbert_between_on_line
      Geo H X L
      lineHAL
      hHlineHAL hLlineHAL
      hHXL

  --------------------------------------------------------------------
  -- The two carriers HAL and BE already meet at A.
  -- Therefore the crossing point X must be A.
  --------------------------------------------------------------------

  have hXA :
      X = A := by

    by_contra hXA

    have hEq :
        lineHAL = lineBE :=
      HilbertPlaneIncidence.line_unique
        X A hXA
        lineHAL lineBE
        hXlineHAL hAlineHAL
        hXlineBE hAlineBE

    apply hHoffBE

    rw [← hEq]

    exact hHlineHAL

  subst X

  exact hHXL

/--
The point M lies between L and K in the I.44 construction:

    L - M - K.

Use the line GB as separator.

Since H-A-L and AH || GB, the points H and L lie on the same side
of GB.

Since H-B-K and B lies on GB, the points H and K lie on opposite
sides of GB.

Hence L and K lie on opposite sides of GB. Their carrier is LKM,
and M lies on GB, so M is the crossing point.
-/
theorem i44_order_LMK
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H K L M : Geo.Point)
    (hHBK : Geo.Between H B K)
    (hHAL : Geo.Between H A L)
    (hFEK : Geo.Between F E K)
    (hPar : IsParallelogram Geo B E F G)
    (hAH_GB : Geo.Parallel A H G B)
    (hGBM : Collinear Geo G B M)
    (hLKM : Collinear Geo L K M) :
    Geo.Between L M K := by

  have hHBKData :=
    HilbertOrder.between_incidence
      H B K hHBK

  have hHALData :=
    HilbertOrder.between_incidence
      H A L hHAL

  have hFEKData :=
    HilbertOrder.between_incidence
      F E K hFEK

  have hGB : G ≠ B :=
    hPar.2.2.1

  --------------------------------------------------------------------
  -- HL || GB.
  --------------------------------------------------------------------

  have hHL : H ≠ L :=
    hHALData.2.2.1

  have hHLA :
      Collinear Geo H L A :=
    PrimCollinearRotate
      Geo H A L
      hHALData.2.2.2.1

  have hHA_GB :
      Geo.Parallel H A G B :=
    ParallelSwapFirstLine
      Geo A H G B hAH_GB

  have hHL_GB :
      Geo.Parallel H L G B :=
    collinear_parallel_trans
      Geo
      H L A
      G B
      hHL
      hHLA
      hHA_GB

  --------------------------------------------------------------------
  -- Therefore H and L are on the same side of GB.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo H L G B hHL_GB
    with
    ⟨lineGB,
      hGlineGB,
      hBlineGB,
      hHLSame⟩

  have hHoffGB :
      Not (HilbertIncidence.OnLine H lineGB) :=
    hHLSame.1

  have hLoffGB :
      Not (HilbertIncidence.OnLine L lineGB) :=
    hHLSame.2.1

  --------------------------------------------------------------------
  -- EK || GB.
  --------------------------------------------------------------------

  have hEK : E ≠ K :=
    hFEKData.2.1

  have hEKF :
      Collinear Geo E K F :=
    PrimCollinearCycle
      Geo F E K
      hFEKData.2.2.2.1

  have hEK_GB :
      Geo.Parallel E K G B :=
    collinear_parallel_trans
      Geo
      E K F
      G B
      hEK
      hEKF
      hPar.2

  --------------------------------------------------------------------
  -- Hence E and K are on the same side of GB.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo E K G B hEK_GB
    with
    ⟨lineGB',
      hGlineGB',
      hBlineGB',
      hEKSame'⟩

  have hLineGB :
      lineGB = lineGB' :=
    HilbertPlaneIncidence.line_unique
      G B hGB
      lineGB lineGB'
      hGlineGB hBlineGB
      hGlineGB' hBlineGB'

  have hEKSame :
      HilbertSameSide Geo E K lineGB := by
    rw [hLineGB]
    exact hEKSame'

  have hKoffGB :
      Not (HilbertIncidence.OnLine K lineGB) :=
    hEKSame.2.1

  --------------------------------------------------------------------
  -- H-B-K shows that H and K are opposite with respect to GB.
  --------------------------------------------------------------------

  have hHKOpp :
      HilbertOppositeSide Geo H K lineGB :=
    ⟨hHoffGB,
     hKoffGB,
     ⟨B, hHBK, hBlineGB⟩⟩

  --------------------------------------------------------------------
  -- Move H to L on the same side.
  --------------------------------------------------------------------

  have hKHOpp :
      HilbertOppositeSide Geo K H lineGB :=
    hilbert_oppositeSide_symm
      Geo H K lineGB hHKOpp

  have hKLOpp :
      HilbertOppositeSide Geo K L lineGB :=
    hilbert_oppositeSide_transport_right
      Geo
      K H L
      lineGB
      hKHOpp
      hHLSame

  have hLKOpp :
      HilbertOppositeSide Geo L K lineGB :=
    hilbert_oppositeSide_symm
      Geo K L lineGB hKLOpp

  --------------------------------------------------------------------
  -- Let X be the crossing point of LK with GB.
  --------------------------------------------------------------------

  rcases hLKOpp.2.2 with
    ⟨X, hLXK, hXlineGB⟩

  --------------------------------------------------------------------
  -- Recover the carrier LKM.
  --------------------------------------------------------------------

  rcases hLKM with
    ⟨lineLKM,
      hLlineLKM,
      hKlineLKM,
      hMlineLKM⟩

  have hXlineLKM :
      HilbertIncidence.OnLine X lineLKM :=
    hilbert_between_on_line
      Geo L X K
      lineLKM
      hLlineLKM hKlineLKM
      hLXK

  --------------------------------------------------------------------
  -- Put M on our chosen carrier GB.
  --------------------------------------------------------------------

  rcases hGBM with
    ⟨lineGBM,
      hGlineGBM,
      hBlineGBM,
      hMlineGBM⟩

  have hLineGBM :
      lineGBM = lineGB :=
    HilbertPlaneIncidence.line_unique
      G B hGB
      lineGBM lineGB
      hGlineGBM hBlineGBM
      hGlineGB hBlineGB

  have hMlineGB :
      HilbertIncidence.OnLine M lineGB := by
    rw [← hLineGBM]
    exact hMlineGBM

  --------------------------------------------------------------------
  -- X and M are both intersections of LKM with GB.
  -- Since L is off GB, the two carriers are distinct.
  --------------------------------------------------------------------

  have hXM :
      X = M := by

    by_contra hXM

    have hEq :
        lineLKM = lineGB :=
      HilbertPlaneIncidence.line_unique
        X M hXM
        lineLKM lineGB
        hXlineLKM hMlineLKM
        hXlineGB hMlineGB

    apply hLoffGB

    rw [← hEq]

    exact hLlineLKM

  subst X

  exact hLXK

/--
The second diagonal parallelogram required by Euclid I.43:

    B M K E.

The sides BM and KE are parallel because they lie respectively on
GB and EF, which are opposite sides of the original parallelogram.

The sides MK and EB are parallel because MK lies on the transversal
KQ constructed parallel to BE.
-/
theorem i44_second_diagonal_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B E F G K Q L M : Geo.Point)
    (hFEK : Geo.Between F E K)
    (hLMK : Geo.Between L M K)
    (hPar : IsParallelogram Geo B E F G)
    (hKQ : K ≠ Q)
    (hParBE_KQ : Geo.Parallel B E K Q)
    (hGBM : Collinear Geo G B M)
    (hKQM : Collinear Geo K Q M) :
    IsParallelogram Geo B M K E := by

  have hFEKData :=
    HilbertOrder.between_incidence
      F E K hFEK

  have hLMKData :=
    HilbertOrder.between_incidence
      L M K hLMK

  --------------------------------------------------------------------
  -- B != M.
  --
  -- B lies on BE and M lies on KQ, while BE || KQ.
  --------------------------------------------------------------------

  rcases hKQM with
    ⟨lineKQM,
      hKlineKQM,
      hQlineKQM,
      hMlineKQM⟩

  have hM_KQ :
      M ∈ Geo.PointLine K Q :=
    (hilbert_mem_pointLine_iff_onLine
      Geo K Q M
      lineKQM
      hKQ
      hKlineKQM hQlineKQM).mpr
      hMlineKQM

  have hBM : B ≠ M := by

    intro hEq

    subst M

    exact
      Set.disjoint_left.mp
        hParBE_KQ.2.2
        (intersection_test_left_mem Geo B E)
        hM_KQ

  --------------------------------------------------------------------
  -- Reconstruct K-Q-M after extracting its carrier.
  --------------------------------------------------------------------

  have hKQM' :
      Collinear Geo K Q M :=
    ⟨lineKQM,
      hKlineKQM,
      hQlineKQM,
      hMlineKQM⟩

  --------------------------------------------------------------------
  -- BM || KE.
  --
  -- First transport GB || EF to BM || EF.
  --------------------------------------------------------------------

  have hParGB_EF :
      Geo.Parallel G B E F :=
    ParallelSymmetry
      Geo E F G B hPar.2

  have hParBG_EF :
      Geo.Parallel B G E F :=
    ParallelSwapFirstLine
      Geo G B E F hParGB_EF

  have hBMG :
      Collinear Geo B M G := by
    exact
      PrimCollinearCycle
        Geo G B M hGBM

  have hParBM_EF :
      Geo.Parallel B M E F :=
    collinear_parallel_trans
      Geo
      B M G
      E F
      hBM
      hBMG
      hParBG_EF

  have hParEF_BM :
      Geo.Parallel E F B M :=
    ParallelSymmetry
      Geo B M E F hParBM_EF

  --------------------------------------------------------------------
  -- Replace EF by EK.
  --------------------------------------------------------------------

  have hEK : E ≠ K :=
    hFEKData.2.1

  have hEKF :
      Collinear Geo E K F :=
    PrimCollinearCycle
      Geo F E K
      hFEKData.2.2.2.1

  have hParEK_BM :
      Geo.Parallel E K B M :=
    collinear_parallel_trans
      Geo
      E K F
      B M
      hEK
      hEKF
      hParEF_BM

  have hParKE_BM :
      Geo.Parallel K E B M :=
    ParallelSwapFirstLine
      Geo E K B M hParEK_BM

  have hParBM_KE :
      Geo.Parallel B M K E :=
    ParallelSymmetry
      Geo K E B M hParKE_BM

  --------------------------------------------------------------------
  -- MK || EB.
  --
  -- M,K lie on KQ and KQ || BE.
  --------------------------------------------------------------------

  have hMK : M ≠ K :=
    hLMKData.2.1

  have hKM : K ≠ M :=
    Ne.symm hMK

  have hKMQ :
      Collinear Geo K M Q :=
    PrimCollinearRotate
      Geo K Q M hKQM'

  have hParKQ_BE :
      Geo.Parallel K Q B E :=
    ParallelSymmetry
      Geo B E K Q hParBE_KQ

  have hParKM_BE :
      Geo.Parallel K M B E :=
    collinear_parallel_trans
      Geo
      K M Q
      B E
      hKM
      hKMQ
      hParKQ_BE

  have hParMK_BE :
      Geo.Parallel M K B E :=
    ParallelSwapFirstLine
      Geo K M B E hParKM_BE

  have hParMK_EB :
      Geo.Parallel M K E B :=
    ParallelSwapSecondLine
      Geo M K B E hParMK_BE

  exact
    ⟨hParBM_KE, hParMK_EB⟩

/--
The large parallelogram in the Euclid I.44 configuration:

    H L K F.

Its first pair of opposite sides comes from

    HA || GB
    EF || GB,

hence HA || EF, and then H-A-L and F-E-K transport this to

    HL || KF.

Its second pair comes from

    KQ || BE
    FG || BE,

hence KQ || FG, and the collinearities transport this to

    LK || FH.
-/
theorem i44_big_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H K Q L M : Geo.Point)
    (hABE : Geo.Between A B E)
    (hHGF : Geo.Between H G F)
    (hFEK : Geo.Between F E K)
    (hHAL : Geo.Between H A L)
    (hLMK : Geo.Between L M K)
    (hPar : IsParallelogram Geo B E F G)
    (hAH_GB : Geo.Parallel A H G B)
    (hParBE_KQ : Geo.Parallel B E K Q)
    (hKQL : Collinear Geo K Q L) :
    IsParallelogram Geo H L K F := by

  have hABEData :=
    HilbertOrder.between_incidence
      A B E hABE

  have hHGFData :=
    HilbertOrder.between_incidence
      H G F hHGF

  have hFEKData :=
    HilbertOrder.between_incidence
      F E K hFEK

  have hHALData :=
    HilbertOrder.between_incidence
      H A L hHAL

  have hLMKData :=
    HilbertOrder.between_incidence
      L M K hLMK

  have hBE : B ≠ E :=
    hPar.1.1

  have hFG : F ≠ G :=
    hPar.1.2.1

  have hEF : E ≠ F :=
    hPar.2.1

  have hAE : A ≠ E :=
    hABEData.2.2.1

  have hFK : F ≠ K :=
    hFEKData.2.2.1

  have hHF : H ≠ F :=
    hHGFData.2.2.1

  have hFH : F ≠ H :=
    Ne.symm hHF

  have hHL : H ≠ L :=
    hHALData.2.2.1

  have hLK : L ≠ K :=
    hLMKData.2.2.1

  have hKL : K ≠ L :=
    Ne.symm hLK

  have hKQ : K ≠ Q :=
    hParBE_KQ.2.1

  --------------------------------------------------------------------
  -- Fix carriers that will be used in the distinctness arguments.
  --------------------------------------------------------------------

  rcases hABEData.2.2.2.1 with
    ⟨lineABE,
      hAlineABE,
      hBlineABE,
      hElineABE⟩

  rcases hHGFData.2.2.2.1 with
    ⟨lineHGF,
      hHlineHGF,
      hGlineHGF,
      hFlineHGF⟩

  rcases hFEKData.2.2.2.1 with
    ⟨lineFEK,
      hFlineFEK,
      hElineFEK,
      hKlineFEK⟩

  --------------------------------------------------------------------
  -- First pair: HL || KF.
  --
  -- First show that HA and EF are distinct carriers.
  --------------------------------------------------------------------

  have hHA_EF_distinct :
      Geo.PointLine H A ≠ Geo.PointLine E F := by

    intro hSame

    have hA_EF :
        A ∈ Geo.PointLine E F := by
      rw [← hSame]
      exact
        intersection_test_right_mem
          Geo H A

    have hAlineFEK :
        HilbertIncidence.OnLine A lineFEK :=
      (hilbert_mem_pointLine_iff_onLine
        Geo E F A
        lineFEK
        hEF
        hElineFEK hFlineFEK).mp
        hA_EF

    have hLineEq :
        lineABE = lineFEK :=
      HilbertPlaneIncidence.line_unique
        A E hAE
        lineABE lineFEK
        hAlineABE hElineABE
        hAlineFEK hElineFEK

    have hFlineABE :
        HilbertIncidence.OnLine F lineABE := by
      rw [hLineEq]
      exact hFlineFEK

    have hF_BE :
        F ∈ Geo.PointLine B E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B E F
        lineABE
        hBE
        hBlineABE hElineABE).mpr
        hFlineABE

    exact
      Set.disjoint_left.mp
        hPar.1.2.2
        hF_BE
        (intersection_test_left_mem Geo F G)

  --------------------------------------------------------------------
  -- HA || EF because both are parallel to GB.
  --------------------------------------------------------------------

  have hParHA_GB :
      Geo.Parallel H A G B :=
    ParallelSwapFirstLine
      Geo A H G B hAH_GB

  have hParHA_EF :
      Geo.Parallel H A E F :=
    hilbert_parallel_transitive_distinct
      Geo
      H A
      E F
      G B
      hParHA_GB
      hPar.2
      hHA_EF_distinct

  --------------------------------------------------------------------
  -- Replace HA by HL.
  --------------------------------------------------------------------

  have hHLA :
      Collinear Geo H L A :=
    PrimCollinearRotate
      Geo H A L
      hHALData.2.2.2.1

  have hParHL_EF :
      Geo.Parallel H L E F :=
    collinear_parallel_trans
      Geo
      H L A
      E F
      hHL
      hHLA
      hParHA_EF

  --------------------------------------------------------------------
  -- Replace EF by KF.
  --------------------------------------------------------------------

  have hParEF_HL :
      Geo.Parallel E F H L :=
    ParallelSymmetry
      Geo H L E F hParHL_EF

  have hParFE_HL :
      Geo.Parallel F E H L :=
    ParallelSwapFirstLine
      Geo E F H L hParEF_HL

  have hFKE :
      Collinear Geo F K E :=
    PrimCollinearRotate
      Geo F E K
      hFEKData.2.2.2.1

  have hParFK_HL :
      Geo.Parallel F K H L :=
    collinear_parallel_trans
      Geo
      F K E
      H L
      hFK
      hFKE
      hParFE_HL

  have hParKF_HL :
      Geo.Parallel K F H L :=
    ParallelSwapFirstLine
      Geo F K H L hParFK_HL

  have hParHL_KF :
      Geo.Parallel H L K F :=
    ParallelSymmetry
      Geo K F H L hParKF_HL

  --------------------------------------------------------------------
  -- Second pair: LK || FH.
  --
  -- First show that KQ and FG are distinct carriers.
  --------------------------------------------------------------------

  have hKQ_FG_distinct :
      Geo.PointLine K Q ≠ Geo.PointLine F G := by

    intro hSame

    have hK_FG :
        K ∈ Geo.PointLine F G := by
      rw [← hSame]
      exact
        intersection_test_left_mem
          Geo K Q

    have hKlineHGF :
        HilbertIncidence.OnLine K lineHGF :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F G K
        lineHGF
        hFG
        hFlineHGF hGlineHGF).mp
        hK_FG

    have hLineEq :
        lineFEK = lineHGF :=
      HilbertPlaneIncidence.line_unique
        F K hFK
        lineFEK lineHGF
        hFlineFEK hKlineFEK
        hFlineHGF hKlineHGF

    have hElineHGF :
        HilbertIncidence.OnLine E lineHGF := by
      rw [← hLineEq]
      exact hElineFEK

    have hE_FG :
        E ∈ Geo.PointLine F G :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F G E
        lineHGF
        hFG
        hFlineHGF hGlineHGF).mpr
        hElineHGF

    exact
      Set.disjoint_left.mp
        hPar.1.2.2
        (intersection_test_right_mem Geo B E)
        hE_FG

  --------------------------------------------------------------------
  -- KQ || FG because both are parallel to BE.
  --------------------------------------------------------------------

  have hParKQ_BE :
      Geo.Parallel K Q B E :=
    ParallelSymmetry
      Geo B E K Q hParBE_KQ

  have hParFG_BE :
      Geo.Parallel F G B E :=
    ParallelSymmetry
      Geo B E F G hPar.1

  have hParKQ_FG :
      Geo.Parallel K Q F G :=
    hilbert_parallel_transitive_distinct
      Geo
      K Q
      F G
      B E
      hParKQ_BE
      hParFG_BE
      hKQ_FG_distinct

  --------------------------------------------------------------------
  -- Replace KQ by KL.
  --------------------------------------------------------------------

  have hKLQ :
      Collinear Geo K L Q :=
    PrimCollinearRotate
      Geo K Q L hKQL

  have hParKL_FG :
      Geo.Parallel K L F G :=
    collinear_parallel_trans
      Geo
      K L Q
      F G
      hKL
      hKLQ
      hParKQ_FG

  have hParLK_FG :
      Geo.Parallel L K F G :=
    ParallelSwapFirstLine
      Geo K L F G hParKL_FG

  --------------------------------------------------------------------
  -- Replace FG by FH.
  --------------------------------------------------------------------

  have hParFG_LK :
      Geo.Parallel F G L K :=
    ParallelSymmetry
      Geo L K F G hParLK_FG

  have hFGH :
      Collinear Geo F G H :=
    PrimCollinearSymm
      Geo H G F
      hHGFData.2.2.2.1

  have hFHG :
      Collinear Geo F H G :=
    PrimCollinearRotate
      Geo F G H hFGH

  have hParFH_LK :
      Geo.Parallel F H L K :=
    collinear_parallel_trans
      Geo
      F H G
      L K
      hFH
      hFHG
      hParFG_LK

  have hParLK_FH :
      Geo.Parallel L K F H :=
    ParallelSymmetry
      Geo F H L K hParFH_LK

  exact
    ⟨hParHL_KF, hParLK_FH⟩

/--
The target parallelogram of Euclid I.44:

    A B M L.

The pair AB || ML follows from the second diagonal parallelogram
BMKE together with A-B-E and L-M-K.

The pair BM || LA follows from AH || GB together with the
collinearities G-B-M and H-A-L.
-/
theorem i44_target_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E G H K L M : Geo.Point)
    (hABE : Geo.Between A B E)
    (hHAL : Geo.Between H A L)
    (hLMK : Geo.Between L M K)
    (hAH_GB : Geo.Parallel A H G B)
    (hGBM : Collinear Geo G B M)
    (hBMKE : IsParallelogram Geo B M K E) :
    IsParallelogram Geo A B M L := by

  have hABEData :=
    HilbertOrder.between_incidence
      A B E hABE

  have hHALData :=
    HilbertOrder.between_incidence
      H A L hHAL

  have hLMKData :=
    HilbertOrder.between_incidence
      L M K hLMK

  --------------------------------------------------------------------
  -- AB || ML.
  --------------------------------------------------------------------

  have hML : M ≠ L :=
    Ne.symm hLMKData.1

  have hMLK :
      Collinear Geo M L K :=
    PrimCollinearSwap
      Geo L M K
      hLMKData.2.2.2.1

  have hParML_EB :
      Geo.Parallel M L E B :=
    collinear_parallel_trans
      Geo
      M L K
      E B
      hML
      hMLK
      hBMKE.2

  have hParML_BE :
      Geo.Parallel M L B E :=
    ParallelSwapSecondLine
      Geo M L E B hParML_EB

  have hParBE_ML :
      Geo.Parallel B E M L :=
    ParallelSymmetry
      Geo M L B E hParML_BE

  have hAE : A ≠ E :=
    hABEData.2.2.1

  have hABEcol :
      Collinear Geo A B E :=
    hABEData.2.2.2.1

  have hParAE_ML :
      Geo.Parallel A E M L :=
    ParallelCollinearLeft
      Geo
      B E A M L
      hAE
      hParBE_ML
      hABEcol

  have hAB : A ≠ B :=
    hABEData.1

  have hParAB_ML :
      Geo.Parallel A B M L :=
    collinear_parallel_trans
      Geo
      A B E
      M L
      hAB
      hABEcol
      hParAE_ML

  --------------------------------------------------------------------
  -- BM || LA.
  --------------------------------------------------------------------

  have hBM : B ≠ M :=
    hBMKE.1.1

  have hParGB_AH :
      Geo.Parallel G B A H :=
    ParallelSymmetry
      Geo A H G B hAH_GB

  have hParBG_AH :
      Geo.Parallel B G A H :=
    ParallelSwapFirstLine
      Geo G B A H hParGB_AH

  have hBMG :
      Collinear Geo B M G :=
    PrimCollinearCycle
      Geo G B M hGBM

  have hParBM_AH :
      Geo.Parallel B M A H :=
    collinear_parallel_trans
      Geo
      B M G
      A H
      hBM
      hBMG
      hParBG_AH

  have hParAH_BM :
      Geo.Parallel A H B M :=
    ParallelSymmetry
      Geo B M A H hParBM_AH

  have hAL : A ≠ L :=
    hHALData.2.1

  have hALH :
      Collinear Geo A L H :=
    PrimCollinearCycle
      Geo H A L
      hHALData.2.2.2.1

  have hParAL_BM :
      Geo.Parallel A L B M :=
    collinear_parallel_trans
      Geo
      A L H
      B M
      hAL
      hALH
      hParAH_BM

  have hParLA_BM :
      Geo.Parallel L A B M :=
    ParallelSwapFirstLine
      Geo A L B M hParAL_BM

  have hParBM_LA :
      Geo.Parallel B M L A :=
    ParallelSymmetry
      Geo L A B M hParLA_BM

  exact
    ⟨hParAB_ML, hParBM_LA⟩

/--
The content step in Euclid I.44.

Assume the full I.43 configuration occurring in Euclid's construction:

  big parallelogram: H L K F
  diagonal:          H - B - K

  first diagonal parallelogram:  H A B G
  second diagonal parallelogram: B M K E

Then I.43 identifies the two complements:

  A L M B   and   G B E F.

The first is the new parallelogram ABML and the second is the
original parallelogram BEFG.
-/
theorem i44_i43_content_bridge
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H K L M : Geo.Point)
    (hBig : IsParallelogram Geo H L K F)
    (hHBK : Geo.Between H B K)
    (hHAL : Geo.Between H A L)
    (hHGF : Geo.Between H G F)
    (hLMK : Geo.Between L M K)
    (hFEK : Geo.Between F E K)
    (hHABG : IsParallelogram Geo H A B G)
    (hBMKE : IsParallelogram Geo B M K E)
    (hABML : IsParallelogram Geo A B M L) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B M L)
      (hilbertParallelogramTerm Geo B E F G) := by

  have h43 :=
    euclid_proposition_43
      Geo
      H L K F
      B
      A G M E
      hBig
      hHBK
      hHAL
      hHGF
      hLMK
      hFEK
      hHABG
      hBMKE

  have hNew :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B M L)
        (hilbertScissorsTriangle Geo A L B +
         hilbertScissorsTriangle Geo B L M) := by

    have h :=
      parallelogram_two_triangulations
        Geo A B M L hABML

    rw [scissors_triangle_swap23 Geo A B L,
        scissors_triangle_swap23 Geo B M L] at h

    exact h

  have hOld :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B E F G)
        (hilbertScissorsTriangle Geo G F B +
         hilbertScissorsTriangle Geo B F E) := by

    unfold hilbertParallelogramTerm

    rw [scissors_triangle_swap12 Geo G F B,
        scissors_triangle_swap23 Geo F G B,
        scissors_triangle_swap12 Geo F B G,
        scissors_triangle_swap23 Geo B F E]

    rw [Multiset.add_comm
          (hilbertScissorsTriangle Geo B F G)
          (hilbertScissorsTriangle Geo B E F)]

    exact
      HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo B E F +
         hilbertScissorsTriangle Geo B F G)

  exact
    equicomplementable_transport
      Geo
      hNew
      hOld
      h43

/--
In the I.44 configuration the point B lies between G and M:

    G - B - M.

Use BE as separator.

H and G lie on the same side of BE because HG || BE.
K and M lie on the same side of BE because KM || BE.
Since H-B-K, H and K lie on opposite sides of BE.

Therefore G and M lie on opposite sides of BE.
Their carrier is GBM, and B lies on BE, so B is the crossing point.
-/
theorem i44_order_GBM
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B E F G H K M : Geo.Point)
    (hHGF : Geo.Between H G F)
    (hHBK : Geo.Between H B K)
    (hPar : IsParallelogram Geo B E F G)
    (hBMKE : IsParallelogram Geo B M K E)
    (hGBM : Collinear Geo G B M) :
    Geo.Between G B M := by

  have hHGFData :=
    HilbertOrder.between_incidence
      H G F hHGF

  have hBE : B ≠ E :=
    hPar.1.1

  --------------------------------------------------------------------
  -- HG || BE.
  --------------------------------------------------------------------

  have hHG : H ≠ G :=
    hHGFData.1

  have hHFG :
      Collinear Geo H F G :=
    PrimCollinearRotate
      Geo H G F
      hHGFData.2.2.2.1

  have hParFG_BE :
      Geo.Parallel F G B E :=
    ParallelSymmetry
      Geo B E F G hPar.1

  have hParHG_BE :
      Geo.Parallel H G B E :=
    ParallelCollinearLeft
      Geo
      F G H
      B E
      hHG
      hParFG_BE
      hHFG

  --------------------------------------------------------------------
  -- H and G are on the same side of BE.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo H G B E hParHG_BE
    with
    ⟨lineBE,
      hBlineBE,
      hElineBE,
      hHGSame⟩

  --------------------------------------------------------------------
  -- KM || BE from the second diagonal parallelogram BMKE.
  --------------------------------------------------------------------

  have hParKM_EB :
      Geo.Parallel K M E B :=
    ParallelSwapFirstLine
      Geo M K E B hBMKE.2

  have hParKM_BE :
      Geo.Parallel K M B E :=
    ParallelSwapSecondLine
      Geo K M E B hParKM_EB

  --------------------------------------------------------------------
  -- K and M are on the same side of BE.
  --------------------------------------------------------------------

  rcases
      parallel_endpoints_sameSide
        Geo K M B E hParKM_BE
    with
    ⟨lineBE',
      hBlineBE',
      hElineBE',
      hKMSame'⟩

  have hLineBE :
      lineBE = lineBE' :=
    HilbertPlaneIncidence.line_unique
      B E hBE
      lineBE lineBE'
      hBlineBE hElineBE
      hBlineBE' hElineBE'

  have hKMSame :
      HilbertSameSide Geo K M lineBE := by
    rw [hLineBE]
    exact hKMSame'

  --------------------------------------------------------------------
  -- H-B-K makes H and K opposite with respect to BE.
  --------------------------------------------------------------------

  have hHoffBE :
      Not (HilbertIncidence.OnLine H lineBE) :=
    hHGSame.1

  have hKoffBE :
      Not (HilbertIncidence.OnLine K lineBE) :=
    hKMSame.1

  have hHKOpp :
      HilbertOppositeSide Geo H K lineBE :=
    ⟨hHoffBE,
     hKoffBE,
     ⟨B, hHBK, hBlineBE⟩⟩

  --------------------------------------------------------------------
  -- Move H to G, and K to M.
  --------------------------------------------------------------------

  have hKHOpp :
      HilbertOppositeSide Geo K H lineBE :=
    hilbert_oppositeSide_symm
      Geo H K lineBE hHKOpp

  have hKGOpp :
      HilbertOppositeSide Geo K G lineBE :=
    hilbert_oppositeSide_transport_right
      Geo
      K H G
      lineBE
      hKHOpp
      hHGSame

  have hGKOpp :
      HilbertOppositeSide Geo G K lineBE :=
    hilbert_oppositeSide_symm
      Geo K G lineBE hKGOpp

  have hGMOpp :
      HilbertOppositeSide Geo G M lineBE :=
    hilbert_oppositeSide_transport_right
      Geo
      G K M
      lineBE
      hGKOpp
      hKMSame

  --------------------------------------------------------------------
  -- Let X be the crossing point of GM with BE.
  --------------------------------------------------------------------

  rcases hGMOpp.2.2 with
    ⟨X, hGXM, hXlineBE⟩

  --------------------------------------------------------------------
  -- X also lies on the carrier GBM.
  --------------------------------------------------------------------

  rcases hGBM with
    ⟨lineGBM,
      hGlineGBM,
      hBlineGBM,
      hMlineGBM⟩

  have hXlineGBM :
      HilbertIncidence.OnLine X lineGBM :=
    hilbert_between_on_line
      Geo G X M
      lineGBM
      hGlineGBM hMlineGBM
      hGXM

  --------------------------------------------------------------------
  -- B is the unique intersection of GBM and BE.
  --------------------------------------------------------------------

  have hGoffBE :
      Not (HilbertIncidence.OnLine G lineBE) :=
    hHGSame.2.1

  have hXB :
      X = B := by

    by_contra hXB

    have hEq :
        lineGBM = lineBE :=
      HilbertPlaneIncidence.line_unique
        X B hXB
        lineGBM lineBE
        hXlineGBM hBlineGBM
        hXlineBE hBlineBE

    apply hGoffBE

    rw [← hEq]

    exact hGlineGBM

  subst X

  exact hGXM

/--
The positioned content core of Euclid I.44.

Starting from

    A-B-E

and a parallelogram BEFG, construct a parallelogram ABML on the
prescribed base AB having the same scissors content as BEFG.

All geometric construction has already been isolated in the preceding
lemmas.  This theorem only assembles those pieces and invokes I.43
through `i44_i43_content_bridge`.
-/
theorem i44_positioned_content
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G : Geo.Point)
    (hABE : Geo.Between A B E)
    (hPar : IsParallelogram Geo B E F G) :
        ∃ M L : Geo.Point,
      IsParallelogram Geo A B M L ∧
      Geo.Between G B M ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B M L)
        (hilbertParallelogramTerm Geo B E F G) := by

  --------------------------------------------------------------------
  -- Construct H with H-G-F and AH || GB.
  --------------------------------------------------------------------

  rcases
      i44_construct_H_ordered
        Geo A B E F G
        hABE hPar
    with
    ⟨H, hHGF, hAH_GB⟩

  --------------------------------------------------------------------
  -- Construct K with H-B-K and F-E-K.
  --------------------------------------------------------------------

  rcases
      i44_construct_K_ordered
        Geo A B E F G H
        hABE hPar hHGF hAH_GB
    with
    ⟨K, hHBK, hFEK⟩

  --------------------------------------------------------------------
  -- Construct the transversal through K and its intersections L,M.
  --------------------------------------------------------------------

  rcases
      i44_construct_LM
        Geo A B E F G H K
        hABE hHGF hFEK
        hPar hAH_GB
    with
    ⟨Q, L, M,
      hKQ,
      hParBE_KQ,
      hHALcol,
      hGBM,
      hKQL,
      hKQM,
      hLKMcol⟩

  --------------------------------------------------------------------
  -- Recover the remaining order relations.
  --------------------------------------------------------------------

  have hHAL :
      Geo.Between H A L :=
    i44_order_HAL
      Geo
      A B E F G H K Q L
      hABE
      hHGF
      hHBK
      hPar
      hAH_GB
      hKQ
      hParBE_KQ
      hHALcol
      hKQL

  have hLMK :
      Geo.Between L M K :=
    i44_order_LMK
      Geo
      A B E F G H K L M
      hHBK
      hHAL
      hFEK
      hPar
      hAH_GB
      hGBM
      hLKMcol

  --------------------------------------------------------------------
  -- The two diagonal parallelograms.
  --------------------------------------------------------------------

  have hHABG :
      IsParallelogram Geo H A B G :=
    i44_first_diagonal_parallelogram
      Geo
      A B E F G H
      hABE
      hHGF
      hPar
      hAH_GB

  have hBMKE :
      IsParallelogram Geo B M K E :=
    i44_second_diagonal_parallelogram
      Geo
      B E F G K Q L M
      hFEK
      hLMK
      hPar
      hKQ
      hParBE_KQ
      hGBM
      hKQM

  have hGBMOrder :
      Geo.Between G B M :=
    i44_order_GBM
      Geo
      B E F G H K M
      hHGF
      hHBK
      hPar
      hBMKE
      hGBM

  --------------------------------------------------------------------
  -- The large parallelogram HLKF.
  --------------------------------------------------------------------

  have hBig :
      IsParallelogram Geo H L K F :=
    i44_big_parallelogram
      Geo
      A B E F G H K Q L M
      hABE
      hHGF
      hFEK
      hHAL
      hLMK
      hPar
      hAH_GB
      hParBE_KQ
      hKQL

  --------------------------------------------------------------------
  -- The target parallelogram ABML.
  --------------------------------------------------------------------

  have hABML :
      IsParallelogram Geo A B M L :=
    i44_target_parallelogram
      Geo
      A B E G H K L M
      hABE
      hHAL
      hLMK
      hAH_GB
      hGBM
      hBMKE

  --------------------------------------------------------------------
  -- I.43 identifies ABML with the original BEFG in scissors content.
  --------------------------------------------------------------------

  have hContent :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B M L)
        (hilbertParallelogramTerm Geo B E F G) :=
    i44_i43_content_bridge
      Geo
      A B E F G H K L M
      hBig
      hHBK
      hHAL
      hHGF
      hLMK
      hFEK
      hHABG
      hBMKE
      hABML

  exact
    ⟨M, L, hABML, hGBMOrder, hContent⟩

/-
The content step in Euclid I.44.

Assume the full I.43 configuration occurring in Euclid's construction:

  big parallelogram: H L K F
  diagonal:          H - B - K

  first diagonal parallelogram:  H A B G
  second diagonal parallelogram: B M K E

Then I.43 identifies the two complements:

  A L M B   and   G B E F.

The first is the new parallelogram ABML and the second is the
original parallelogram BEFG.
-/
/-
theorem i44_i43_content_bridge
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G H K L M : Geo.Point)
    (hBig : IsParallelogram Geo H L K F)
    (hHBK : Geo.Between H B K)
    (hHAL : Geo.Between H A L)
    (hHGF : Geo.Between H G F)
    (hLMK : Geo.Between L M K)
    (hFEK : Geo.Between F E K)
    (hHABG : IsParallelogram Geo H A B G)
    (hBMKE : IsParallelogram Geo B M K E)
    (hABML : IsParallelogram Geo A B M L) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo A B M L)
      (hilbertParallelogramTerm Geo B E F G) := by

  --------------------------------------------------------------------
  -- I.43 on the large parallelogram HLKF with diagonal HK.
  --
  -- Mapping from I.43:
  --
  --   A B C D K G E F H
  --   H L K F B A G M E
  --
  -- The complements returned by I.43 are therefore:
  --
  --   ALB + BLM
  --   GFB + BFE
  --------------------------------------------------------------------

  have h43 :=
    euclid_proposition_43
      Geo
      H L K F
      B
      A G M E
      hBig
      hHBK
      hHAL
      hHGF
      hLMK
      hFEK
      hHABG
      hBMKE

  --------------------------------------------------------------------
  -- The first complement is the alternate triangulation of ABML.
  --------------------------------------------------------------------

  have hNew :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo A B M L)
        (hilbertScissorsTriangle Geo A L B +
         hilbertScissorsTriangle Geo B L M) := by

    have h :=
      parallelogram_two_triangulations
        Geo A B M L hABML

    rw [scissors_triangle_swap23 Geo A B L,
        scissors_triangle_swap23 Geo B M L] at h

    exact h

  --------------------------------------------------------------------
  -- The second complement is just the standard triangulation of BEFG,
  -- with triangle vertices and the two summands reordered.
  --------------------------------------------------------------------

  have hOld :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B E F G)
        (hilbertScissorsTriangle Geo G F B +
         hilbertScissorsTriangle Geo B F E) := by

    unfold hilbertParallelogramTerm

    rw [scissors_triangle_swap12 Geo G F B,
        scissors_triangle_swap23 Geo F G B,
        scissors_triangle_swap12 Geo F B G,
        scissors_triangle_swap23 Geo B F E]

    rw [Multiset.add_comm
          (hilbertScissorsTriangle Geo B F G)
          (hilbertScissorsTriangle Geo B E F)]

    exact
      HilbertScissorsEq.refl
        (Geo := Geo)
        (hilbertScissorsTriangle Geo B E F +
         hilbertScissorsTriangle Geo B F G)

  --------------------------------------------------------------------
  -- Replace I.43's two explicit complement triangulations by the
  -- parallelogram terms.
  --------------------------------------------------------------------

  exact
    equicomplementable_transport
      Geo
      hNew
      hOld
      h43
-/
/-
The positioned content core of Euclid I.44.

Starting from

    A-B-E

and a parallelogram BEFG, construct a parallelogram ABML on the
prescribed base AB having the same scissors content as BEFG.

All geometric construction has already been isolated in the preceding
lemmas.  This theorem only assembles those pieces and invokes I.43
through `i44_i43_content_bridge`.
-/
/-
theorem i44_positioned_content
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E F G : Geo.Point)
    (hABE : Geo.Between A B E)
    (hPar : IsParallelogram Geo B E F G) :
    ∃ M L : Geo.Point,
      IsParallelogram Geo A B M L ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B M L)
        (hilbertParallelogramTerm Geo B E F G) := by

  --------------------------------------------------------------------
  -- Construct H with H-G-F and AH || GB.
  --------------------------------------------------------------------

  rcases
      i44_construct_H_ordered
        Geo A B E F G
        hABE hPar
    with
    ⟨H, hHGF, hAH_GB⟩

  --------------------------------------------------------------------
  -- Construct K with H-B-K and F-E-K.
  --------------------------------------------------------------------

  rcases
      i44_construct_K_ordered
        Geo A B E F G H
        hABE hPar hHGF hAH_GB
    with
    ⟨K, hHBK, hFEK⟩

  --------------------------------------------------------------------
  -- Construct the transversal through K and its intersections L,M.
  --------------------------------------------------------------------

  rcases
      i44_construct_LM
        Geo A B E F G H K
        hABE hHGF hFEK
        hPar hAH_GB
    with
    ⟨Q, L, M,
      hKQ,
      hParBE_KQ,
      hHALcol,
      hGBM,
      hKQL,
      hKQM,
      hLKMcol⟩

  --------------------------------------------------------------------
  -- Recover the remaining order relations.
  --------------------------------------------------------------------

  have hHAL :
      Geo.Between H A L :=
    i44_order_HAL
      Geo
      A B E F G H K Q L
      hABE
      hHGF
      hHBK
      hPar
      hAH_GB
      hKQ
      hParBE_KQ
      hHALcol
      hKQL

  have hLMK :
      Geo.Between L M K :=
    i44_order_LMK
      Geo
      A B E F G H K L M
      hHBK
      hHAL
      hFEK
      hPar
      hAH_GB
      hGBM
      hLKMcol

  --------------------------------------------------------------------
  -- The two diagonal parallelograms.
  --------------------------------------------------------------------

  have hHABG :
      IsParallelogram Geo H A B G :=
    i44_first_diagonal_parallelogram
      Geo
      A B E F G H
      hABE
      hHGF
      hPar
      hAH_GB

  have hBMKE :
      IsParallelogram Geo B M K E :=
    i44_second_diagonal_parallelogram
      Geo
      B E F G K Q L M
      hFEK
      hLMK
      hPar
      hKQ
      hParBE_KQ
      hGBM
      hKQM

  --------------------------------------------------------------------
  -- The large parallelogram HLKF.
  --------------------------------------------------------------------

  have hBig :
      IsParallelogram Geo H L K F :=
    i44_big_parallelogram
      Geo
      A B E F G H K Q L M
      hABE
      hHGF
      hFEK
      hHAL
      hLMK
      hPar
      hAH_GB
      hParBE_KQ
      hKQL

  --------------------------------------------------------------------
  -- The target parallelogram ABML.
  --------------------------------------------------------------------

  have hABML :
      IsParallelogram Geo A B M L :=
    i44_target_parallelogram
      Geo
      A B E G H K L M
      hABE
      hHAL
      hLMK
      hAH_GB
      hGBM
      hBMKE

  --------------------------------------------------------------------
  -- I.43 identifies ABML with the original BEFG in scissors content.
  --------------------------------------------------------------------

  have hContent :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo A B M L)
        (hilbertParallelogramTerm Geo B E F G) :=
    i44_i43_content_bridge
      Geo
      A B E F G H K L M
      hBig
      hHBK
      hHAL
      hHGF
      hLMK
      hFEK
      hHABG
      hBMKE
      hABML

  exact
    ⟨M, L, hABML, hContent⟩
-/



/--
The angle transfer in Euclid I.44.

From

    A - B - E
    G - B - M

the angles ABM and EBG are vertical. Hence if EBG is congruent to
the prescribed angle XYZ, then so is ABM.
-/
theorem i44_angle_transfer
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B E G L M X Y Z : Geo.Point)
    (hABE : Geo.Between A B E)
    (hGBM : Geo.Between G B M)
    (hABML : IsParallelogram Geo A B M L)
    (hAngle : Geo.AngleCongruent E B G X Y Z) :
    Geo.AngleCongruent A B M X Y Z := by

  --------------------------------------------------------------------
  -- ABM is nondegenerate.
  --------------------------------------------------------------------

  have hABM :
      Not (Collinear Geo A B M) := by

    intro hCol

    rcases hCol with
      ⟨lineABM,
        hAlineABM,
        hBlineABM,
        hMlineABM⟩

    have hBM : B ≠ M :=
      hABML.2.1

    have hA_BM :
        A ∈ Geo.PointLine B M :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B M A
        lineABM
        hBM
        hBlineABM hMlineABM).mpr
        hAlineABM

    exact
      Set.disjoint_left.mp
        hABML.2.2.2
        hA_BM
        (intersection_test_right_mem Geo L A)

  --------------------------------------------------------------------
  -- Reverse G-B-M to M-B-G.
  --------------------------------------------------------------------

  have hMBG :
      Geo.Between M B G :=
    (HilbertOrder.between_incidence
      G B M hGBM).2.2.2.2

  --------------------------------------------------------------------
  -- Vertical angles:
  --
  --     ABM ~= EBG.
  --------------------------------------------------------------------

  have hVertical :
      Geo.AngleCongruent A B M E B G :=
    VerticalAngles
      Geo
      A B M E G
      hABE
      hMBG
      hABM

  --------------------------------------------------------------------
  -- Chain with the prescribed angle.
  --------------------------------------------------------------------

  exact
    Geo.angle_congruent_transitivity
      A B M
      E B G
      X Y Z
      hVertical
      hAngle

/--
Rigid placement of the two adjacent sides of a parallelogram.

Given a parallelogram STUV and a nondegenerate segment AB:

1. extend AB beyond B;
2. lay off BE congruent to TS on that ray;
3. copy angle STU at B with first arm BE;
4. lay off BG congruent to TU on the copied angle ray;
5. complete BEG to the parallelogram BEFG.

Thus A-B-E and angle EBG is congruent to angle STU.
-/
theorem i44_place_parallelogram_shape
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B S T U V : Geo.Point)
    (hAB : A ≠ B)
    (hParallelogram : IsParallelogram Geo S T U V) :
    ∃ E F G : Geo.Point,
      Geo.Between A B E ∧
      IsParallelogram Geo B E F G ∧
      Geo.AngleCongruent E B G S T U ∧
      Geo.Congruent B E T S ∧
      Geo.Congruent B G T U := by

  --------------------------------------------------------------------
  -- STU is a genuine triangle.
  --------------------------------------------------------------------

  have hSTU :
      Not (Collinear Geo S T U) := by

    intro hCol

    rcases hCol with
      ⟨lineSTU,
        hSlineSTU,
        hTlineSTU,
        hUlineSTU⟩

    have hST : S ≠ T :=
      hParallelogram.1.1

    have hU_ST :
        U ∈ Geo.PointLine S T :=
      (hilbert_mem_pointLine_iff_onLine
        Geo S T U
        lineSTU
        hST
        hSlineSTU hTlineSTU).mpr
        hUlineSTU

    exact
      Set.disjoint_left.mp
        hParallelogram.1.2.2
        hU_ST
        (intersection_test_left_mem Geo U V)

  --------------------------------------------------------------------
  -- Extend AB beyond B.
  --------------------------------------------------------------------

  rcases
      HilbertOrder.between_extension
        A B hAB
    with
    ⟨R, hABR⟩

  have hABRData :=
    HilbertOrder.between_incidence
      A B R hABR

  have hBR : B ≠ R :=
    hABRData.2.1

  --------------------------------------------------------------------
  -- Lay off TS on ray BR.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        T S
        B R
        hBR
    with
    ⟨E, hRayBRE, hBE_TS⟩

  have hBE : B ≠ E :=
    Ne.symm hRayBRE.2.1

  have hEB : E ≠ B :=
    hRayBRE.2.1

  --------------------------------------------------------------------
  -- Because R and E are on the same ray from B, A-B-E.
  --------------------------------------------------------------------

  have hRayBAA :
      HilbertSameRay Geo B A A :=
    hilbert_sameRay_refl
      Geo B A hAB

  have hABE :
      Geo.Between A B E :=
    hilbert_between_transport_sameRays
      Geo
      A B R
      A E
      hABR
      hRayBAA
      hRayBRE

  --------------------------------------------------------------------
  -- Carrier BE.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        B E hBE
    with
    ⟨lineBE, hBlineBE, hElineBE⟩

  --------------------------------------------------------------------
  -- Choose a side of BE on which to construct the copied angle.
  --------------------------------------------------------------------

  rcases
      hilbert_point_off_line
        Geo lineBE
    with
    ⟨W, hWoffBE⟩

  --------------------------------------------------------------------
  -- Copy angle STU at B, with first arm BE.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        S T U
        E B W
        hSTU
        hEB
        lineBE
        hElineBE
        hBlineBE
        hWoffBE
    with
    ⟨D, hDWSame, hAngleD, _⟩

  have hBD : B ≠ D := by

    intro hEq
    subst D

    exact
      hDWSame.1 hBlineBE

  --------------------------------------------------------------------
  -- Lay off TU on the copied ray BD.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        T U
        B D
        hBD
    with
    ⟨G, hRayBDG, hBG_TU⟩

  have hBG : B ≠ G :=
    Ne.symm hRayBDG.2.1

  --------------------------------------------------------------------
  -- Replacing D by G on the same ray does not change the angle.
  --------------------------------------------------------------------

  have hAngleEq :
      Geo.Angle E B D =
      Geo.Angle E B G :=
    hilbert_angle_eq_of_sameRay_second
      Geo
      B E D G
      hRayBDG

  have hSTU_EBG :
      Geo.AngleCongruent S T U E B G := by

    unfold Geometry.Geo.AngleCongruent
      at hAngleD ⊢

    rw [← hAngleEq]

    exact hAngleD

  have hEBG_STU :
      Geo.AngleCongruent E B G S T U :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      S T U
      E B G
      hSTU_EBG

  --------------------------------------------------------------------
  -- G is off BE.
  --------------------------------------------------------------------

  have hGoffBE :
      Not (HilbertIncidence.OnLine G lineBE) := by

    intro hGlineBE

    rcases hRayBDG.2.2.1 with
      ⟨lineBDG,
        hBlineBDG,
        hDlineBDG,
        hGlineBDG⟩

    have hLineEq :
        lineBDG = lineBE :=
      HilbertPlaneIncidence.line_unique
        B G hBG
        lineBDG lineBE
        hBlineBDG hGlineBDG
        hBlineBE hGlineBE

    have hDlineBE :
        HilbertIncidence.OnLine D lineBE := by
      rw [← hLineEq]
      exact hDlineBDG

    exact
      hDWSame.1 hDlineBE

  have hBEG :
      Not (Collinear Geo B E G) :=
    hilbert_not_collinear_of_off_line
      Geo
      B E G
      lineBE
      hBE
      hBlineBE
      hElineBE
      hGoffBE

  --------------------------------------------------------------------
  -- Complete BEG to parallelogram BEFG.
  --------------------------------------------------------------------

  rcases
      hilbert_parallelogram_fourth_vertex_exists
        Geo
        B E G
        hBEG
    with
    ⟨F, hBEFG⟩

  exact
    ⟨E, F, G,
      hABE,
      hBEFG,
      hEBG_STU,
      hBE_TS,
      hBG_TU⟩

/--
A rigidly placed parallelogram has the same scissors content as the
original parallelogram.

The diagonal EG splits BEFG into BEG and EFG.

The first triangle BEG is congruent to TSU by SAS.
The second triangle EFG is congruent to SVU by SSS, using opposite
side congruences of the two parallelograms and the already obtained
diagonal congruence EG ~= SU.
-/
theorem i44_placed_parallelogram_content
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B E F G S T U V : Geo.Point)
    (hOriginal : IsParallelogram Geo S T U V)
    (hPlaced : IsParallelogram Geo B E F G)
    (hAngle : Geo.AngleCongruent E B G S T U)
    (hBE_TS : Geo.Congruent B E T S)
    (hBG_TU : Geo.Congruent B G T U) :
    HilbertScissorsEquicomplementable Geo
      (hilbertParallelogramTerm Geo S T U V)
      (hilbertParallelogramTerm Geo B E F G) := by

  --------------------------------------------------------------------
  -- Noncollinearity of STU.
  --------------------------------------------------------------------

  have hSTU :
      Not (Collinear Geo S T U) := by

    intro hCol

    rcases hCol with
      ⟨lineSTU,
        hSlineSTU,
        hTlineSTU,
        hUlineSTU⟩

    have hST : S ≠ T :=
      hOriginal.1.1

    have hU_ST :
        U ∈ Geo.PointLine S T :=
      (hilbert_mem_pointLine_iff_onLine
        Geo S T U
        lineSTU
        hST
        hSlineSTU hTlineSTU).mpr
        hUlineSTU

    exact
      Set.disjoint_left.mp
        hOriginal.1.2.2
        hU_ST
        (intersection_test_left_mem Geo U V)

  have hTSU :
      Not (Collinear Geo T S U) := by

    intro h

    exact
      hSTU
        (PrimCollinearSwap
          Geo T S U h)

  --------------------------------------------------------------------
  -- Noncollinearity of BEG.
  --------------------------------------------------------------------

  have hBEG :
      Not (Collinear Geo B E G) := by

    intro hCol

    rcases hCol with
      ⟨lineBEG,
        hBlineBEG,
        hElineBEG,
        hGlineBEG⟩

    have hBE : B ≠ E :=
      hPlaced.1.1

    have hG_BE :
        G ∈ Geo.PointLine B E :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B E G
        lineBEG
        hBE
        hBlineBEG hElineBEG).mpr
        hGlineBEG

    exact
      Set.disjoint_left.mp
        hPlaced.1.2.2
        hG_BE
        (intersection_test_right_mem Geo F G)

  --------------------------------------------------------------------
  -- SAS:
  --
  --     BEG ~= TSU.
  --------------------------------------------------------------------

  have hTri1 :
      TriangleCongruenceResult
        Geo B E G T S U :=
    SAS
      Geo
      B E G
      T S U
      hBEG
      hTSU
      hBE_TS
      hAngle
      hBG_TU

  have hEG_SU :
      Geo.Congruent E G S U :=
    hTri1.sideBC

  --------------------------------------------------------------------
  -- Noncollinearity of EFG.
  --------------------------------------------------------------------

  have hEFG :
      Not (Collinear Geo E F G) := by

    intro hCol

    rcases hCol with
      ⟨lineEFG,
        hElineEFG,
        hFlineEFG,
        hGlineEFG⟩

    have hFG : F ≠ G :=
      hPlaced.1.2.1

    have hE_FG :
        E ∈ Geo.PointLine F G :=
      (hilbert_mem_pointLine_iff_onLine
        Geo F G E
        lineEFG
        hFG
        hFlineEFG hGlineEFG).mpr
        hElineEFG

    exact
      Set.disjoint_left.mp
        hPlaced.1.2.2
        (intersection_test_right_mem Geo B E)
        hE_FG

  --------------------------------------------------------------------
  -- Opposite sides of both parallelograms are congruent.
  --------------------------------------------------------------------

  have hOriginalSides :
      OppositeSidesCongruent Geo S T U V :=
    ParallelogramOppositeSidesCongruent
      Geo S T U V hOriginal

  have hPlacedSides :
      OppositeSidesCongruent Geo B E F G :=
    ParallelogramOppositeSidesCongruent
      Geo B E F G hPlaced

  --------------------------------------------------------------------
  -- EF ~= SV.
  --------------------------------------------------------------------

  have hGB_TU :
      Geo.Congruent G B T U :=
    CongruentReverseFirst
      Geo B G T U hBG_TU

  have hEF_TU :
      Geo.Congruent E F T U :=
    hilbert_congruent_transitivity
      Geo
      E F
      G B
      T U
      hPlacedSides.2
      hGB_TU

  have hTU_SV :
      Geo.Congruent T U S V :=
    CongruentSwapSecond
      Geo T U V S hOriginalSides.2

  have hEF_SV :
      Geo.Congruent E F S V :=
    hilbert_congruent_transitivity
      Geo
      E F
      T U
      S V
      hEF_TU
      hTU_SV

  --------------------------------------------------------------------
  -- FG ~= VU.
  --------------------------------------------------------------------

  have hFG_BE :
      Geo.Congruent F G B E :=
    hilbert_congruent_symmetry
      Geo B E F G hPlacedSides.1

  have hFG_TS :
      Geo.Congruent F G T S :=
    hilbert_congruent_transitivity
      Geo
      F G
      B E
      T S
      hFG_BE
      hBE_TS

  have hTS_VU :
      Geo.Congruent T S V U :=
    CongruentReverseBoth
      Geo S T U V hOriginalSides.1

  have hFG_VU :
      Geo.Congruent F G V U :=
    hilbert_congruent_transitivity
      Geo
      F G
      T S
      V U
      hFG_TS
      hTS_VU

  --------------------------------------------------------------------
  -- SSS:
  --
  --     EFG ~= SVU.
  --------------------------------------------------------------------

  have hSSS :=
    HilbertSSS
      Geo
      E F G
      S V U
      hEFG
      hEF_SV
      hFG_VU
      hEG_SU

  have hTri2 :
      TriangleCongruenceResult
        Geo E F G S V U :=
    hSSS.2

  --------------------------------------------------------------------
  -- Convert the two triangle congruences to scissors equalities.
  --------------------------------------------------------------------

  have hFirst :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B E G)
        (hilbertScissorsTriangle Geo T S U) :=
    scissors_congruent
      Geo
      B E G
      T S U
      hTri1

  have hSecond :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo E F G)
        (hilbertScissorsTriangle Geo S V U) :=
    scissors_congruent
      Geo
      E F G
      S V U
      hTri2

  have hBoth :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B E G +
         hilbertScissorsTriangle Geo E F G)
        (hilbertScissorsTriangle Geo T S U +
         hilbertScissorsTriangle Geo S V U) :=
    HilbertScissorsEq.add
      (Geo := Geo)
      hFirst
      hSecond

  --------------------------------------------------------------------
  -- Reorder the original triangles:
  --
  --     TSU = STU
  --     SVU = SUV.
  --------------------------------------------------------------------

  have hBothOriginal :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B E G +
         hilbertScissorsTriangle Geo E F G)
        (hilbertScissorsTriangle Geo S T U +
         hilbertScissorsTriangle Geo S U V) := by

    rw [scissors_triangle_swap12 Geo S T U,
        scissors_triangle_swap23 Geo S U V]

    exact hBoth

  --------------------------------------------------------------------
  -- Alternate triangulation of BEFG along EG.
  --------------------------------------------------------------------

  have hPlacedAlt :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B E F G)
        (hilbertScissorsTriangle Geo B E G +
         hilbertScissorsTriangle Geo E F G) := by

    unfold hilbertParallelogramTerm

    exact
      parallelogram_two_triangulations
        Geo B E F G hPlaced

  --------------------------------------------------------------------
  -- Therefore BEFG and STUV are scissors equal.
  --------------------------------------------------------------------

  have hPlacedOriginal :
      HilbertScissorsEq Geo
        (hilbertParallelogramTerm Geo B E F G)
        (hilbertParallelogramTerm Geo S T U V) := by

    exact
      HilbertScissorsEq.trans
        (Geo := Geo)
        hPlacedAlt
        hBothOriginal

  --------------------------------------------------------------------
  -- Reverse orientation to match the theorem statement.
  --------------------------------------------------------------------

  exact
    equicomplementable_of_scissorsEq
      Geo
      (HilbertScissorsEq.symm
        (Geo := Geo)
        hPlacedOriginal)

/--
Derived transport step for Euclid I.44.

A congruent copy of STUV is first placed beyond B, then the I.43
construction applies it to the prescribed base AB.
-/
theorem i44_transport_onto_line
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B S T U V X Y Z : Geo.Point)
    (hAB : Not (A = B))
    (hParallelogram : IsParallelogram Geo S T U V)
    (hAngle : Geo.AngleCongruent S T U X Y Z) :
    ∃ M L : Geo.Point,
      IsParallelogram Geo A B M L ∧
      Geo.AngleCongruent A B M X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo S T U V)
        (hilbertParallelogramTerm Geo A B M L) := by

  --------------------------------------------------------------------
  -- Place a congruent copy BEFG beyond B.
  --------------------------------------------------------------------

  rcases
      i44_place_parallelogram_shape
        Geo
        A B S T U V
        hAB
        hParallelogram
    with
    ⟨E, F, G,
      hABE,
      hBEFG,
      hEBG_STU,
      hBE_TS,
      hBG_TU⟩

  --------------------------------------------------------------------
  -- STUV and BEFG have the same scissors content.
  --------------------------------------------------------------------

  have hPlacedContent :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo S T U V)
        (hilbertParallelogramTerm Geo B E F G) :=
    i44_placed_parallelogram_content
      Geo
      B E F G
      S T U V
      hParallelogram
      hBEFG
      hEBG_STU
      hBE_TS
      hBG_TU

  --------------------------------------------------------------------
  -- Apply the positioned I.44 construction.
  --------------------------------------------------------------------

  rcases
      i44_positioned_content
        Geo
        A B E F G
        hABE
        hBEFG
    with
    ⟨M, L,
      hABML,
      hGBM,
      hPositionedContent⟩

  --------------------------------------------------------------------
  -- The placed angle EBG is the prescribed angle XYZ.
  --------------------------------------------------------------------

  have hEBG_XYZ :
      Geo.AngleCongruent E B G X Y Z :=
    Geometry.Geo.angle_congruent_transitivity
      Geo
      E B G
      S T U
      X Y Z
      hEBG_STU
      hAngle

  --------------------------------------------------------------------
  -- Vertical angles transfer EBG to ABM.
  --------------------------------------------------------------------

  have hABM_XYZ :
      Geo.AngleCongruent A B M X Y Z :=
    i44_angle_transfer
      Geo
      A B E G L M X Y Z
      hABE
      hGBM
      hABML
      hEBG_XYZ

  --------------------------------------------------------------------
  -- STUV ~ BEFG ~ ABML.
  --------------------------------------------------------------------

  have hBEFG_ABML :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo B E F G)
        (hilbertParallelogramTerm Geo A B M L) :=
    equicomplementable_symm
      Geo
      hPositionedContent

  have hFinalContent :
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo S T U V)
        (hilbertParallelogramTerm Geo A B M L) :=
    equicomplementable_trans
      Geo
      hPlacedContent
      hBEFG_ABML

  exact
    ⟨M, L,
      hABML,
      hABM_XYZ,
      hFinalContent⟩

/-
Local axiom.

Any parallelogram `S T U V` (with its angle at `T`, namely `∠ S T U`,
recorded) can be transported -- rigidly, preserving area and that
angle -- so that it shares the vertex `B` with a given segment `A B`,
with one side lying along the line `A B`.

This packages Euclid's construction of `H`, `K`, `L`, `M` (I.31,
Postulate 5, I.43, I.15) used in the proof of I.44 to slide the
I.42-parallelogram from its initially unconstrained position onto the
given line.
-/
/-
axiom i44_transport_onto_line
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B S T U V X Y Z : Geo.Point)
    (hAB : Not (A = B))
    (hParallelogram : IsParallelogram Geo S T U V)
    (hAngle : Geo.AngleCongruent S T U X Y Z) :
    ∃ M L : Geo.Point,
      IsParallelogram Geo B A L M ∧
      Geo.AngleCongruent L B A X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertParallelogramTerm Geo S T U V)
        (hilbertParallelogramTerm Geo B A L M)
-/

/--
Euclid I.44.

To a given straight line `AB`, apply, in a given angle `XYZ`, a
parallelogram equal to a given triangle `PQR`.

The resulting parallelogram `ABML` has side `AB`, angle `ABM`
congruent to the prescribed angle `XYZ`, and the same scissors content
as triangle `PQR`.
-/
theorem euclid_proposition_44
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B P Q R X Y Z : Geo.Point)
    (hAB : Not (A = B))
    (hPQR : Not (Collinear Geo P Q R))
    (hXYZ : Not (Collinear Geo X Y Z)) :
    ∃ M L : Geo.Point,
      IsParallelogram Geo A B M L ∧
      Geo.AngleCongruent A B M X Y Z ∧
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo P Q R)
        (hilbertParallelogramTerm Geo A B M L) := by

  --------------------------------------------------------------------
  -- Step 1 [I.42]:
  --
  -- Construct FERG equal in content to triangle PQR, with
  -- angle FER congruent to XYZ.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_42
        Geo P Q R X Y Z
        hPQR hXYZ
    with
    ⟨E, F, G,
      hParallelogram,
      hAngle,
      hEquicomp⟩

  --------------------------------------------------------------------
  -- Steps 2-6:
  --
  -- Apply the derived I.44 transport construction to the prescribed
  -- base AB.
  --------------------------------------------------------------------

  rcases
      i44_transport_onto_line
        Geo
        A B
        F E R G
        X Y Z
        hAB
        hParallelogram
        hAngle
    with
    ⟨M, L,
      hABML,
      hABM_XYZ,
      hTransportContent⟩

  --------------------------------------------------------------------
  -- Step 7:
  --
  -- PQR ~ FERG ~ ABML.
  --------------------------------------------------------------------

  have hFinal :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo P Q R)
        (hilbertParallelogramTerm Geo A B M L) :=
    equicomplementable_trans
      Geo
      hEquicomp
      hTransportContent

  exact
    ⟨M, L,
      hABML,
      hABM_XYZ,
      hFinal⟩

end Geometry

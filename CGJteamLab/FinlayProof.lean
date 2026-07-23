import CGJteamLab.MidsegmentParallel

namespace Geometry

universe u

variable (Geo : Geo)
variable [HilbertIncidence Geo]
variable [HilbertCongruence Geo]


theorem Finlay
  (A B C E F G P D : Geo.Point)
  (hE : HilbertIsMidpoint Geo E A C)
  (hF : HilbertIsMidpoint Geo F A B)
  (hG : HilbertIsMidpoint Geo G A P)
  (hGP : G ≠ P)
  (hBE : Collinear Geo B G E)
  (hCF : Collinear Geo C G F)
  (hAP : Collinear Geo A D P)
  (hBC : Collinear Geo B D C) :
  IsMedian Geo A D B C ∧
  Collinear Geo A G D := by

  have hCFG : Collinear Geo C F G := by
    exact CollinearRotate Geo C G F hCF

  have hBEG : Collinear Geo B E G := by
    exact CollinearRotate Geo B G E hBE

  -- Step 1.
  -- Apply the Midsegment Theorem twice to obtain
  -- CG ∥ BP and BG ∥ CP.

  have hFG : Geo.Parallel F G B P := by
    exact
      MidsegmentTheorem
        Geo
        A B P F G
        hF
        hG

  have hCG : Geo.Parallel C G B P := by
    exact
      ParallelCollinearLeft
        Geo
        F G C
        B P
        hFG
        hCFG

  have hEG : Geo.Parallel E G C P := by
    exact
      MidsegmentTheorem
        Geo
        A C P E G
        hE
        hG

  have hBG : Geo.Parallel B G C P := by
    exact
      ParallelCollinearLeft
        Geo
        E G B
        C P
        hEG
        hBEG

  -- Step 2.
  -- A quadrilateral whose opposite sides are parallel
  -- is a parallelogram.

  have h1 : Geo.Parallel B P C G := by
    exact
      ParallelSymmetry
        Geo
        C G B P
        hCG

  have h2 : Geo.Parallel B G P C := by
    exact
      ParallelSwapSecondLine
        Geo
        B G C P
        hBG

  have hPar : IsParallelogram Geo B P C G := by
    exact
      ParallelogramOfParallel
        Geo
        B P C G
        h1
        h2

  -- G is the midpoint of AP, hence A, G and P are collinear.

  -- Step 3.
-- Since A, G and P are collinear, the same intersection
-- can be regarded as lying on the diagonal PG.

  have hAGP : Collinear Geo A G P := by
    exact
      midpoint_collinear Geo A P G
        (midpoint_of_hilbert Geo G A P hG)

  -- D is assumed to lie on AP and BC,
  -- so it is the intersection of these two lines.
  have hIntAP : IsIntersection Geo A P B C D := by
    exact And.intro hAP hBC

  have hAPne : A ≠ P :=
    (HilbertOrder.between_incidence A G P hG.left).2.2.1

  have hIntPG : IsIntersection Geo P G B C D := by
    exact
    IntersectionOnSameLine
      Geo
      A G P B C D
      hAPne
      hAGP
      hIntAP

-- Step 4.
-- In a parallelogram the diagonals bisect each other,
-- therefore D is the midpoint of BC.
  have hMid : IsMidpoint Geo D B C := by
    exact
    ParallelogramDiagonals
      Geo
      B P C G D
      hPar
      hIntPG.right
      hIntPG.left

--Step 5.
--Complete the proof.
 --The midpoint yields the median AD,
--while the transferred intersection implies
--that G lies on AD.
  have hMedian : IsMedian Geo A D B C := by
    exact
      MidpointMedian
        Geo
        A B C D
        hMid

  -- Extract the collinearity of P, D and G
  -- from the intersection property.
  have hPG : Collinear Geo P D G := by
    exact hIntPG.left

  -- Since A, G, P and P, D, G are collinear,
  -- points A, G and D are collinear.
  have hAGD : Collinear Geo A G D := by
    exact
      CollinearTrans
        Geo
        A G P D
        hGP
        hAGP
        hPG

  -- The line AD is a median and passes through Geo.
  exact And.intro hMedian hAGD


end Geometry

/-
============================================================
Dependency graph of Finlay's proof
============================================================

Step 1. Midsegment geometry

    MidsegmentTheorem
            |
            +--> ParallelCollinearLeft
            |
            +--> ParallelCollinearLeft
            |
            v
      CG ∥ BP   and   BG ∥ CP

                    |
                    v

Step 2. Construct a parallelogram

    ParallelSymmetry
            |
    ParallelSwapSecondLine
            |
    ParallelogramOfParallel
            |
            v
    IsParallelogram B P C G

                    |
                    v

Step 3. Transfer the intersection

    midpoint_collinear
            |
    IntersectionOnSameLine
            |
            v
    D lies on diagonal PG

                    |
                    v

Step 4. Use the parallelogram

    ParallelogramDiagonals
            |
            v
    D is the midpoint of BC

                    |
                    v

Step 5. Conclude

    MidpointMedian -------------> AD is a median

    IntersectionOnSameLine
            |
    CollinearTrans -------------> A, G, D are collinear

                    |
                    v

      Finlay
      = IsMedian A D B C
        ∧ Collinear A G D

============================================================
============================================================
This proof is intentionally organized as a path through the
GeometryBase library.

Each step corresponds to a reusable geometric result from
GeometryBase rather than to a proof-specific lemma. The goal
is to expose the mathematical dependency graph explicitly,
so that different proofs can later be viewed as different
paths through the same geometric theory.
============================================================
============================================================
-/

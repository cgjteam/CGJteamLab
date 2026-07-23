import CGJteamLab.GeometryBase

/-!
# The common upper part of Finlay's proof

The foundational paths differ in how they prove the two applications
of the Midsegment Theorem.  Once the parallelisms `FG ∥ BP` and
`EG ∥ CP` have been obtained, Finlay's remaining argument is identical.

This module contains that argument once.  `FinlayProof`,
`FinlayProofSuppes`, and `FinlayProofTarski` are thin adapters which
produce the two parallelisms and translate their foundational language
to the shared `GeometryBase` interface.
-/

namespace Geometry

universe u

variable (Geo : Geo)
variable [HilbertIncidence Geo]
variable [HilbertOrder Geo]

/--
The foundation-independent upper part of Finlay's five-step argument.

The hypotheses `hFG` and `hEG` are precisely the two facts supplied by
the foundation-specific Midsegment Theorem.  Everything after them is
shared: transport parallelism along the median lines, recognize the
parallelogram `BPCG`, transfer the diagonal intersection, use diagonal
bisection, and conclude that the third median passes through `G`.
-/
theorem FinlayFromMidsegmentParallels
    (A B C E F G P D : Geo.Point)
    (hFG : Geo.Parallel F G B P)
    (hEG : Geo.Parallel E G C P)
    (hAGP : Collinear Geo A G P)
    (hGP : G ≠ P)
    (hAPne : A ≠ P)
    (hCGne : C ≠ G)
    (hBGne : B ≠ G)
    (hBE : Collinear Geo B G E)
    (hCF : Collinear Geo C G F)
    (hAP : Collinear Geo A D P)
    (hBC : Collinear Geo B D C) :
    IsMedian Geo A D B C ∧
    Collinear Geo A G D := by
  -- Step 1. Transport the two midsegment parallelisms from `FG` and
  -- `EG` to the collinear lines `CG` and `BG`.
  have hCFG : Collinear Geo C F G :=
    CollinearRotate Geo C G F hCF
  have hBEG : Collinear Geo B E G :=
    CollinearRotate Geo B G E hBE
  have hCG : Geo.Parallel C G B P :=
    ParallelCollinearLeft Geo F G C B P hCGne hFG hCFG
  have hBG : Geo.Parallel B G C P :=
    ParallelCollinearLeft Geo E G B C P hBGne hEG hBEG

  -- Step 2. The two transported pairs of opposite sides make `BPCG`
  -- a parallelogram.
  have hBP_CG : Geo.Parallel B P C G :=
    ParallelSymmetry Geo C G B P hCG
  have hBG_PC : Geo.Parallel B G P C :=
    ParallelSwapSecondLine Geo B G C P hBG
  have hParallelogram : IsParallelogram Geo B P C G :=
    ParallelogramOfParallel Geo B P C G hBP_CG hBG_PC

  -- Step 3. Since `A`, `G`, and `P` are collinear, the intersection of
  -- `AP` and `BC` is also the intersection of diagonals `PG` and `BC`.
  have hIntersectionAP : IsIntersection Geo A P B C D :=
    ⟨hAP, hBC⟩
  have hIntersectionPG : IsIntersection Geo P G B C D :=
    IntersectionOnSameLine
      Geo A G P B C D hAPne hAGP hIntersectionAP

  -- Step 4. The diagonals of the parallelogram bisect each other.
  have hMidpoint : IsMidpoint Geo D B C :=
    ParallelogramDiagonals
      Geo B P C G D
      hParallelogram
      hIntersectionPG.right
      hIntersectionPG.left

  -- Step 5. The midpoint gives the third median, and collinearity
  -- transitivity shows that this median contains `G`.
  have hMedian : IsMedian Geo A D B C :=
    MidpointMedian Geo A B C D hMidpoint
  have hPG : Collinear Geo P D G :=
    hIntersectionPG.left
  have hAGD : Collinear Geo A G D :=
    CollinearTrans Geo A G P D hGP hAGP hPG

  exact ⟨hMedian, hAGD⟩

end Geometry


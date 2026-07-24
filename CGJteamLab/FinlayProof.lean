import CGJteamLab.MidsegmentParallel

/-!
# Finlay's Synthetic Proof

This file is the formal pseudocode of Finlay's five-step proof that
the three medians of a triangle are concurrent.  Its organization
deliberately follows `log-001.md`: every mathematical step is visible
here and is discharged by a reusable result from the lower geometry
layers.
-/

namespace Geometry

universe u

variable (Geo : Geo)
variable [HilbertIncidence Geo]
variable [HilbertEuclideanPlane Geo]

/--
Finlay's synthetic proof in the Hilbert path.

`E` and `F` are the midpoints of `AC` and `AB`; `G` lies on the
medians through `B` and `C`; `P` is chosen so that `G` is the midpoint
of `AP`; and `D` is the intersection of `AP` and `BC`.
-/
theorem Finlay
    (A B C E F G P D : Geo.Point)
    (hE : HilbertIsMidpoint Geo E A C)
    (hF : HilbertIsMidpoint Geo F A B)
    (hG : HilbertIsMidpoint Geo G A P)
    (hGFA : ¬ Collinear Geo G F A)
    (hGEA : ¬ Collinear Geo G E A)
    (hGP : G ≠ P)
    (hBE : Collinear Geo B G E)
    (hCF : Collinear Geo C G F)
    (hAP : Collinear Geo A D P)
    (hBC : Collinear Geo B D C) :
    IsMedian Geo A D B C ∧
    Collinear Geo A G D := by

  -- Step 1.
  -- Apply the Midsegment Theorem in triangles `ABP` and `ACP`.
  -- It gives `FG ∥ BP` and `EG ∥ CP`; because `C,F,G` and `B,E,G`
  -- are collinear, these parallelisms transport to
  -- `CG ∥ BP` and `BG ∥ CP`.

  have hCFG : Collinear Geo C F G := by
    exact CollinearRotate Geo C G F hCF

  have hBEG : Collinear Geo B E G := by
    exact CollinearRotate Geo B G E hBE

  have hCGne : C ≠ G := by
    intro hCG
    subst C
    exact
      hGEA
        (PrimCollinearSymm Geo A E G
          (HilbertOrder.between_incidence
            A E G hE.left).2.2.2.1)

  have hBGne : B ≠ G := by
    intro hBG
    subst B
    exact
      hGFA
        (PrimCollinearSymm Geo A F G
          (HilbertOrder.between_incidence
            A F G hF.left).2.2.2.1)

  have hFG : Geo.Parallel F G B P := by
    exact
      MidsegmentTheorem
        Geo
        A B P F G
        hF
        hG
        hGFA

  have hCG : Geo.Parallel C G B P := by
    exact
      ParallelCollinearLeft
        Geo
        F G C
        B P
        hCGne
        hFG
        hCFG

  have hEG : Geo.Parallel E G C P := by
    exact
      MidsegmentTheorem
        Geo
        A C P E G
        hE
        hG
        hGEA

  have hBG : Geo.Parallel B G C P := by
    exact
      ParallelCollinearLeft
        Geo
        E G B
        C P
        hBGne
        hEG
        hBEG

  -- Step 2.
  -- Since `CG ∥ BP` and `BG ∥ CP`, both pairs of opposite sides of
  -- the quadrilateral `BPCG` are parallel.  Hence `BPCG` is a
  -- parallelogram.

  have hBP_CG : Geo.Parallel B P C G := by
    exact
      ParallelSymmetry
        Geo
        C G B P
        hCG

  have hBG_PC : Geo.Parallel B G P C := by
    exact
      ParallelSwapSecondLine
        Geo
        B G C P
        hBG

  have hParallelogram : IsParallelogram Geo B P C G := by
    exact
      ParallelogramOfParallel
        Geo
        B P C G
        hBP_CG
        hBG_PC

  -- Step 3.
  -- Since `G` is the midpoint of `AP`, the points `A,G,P` are
  -- collinear.  Therefore the given intersection `D = AP ∩ BC` can
  -- also be viewed as the intersection of the diagonals `PG` and
  -- `BC` of the parallelogram `BPCG`.

  have hAGP : Collinear Geo A G P := by
    exact
      midpoint_collinear Geo A P G
        (midpoint_of_hilbert Geo G A P hG)

  have hIntersectionAP : IsIntersection Geo A P B C D := by
    exact And.intro hAP hBC

  have hAPne : A ≠ P :=
    (HilbertOrder.between_incidence
      A G P hG.left).2.2.1

  have hIntersectionPG : IsIntersection Geo P G B C D := by
    exact
      IntersectionOnSameLine
        Geo
        A G P B C D
        hAPne
        hAGP
        hIntersectionAP

  -- Step 4.
  -- The diagonals of a parallelogram bisect each other.  Therefore
  -- their intersection `D` is the midpoint of `BC`, and `AD` is a
  -- median of triangle `ABC`.

  have hMidpoint : IsMidpoint Geo D B C := by
    exact
      ParallelogramDiagonals
        Geo
        B P C G D
        hParallelogram
        hIntersectionPG.right
        hIntersectionPG.left

  have hMedian : IsMedian Geo A D B C := by
    exact
      MidpointMedian
        Geo
        A B C D
        hMidpoint

  -- Step 5.
  -- The transferred intersection says that `P,D,G` are collinear.
  -- Together with `A,G,P`, this implies that `A,G,D` are collinear.
  -- Thus the third median `AD` passes through `G`.

  have hPG : Collinear Geo P D G := by
    exact hIntersectionPG.left

  have hAGD : Collinear Geo A G D := by
    exact
      CollinearTrans
        Geo
        A G P D
        hGP
        hAGP
        hPG

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

Step 2. Recognize a parallelogram

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
This proof is intentionally organized as a path through the
GeometryBase library.

Each step corresponds to a reusable geometric result from
GeometryBase rather than to a proof-specific lemma.  The goal is to
expose the mathematical dependency graph explicitly, so that changing
the foundational path does not obscure the pseudocode of Finlay's
mathematical argument.
============================================================
-/

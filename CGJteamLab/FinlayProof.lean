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

For every triangle `ABC`, there exist three medians and a point common
to all of them.  The proof constructs the midpoints `E` and `F`, their
median intersection `G`, the auxiliary point `P`, and finally the
intersection `D = AP ∩ BC`; none of these points is assumed.
-/
theorem Finlay
    (A B C : Geo.Point)
    (hABC : ¬ Collinear Geo A B C) :
    ∃ E F G D : Geo.Point,
      IsMedian Geo B E A C ∧
      IsMedian Geo C F A B ∧
      Collinear Geo B G E ∧
      Collinear Geo C G F ∧
      IsMedian Geo A D B C ∧
      Collinear Geo A G D := by

  ------------------------------------------------------------------------
  -- Finlay's construction.
  ------------------------------------------------------------------------

  -- Since `ABC` is a triangle, its sides are nondegenerate.  Hilbert's
  -- midpoint construction supplies the first two medians.

  have hACB : ¬ Collinear Geo A C B := by
    intro h
    exact hABC (PrimCollinearRotate Geo A C B h)

  have hAB : A ≠ B :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hAC : A ≠ C :=
    hilbert_noncollinear_ne_first
      Geo A C B hACB

  rcases HilbertMidpointExists Geo A C hAC with
    ⟨E, hE⟩

  rcases HilbertMidpointExists Geo A B hAB with
    ⟨F, hF⟩

  -- Inner Pasch applied to triangle `BAE` shows that the two median
  -- segments `BE` and `CF` meet.  Their intersection is `G`.

  have hEData :=
    HilbertOrder.between_incidence A E C hE.left

  have hFData :=
    HilbertOrder.between_incidence A F B hF.left

  have hBAE : ¬ Collinear Geo B A E := by
    intro h
    have hBAC : Collinear Geo B A C :=
      hilbert_primCollinear_trans
        Geo B A E C hEData.1
        h hEData.2.2.2.1
    exact hABC (PrimCollinearSwap Geo B A C hBAC)

  have hBFA : Geo.Between B F A :=
    hFData.2.2.2.2

  rcases hilbert_inner_pasch_strong
      Geo B A E C F
      hBAE hE.left hBFA with
    ⟨G, hCGFbetween, hBGEbetween⟩

  have hCF : Collinear Geo C G F :=
    (HilbertOrder.between_incidence
      C G F hCGFbetween).2.2.2.1

  have hBE : Collinear Geo B G E :=
    (HilbertOrder.between_incidence
      B G E hBGEbetween).2.2.2.1

  -- The two small triangles used in Step 1 are genuine triangles.
  -- These facts follow from the original noncollinearity of `ABC`;
  -- they are not extra hypotheses of Finlay's theorem.

  have hCGFData :=
    HilbertOrder.between_incidence
      C G F hCGFbetween

  have hBGEData :=
    HilbertOrder.between_incidence
      B G E hBGEbetween

  have hGFA : ¬ Collinear Geo G F A := by
    rintro ⟨lineGF, hGgf, hFgf, hAgf⟩
    rcases hCF with
      ⟨lineCF, hCcf, hGcf, hFcf⟩
    have hLinesGF :
        lineGF = lineCF :=
      HilbertPlaneIncidence.line_unique
        G F hCGFData.2.1
        lineGF lineCF
        hGgf hFgf hGcf hFcf
    have hCgf : HilbertIncidence.OnLine C lineGF := by
      rw [hLinesGF]
      exact hCcf
    rcases hFData.2.2.2.1 with
      ⟨lineAB, hAab, hFab, hBab⟩
    have hLinesAB :
        lineGF = lineAB :=
      HilbertPlaneIncidence.line_unique
        A F hFData.1
        lineGF lineAB
        hAgf hFgf hAab hFab
    have hBgf : HilbertIncidence.OnLine B lineGF := by
      rw [hLinesAB]
      exact hBab
    exact hABC ⟨lineGF, hAgf, hBgf, hCgf⟩

  have hGEA : ¬ Collinear Geo G E A := by
    rintro ⟨lineGE, hGge, hEge, hAge⟩
    rcases hBE with
      ⟨lineBE, hBbe, hGbe, hEbe⟩
    have hLinesGE :
        lineGE = lineBE :=
      HilbertPlaneIncidence.line_unique
        G E hBGEData.2.1
        lineGE lineBE
        hGge hEge hGbe hEbe
    have hBge : HilbertIncidence.OnLine B lineGE := by
      rw [hLinesGE]
      exact hBbe
    rcases hEData.2.2.2.1 with
      ⟨lineAC, hAac, hEac, hCac⟩
    have hLinesAC :
        lineGE = lineAC :=
      HilbertPlaneIncidence.line_unique
        A E hEData.1
        lineGE lineAC
        hAge hEge hAac hEac
    have hCge : HilbertIncidence.OnLine C lineGE := by
      rw [hLinesAC]
      exact hCac
    exact hABC ⟨lineGE, hAge, hBge, hCge⟩

  -- Choose `P` beyond `G` on `AG`, with `AG ≅ GP`.  Thus `G` is the
  -- strict midpoint of `AP`, exactly as in Finlay's construction.

  have hAG : A ≠ G := by
    intro h
    subst G
    rcases hFData.2.2.2.1 with
      ⟨lineAB, hAab, hFab, _⟩
    exact hGFA ⟨lineAB, hAab, hFab, hAab⟩

  rcases ExtendSegmentBeyond Geo A G hAG with
    ⟨P, hAGPbetween, hAG_GP⟩

  have hG : HilbertIsMidpoint Geo G A P :=
    ⟨hAGPbetween, hAG_GP⟩

  have hAGP : Collinear Geo A G P :=
    (HilbertOrder.between_incidence
      A G P hAGPbetween).2.2.2.1

  have hGP : G ≠ P :=
    (HilbertOrder.between_incidence
      A G P hAGPbetween).2.1

  -- Step 1.
  -- Apply the Midsegment Theorem in triangles `ABP` and `ACP`.
  -- It gives `FG ∥ BP` and `EG ∥ CP`; because `C,F,G` and `B,E,G`
  -- are collinear, these parallelisms transport to
  -- `CG ∥ BP` and `BG ∥ CP`.

  have hCFG : Collinear Geo C F G := by
    exact CollinearRotate Geo C G F hCF

  have hBEG : Collinear Geo B E G := by
    exact CollinearRotate Geo B G E hBE

  have hCGne : C ≠ G :=
    hCGFData.1

  have hBGne : B ≠ G :=
    hBGEData.1

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
  -- The diagonal-crossing theorem now *constructs* `D`; no
  -- intersection point is assumed.  It gives `B-D-C` and `P-D-G`.
  -- Since `A-G-P`, Theorem 5 yields `A-D-P`.  Consequently `D`
  -- belongs to the ray `AP`: this is the formal version of the
  -- geometric statement that the ray `AP` cuts the side `BC`.

  rcases ParallelogramDiagonalIntersectionExists
      Geo B P C G hParallelogram with
    ⟨D, hBDCbetween, hPDGbetween⟩

  have hPGA : Geo.Between P G A :=
    (HilbertOrder.between_incidence
      A G P hAGPbetween).2.2.2.2

  have hPDA : Geo.Between P D A :=
    (hilbert_between_inner_trans
      Geo P D G A hPDGbetween hPGA).2

  have hADP : Geo.Between A D P :=
    (HilbertOrder.between_incidence
      P D A hPDA).2.2.2.2

  have hDOnRayAP : HilbertSameRay Geo A P D :=
    hilbert_sameRay_symm
      Geo A D P
      (hilbert_sameRay_of_between
        Geo A D P hADP)

  have hAP : Collinear Geo A D P :=
    PrimCollinearRotate
      Geo A P D hDOnRayAP.2.2.1

  have hBC : Collinear Geo B D C :=
    (HilbertOrder.between_incidence
      B D C hBDCbetween).2.2.2.1

  have hIntersectionAP :
      IsIntersection Geo A P B C D :=
    ⟨hAP, hBC⟩

  have hPG : Collinear Geo P D G :=
    (HilbertOrder.between_incidence
      P D G hPDGbetween).2.2.2.1

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
        hBC
        hPG

  have hMedian : IsMedian Geo A D B C := by
    exact
      MidpointMedian
        Geo
        A B C D
        hMidpoint

  -- Step 5.
  -- The constructed intersection says that `P,D,G` are collinear.
  -- Together with `A,G,P`, this implies that `A,G,D` are collinear,
  -- so the third median `AD` passes through the already constructed
  -- intersection `G` of the first two medians.

  have hAGD : Collinear Geo A G D := by
    exact
      CollinearTrans
        Geo
        A G P D
        hGP
        hAGP
        hPG

  have hMedianE : IsMedian Geo B E A C :=
    MidpointMedian
      Geo B A C E
      (midpoint_of_hilbert
        Geo E A C hE)

  have hMedianF : IsMedian Geo C F A B :=
    MidpointMedian
      Geo C A B F
      (midpoint_of_hilbert
        Geo F A B hF)

  exact
    ⟨E, F, G, D,
      hMedianE,
      hMedianF,
      hBE,
      hCF,
      hMedian,
      hAGD⟩

end Geometry

/-
============================================================
Dependency graph of Finlay's proof
============================================================

Finlay's construction

    ¬ Collinear A B C
            |
    HilbertMidpointExists ------> E midpoint of AC
            |                    F midpoint of AB
            |
    hilbert_inner_pasch_strong
            |
            v
    G ∈ BE   and   G ∈ CF
            |
    ExtendSegmentBeyond
            |
            v
    A-G-P   and   AG ≅ GP

                    |
                    v

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

Step 3. Construct the diagonal intersection

    ParallelogramDiagonalIntersectionExists
            |
            +--> B-D-C
            |
            +--> P-D-G
            |
    hilbert_between_inner_trans
            |
    hilbert_sameRay_of_between
            |
            v
    D ∈ ray AP   and   D ∈ BC

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

    CollinearTrans -------------> A, G, D are collinear

                    |
                    v

      Finlay
      = ∃ E F G D,
          BE, CF, AD are medians
          ∧ G ∈ BE
          ∧ G ∈ CF
          ∧ G ∈ AD

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

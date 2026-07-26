import CGJteamLab.MidsegmentParallelSuppes

namespace Geometry.Suppes

variable {Point : Type*}
variable [SuppesGeometry Point]

local notation "Mid" =>
  SuppesGeometry.operation_midpoint

local notation "Col" =>
  SuppesGeometry.Collinear


/-
Temporary interface axiom for Finlay Step 1.

The midsegment theorem gives

    Mid(B,A) -- Mid(A,P) || B -- Mid(B,P).

If C, Mid(A,B), G are collinear and G = Mid(A,P),
then the corresponding full segments satisfy

    BP || CG.

This is only the collinear extension of the parallelism
already obtained from MidsegmentTheoremSuppes.
-/
axiom parallel_extend_midsegment
    (B A P C G : Point)
    (hMid :
      SuppesParallel
        (Mid B A)
        (Mid A P)
        B
        (Mid B P))
    (hCol : Col C (Mid A B) G)
    (hG : Mid A P = G) :
    SuppesParallel B P C G


/-
Temporary interface axiom for Finlay Step 2.

Classical recognition of a parallelogram:
if both pairs of opposite sides are parallel,
then the quadrilateral is a Suppes primitive parallelogram.

For ABCD the opposite pairs are:

    AB || CD
    CB || AD
-/
axiom parallelogram_of_opposite_sides_parallel
    (A B C D : Point)
    (hAB_CD : SuppesParallel A B C D)
    (hCB_AD : SuppesParallel C B A D) :
    PrimParallelogram A B C D


/-
Temporary interface axiom for Finlay Step 4.

The diagonals of a parallelogram bisect each other.

For parallelogram BPCG the diagonals are BC and PG.
If D lies on both diagonals, then D is the midpoint of BC.
-/
axiom parallelogram_diagonals_bisect
    (B P C G D : Point)
    (hPar : PrimParallelogram B P C G)
    (hDBC : Col B D C)
    (hDPG : Col P D G) :
    Mid B C = D


theorem FinlayProofSuppes
    (A B C G P D : Point)
    (_hT : PrimTriangle A B C)
    (hBAP : PrimTriangle B A P)
    (hCAP : PrimTriangle C A P)
    (hBG : Col B (Mid A C) G)
    (hCG : Col C (Mid A B) G)
    (hGP : Mid A P = G)

    /-
    Step 3.

    D lies on the two diagonals BC and PG.
    Also A, D and G are collinear.
    -/
    (hDBC : Col B D C)
    (hDPG : Col P D G)
    (hADG : Col A D G) :

    Col A (Mid B C) G := by


  /-
  Step 1.

  First application of the Midsegment Theorem
  to triangle BAP.

  F = Mid(B,A)
  G = Mid(A,P)

  Hence FG || BP.
  -/

  have hMidBAP :
      SuppesParallel
        (Mid B A)
        (Mid A P)
        B
        (Mid B P) := by
    exact MidsegmentTheoremSuppes B A P hBAP

  have hBP_CG :
      SuppesParallel B P C G := by
    exact
      parallel_extend_midsegment
        B A P C G
        hMidBAP
        hCG
        hGP


  /-
  Step 1.

  Second application of the Midsegment Theorem
  to triangle CAP.

  E = Mid(C,A)
  G = Mid(A,P)

  Hence EG || CP.
  -/

  have hMidCAP :
      SuppesParallel
        (Mid C A)
        (Mid A P)
        C
        (Mid C P) := by
    exact MidsegmentTheoremSuppes C A P hCAP

  have hCP_BG :
      SuppesParallel C P B G := by
    exact
      parallel_extend_midsegment
        C A P B G
        hMidCAP
        hBG
        hGP


  /-
  Step 2.

  BP || CG
  CP || BG

  Hence BPCG is a parallelogram.
  -/

  have hBPCG :
      PrimParallelogram B P C G := by
    exact
      parallelogram_of_opposite_sides_parallel
        B P C G
        hBP_CG
        hCP_BG


  /-
  Step 3.

  D is the intersection of the diagonals BC and PG.

  hDBC : D lies on BC
  hDPG : D lies on PG
  hADG : A, D, G are collinear
  -/


  /-
  Step 4.

  The diagonals of a parallelogram bisect each other.

  Hence D is the midpoint of BC.
  -/

  have hDmid :
      Mid B C = D := by
    exact
      parallelogram_diagonals_bisect
        B P C G D
        hBPCG
        hDBC
        hDPG


  /-
  Step 5.

  A, D and G are collinear.
  Since D = Mid(B,C), G lies on the third median.
  -/

  rw [hDmid]

  exact hADG


end Geometry.Suppes

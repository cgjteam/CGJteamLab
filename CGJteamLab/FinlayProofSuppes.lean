import CGJteamLab.MidsegmentParallelSuppes

namespace Geometry
namespace Suppes

universe u

variable {Point : Type u}
variable [SuppesGeometry Point]

local notation "Mid" =>
  (SuppesGeometry.operation_midpoint (Point := Point))

local notation "Dbl" =>
  (SuppesGeometry.operation_double (Point := Point))

local notation "Col" =>
  SuppesGeometry.Collinear


/-!
# Finlay proof in Suppes geometry

The main proof follows Finlay's five-step synthetic argument.
Only the genuinely missing pieces of the current Suppes interface
are left as explicit axioms.

Current interface gaps:

1. The auxiliary triangles needed to invoke the Midsegment Theorem
   in Step 1.
2. The collinearity transfer needed at the end of Step 1.
3. Recognition of a parallelogram from two pairs of opposite
   parallel sides in Step 2.

Steps 3-5 are proved from the existing midpoint and parallelogram API.
-/


/-!
## Missing interface facts
-/

/--
Auxiliary triangles needed for the two applications of the
Midsegment Theorem in Finlay Step 1.
-/
axiom FinlayStep1Triangles
    (A B C G P : Point)
    (hT : PrimTriangle A B C)
    (hBG : Col B (Mid A C) G)
    (hCG : Col C (Mid A B) G)
    (hGP : Mid A P = G) :
    PrimTriangle B A P /\
    PrimTriangle C A P

/--
Collinearity transfer used at the end of Finlay Step 1.

The Midsegment Theorem gives

  FG || B-Mid(B,P)
  EG || C-Mid(C,P).

Together with

  C,F,G collinear
  B,E,G collinear

this yields

  CG || BP
  BG || CP.
-/
axiom FinlayStep1Transfer
    (A B C G P : Point)
    (hBG : Col B (Mid A C) G)
    (hCG : Col C (Mid A B) G)
    (hFG :
      SuppesParallel
        (Mid A B) G
        B (Mid B P))
    (hEG :
      SuppesParallel
        (Mid A C) G
        C (Mid C P)) :
    SuppesParallel C G B P /\
    SuppesParallel B G C P

/--
Recognition principle used in Finlay Step 2.

Two pairs of opposite parallel sides determine the parallelogram BPCG.
-/
axiom parallelogram_from_two_parallel_pairs
    (B P C G : Point)
    (hCG_BP : SuppesParallel C G B P)
    (hBG_CP : SuppesParallel B G C P) :
    PrimParallelogram B P C G


/-!
## Finlay Step 1
-/

/--
Finlay Step 1.

The two calls of the Midsegment Theorem are performed explicitly.
Only the auxiliary-triangle fact and the final collinearity transfer
remain interface assumptions.
-/
theorem FinlayStep1
    (A B C G P : Point)
    (hT : PrimTriangle A B C)
    (hBG : Col B (Mid A C) G)
    (hCG : Col C (Mid A B) G)
    (hGP : Mid A P = G) :
    SuppesParallel C G B P /\
    SuppesParallel B G C P := by

  have hTriangles :=
    FinlayStep1Triangles
      A B C G P
      hT hBG hCG hGP

  have hBAP : PrimTriangle B A P :=
    hTriangles.1

  have hCAP : PrimTriangle C A P :=
    hTriangles.2

  -- F = Mid A B and G = Mid A P, hence FG is parallel to BP.
  have hFG0 :=
    MidsegmentTheoremSuppes
      B A P
      hBAP

  have hFG :
      SuppesParallel
        (Mid A B) G
        B (Mid B P) := by
    simpa [
      midpoint_commutative B A,
      hGP
    ] using hFG0

  -- E = Mid A C and G = Mid A P, hence EG is parallel to CP.
  have hEG0 :=
    MidsegmentTheoremSuppes
      C A P
      hCAP

  have hEG :
      SuppesParallel
        (Mid A C) G
        C (Mid C P) := by
    simpa [
      midpoint_commutative C A,
      hGP
    ] using hEG0

  exact
    FinlayStep1Transfer
      A B C G P
      hBG hCG
      hFG hEG


/-!
## Finlay Step 2
-/

/--
Finlay Step 2.

From

  CG || BP
  BG || CP

we recognize BPCG as a parallelogram.
-/
theorem FinlayStep2
    (B P C G : Point)
    (hCG_BP : SuppesParallel C G B P)
    (hBG_CP : SuppesParallel B G C P) :
    PrimParallelogram B P C G := by
  exact
    parallelogram_from_two_parallel_pairs
      B P C G
      hCG_BP hBG_CP


/-!
## Finlay Steps 3-5
-/

/--
Finlay Step 3 in midpoint form.

Since G = Mid A P, the point Mid P G lies on AP.
This point will serve as the diagonal-intersection point D.
-/
theorem FinlayStep3
    (A G P : Point)
    (hGP : Mid A P = G) :
    Col A P (Mid P G) := by

  have hAPG : Col A P G := by
    rw [hGP.symm]
    exact midpoint_collinear A P

  by_cases hPG : P = G

  · rw [hPG.symm, midpoint_idempotent P]
    apply L2
    exact Or.inr (Or.inr rfl)

  · have hPGA : Col P G A := by
      exact collinear_rotate hAPG

    have hPGP : Col P G P := by
      apply L2
      exact Or.inr (Or.inl rfl)

    have hPGM : Col P G (Mid P G) := by
      exact midpoint_collinear P G

    exact
      L3
        P G
        A P (Mid P G)
        hPG
        hPGA
        hPGP
        hPGM

/--
Finlay Step 4.

For the parallelogram BPCG, the defining midpoint identity says
that the diagonals BC and PG have the same midpoint.
-/
theorem FinlayStep4
    (B P C G : Point)
    (hPara : PrimParallelogram B P C G) :
    Mid P G = Mid B C := by
  exact hPara.2.symm

/--
Finlay Step 5.

If D is the midpoint of BC and D and G both lie on AP,
then G lies on the median from A.
-/
theorem FinlayStep5
    (A B C G P D : Point)
    (hGP : Mid A P = G)
    (hAPD : Col A P D)
    (hDmid : D = Mid B C) :
    Col A (Mid B C) G := by

  have hAPG : Col A P G := by
    rw [hGP.symm]
    exact midpoint_collinear A P

  by_cases hAP : A = P

  · subst P
    rw [midpoint_idempotent A] at hGP
    subst G
    apply L2
    exact Or.inr (Or.inl rfl)

  · have hAPA : Col A P A := by
      apply L2
      exact Or.inr (Or.inl rfl)

    have hADG : Col A D G := by
      exact
        L3
          A P
          A D G
          hAP
          hAPA
          hAPD
          hAPG

    rw [hDmid.symm]
    exact hADG

/--
Finlay Steps 3-5 assembled.

Take D = Mid P G. Step 3 puts D on AP. Step 4 identifies D
with Mid B C. Step 5 gives the third median.
-/
theorem FinlayDiagonalStep
    (A B C G P : Point)
    (hGP : Mid A P = G)
    (hPara : PrimParallelogram B P C G) :
    Col A (Mid B C) G := by

  let D : Point := Mid P G

  have hAPD : Col A P D := by
    exact
      FinlayStep3
        A G P
        hGP

  have hDmid : D = Mid B C := by
    exact
      FinlayStep4
        B P C G
        hPara

  exact
    FinlayStep5
      A B C G P D
      hGP hAPD hDmid


/-!
## Finlay theorem
-/

/--
Finlay's theorem in Suppes geometry.

Given a triangle ABC and a point G lying on the medians
from B and C, G also lies on the median from A.
-/
theorem FinlaySuppes
    (A B C G : Point)
    (hT : PrimTriangle A B C)
    (hBG : Col B (Mid A C) G)
    (hCG : Col C (Mid A B) G) :
    Col A (Mid B C) G := by

  let P : Point := Dbl A G

  have hGP : Mid A P = G := by
    dsimp [P]
    exact midpoint_double_reduction A G

  have hStep1 :
      SuppesParallel C G B P /\
      SuppesParallel B G C P :=
    FinlayStep1
      A B C G P
      hT hBG hCG hGP

  have hCG_BP : SuppesParallel C G B P :=
    hStep1.1

  have hBG_CP : SuppesParallel B G C P :=
    hStep1.2

  have hBPCG :
      PrimParallelogram B P C G :=
    FinlayStep2
      B P C G
      hCG_BP hBG_CP

  exact
    FinlayDiagonalStep
      A B C G P
      hGP hBPCG


end Suppes
end Geometry

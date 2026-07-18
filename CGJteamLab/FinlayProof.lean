import CGJteamLab.MidsegmentParallel

namespace Geometry

universe u

variable (Geo : Geo)
variable [HilbertIncidence Geo]

theorem ParallelogramOfParallel
    (Geo : Geometry.Geo)
    (A B C D : Geo.Point) :
    Geo.Parallel A B C D →
    Geo.Parallel A D B C →
    IsParallelogram Geo A B C D := by
  intro h1 h2

  have h2' : Geo.Parallel B C D A := by
    exact
      ParallelSwapSecondLine
        Geo
        B C A D
        (ParallelSymmetry Geo A D B C h2)

  exact And.intro h1 h2'

theorem FinlayStep1
  (A B C E F G P : Geo.Point)
  (hE : IsMidpoint Geo E A C)
  (hF : IsMidpoint Geo F A B)
  (hG : IsMidpoint Geo G A P)
  (hCFG : Collinear Geo C F G)
  (hBEG : Collinear Geo B E G) :
  Geo.Parallel C G B P ∧
  Geo.Parallel B G C P := by
  constructor
  ·
    have hFG : Geo.Parallel F G B P := by
      exact MidsegmentTheorem Geo A B P F G hF hG

    exact ParallelCollinearLeft
      Geo
      F G C
      B P
      hFG
      hCFG

  ·
    have hEG : Geo.Parallel E G C P := by
      exact MidsegmentTheorem Geo A C P E G hE hG

    exact ParallelCollinearLeft
      Geo
      E G B
      C P
      hEG
      hBEG



theorem FinlayStep2
  (B C G P : Geo.Point)
  (hCG : Geo.Parallel C G B P)
  (hBG : Geo.Parallel B G C P) :
  IsParallelogram Geo B P C G := by

  have h1 : Geo.Parallel B P C G := by
    exact ParallelSymmetry Geo C G B P hCG

  have h2 : Geo.Parallel B G P C := by
    exact ParallelSwapSecondLine Geo B G C P hBG

  exact
    ParallelogramOfParallel
      Geo
      B P C G
      h1
      h2


theorem FinlayStep3
  (A B C G P D : Geo.Point)
  (hAGP : Collinear Geo A G P)
  (hInt : IsIntersection Geo A P B C D) :
  IsIntersection Geo P G B C D := by
  exact
    IntersectionOnSameLine
      Geo
      A G P B C D
      hAGP
      hInt
theorem FinlayStep4
  (B C G P D : Geo.Point)
  (hPar : IsParallelogram Geo B P C G)
  (hInt : IsIntersection Geo P G B C D) :
  IsMidpoint Geo D B C := by

  have hPG : Collinear Geo P D G := hInt.left
  have hBC : Collinear Geo B D C := hInt.right

  exact
    ParallelogramDiagonals
      Geo
      B P C G D
      hPar
      hBC
      hPG


theorem FinlayStep5
  (A B C D : Geo.Point)
  (hMid : IsMidpoint Geo D B C) :
  IsMedian Geo A D B C := by
  exact
    MidpointMedian
      Geo
      A B C D
      hMid

theorem Finlay
  (A B C E F G P D : Geo.Point)
  (hE : IsMidpoint Geo E A C)
  (hF : IsMidpoint Geo F A B)
  (hG : IsMidpoint Geo G A P)
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
  have hStep1 :=
    FinlayStep1
      Geo
      A B C E F G P
      hE
      hF
      hG
      hCFG
      hBEG

  -- Step 2.
  -- A quadrilateral whose opposite sides are parallel
  -- is a parallelogram.
  have hPar : IsParallelogram Geo B P C G := by
    exact
      FinlayStep2
        Geo
        B C G P
        hStep1.left
        hStep1.right

  -- G is the midpoint of AP, hence A, G and P are collinear.
  have hAGP : Collinear Geo A G P := by
    exact midpoint_collinear Geo A P G hG

  -- D is assumed to lie on AP and BC,
  -- so it is the intersection of these two lines.
  have hIntAP : IsIntersection Geo A P B C D := by
    exact And.intro hAP hBC

  -- Step 3.
  -- Since A, G and P are collinear, the same intersection
  -- can be regarded as lying on the diagonal PGeo.
  have hIntPG : IsIntersection Geo P G B C D := by
    exact
      FinlayStep3
        Geo
        A B C G P D
        hAGP
        hIntAP

  -- Step 4.
  -- In a parallelogram the diagonals bisect each other,
  -- therefore D is the midpoint of BC.
  have hMid : IsMidpoint Geo D B C := by
    exact
      FinlayStep4
        Geo
        B C G P D
        hPar
        hIntPG

  -- Step 5.
  -- The segment joining a vertex with the midpoint
  -- of the opposite side is a median.
  have hMedian : IsMedian Geo A D B C := by
    exact
      FinlayStep5
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
        hAGP
        hPG

  -- The line AD is a median and passes through Geo.
  exact And.intro hMedian hAGD


end Geometry

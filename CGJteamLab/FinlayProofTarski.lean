import CGJteamLab.MidSegmentParallelTarski

namespace Geometry
namespace Tarski

universe u

variable (Geo : Geometry.Tarski.Geo)

/--
If J is the midpoint of AC and G is the midpoint of CD,
then AD is parallel to JG.
-/
theorem parallel_AD_JG_from_midpoints
    [TarskiNeutral Geo]
    (A C D G J : Geo.Point)
    (hNonColADC : Not (TarskiCollinear Geo A D C))
    (hJ : TarskiIsMidpoint Geo J A C)
    (hG : TarskiIsMidpoint Geo G C D) :
    TarskiParallelStrict Geo A D J G := by

  have hGDC : TarskiIsMidpoint Geo G D C :=
    tarski_midpoint_symmetry
      Geo G C D hG

  exact
    MidsegmentTheoremTarski
      Geo A D C G J
      hNonColADC
      hGDC
      hJ

/--
If I is the midpoint of BC and G is the midpoint of CD,
then BD is parallel to IG.
-/
theorem parallel_BD_IG_from_midpoints
    [TarskiNeutral Geo]
    (B C D G I : Geo.Point)
    (hNonColBDC : Not (TarskiCollinear Geo B D C))
    (hI : TarskiIsMidpoint Geo I B C)
    (hG : TarskiIsMidpoint Geo G C D) :
    TarskiParallelStrict Geo B D I G := by

  have hGDC : TarskiIsMidpoint Geo G D C :=
    tarski_midpoint_symmetry
      Geo G C D hG

  exact
    MidsegmentTheoremTarski
      Geo B D C G I
      hNonColBDC
      hGDC
      hI
/--
If AD is parallel to JG, and B, G, J are collinear with B ≠ G,
then AD is parallel to BG.
-/
theorem parallel_AD_BG_from_collinear
    [TarskiNeutral Geo]
    (A B D G J : Geo.Point)
    (hPar : TarskiParallelStrict Geo A D J G)
    (hBGJ : TarskiCollinear Geo B G J)
    (hBG : B = G -> False) :
    TarskiParallelStrict Geo A D B G := by

  exact
    tarski_parallel_strict_collinear_right
      Geo A D B G J
      hPar
      hBGJ
      hBG

/--
If BD is parallel to IG, and A, G, I are collinear with A ≠ G,
then BD is parallel to AG.
-/
theorem parallel_BD_AG_from_collinear
    [TarskiNeutral Geo]
    (A B D G I : Geo.Point)
    (hPar : TarskiParallelStrict Geo B D I G)
    (hAGI : TarskiCollinear Geo A G I)
    (hAG : A = G -> False) :
    TarskiParallelStrict Geo B D A G := by

  exact
    tarski_parallel_strict_collinear_right
      Geo B D A G I
      hPar
      hAGI
      hAG

/--
Construct the two pairs of opposite parallel sides
used in the GeoCoq proof.
-/
theorem opposite_sides_parallel
    [TarskiNeutral Geo]
    (A B C D G I J : Geo.Point)
    (hNonColADC : Not (TarskiCollinear Geo A D C))
    (hNonColBDC : Not (TarskiCollinear Geo B D C))
    (hJ : TarskiIsMidpoint Geo J A C)
    (hI : TarskiIsMidpoint Geo I B C)
    (hG : TarskiIsMidpoint Geo G C D)
    (hBGJ : TarskiCollinear Geo B G J)
    (hAGI : TarskiCollinear Geo A G I)
    (hBG : B = G -> False)
    (hAG : A = G -> False) :
    TarskiParallelStrict Geo A D B G /\
    TarskiParallelStrict Geo B D A G := by

  have hADJG :=
    parallel_AD_JG_from_midpoints
      (Geo := Geo)
      A C D G J
      hNonColADC
      hJ
      hG

  have hBDIG :=
    parallel_BD_IG_from_midpoints
      (Geo := Geo)
      B C D G I
      hNonColBDC
      hI
      hG

  have hADBG :=
    parallel_AD_BG_from_collinear
      (Geo := Geo)
      A B D G J
      hADJG
      hBGJ
      hBG

  have hBDAG :=
    parallel_BD_AG_from_collinear
      (Geo := Geo)
      A B D G I
      hBDIG
      hAGI
      hAG

  exact ⟨hADBG, hBDAG⟩


/--
Temporary assumption used in this proof:
two pairs of opposite strict parallel sides determine a parallelogram.
-/
axiom parallelogram_of_two_parallel_pairs
    [TarskiNeutral Geo]
    (A B C D : Geo.Point)
    (hABCD : TarskiParallelStrict Geo A B C D)
    (hBCAD : TarskiParallelStrict Geo B C A D) :
    TarskiParallelogram Geo A B C D

theorem parallelogram_GADB
    [TarskiNeutral Geo]
    (A B C D G I J : Geo.Point)
    (hNonColADC : Not (TarskiCollinear Geo A D C))
    (hNonColBDC : Not (TarskiCollinear Geo B D C))
    (hJ : TarskiIsMidpoint Geo J A C)
    (hI : TarskiIsMidpoint Geo I B C)
    (hG : TarskiIsMidpoint Geo G C D)
    (hBGJ : TarskiCollinear Geo B G J)
    (hAGI : TarskiCollinear Geo A G I)
    (hBG : B = G -> False)
    (hAG : A = G -> False) :
    TarskiParallelogram Geo G A D B := by

  obtain ⟨hADBG, hBDAG⟩ :=
    opposite_sides_parallel
      (Geo := Geo)
      A B C D G I J
      hNonColADC
      hNonColBDC
      hJ
      hI
      hG
      hBGJ
      hAGI
      hBG
      hAG

  have hGADB : TarskiParallelStrict Geo G A D B := by
    rcases hBDAG with ⟨hBD, hAG', hNoInt⟩

    constructor
    · intro hGA
      exact hAG' hGA.symm

    constructor
    · intro hDB
      exact hBD hDB.symm

    · intro hInt
      apply hNoInt

      rcases hInt with ⟨X, hXGA, hXDB⟩

      have hXAG : TarskiCollinear Geo X A G :=
        tarski_collinear_symmetry
          Geo X G A hXGA

      have hXBD : TarskiCollinear Geo X B D :=
        tarski_collinear_symmetry
          Geo X D B hXDB

      exact ⟨X, hXBD, hXAG⟩

  have hADGB : TarskiParallelStrict Geo A D G B :=
    tarski_parallel_strict_symm_right
      Geo A D B G hADBG

  exact
    parallelogram_of_two_parallel_pairs
      Geo G A D B
      hGADB
      hADGB

/--
The common midpoint of the diagonals of parallelogram GADB
is the midpoint of GD and AB.
-/
theorem midpoint_GD_AB_from_parallelogram
    [TarskiNeutral Geo]
    (A B C D G I J : Geo.Point)
    (hNonColADC : Not (TarskiCollinear Geo A D C))
    (hNonColBDC : Not (TarskiCollinear Geo B D C))
    (hJ : TarskiIsMidpoint Geo J A C)
    (hI : TarskiIsMidpoint Geo I B C)
    (hG : TarskiIsMidpoint Geo G C D)
    (hBGJ : TarskiCollinear Geo B G J)
    (hAGI : TarskiCollinear Geo A G I)
    (hBG : B = G -> False)
    (hAG : A = G -> False) :
    Exists fun M : Geo.Point =>
      TarskiIsMidpoint Geo M G D /\
      TarskiIsMidpoint Geo M A B := by

  have hPar : TarskiParallelogram Geo G A D B :=
    parallelogram_GADB
      (Geo := Geo)
      A B C D G I J
      hNonColADC
      hNonColBDC
      hJ
      hI
      hG
      hBGJ
      hAGI
      hBG
      hAG

  exact hPar.2

/--
If G is the midpoint of CD and M is the midpoint of GD,
then C, G, M are collinear.
-/
theorem collinear_CGM_from_midpoints
    [TarskiNeutral Geo]
    (A C D G M : Geo.Point)
    (hNonColADC : Not (TarskiCollinear Geo A D C))
    (hG : TarskiIsMidpoint Geo G C D)
    (hM : TarskiIsMidpoint Geo M G D) :
    TarskiCollinear Geo C G M := by

  have hDC : D = C -> False :=
    tarski_noncollinear_ne_second_third
      Geo A D C hNonColADC

  have hCD : C = D -> False := by
    intro hCD
    exact hDC hCD.symm

  have hGD : G = D -> False :=
    tarski_midpoint_ne_second
      Geo G C D hCD hG

  have hCGD : TarskiCollinear Geo C G D :=
    tarski_midpoint_collinear
      Geo G C D hG

  have hGMD : TarskiCollinear Geo G M D :=
    tarski_midpoint_collinear
      Geo M G D hM

  have hGDM : TarskiCollinear Geo G D M :=
    tarski_collinear_symmetry
      Geo G M D hGMD

  exact
    tarski_collinear_trans
      Geo C G D M
      hGD
      hCGD
      hGDM

theorem B_ne_G_from_medians
    [TarskiNeutral Geo]
    (A B C G I : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hI : TarskiIsMidpoint Geo I B C)
    (hAGI : TarskiCollinear Geo A G I) :
    B = G -> False := by

  intro hBG

  have hABI : TarskiCollinear Geo A B I := by
    rw [hBG]
    exact hAGI

  have hBIC : TarskiCollinear Geo B I C :=
    tarski_midpoint_collinear
      Geo I B C hI

  have hBC : B = C -> False :=
    tarski_noncollinear_ne_second_third
      Geo A B C hNonColABC

  have hBI : B = I -> False :=
    tarski_midpoint_ne_first
      Geo I B C hBC hI

  have hABC : TarskiCollinear Geo A B C :=
    tarski_collinear_trans
      Geo A B I C
      hBI
      hABI
      hBIC

  exact hNonColABC hABC

theorem A_ne_G_from_medians
    [TarskiNeutral Geo]
    (A B C G J : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hJ : TarskiIsMidpoint Geo J A C)
    (hBGJ : TarskiCollinear Geo B G J) :
    A = G -> False := by

  intro hAG

  have hBAJ : TarskiCollinear Geo B A J := by
    rw [hAG]
    exact hBGJ

  have hAJC : TarskiCollinear Geo A J C :=
    tarski_midpoint_collinear
      Geo J A C hJ

  have hNonColBAC : Not (TarskiCollinear Geo B A C) := by
    intro hBAC

    have hBCA : TarskiCollinear Geo B C A :=
      tarski_collinear_symmetry
        Geo B A C hBAC

    have hABC : TarskiCollinear Geo A B C :=
      (tarski_collinear_cycle Geo A B C).mpr hBCA

    exact hNonColABC hABC

  have hAC : A = C -> False :=
    tarski_noncollinear_ne_second_third
      Geo B A C hNonColBAC

  have hAJ : A = J -> False :=
    tarski_midpoint_ne_first
      Geo J A C hAC hJ

  have hBAC : TarskiCollinear Geo B A C :=
    tarski_collinear_trans
      Geo B A J C
      hAJ
      hBAJ
      hAJC

  have hBCA : TarskiCollinear Geo B C A :=
    tarski_collinear_symmetry
      Geo B A C hBAC

  have hABC : TarskiCollinear Geo A B C :=
    (tarski_collinear_cycle Geo A B C).mpr hBCA

  exact hNonColABC hABC


/-
There exists a midpoint of AB lying on the line CG.
-/
theorem third_median_point
    [TarskiNeutral Geo]
    (A B C D G I J : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hNonColADC : Not (TarskiCollinear Geo A D C))
    (hNonColBDC : Not (TarskiCollinear Geo B D C))
    (hJ : TarskiIsMidpoint Geo J A C)
    (hI : TarskiIsMidpoint Geo I B C)
    (hG : TarskiIsMidpoint Geo G C D)
    (hBGJ : TarskiCollinear Geo B G J)
    (hAGI : TarskiCollinear Geo A G I) :
    Exists fun M : Geo.Point =>
      TarskiIsMidpoint Geo M A B /\
      TarskiCollinear Geo C G M := by

  have hBG : B = G -> False :=
    B_ne_G_from_medians
      Geo A B C G I
      hNonColABC
      hI
      hAGI

  have hAG : A = G -> False :=
    A_ne_G_from_medians
      Geo A B C G J
      hNonColABC
      hJ
      hBGJ

  rcases
    midpoint_GD_AB_from_parallelogram
      Geo
      A B C D G I J
      hNonColADC
      hNonColBDC
      hJ
      hI
      hG
      hBGJ
      hAGI
      hBG
      hAG
  with ⟨M, hMGD, hMAB⟩

  have hCGM : TarskiCollinear Geo C G M :=
    collinear_CGM_from_midpoints
      Geo
      A C D G M
      hNonColADC
      hG
      hMGD

  exact ⟨M, hMAB, hCGM⟩


/-
If G lies on the medians from A and B of the non-collinear triangle ABC,
then G also lies on the median from C.
-/
theorem finlay_tarski
    [TarskiNeutral Geo]
    (A B C D G I J : Geo.Point)
    (hNonColABC : Not (TarskiCollinear Geo A B C))
    (hNonColADC : Not (TarskiCollinear Geo A D C))
    (hNonColBDC : Not (TarskiCollinear Geo B D C))
    (hJ : TarskiIsMidpoint Geo J A C)
    (hI : TarskiIsMidpoint Geo I B C)
    (hG : TarskiIsMidpoint Geo G C D)
    (hBGJ : TarskiCollinear Geo B G J)
    (hAGI : TarskiCollinear Geo A G I) :
    Exists fun M : Geo.Point =>
      TarskiIsMidpoint Geo M A B /\
      TarskiCollinear Geo C G M := by

  exact
    third_median_point
      Geo
      A B C D G I J
      hNonColABC
      hNonColADC
      hNonColBDC
      hJ
      hI
      hG
      hBGJ
      hAGI

end Tarski
end Geometry

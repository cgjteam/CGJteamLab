import CGJteamLab.Proposition38
import CGJteamLab.Proposition39

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

------------------------------------------------------------------------
-- Euclid I.40
--
-- Equal triangles which are on equal bases and on the same side are
-- also between the same parallels.
--
-- The equal-base construction is not repeated here.  It is the
-- construction isolated in Proposition38 as `i38_copy_parallelogram`.
--
-- Proof architecture:
--
--   1. Put E and F on the common base carrier.
--   2. Use `i38_copy_parallelogram` to copy ABC onto EF.  This gives
--      a point G, triangle BAC congruent to EGF, and parallelogram
--      A-G-E-B.  Hence AG || EB, and therefore AG || BC.
--   3. Congruence gives scissors equality ABC = GEF.  Together with
--      the hypothesis ABC = DEF, this gives GEF = DEF.
--   4. Apply Euclid I.39 to the two triangles GEF and DEF on the same
--      base EF.  Thus G and D lie on a line `top` disjoint from `base`.
--   5. The line AG is also disjoint from `base` because AG || BC.
--      Both it and `top` pass through G, so uniqueness of the parallel
--      through G identifies the two lines.  Therefore A lies on `top`.
------------------------------------------------------------------------

/--
The endpoints E and F of the second base lie on the same carrier line
as B and C once B-C-E and C-E-F.
-/
theorem i40_base_endpoints
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (B C E F : Geo.Point)
    (base : Geo.Line)
    (hBCE : Geo.Between B C E)
    (hCEF : Geo.Between C E F)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base) :
    HilbertIncidence.OnLine E base ∧
    HilbertIncidence.OnLine F base := by

  have hBCEData :=
    HilbertOrder.between_incidence
      B C E hBCE

  have hBC :
      Not (B = C) := by
    exact hBCEData.1

  have hBCEcol :
      Collinear Geo B C E :=
    hBCEData.2.2.2.1

  have hEbase :
      HilbertIncidence.OnLine E base :=
    hilbert_collinear_on_line
      Geo B C E base
      hBC hBbase hCbase hBCEcol

  have hCEFData :=
    HilbertOrder.between_incidence
      C E F hCEF

  have hCE :
      Not (C = E) := by
    exact hCEFData.1

  have hCEFcol :
      Collinear Geo C E F :=
    hCEFData.2.2.2.1

  have hFbase :
      HilbertIncidence.OnLine F base :=
    hilbert_collinear_on_line
      Geo C E F base
      hCE hCbase hEbase hCEFcol

  exact ⟨hEbase, hFbase⟩

/--
Reuse the equal-base construction from I.38 and retain only the data
needed by I.40: the copied congruent triangle, its side relative to the
base, and AG parallel to BC.
-/
theorem i40_copy_parallel
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C E F : Geo.Point)
    (base : Geo.Line)
    (hBCE : Geo.Between B C E)
    (hCEF : Geo.Between C E F)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hEbase : HilbertIncidence.OnLine E base)
    (hFbase : HilbertIncidence.OnLine F base)
    (hBC_EF : Geo.Congruent B C E F)
    (hAoff : Not (HilbertIncidence.OnLine A base)) :
    ∃ G : Geo.Point,
      HilbertSameSide Geo A G base ∧
      TriangleCongruenceResult Geo B A C E G F ∧
      Geo.Parallel A G B C := by

  rcases
      i38_copy_parallelogram
        Geo
        A B C E F
        base
        hBCE hCEF
        hBbase hCbase
        hEbase hFbase
        hBC_EF
        hAoff
    with
    ⟨G, hAGsame, hAGEB, hTriangles⟩

  have hAG_EB :
      Geo.Parallel A G E B :=
    hAGEB.1

  have hEB_AG :
      Geo.Parallel E B A G :=
    ParallelSymmetry
      Geo A G E B hAG_EB

  have hBCEData :=
    HilbertOrder.between_incidence
      B C E hBCE

  have hBC :
      Not (B = C) := by
    exact hBCEData.1

  have hCB :
      Not (C = B) := by
    intro h
    exact hBC h.symm

  have hBCEcol :
      Collinear Geo B C E :=
    hBCEData.2.2.2.1

  have hCEB :
      Collinear Geo C E B :=
    PrimCollinearCycle
      Geo B C E hBCEcol

  have hCB_AG :
      Geo.Parallel C B A G :=
    ParallelCollinearLeft
      Geo
      E B C
      A G
      hCB
      hEB_AG
      hCEB

  have hBC_AG :
      Geo.Parallel B C A G :=
    ParallelSwapFirstLine
      Geo C B A G hCB_AG

  have hAG_BC :
      Geo.Parallel A G B C :=
    ParallelSymmetry
      Geo B C A G hBC_AG

  exact
    ⟨G,
      hAGsame,
      hTriangles,
      hAG_BC⟩

/--
Euclid I.40.

Equal (equicomplementable) triangles which are on equal bases and on
the same side are also between the same parallels.

The bases BC and EF are laid out consecutively on the common line
`base` by B-C-E and C-E-F, matching the configuration used in I.38.
-/
theorem euclid_proposition_40
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (base : Geo.Line)
    (hBCE : Geo.Between B C E)
    (hCEF : Geo.Between C E F)
    (hBbase : HilbertIncidence.OnLine B base)
    (hCbase : HilbertIncidence.OnLine C base)
    (hBC_EF : Geo.Congruent B C E F)
    (hSame : HilbertSameSide Geo A D base)
    (hEqual :
      HilbertScissorsEquicomplementable
        Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo D E F)) :
    ∃ top : Geo.Line,
      HilbertIncidence.OnLine A top ∧
      HilbertIncidence.OnLine D top ∧
      HilbertLinesDisjoint Geo top base := by

  --------------------------------------------------------------------
  -- E and F lie on the common base carrier.
  --------------------------------------------------------------------

  rcases
      i40_base_endpoints
        Geo B C E F base
        hBCE hCEF hBbase hCbase
    with
    ⟨hEbase, hFbase⟩

  have hAoff :
      Not (HilbertIncidence.OnLine A base) :=
    hSame.1

  --------------------------------------------------------------------
  -- Reuse the I.38 equal-base construction.
  --------------------------------------------------------------------

  rcases
      i40_copy_parallel
        Geo
        A B C E F
        base
        hBCE hCEF
        hBbase hCbase
        hEbase hFbase
        hBC_EF
        hAoff
    with
    ⟨G, hAGsame, hTriangles, hAG_BC⟩

  --------------------------------------------------------------------
  -- Triangle congruence gives scissors equality ABC = GEF.
  --------------------------------------------------------------------

  have hCopy0 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B A C)
        (hilbertScissorsTriangle Geo E G F) :=
    scissors_congruent
      Geo B A C E G F hTriangles

  have hCopy :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo G E F) := by
    rw [scissors_triangle_swap12 Geo B A C] at hCopy0
    rw [scissors_triangle_swap12 Geo E G F] at hCopy0
    exact hCopy0

  have hABC_GEF :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo A B C)
        (hilbertScissorsTriangle Geo G E F) :=
    equicomplementable_of_scissorsEq Geo hCopy

  have hGEF_ABC :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo G E F)
        (hilbertScissorsTriangle Geo A B C) :=
    equicomplementable_symm Geo hABC_GEF

  have hGEF_DEF :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo G E F)
        (hilbertScissorsTriangle Geo D E F) :=
    equicomplementable_trans Geo hGEF_ABC hEqual

  --------------------------------------------------------------------
  -- G and D lie on the same side of the base.
  --------------------------------------------------------------------

  have hGAsame :
      HilbertSameSide Geo G A base :=
    hilbert_sameSide_symm
      Geo A G base hAGsame

  have hGDsame :
      HilbertSameSide Geo G D base :=
    hilbert_sameSide_trans
      Geo G A D base hGAsame hSame

  have hEF :
      Not (E = F) := by
    exact
      (HilbertOrder.between_incidence
        C E F hCEF).2.1

  --------------------------------------------------------------------
  -- I.39 now applies on the common base EF.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_39
        Geo G E F D base
        hEF hEbase hFbase
        hGDsame hGEF_DEF
    with
    ⟨top, hGtop, hDtop, hTopDisjoint⟩

  --------------------------------------------------------------------
  -- The carrier of AG is also disjoint from base because AG || BC.
  --------------------------------------------------------------------

  have hAG :
      Not (A = G) := by
    exact hAG_BC.1

  rcases
      HilbertPlaneIncidence.line_through
        A G hAG
    with
    ⟨topAG, hAtopAG, hGtopAG⟩

  have hBC :
      Not (B = C) := by
    exact
      (HilbertOrder.between_incidence
        B C E hBCE).1

  have hTopAGDisjoint :
      HilbertLinesDisjoint Geo topAG base := by
    rintro ⟨X, hXtopAG, hXbase⟩

    have hXAG :
        X ∈ Geo.PointLine A G :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A G X topAG
        hAG hAtopAG hGtopAG).mpr hXtopAG

    have hXBC :
        X ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X base
        hBC hBbase hCbase).mpr hXbase

    exact
      Set.disjoint_left.mp
        hAG_BC.2.2
        hXAG
        hXBC

  --------------------------------------------------------------------
  -- Both topAG and top pass through G and avoid base.  Parallel
  -- uniqueness therefore identifies them.
  --------------------------------------------------------------------

  have hGoff :
      Not (HilbertIncidence.OnLine G base) :=
    hAGsame.2.1

  have hTopEq :
      topAG = top :=
    HilbertEuclideanPlane.parallel_unique
      (Geo := Geo)
      base G hGoff
      topAG top
      hGtopAG hTopAGDisjoint
      hGtop hTopDisjoint

  have hAtop :
      HilbertIncidence.OnLine A top := by
    rw [← hTopEq]
    exact hAtopAG

  exact
    ⟨top,
      hAtop,
      hDtop,
      hTopDisjoint⟩

end Geometry

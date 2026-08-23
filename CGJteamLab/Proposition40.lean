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
-- Strategy (mirrors exactly how Proposition38.lean reduces the
-- equal-base case of I.36 to the same-base case of I.37):
--
--   1. Copy triangle ABC by SAS onto the second base, at E, along
--      the ray toward F.  This produces a point G with
--        - G on the same side of `base` as A,
--        - triangle EGF congruent to triangle BAC,
--        - AG parallel to BC (a byproduct of the SAS copy, exactly
--          as in `i38_copy_parallelogram` / `i38_copy_upper_position`,
--          and in particular NOT dependent on any assumption that
--          AD is already parallel to BC -- that is what I.40 has to
--          establish, not what it may assume).
--
--   2. Triangle GEF is scissors-congruent to triangle ABC, hence
--      (by hypothesis) equicomplementable with triangle DEF.  Now
--      GEF and DEF sit on the *same* base EF, on the same side.
--
--   3. Apply the already-formalized Euclid I.39
--      (`euclid_proposition_39`, currently itself resting on the
--      single temporary axiom `proposition39_test_hilbert_48`) to
--      conclude that G and D lie on a common line `top` disjoint
--      from `base`.
--
--   4. Since AG || BC and both `top` and the line AG pass through G
--      and are disjoint from `base`, Hilbert's parallel axiom
--      (`HilbertEuclideanPlane.parallel_unique`) forces the two
--      lines to coincide.  Hence A also lies on `top`.
--
-- This makes I.40 a genuine theorem reduced to I.39, exactly as
-- Euclid's own proof of I.40 reduces to I.39 (the "same base" case)
-- by the same auxiliary construction used for I.38.
------------------------------------------------------------------------

/--
The far endpoints `E`, `F` of the second, congruent base lie on the
same carrier line as `B`, `C`, once `B-C-E` and `C-E-F`.

No parallelism assumption is needed for this: it is pure incidence.
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
      Not (B = C) :=
    hBCEData.1

  have hBCEcol :
      Collinear Geo B C E :=
    hBCEData.2.2.2.1

  have hEbase :
      HilbertIncidence.OnLine E base :=
    hilbert_collinear_on_line
      Geo B C E base hBC hBbase hCbase hBCEcol

  have hCEFData :=
    HilbertOrder.between_incidence
      C E F hCEF

  have hCE :
      Not (C = E) :=
    hCEFData.1

  have hCEFcol :
      Collinear Geo C E F :=
    hCEFData.2.2.2.1

  have hFbase :
      HilbertIncidence.OnLine F base :=
    hilbert_collinear_on_line
      Geo C E F base hCE hCbase hEbase hCEFcol

  exact ⟨hEbase, hFbase⟩

/--
SAS copy of triangle `ABC` onto the second base at `E`, along the ray
towards `F`, on the side of `base` containing `A`.

This is `i38_equal_base_copy` with the parallelism hypothesis
`Parallel A D B C` replaced by the fact that `A` is off `base`
(available here directly from `hSame`, without needing the parallel
we are trying to prove).
-/
theorem i40_equal_base_copy
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
      TriangleCongruenceResult Geo B A C E G F := by

  have hBC :
      Not (B = C) :=
    (HilbertOrder.between_incidence
      B C E hBCE).1

  have hBCA :
      Not (Collinear Geo B C A) :=
    hilbert_not_collinear_of_off_line
      Geo B C A base hBC hBbase hCbase hAoff

  have hABC :
      Not (Collinear Geo A B C) := by
    intro h
    exact hBCA (PrimCollinearCycle Geo A B C h)

  have hCEFData :=
    HilbertOrder.between_incidence
      C E F hCEF

  have hEF :
      Not (E = F) :=
    hCEFData.2.1

  have hFE :
      Not (F = E) := by
    intro h
    exact hEF h.symm

  rcases
      HilbertCongruence.angle_construction
        (Geo := Geo)
        A B C
        F E A
        hABC
        hFE
        base
        hFbase
        hEbase
        hAoff
    with
    ⟨G0, hG0ASame, hAngleG0, _⟩

  have hEG0 :
      Not (E = G0) := by
    intro h
    subst G0
    exact hG0ASame.1 hEbase

  have hG0E :
      Not (G0 = E) := by
    intro h
    exact hEG0 h.symm

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        A B
        E G0
        hEG0
    with
    ⟨G, hRayG0G, hEG_AB⟩

  rcases
      HilbertPlaneIncidence.line_through
        E G0 hEG0
    with
    ⟨rayLine, hEray, hG0ray⟩

  have hFray :
      Not (HilbertIncidence.OnLine F rayLine) := by
    intro hFray
    have hBaseRay :
        base = rayLine :=
      HilbertPlaneIncidence.line_unique
        E F hEF
        base rayLine
        hEbase hFbase
        hEray hFray
    exact
      hG0ASame.1
        (hBaseRay ▸ hG0ray)

  have hG0Gsame :
      HilbertSameSide Geo G0 G base :=
    hilbert_sameRay_points_sameSide
      Geo
      E G0
      G0 G
      F
      rayLine base
      hEray hG0ray
      hEbase hFbase
      hFray
      (hilbert_sameRay_refl Geo E G0 hG0E)
      hRayG0G

  have hAG0same :
      HilbertSameSide Geo A G0 base :=
    hilbert_sameSide_symm
      Geo G0 A base hG0ASame

  have hAGsame :
      HilbertSameSide Geo A G base :=
    hilbert_sameSide_trans
      Geo A G0 G base
      hAG0same hG0Gsame

  have hAtE :
      Geo.Angle F E G0 =
      Geo.Angle F E G :=
    hilbert_angle_eq_of_sameRay_second
      Geo E F G0 G hRayG0G

  have hAngle :
      Geo.AngleCongruent A B C F E G := by
    unfold Geometry.Geo.AngleCongruent
      at hAngleG0 ⊢
    rw [← hAtE]
    exact hAngleG0

  have hBAC :
      Not (Collinear Geo B A C) := by
    intro h
    exact hABC (PrimCollinearSwap Geo B A C h)

  have hGoff :
      Not (HilbertIncidence.OnLine G base) :=
    hAGsame.2.1

  have hEFG :
      Not (Collinear Geo E F G) :=
    hilbert_not_collinear_of_off_line
      Geo E F G base hEF hEbase hFbase hGoff

  have hEGF :
      Not (Collinear Geo E G F) := by
    intro h
    exact hEFG (PrimCollinearRotate Geo E G F h)

  have hAB_EG :
      Geo.Congruent A B E G :=
    hilbert_congruent_symmetry
      Geo E G A B hEG_AB

  have hBA_EG :
      Geo.Congruent B A E G :=
    CongruentReverseFirst
      Geo A B E G hAB_EG

  have hAngleSAS :
      Geo.AngleCongruent A B C G E F :=
    (Geo.angle_congruent_reverse_second
      A B C F E G).mp hAngle

  have hTriangles :
      TriangleCongruenceResult Geo B A C E G F :=
    SAS
      Geo B A C E G F
      hBAC hEGF hBA_EG hAngleSAS hBC_EF

  exact ⟨G, hAGsame, hTriangles⟩

/--
The SAS copy also yields `A G || B C`, the byproduct that Proposition38
extracts to relate the copy's upper vertex to the parallel through `A`
(there, `AD`; here we simply keep it as a free fact about `A` and `G`).
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
      i40_equal_base_copy
        Geo A B C E F base
        hBCE hCEF hBbase hCbase hEbase hFbase hBC_EF hAoff
    with
    ⟨G, hAGsame, hTriangles⟩

  have hGoff :
      Not (HilbertIncidence.OnLine G base) :=
    hAGsame.2.1

  have hBC :
      Not (B = C) :=
    (HilbertOrder.between_incidence
      B C E hBCE).1

  have hABC :
      Not (Collinear Geo A B C) := by
    have hBCA :
        Not (Collinear Geo B C A) :=
      hilbert_not_collinear_of_off_line
        Geo B C A base hBC hBbase hCbase hAoff
    intro h
    exact hBCA (PrimCollinearCycle Geo A B C h)

  have hAB :
      Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hBA :
      Not (B = A) := by
    intro h
    exact hAB h.symm

  have hGE :
      Not (G = E) := by
    intro h
    subst G
    exact hGoff hEbase

  have hEG :
      Not (E = G) := by
    intro h
    exact hGE h.symm

  rcases
      HilbertOrder.between_extension
        G E hGE
    with
    ⟨Y, hGEY⟩

  have hGEYData :=
    HilbertOrder.between_incidence
      G E Y hGEY

  have hEY :
      Not (E = Y) :=
    hGEYData.2.1

  have hGEYcol :
      Collinear Geo G E Y :=
    hGEYData.2.2.2.1

  have hYEG :
      Geo.Between Y E G :=
    hGEYData.2.2.2.2

  have hEYG :
      Collinear Geo E Y G :=
    PrimCollinearCycle Geo G E Y hGEYcol

  have hYoff :
      Not (HilbertIncidence.OnLine Y base) := by
    intro hYbase
    have hGbase :
        HilbertIncidence.OnLine G base :=
      hilbert_collinear_on_line
        Geo E Y G base hEY hEbase hYbase hEYG
    exact hGoff hGbase

  have hOppGY :
      HilbertOppositeSide Geo G Y base :=
    ⟨hGoff, hYoff, ⟨E, hGEY, hEbase⟩⟩

  have hOppYG :
      HilbertOppositeSide Geo Y G base :=
    hilbert_oppositeSide_symm
      Geo G Y base hOppGY

  have hGAsame :
      HilbertSameSide Geo G A base :=
    hilbert_sameSide_symm
      Geo A G base hAGsame

  have hOppYA :
      HilbertOppositeSide Geo Y A base :=
    hilbert_oppositeSide_transport_right
      Geo Y G A base hOppYG hGAsame

  rcases
      HilbertOrder.between_extension
        A B hAB
    with
    ⟨X, hABX⟩

  have hABXData :=
    HilbertOrder.between_incidence
      A B X hABX

  have hXBA :
      Geo.Between X B A :=
    hABXData.2.2.2.2

  have hABXcol :
      Collinear Geo A B X :=
    hABXData.2.2.2.1

  have hBXA :
      Collinear Geo B X A :=
    PrimCollinearCycle Geo A B X hABXcol

  have hBottom :=
    hilbert_between_outer_trans
      Geo B C E F hBCE hCEF

  have hBEF :
      Geo.Between B E F :=
    hBottom.1

  have hFEB :
      Geo.Between F E B :=
    (HilbertOrder.between_incidence
      B E F hBEF).2.2.2.2

  have hBCEData :=
    HilbertOrder.between_incidence
      B C E hBCE

  have hBE :
      Not (B = E) :=
    hBCEData.2.2.1

  have hEB :
      Not (E = B) := by
    intro h
    exact hBE h.symm

  have hEBY :
      Not (Collinear Geo E B Y) :=
    hilbert_not_collinear_of_off_line
      Geo E B Y base hEB hEbase hBbase hYoff

  have hYEB :
      Not (Collinear Geo Y E B) := by
    intro h
    exact hEBY (PrimCollinearCycle Geo Y E B h)

  have hRayBCE :
      HilbertSameRay Geo B C E :=
    hilbert_sameRay_of_between
      Geo B C E hBCE

  have hAtB :
      Geo.Angle A B C =
      Geo.Angle A B E :=
    hilbert_angle_eq_of_sameRay_second
      Geo B A C E hRayBCE

  have hAngle0 :
      Geo.AngleCongruent A B C G E F :=
    hTriangles.angleA

  have hABE_GEF :
      Geo.AngleCongruent A B E G E F := by
    unfold Geometry.Geo.AngleCongruent
      at hAngle0 ⊢
    rw [← hAtB]
    exact hAngle0

  have hEBA_GEF :
      Geo.AngleCongruent E B A G E F :=
    (Geo.angle_congruent_reverse_first
      A B E G E F).mp hABE_GEF

  have hGEF_EBA :
      Geo.AngleCongruent G E F E B A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo E B A G E F hEBA_GEF

  have hCorresponding :
      Geo.AngleCongruent F E G E B A :=
    (Geo.angle_congruent_reverse_first
      G E F E B A).mp hGEF_EBA

  have hYG_XA :
      Geo.Parallel Y G X A :=
    euclid_proposition_28_corresponding
      Geo Y G X A F E B base
      hYEG hXBA hFEB hEB hEbase hBbase hOppYA hYEB hCorresponding

  have hEG_XA :
      Geo.Parallel E G X A :=
    ParallelCollinearLeft
      Geo Y G E X A hEG hYG_XA hEYG

  have hXA_EG :
      Geo.Parallel X A E G :=
    ParallelSymmetry
      Geo E G X A hEG_XA

  have hBA_EG :
      Geo.Parallel B A E G :=
    ParallelCollinearLeft
      Geo X A B E G hBA hXA_EG hBXA

  have hAB_EG :
      Geo.Parallel A B E G :=
    ParallelSwapFirstLine
      Geo B A E G hBA_EG

  have hAB_GE :
      Geo.Parallel A B G E :=
    ParallelSwapSecondLine
      Geo A B E G hAB_EG

  have hAB_GE_congruent :
      Geo.Congruent A B G E :=
    CongruentReverseBoth
      Geo B A E G hTriangles.sideAB

  have hOnePair :
      OnePairParallelCongruent Geo A G E B :=
    { parallel := hAB_GE
      congruent := hAB_GE_congruent
      oriented := ⟨base, hBbase, hEbase, hAGsame⟩ }

  have hParallelogram :
      IsParallelogram Geo A G E B :=
    OnePairParallelCongruentCriterion
      Geo A G E B hOnePair

  have hAG_EB :
      Geo.Parallel A G E B :=
    hParallelogram.1

  have hEB_AG :
      Geo.Parallel E B A G :=
    ParallelSymmetry
      Geo A G E B hAG_EB

  have hBCEcol :
      Collinear Geo B C E :=
    hBCEData.2.2.2.1

  have hECB :
      Collinear Geo E C B :=
    PrimCollinearSymm
      Geo B C E hBCEcol

  have hEBC :
      Collinear Geo E B C :=
    PrimCollinearRotate
      Geo E C B hECB

  have hCB :
      Not (C = B) := by
    intro h
    exact hBC h.symm

  have hCEB :
      Collinear Geo C E B :=
    PrimCollinearCycle
      Geo B C E
      (PrimCollinearCycle Geo E B C hEBC)

  have hCB_AG :
      Geo.Parallel C B A G :=
    ParallelCollinearLeft
      Geo E B C A G hCB hEB_AG hCEB

  have hBC_AG :
      Geo.Parallel B C A G :=
    ParallelSwapFirstLine
      Geo C B A G hCB_AG

  have hAG_BC :
      Geo.Parallel A G B C :=
    ParallelSymmetry
      Geo B C A G hBC_AG

  exact ⟨G, hAGsame, hTriangles, hAG_BC⟩

/--
Euclid I.40.

Equal (equicomplementable) triangles which are on equal bases and on
the same side are also between the same parallels.

The bases `BC` and `EF` are laid out consecutively on the common line
`base` (`B-C-E`, `C-E-F`); this matches exactly the configuration used
by `euclid_proposition_38` for the converse direction.
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
  -- Carrier of the second base.
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
  -- SAS copy of ABC onto the second base, at E: gives G with
  -- AG || BC.
  --------------------------------------------------------------------

  rcases
      i40_copy_parallel
        Geo A B C E F base
        hBCE hCEF hBbase hCbase hEbase hFbase hBC_EF hAoff
    with
    ⟨G, hAGsame, hTriangles, hAG_BC⟩

  --------------------------------------------------------------------
  -- ABC is scissors-congruent to GEF.
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

  --------------------------------------------------------------------
  -- Transport the hypothesis: GEF is equicomplementable with DEF,
  -- and both now sit on the SAME base EF.
  --------------------------------------------------------------------

  have hGEF_DEF :
      HilbertScissorsEquicomplementable Geo
        (hilbertScissorsTriangle Geo G E F)
        (hilbertScissorsTriangle Geo D E F) :=
    equicomplementable_trans Geo hGEF_ABC hEqual

  --------------------------------------------------------------------
  -- G and D are on the same side of base.
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
      Not (E = F) :=
    (HilbertOrder.between_incidence
      C E F hCEF).2.1

  --------------------------------------------------------------------
  -- Euclid I.39 on the reduced, same-base configuration.
  --------------------------------------------------------------------

  rcases
      euclid_proposition_39
        Geo G E F D base
        hEF hEbase hFbase hGDsame hGEF_DEF
    with
    ⟨top, hGtop, hDtop, hTopDisjoint⟩

  --------------------------------------------------------------------
  -- The line through A and G is also disjoint from base, since
  -- AG || BC and B, C lie on base.
  --------------------------------------------------------------------

  have hAG :
      Not (A = G) :=
    hAG_BC.1

  rcases
      HilbertPlaneIncidence.line_through
        A G hAG
    with
    ⟨topAG, hAtopAG, hGtopAG⟩

  have hBC :
      Not (B = C) :=
    (HilbertOrder.between_incidence
      B C E hBCE).1

  have hTopAGDisjoint :
      HilbertLinesDisjoint Geo topAG base := by
    rintro ⟨X, hXtopAG, hXbase⟩
    have hXAG :
        X ∈ Geo.PointLine A G :=
      (hilbert_mem_pointLine_iff_onLine
        Geo A G X topAG hAG hAtopAG hGtopAG).mpr hXtopAG
    have hXBC :
        X ∈ Geo.PointLine B C :=
      (hilbert_mem_pointLine_iff_onLine
        Geo B C X base hBC hBbase hCbase).mpr hXbase
    exact
      Set.disjoint_left.mp hAG_BC.2.2 hXAG hXBC

  --------------------------------------------------------------------
  -- Two lines through G, both disjoint from base: by uniqueness of
  -- the parallel (HilbertEuclideanPlane IV) they coincide.
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

  exact ⟨top, hAtop, hDtop, hTopDisjoint⟩

end Geometry

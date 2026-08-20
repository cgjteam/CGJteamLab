import CGJteamLab.Proposition28
import CGJteamLab.Proposition37

namespace Geometry

universe u

variable (Geo : Geometry.Geo)

theorem i38_base_carrier
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C)
    (hBCE : Geo.Between B C E)
    (hCEF : Geo.Between C E F) :
    exists base : Geo.Line,
      HilbertIncidence.OnLine B base /\
      HilbertIncidence.OnLine C base /\
      HilbertIncidence.OnLine E base /\
      HilbertIncidence.OnLine F base /\
      HilbertSameSide Geo A D base := by

  rcases
      parallel_endpoints_sameSide
        Geo A D B C hAD_BC
    with
    ⟨base, hBbase, hCbase, hADsame⟩

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
      Geo
      B C E
      base
      hBC
      hBbase
      hCbase
      hBCEcol

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
      Geo
      C E F
      base
      hCE
      hCbase
      hEbase
      hCEFcol

  exact
    ⟨base,
      hBbase,
      hCbase,
      hEbase,
      hFbase,
      hADsame⟩

theorem i38_nondegenerate
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C)
    (hBCE : Geo.Between B C E)
    (hCEF : Geo.Between C E F) :
    Not (Collinear Geo A B C) /\
    Not (Collinear Geo D E F) := by

  rcases
      i38_base_carrier
        Geo A B C D E F
        hAD_BC hBCE hCEF
    with
    ⟨base,
      hBbase,
      hCbase,
      hEbase,
      hFbase,
      hADsame⟩

  have hAoff :
      Not (HilbertIncidence.OnLine A base) :=
    hADsame.1

  have hDoff :
      Not (HilbertIncidence.OnLine D base) :=
    hADsame.2.1

  --------------------------------------------------------------------
  -- ABC is noncollinear because B,C are on base and A is off base.
  --------------------------------------------------------------------

  have hBCEData :=
    HilbertOrder.between_incidence
      B C E hBCE

  have hBC :
      Not (B = C) :=
    hBCEData.1

  have hBCA :
      Not (Collinear Geo B C A) :=
    hilbert_not_collinear_of_off_line
      Geo
      B C A
      base
      hBC
      hBbase
      hCbase
      hAoff

  have hABC :
      Not (Collinear Geo A B C) := by
    intro h
    exact
      hBCA
        (PrimCollinearCycle
          Geo A B C h)

  --------------------------------------------------------------------
  -- DEF is noncollinear because E,F are on base and D is off base.
  --------------------------------------------------------------------

  have hCEFData :=
    HilbertOrder.between_incidence
      C E F hCEF

  have hEF :
      Not (E = F) :=
    hCEFData.2.1

  have hEFD :
      Not (Collinear Geo E F D) :=
    hilbert_not_collinear_of_off_line
      Geo
      E F D
      base
      hEF
      hEbase
      hFbase
      hDoff

  have hDEF :
      Not (Collinear Geo D E F) := by
    intro h
    exact
      hEFD
        (PrimCollinearCycle
          Geo D E F h)

  exact ⟨hABC, hDEF⟩

theorem i38_equal_base_copy
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C)
    (hBCE : Geo.Between B C E)
    (hCEF : Geo.Between C E F)
    (hBC_EF : Geo.Congruent B C E F) :
    exists base G,
      HilbertIncidence.OnLine B base /\
      HilbertIncidence.OnLine C base /\
      HilbertIncidence.OnLine E base /\
      HilbertIncidence.OnLine F base /\
      HilbertSameSide Geo A G base /\
      TriangleCongruenceResult
        Geo B A C E G F := by

  --------------------------------------------------------------------
  -- Common base carrier.
  --------------------------------------------------------------------

  rcases
      i38_base_carrier
        Geo A B C D E F
        hAD_BC hBCE hCEF
    with
    ⟨base,
      hBbase,
      hCbase,
      hEbase,
      hFbase,
      hADsame⟩

  have hAoff :
      Not (HilbertIncidence.OnLine A base) :=
    hADsame.1

  --------------------------------------------------------------------
  -- Nondegeneracy of ABC.
  --------------------------------------------------------------------

  rcases
      i38_nondegenerate
        Geo A B C D E F
        hAD_BC hBCE hCEF
    with
    ⟨hABC, _hDEF⟩

  --------------------------------------------------------------------
  -- E and F are distinct.
  --------------------------------------------------------------------

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

  --------------------------------------------------------------------
  -- Copy angle ABC at E.
  --
  -- The first target ray is EF, and the new ray is chosen
  -- on the side of base containing A.
  --------------------------------------------------------------------

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

  --------------------------------------------------------------------
  -- G0 is off the base, hence E != G0.
  --------------------------------------------------------------------

  have hEG0 :
      Not (E = G0) := by
    intro h
    subst G0
    exact hG0ASame.1 hEbase

  have hG0E :
      Not (G0 = E) := by
    intro h
    exact hEG0 h.symm

  --------------------------------------------------------------------
  -- Lay off EG ~= AB on the constructed ray EG0.
  --------------------------------------------------------------------

  rcases
      HilbertCongruence.segment_construction
        (Geo := Geo)
        A B
        E G0
        hEG0
    with
    ⟨G, hRayG0G, hEG_AB⟩

  --------------------------------------------------------------------
  -- The ray EG0 has its own carrier.
  --------------------------------------------------------------------

  rcases
      HilbertPlaneIncidence.line_through
        E G0 hEG0
    with
    ⟨rayLine, hEray, hG0ray⟩

  --------------------------------------------------------------------
  -- F cannot lie on rayLine.
  --
  -- Otherwise base and rayLine would both be the line EF,
  -- forcing G0 onto base.
  --------------------------------------------------------------------

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

  --------------------------------------------------------------------
  -- Moving from G0 to G on the same ray preserves the side of base.
  --------------------------------------------------------------------

  have hG0Gsame :
      HilbertSameSide Geo G0 G base :=
    hilbert_sameRay_points_sameSide
      Geo
      E G0
      G0 G
      F
      rayLine base
      hEray
      hG0ray
      hEbase
      hFbase
      hFray
      (hilbert_sameRay_refl
        Geo E G0 hG0E)
      hRayG0G

  have hAG0same :
      HilbertSameSide Geo A G0 base :=
    hilbert_sameSide_symm
      Geo G0 A base hG0ASame

  have hAGsame :
      HilbertSameSide Geo A G base :=
    hilbert_sameSide_trans
      Geo A G0 G base
      hAG0same
      hG0Gsame

  --------------------------------------------------------------------
  -- Replace G0 by G in the copied angle.
  --------------------------------------------------------------------

  have hAtE :
      Geo.Angle F E G0 =
      Geo.Angle F E G :=
    hilbert_angle_eq_of_sameRay_second
      Geo E F G0 G hRayG0G

  have hAngle :
      Geo.AngleCongruent
        A B C
        F E G := by

    unfold Geometry.Geo.AngleCongruent
      at hAngleG0 ⊢

    rw [← hAtE]

    exact hAngleG0

  --------------------------------------------------------------------
  -- Prepare SAS in the orientation
  --
  --     BAC  <->  EGF.
  --------------------------------------------------------------------

  have hBAC :
      Not (Collinear Geo B A C) := by
    intro h
    exact
      hABC
        (PrimCollinearSwap
          Geo B A C h)

  have hGoff :
      Not (HilbertIncidence.OnLine G base) :=
    hAGsame.2.1

  have hEFG :
      Not (Collinear Geo E F G) :=
    hilbert_not_collinear_of_off_line
      Geo
      E F G
      base
      hEF
      hEbase
      hFbase
      hGoff

  have hEGF :
      Not (Collinear Geo E G F) := by
    intro h
    exact
      hEFG
        (PrimCollinearRotate
          Geo E G F h)

  --------------------------------------------------------------------
  -- BA ~= EG.
  --------------------------------------------------------------------

  have hAB_EG :
      Geo.Congruent A B E G :=
    hilbert_congruent_symmetry
      Geo E G A B hEG_AB

  have hBA_EG :
      Geo.Congruent B A E G :=
    CongruentReverseFirst
      Geo A B E G hAB_EG

  --------------------------------------------------------------------
  -- Reverse the arms of the target angle:
  --
  --     angle FEG = angle GEF.
  --------------------------------------------------------------------

  have hAngleSAS :
      Geo.AngleCongruent
        A B C
        G E F :=
    (Geo.angle_congruent_reverse_second
      A B C F E G).mp hAngle

  --------------------------------------------------------------------
  -- SAS.
  --------------------------------------------------------------------

  have hTriangles :
      TriangleCongruenceResult
        Geo B A C
        E G F :=
    SAS
      Geo
      B A C
      E G F
      hBAC
      hEGF
      hBA_EG
      hAngleSAS
      hBC_EF

  exact
    ⟨base, G,
      hBbase,
      hCbase,
      hEbase,
      hFbase,
      hAGsame,
      hTriangles⟩

theorem i38_copy_parallelogram
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C)
    (hBCE : Geo.Between B C E)
    (hCEF : Geo.Between C E F)
    (hBC_EF : Geo.Congruent B C E F) :
    exists G : Geo.Point,
      IsParallelogram Geo A G E B /\
      TriangleCongruenceResult
        Geo B A C E G F := by

  --------------------------------------------------------------------
  -- Construct the congruent copy BAC -> EGF.
  --------------------------------------------------------------------

  rcases
      i38_equal_base_copy
        Geo A B C D E F
        hAD_BC hBCE hCEF hBC_EF
    with
    ⟨base, G,
      hBbase,
      hCbase,
      hEbase,
      hFbase,
      hAGsame,
      hTriangles⟩

  have hGoff :
      Not (HilbertIncidence.OnLine G base) :=
    hAGsame.2.1

  --------------------------------------------------------------------
  -- Nondegeneracy of ABC gives A != B.
  --------------------------------------------------------------------

  rcases
      i38_nondegenerate
        Geo A B C D E F
        hAD_BC hBCE hCEF
    with
    ⟨hABC, _hDEF⟩

  have hAB :
      Not (A = B) :=
    hilbert_noncollinear_ne_first
      Geo A B C hABC

  have hBA :
      Not (B = A) := by
    intro h
    exact hAB h.symm

  --------------------------------------------------------------------
  -- E != G.
  --------------------------------------------------------------------

  have hGE :
      Not (G = E) := by
    intro h
    subst G
    exact hGoff hEbase

  have hEG :
      Not (E = G) := by
    intro h
    exact hGE h.symm

  --------------------------------------------------------------------
  -- Extend GE through E:
  --
  --     G-E-Y.
  --
  -- Thus Y lies on the side of base opposite G.
  --------------------------------------------------------------------

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
    PrimCollinearCycle
      Geo G E Y hGEYcol

  --------------------------------------------------------------------
  -- Y is off base.
  --------------------------------------------------------------------

  have hYoff :
      Not (HilbertIncidence.OnLine Y base) := by

    intro hYbase

    have hGbase :
        HilbertIncidence.OnLine G base :=
      hilbert_collinear_on_line
        Geo
        E Y G
        base
        hEY
        hEbase
        hYbase
        hEYG

    exact hGoff hGbase

  --------------------------------------------------------------------
  -- G and Y are on opposite sides of base because G-E-Y.
  --------------------------------------------------------------------

  have hOppGY :
      HilbertOppositeSide Geo G Y base :=
    ⟨hGoff,
      hYoff,
      ⟨E, hGEY, hEbase⟩⟩

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
      Geo
      Y G A
      base
      hOppYG
      hGAsame

  --------------------------------------------------------------------
  -- Extend AB through B:
  --
  --     A-B-X.
  --------------------------------------------------------------------

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
    PrimCollinearCycle
      Geo A B X hABXcol

  --------------------------------------------------------------------
  -- Bottom order:
  --
  --     B-C-E-F
  --
  -- gives B-E-F, hence F-E-B.
  --------------------------------------------------------------------

  have hBottom :=
    hilbert_between_outer_trans
      Geo
      B C E F
      hBCE
      hCEF

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

  --------------------------------------------------------------------
  -- Y,E,B are noncollinear: E,B lie on base and Y is off base.
  --------------------------------------------------------------------

  have hEBY :
      Not (Collinear Geo E B Y) :=
    hilbert_not_collinear_of_off_line
      Geo
      E B Y
      base
      hEB
      hEbase
      hBbase
      hYoff

  have hYEB :
      Not (Collinear Geo Y E B) := by
    intro h
    exact
      hEBY
        (PrimCollinearCycle
          Geo Y E B h)

  --------------------------------------------------------------------
  -- Replace ray BC by ray BE in angle ABC.
  --------------------------------------------------------------------

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
      Geo.AngleCongruent
        A B C
        G E F :=
    hTriangles.angleA

  have hABE_GEF :
      Geo.AngleCongruent
        A B E
        G E F := by

    unfold Geometry.Geo.AngleCongruent
      at hAngle0 ⊢

    rw [← hAtB]

    exact hAngle0

  --------------------------------------------------------------------
  -- Reorient the two unordered angles to the form required by I.28:
  --
  --     angle FEG ~= angle EBA.
  --------------------------------------------------------------------

  have hEBA_GEF :
      Geo.AngleCongruent
        E B A
        G E F :=
    (Geo.angle_congruent_reverse_first
      A B E G E F).mp hABE_GEF

  have hGEF_EBA :
      Geo.AngleCongruent
        G E F
        E B A :=
    Geometry.Geo.angle_congruent_symmetry
      Geo
      E B A
      G E F
      hEBA_GEF

  have hCorresponding :
      Geo.AngleCongruent
        F E G
        E B A :=
    (Geo.angle_congruent_reverse_first
      G E F E B A).mp hGEF_EBA

  --------------------------------------------------------------------
  -- Euclid I.28, corresponding-angle form.
  --
  -- First line:  Y-E-G
  -- Second line: X-B-A
  -- Transversal: F-E-B
  --------------------------------------------------------------------

  have hYG_XA :
      Geo.Parallel Y G X A :=
    euclid_proposition_28_corresponding
      Geo
      Y G
      X A
      F E B
      base
      hYEG
      hXBA
      hFEB
      hEB
      hEbase
      hBbase
      hOppYA
      hYEB
      hCorresponding

  --------------------------------------------------------------------
  -- Transport YG to EG.
  --------------------------------------------------------------------

  have hEG_XA :
      Geo.Parallel E G X A :=
    ParallelCollinearLeft
      Geo
      Y G E
      X A
      hEG
      hYG_XA
      hEYG

  --------------------------------------------------------------------
  -- Transport XA to BA.
  --------------------------------------------------------------------

  have hXA_EG :
      Geo.Parallel X A E G :=
    ParallelSymmetry
      Geo E G X A hEG_XA

  have hBA_EG :
      Geo.Parallel B A E G :=
    ParallelCollinearLeft
      Geo
      X A B
      E G
      hBA
      hXA_EG
      hBXA

  have hAB_EG :
      Geo.Parallel A B E G :=
    ParallelSwapFirstLine
      Geo B A E G hBA_EG

  have hAB_GE :
      Geo.Parallel A B G E :=
    ParallelSwapSecondLine
      Geo A B E G hAB_EG

  --------------------------------------------------------------------
  -- Triangle congruence gives BA ~= EG, hence AB ~= GE.
  --------------------------------------------------------------------

  have hAB_GE_congruent :
      Geo.Congruent A B G E :=
    CongruentReverseBoth
      Geo
      B A
      E G
      hTriangles.sideAB

  --------------------------------------------------------------------
  -- One oriented pair of opposite equal parallel sides:
  --
  --     AB || GE
  --     AB ~= GE
  --     A,G on the same side of BE.
  --
  -- Therefore A-G-E-B is a parallelogram.
  --------------------------------------------------------------------

  have hOnePair :
      OnePairParallelCongruent
        Geo A G E B :=
    {
      parallel := hAB_GE
      congruent := hAB_GE_congruent
      oriented :=
        ⟨base,
          hBbase,
          hEbase,
          hAGsame⟩
    }

  have hParallelogram :
      IsParallelogram Geo A G E B :=
    OnePairParallelCongruentCriterion
      Geo A G E B hOnePair

  exact
    ⟨G,
      hParallelogram,
      hTriangles⟩

theorem i38_copy_upper_position
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C)
    (hBCE : Geo.Between B C E)
    (hCEF : Geo.Between C E F)
    (hBC_EF : Geo.Congruent B C E F) :
    exists G : Geo.Point,
      TriangleCongruenceResult
        Geo B A C E G F /\
      (G = D \/ Geo.Parallel G D E F) := by

  --------------------------------------------------------------------
  -- The copy constructed above gives the parallelogram A-G-E-B.
  --------------------------------------------------------------------

  rcases
      i38_copy_parallelogram
        Geo A B C D E F
        hAD_BC hBCE hCEF hBC_EF
    with
    ⟨G, hAGEB, hTriangles⟩

  --------------------------------------------------------------------
  -- AG || EB.
  --------------------------------------------------------------------

  have hAG_EB :
      Geo.Parallel A G E B :=
    hAGEB.1

  --------------------------------------------------------------------
  -- Transport EB to BC using B-C-E.
  --------------------------------------------------------------------

  have hBCEData :=
    HilbertOrder.between_incidence
      B C E hBCE

  have hBC :
      Not (B = C) :=
    hBCEData.1

  have hCE :
      Not (C = E) :=
    hBCEData.2.1

  have hEC :
      Not (E = C) := by
    intro h
    exact hCE h.symm

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

  have hEB_AG :
      Geo.Parallel E B A G :=
    ParallelSymmetry
      Geo A G E B hAG_EB

  have hCB :
      Not (C = B) := by
    intro h
    exact hBC h.symm

  have hCEB :
      Collinear Geo C E B :=
    PrimCollinearCycle
      Geo B C E
      (PrimCollinearCycle
        Geo E B C hEBC)

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

  --------------------------------------------------------------------
  -- AG and AD are both parallel to BC.
  --
  -- They cannot be distinct point-lines, since both contain A.
  --------------------------------------------------------------------

  have hTopEq :
      Geo.PointLine A G =
      Geo.PointLine A D := by

    by_contra hDistinct

    have hAG_AD :
        Geo.Parallel A G A D :=
      hilbert_parallel_transitive_distinct
        Geo
        A G
        A D
        B C
        hAG_BC
        hAD_BC
        hDistinct

    have hA_AG :
        A ∈ Geo.PointLine A G := by
      change Geometry.Geo.LineCollinear Geo A G A
      exact Or.inr (Or.inl rfl)

    have hA_AD :
        A ∈ Geo.PointLine A D := by
      change Geometry.Geo.LineCollinear Geo A D A
      exact Or.inr (Or.inl rfl)

    exact
      Set.disjoint_left.mp
        hAG_AD.2.2
        hA_AG
        hA_AD

  --------------------------------------------------------------------
  -- Hence G,A,D are collinear.
  --------------------------------------------------------------------

  have hAD :
      Not (A = D) :=
    hAD_BC.1

  rcases
      HilbertPlaneIncidence.line_through
        A D hAD
    with
    ⟨top, hAtop, hDtop⟩

  have hG_AG :
      G ∈ Geo.PointLine A G := by
    change Geometry.Geo.LineCollinear Geo A G G
    exact Or.inr (Or.inr (Or.inl rfl))

  rw [hTopEq] at hG_AG

  have hGtop :
      HilbertIncidence.OnLine G top :=
    (hilbert_mem_pointLine_iff_onLine
      Geo
      A D G
      top
      hAD
      hAtop
      hDtop).mp hG_AG

  have hGAD :
      Collinear Geo G A D :=
    ⟨top, hGtop, hAtop, hDtop⟩

  --------------------------------------------------------------------
  -- If G = D, the copied triangle is already DEF.
  --------------------------------------------------------------------

  by_cases hGD :
      G = D

  · exact
      ⟨G,
        hTriangles,
        Or.inl hGD⟩

  --------------------------------------------------------------------
  -- Otherwise transport AD || BC to GD || BC.
  --------------------------------------------------------------------

  · have hGD_BC :
        Geo.Parallel G D B C :=
      ParallelCollinearLeft
        Geo
        A D G
        B C
        hGD
        hAD_BC
        hGAD

    ------------------------------------------------------------------
    -- Transport the bottom carrier BC to EF.
    ------------------------------------------------------------------

    have hBC_GD :
        Geo.Parallel B C G D :=
      ParallelSymmetry
        Geo G D B C hGD_BC

    have hEC_GD :
        Geo.Parallel E C G D :=
      ParallelCollinearLeft
        Geo
        B C E
        G D
        hEC
        hBC_GD
        hEBC

    have hCEFData :=
      HilbertOrder.between_incidence
        C E F hCEF

    have hEF :
        Not (E = F) :=
      hCEFData.2.1

    have hCEFcol :
        Collinear Geo C E F :=
      hCEFData.2.2.2.1

    have hEFC :
        Collinear Geo E F C :=
      PrimCollinearCycle
        Geo C E F hCEFcol

    have hEF_GD :
        Geo.Parallel E F G D :=
      collinear_parallel_trans
        Geo
        E F C
        G D
        hEF
        hEFC
        hEC_GD

    have hGD_EF :
        Geo.Parallel G D E F :=
      ParallelSymmetry
        Geo E F G D hEF_GD

    exact
      ⟨G,
        hTriangles,
        Or.inr hGD_EF⟩

/--
Euclid I.38.

Triangles on equal bases and between the same parallels are
equicomplementable.
-/
theorem euclid_proposition_38
    [HilbertIncidence Geo]
    [HilbertEuclideanPlane Geo]
    (A B C D E F : Geo.Point)
    (hAD_BC : Geo.Parallel A D B C)
    (hBCE : Geo.Between B C E)
    (hCEF : Geo.Between C E F)
    (hBC_EF : Geo.Congruent B C E F) :
    HilbertScissorsEquicomplementable Geo
      (hilbertScissorsTriangle Geo A B C)
      (hilbertScissorsTriangle Geo D E F) := by

  --------------------------------------------------------------------
  -- Construct G so that BAC is congruent to EGF and either
  -- G = D or GD || EF.
  --------------------------------------------------------------------

  rcases
      i38_copy_upper_position
        Geo A B C D E F
        hAD_BC hBCE hCEF hBC_EF
    with
    ⟨G, hTriangles, hPosition⟩

  --------------------------------------------------------------------
  -- Triangle congruence gives a scissors equivalence
  --
  --     ABC = GEF.
  --
  -- The SAS result is stored as
  --
  --     BAC ~= EGF,
  --
  -- so only unordered-triangle representation has to be normalized.
  --------------------------------------------------------------------

  have hCopy0 :
      HilbertScissorsEq Geo
        (hilbertScissorsTriangle Geo B A C)
        (hilbertScissorsTriangle Geo E G F) :=
    scissors_congruent
      Geo
      B A C
      E G F
      hTriangles

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
    equicomplementable_of_scissorsEq
      Geo hCopy

  --------------------------------------------------------------------
  -- Either the copied upper vertex already is D...
  --------------------------------------------------------------------

  rcases hPosition with hGD | hGD_EF

  · subst D
    exact hABC_GEF

  --------------------------------------------------------------------
  -- ...or GEF and DEF are on the same base EF and between
  -- the same parallels.  This is exactly Euclid I.37.
  --------------------------------------------------------------------

  · have hGEF_DEF :
        HilbertScissorsEquicomplementable Geo
          (hilbertScissorsTriangle Geo G E F)
          (hilbertScissorsTriangle Geo D E F) :=
      euclid_proposition_37
        Geo
        G E F D
        hGD_EF

    exact
      equicomplementable_trans
        Geo
        hABC_GEF
        hGEF_DEF

end Geometry
